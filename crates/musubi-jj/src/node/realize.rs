//! Realizing the hive's canonical operations here as local ones, writing them, and
//! advancing the op heads to them.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::sync::Arc;
use std::thread;

use futures::TryStreamExt as _;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::op_walk;
use jj_lib::operation::Operation;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use pollster::FutureExt as _;

use super::CANONICAL_ATTRIBUTE;
use super::NodeError;
use super::NodeRepo;
use super::catch_jj_panic;
use super::git::Colocation;
use super::translate::target_of;
use super::view::LocalView;
use super::view::PerMachine;
use crate::workspaces;

/// How many realized operations may be written at once. jj's op store syncs each file it
/// writes to disk, which takes milliseconds on a cloud disk, so realizing many operations
/// one write at a time mostly waits.
const MAX_UNWRITTEN: usize = 32;

/// How many operations, each the only parent of the next, have their views made local at
/// once (see [`NodeRepo::realize_pending`]).
pub const REALIZE_AT_ONCE: usize = MAX_UNWRITTEN;

/// A realized operation being written, and the canonical operation it realizes.
pub(super) struct Unwritten {
    write: thread::JoinHandle<Result<(), NodeError>>,
    local: OperationId,
    canonical: OperationId,
}

/// A realized operation, not yet written.
struct Realization {
    id: OperationId,
    op: StoreOperation,
    view: View,
    per_machine: Arc<PerMachine>,
}

impl NodeRepo {
    /// Realizes a stored canonical operation, and any unrealized ancestors, without
    /// publishing it. Returns the local operation id.
    pub fn realize(&mut self, canonical: &OperationId) -> Result<OperationId, NodeError> {
        let local = self.realize_pending(canonical, &[])?;
        self.settle()?;
        Ok(local)
    }

    /// [`Self::realize`], leaving the realizations to be written meanwhile: the store may
    /// lack them until [`Self::settle`], which [`Self::realize`], [`Self::advance`] and
    /// dropping this call, and so must anything else that reads them before then.
    /// [`Self::local_of`] knows them at once.
    ///
    /// `next` are the operations likely realized after this one, in order. Making a view
    /// local is most of realizing an operation, and it takes several at once to keep up with
    /// writing them, so the views of the operations that follow on, from this one's
    /// unrealized ancestors and then `next`, each with the one before as its only parent and
    /// so inheriting the same per-machine fields, are made with this one's, in parallel, and
    /// kept until they are realized.
    pub fn realize_pending(
        &mut self,
        canonical: &OperationId,
        next: &[OperationId],
    ) -> Result<OperationId, NodeError> {
        // Map everything reachable from the op heads first. Otherwise, after losing the
        // translation cache, an operation that already has a reachable realization would be
        // realized again, and two reachable local operations would share a canonical form.
        if !self.heads_mapped {
            self.canonical_heads()?;
            self.heads_mapped = true;
        }
        let order = self.unrealized(canonical)?;
        for (i, (id, op)) in order.iter().enumerate() {
            let parents: Vec<OperationId> = op
                .parents
                .iter()
                .map(|parent| self.local_of(parent).expect("parents realized first"))
                .collect();
            // Realizing it reads its parents from the store, unless its only parent is the
            // operation realized last.
            if !matches!(
                (parents.as_slice(), &self.last_realized),
                ([parent], Some((last, _))) if parent == last
            ) {
                self.settle()?;
            }
            let per_machine = self.inherited_per_machine(&parents)?;
            let prepared = match &mut self.prepared {
                Some((inherited, views)) if Arc::ptr_eq(inherited, &per_machine) => {
                    views.remove(id)
                }
                _ => None,
            };
            let view = match prepared {
                Some(view) => view,
                None => {
                    let later = order[i + 1..].iter().map(|(id, _)| id).chain(next);
                    let run = self.run_after(id, op, later)?;
                    // So that the threads making views each find the presence before theirs
                    // remembered, rather than each reading the history below it.
                    self.presence(id)?;
                    let mut views = self.local_views(&run, &per_machine).into_iter();
                    let view = views
                        .next()
                        .expect("a run starts with its first operation")?;
                    // One that failed is made again when its turn comes.
                    let ahead = run[1..]
                        .iter()
                        .zip(views)
                        .filter_map(|((id, _), view)| Some((id.clone(), view.ok()?)))
                        .collect();
                    self.prepared = Some((per_machine.clone(), ahead));
                    view
                }
            };
            let view = self.with_own_workspaces(id, op, &parents, view)?;
            let own = self.own_of(&view);
            let realization = self.realize_one(id, op, parents, view, per_machine)?;
            self.last_own = Some((realization.id.clone(), Arc::new(own)));
            self.write_later(realization, id.clone())?;
        }
        Ok(self.local_of(canonical).expect("realized above"))
    }

    /// `first`, and the stored, unrealized operations of `later` that follow it, each with
    /// the one before as its only parent, up to [`REALIZE_AT_ONCE`] in all.
    fn run_after<'a>(
        &self,
        first: &OperationId,
        op: &StoreOperation,
        later: impl Iterator<Item = &'a OperationId>,
    ) -> Result<Vec<(OperationId, StoreOperation)>, NodeError> {
        let mut run = vec![(first.clone(), op.clone())];
        for id in later.take(REALIZE_AT_ONCE - 1) {
            if !self.canonical.has_operation(id) || self.local_of(id).is_some() {
                break;
            }
            let op = self.canonical.read_operation(id)?;
            let (last, _) = run.last().expect("a run is never empty");
            if op.parents != std::slice::from_ref(last) {
                break;
            }
            run.push((id.clone(), op));
        }
        Ok(run)
    }

    /// The canonical operations to realize for `canonical`: it and its unrealized ancestors,
    /// parents first, each with its stored form.
    fn unrealized(
        &self,
        canonical: &OperationId,
    ) -> Result<Vec<(OperationId, StoreOperation)>, NodeError> {
        let mut order = vec![];
        let mut ordered = HashSet::new();
        let mut stack: Vec<(OperationId, Option<StoreOperation>)> = vec![(canonical.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if self.local_of(&id).is_some() || ordered.contains(&id) {
                continue;
            }
            if !self.canonical.has_operation(&id) {
                return Err(NodeError::NotRealizable(id.hex(), "operation not stored"));
            }
            let op = match loaded {
                Some(op) => op,
                None => self.canonical.read_operation(&id)?,
            };
            let missing: Vec<_> = op
                .parents
                .iter()
                .filter(|p| self.local_of(p).is_none() && !ordered.contains(*p))
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.push((id, Some(op)));
                stack.extend(missing.into_iter().map(|parent| (parent, None)));
                continue;
            }
            ordered.insert(id.clone());
            order.push((id, op));
        }
        Ok(order)
    }

    /// The local views of `ops`, which all inherit `per_machine`, made in parallel.
    fn local_views(
        &self,
        ops: &[(OperationId, StoreOperation)],
        per_machine: &PerMachine,
    ) -> Vec<Result<LocalView, NodeError>> {
        let make = |part: &[(OperationId, StoreOperation)]| -> Vec<_> {
            part.iter()
                .map(|(id, op)| self.local_view(id, op, per_machine))
                .collect()
        };
        if ops.len() == 1 {
            return make(ops);
        }
        let threads = thread::available_parallelism().map_or(1, |n| n.get());
        thread::scope(|scope| {
            let parts: Vec<_> = ops
                .chunks(ops.len().div_ceil(threads))
                .map(|part| {
                    let made = thread::Builder::new()
                        .name("make views local".to_owned())
                        .spawn_scoped(scope, move || make(part));
                    (part, made)
                })
                .collect();
            let mut views = Vec::with_capacity(ops.len());
            for (part, made) in parts {
                views.extend(match made {
                    Ok(made) => made
                        .join()
                        .unwrap_or_else(|panic| std::panic::resume_unwind(panic)),
                    // No thread to spare: here, then.
                    Err(_) => make(part),
                });
            }
            views
        })
    }

    /// Starts writing a realization, after waiting for those being written if there are
    /// already enough of them.
    fn write_later(
        &mut self,
        realization: Realization,
        canonical: OperationId,
    ) -> Result<(), NodeError> {
        if self.unwritten.len() >= MAX_UNWRITTEN {
            self.settle()?;
        }
        let Realization {
            id,
            op,
            view,
            per_machine,
        } = realization;
        let store = self.loader.op_store().clone();
        let expected = id.clone();
        let write = thread::Builder::new()
            .name("write operation".to_owned())
            .spawn(move || {
                let view_id = store.write_view(&view).block_on()?;
                let written = store.write_operation(&op).block_on()?;
                if view_id != op.view_id || written != expected {
                    return Err(NodeError::MisnamedWrite(expected.hex()));
                }
                Ok(())
            })
            .map_err(|source| NodeError::Io {
                path: self.repo_path.join("op_store"),
                source,
            })?;
        self.map.insert_unwritten(id.clone(), canonical.clone());
        self.last_realized = Some((id.clone(), per_machine));
        self.unwritten.push(Unwritten {
            write,
            local: id,
            canonical,
        });
        Ok(())
    }

    /// Waits for the realizations being written, then records them in the translation
    /// map's file. If any write failed, the map forgets them all: a later realization may
    /// refer to the failed one, and realizing them again writes the same operations.
    pub fn settle(&mut self) -> Result<(), NodeError> {
        let unwritten = std::mem::take(&mut self.unwritten);
        let mut failed = None;
        let mut panicked = None;
        let mut translations = vec![];
        for Unwritten {
            write,
            local,
            canonical,
        } in unwritten
        {
            match write.join() {
                Ok(Ok(())) => {}
                Ok(Err(err)) => {
                    failed.get_or_insert(err);
                }
                Err(panic) => {
                    panicked.get_or_insert(panic);
                }
            }
            translations.push((local, canonical));
        }
        if let Some(panic) = panicked {
            for (local, canonical) in &translations {
                self.map.forget(local, canonical);
            }
            self.last_realized = None;
            self.last_own = None;
            self.prepared = None;
            std::panic::resume_unwind(panic);
        }
        if let Some(err) = failed {
            for (local, canonical) in &translations {
                self.map.forget(local, canonical);
            }
            self.last_realized = None;
            self.last_own = None;
            self.prepared = None;
            return Err(err);
        }
        for (local, canonical) in &translations {
            self.map
                .write(local, canonical)
                .map_err(|source| NodeError::Io {
                    path: self.repo_path.join("musubi/translation"),
                    source,
                })?;
        }
        Ok(())
    }

    /// For tests of crashes: waits for the realizations being written, then, as a crash
    /// before [`Self::settle`] would, records none of them, and forgets them as if their
    /// writes had failed. Returns their local ids.
    pub fn crash_before_settling(&mut self) -> Vec<OperationId> {
        let mut locals = vec![];
        for Unwritten {
            write,
            local,
            canonical,
        } in std::mem::take(&mut self.unwritten)
        {
            // Whether it wrote everything or failed, a crash would leave it unrecorded.
            drop(write.join());
            self.map.forget(&local, &canonical);
            locals.push(local);
        }
        self.last_realized = None;
        self.last_own = None;
        self.prepared = None;
        locals
    }

    /// `local`, the local view of canonical operation `canonical_id`, with this machine's own
    /// workspaces if the hive has forgotten this machine there: as the realization of its
    /// parent with the machine's latest work has them (`latest_work_parent`), following the
    /// operation's rewrites. They are still its working copies, and the hive shows them again
    /// with its next work. A view that has this machine's workspaces, or where it is present
    /// without any, is left as it is.
    fn with_own_workspaces(
        &mut self,
        canonical_id: &OperationId,
        op: &StoreOperation,
        parents: &[OperationId],
        local: LocalView,
    ) -> Result<LocalView, NodeError> {
        if local.names.keys().any(|key| self.is_own_key(key)) {
            return Ok(local);
        }
        let source = self.latest_work_parent(&op.parents)?;
        let mut own = match (parents.get(source), &self.last_own) {
            (None, _) => return Ok(local),
            (Some(parent), Some((last, own))) if parent == last => (**own).clone(),
            (Some(parent), _) => {
                // It may still be being written.
                self.settle()?;
                let op_store = self.loader.op_store();
                let parent_view = op_store
                    .read_view(&op_store.read_operation(parent).block_on()?.view_id)
                    .block_on()?;
                let parent_canonical = self.canonical_of(parent).expect("parents realized first");
                self.own_of_view(parent_view.wc_commit_ids, &parent_canonical)?
            }
        };
        if own.is_empty() || self.presence(canonical_id)?.is_present(self.machine.key()) {
            return Ok(local);
        }
        workspaces::follow_rewrites(&mut own, op.commit_predecessors.as_ref());
        let LocalView {
            mut view, names, ..
        } = local;
        let shown: HashSet<&WorkspaceNameBuf> = names.values().collect();
        for (name, commit) in own {
            if !shown.contains(&name) {
                view.wc_commit_ids.insert(name, commit);
            }
        }
        // The id the op store gives it, worked out as it does.
        let id = jj_lib::op_store::ViewId::new(blake2b_hash(&view).to_vec());
        Ok(LocalView { view, id, names })
    }

    /// Which of a canonical operation's parents has this machine's latest work in its history:
    /// one whose history has every other's (`Presence::worked`), so that a merge of a forget
    /// that saw the machine's latest work with an operation that saw only earlier work keeps
    /// the machine's workspaces as they are now. The first, if they agree or none has all.
    fn latest_work_parent(&self, parents: &[OperationId]) -> Result<usize, NodeError> {
        if parents.len() < 2 {
            return Ok(0);
        }
        let key = self.machine.key();
        let worked: Vec<BTreeSet<OperationId>> = parents
            .iter()
            .map(|parent| {
                Ok(self
                    .presence(parent)?
                    .worked(key)
                    .cloned()
                    .unwrap_or_default())
            })
            .collect::<Result<_, NodeError>>()?;
        if worked.iter().all(|ops| *ops == worked[0]) {
            return Ok(0);
        }
        'parents: for (index, mine) in worked.iter().enumerate() {
            for theirs in &worked {
                for op in theirs.difference(mine) {
                    let mut seen = false;
                    for later in mine {
                        if self.canonical.is_ancestor_of(op, later)? {
                            seen = true;
                            break;
                        }
                    }
                    if !seen {
                        continue 'parents;
                    }
                }
            }
            return Ok(index);
        }
        Ok(0)
    }

    /// This machine's own workspaces in a local view: every one but those named for another
    /// machine's.
    fn own_of(&self, local: &LocalView) -> BTreeMap<WorkspaceNameBuf, jj_lib::backend::CommitId> {
        let others: HashSet<&WorkspaceNameBuf> = local
            .names
            .iter()
            .filter(|(key, _)| !self.is_own_key(key))
            .map(|(_, name)| name)
            .collect();
        local
            .view
            .wc_commit_ids
            .iter()
            .filter(|(name, _)| !others.contains(name))
            .map(|(name, commit)| (name.clone(), commit.clone()))
            .collect()
    }

    /// Realizes one canonical operation whose parents are realized, as `parents`, without
    /// writing it, from its local view.
    fn realize_one(
        &self,
        canonical_id: &OperationId,
        op: &StoreOperation,
        parents: Vec<OperationId>,
        local: LocalView,
        per_machine: Arc<PerMachine>,
    ) -> Result<Realization, NodeError> {
        let LocalView { view, id, names } = local;
        let mut metadata = op.metadata.clone();
        if let Some((prefix, target)) = target_of(&metadata.description)
            && self.canonical.is_ancestor(&target, &op.parents)?
        {
            let local = self.local_of(&target).expect("ancestors realized first");
            metadata.description = format!("{prefix}{}", local.hex());
        }
        metadata.workspace_name = metadata
            .workspace_name
            .map(|key| self.realized_workspace_name(&key, &names));
        metadata
            .attributes
            .insert(CANONICAL_ATTRIBUTE.to_owned(), canonical_id.hex());
        // The id the op store gives it, worked out as it does.
        let local_op = StoreOperation {
            view_id: id,
            parents,
            metadata,
            commit_predecessors: op.commit_predecessors.clone(),
        };
        Ok(Realization {
            id: OperationId::new(blake2b_hash(&local_op).to_vec()),
            op: local_op,
            per_machine,
            view,
        })
    }

    /// The local name of the workspace that made a canonical operation, as the operation's
    /// view names it: `default` for this machine's own, `beta/default` for another's. jj's
    /// `undo` and `redo` refuse to undo another workspace's operation, and they tell
    /// workspaces apart only by name, so with the plain name `jj undo` here would undo
    /// beta's latest operation as if it were this machine's own.
    fn realized_workspace_name(
        &self,
        key: &WorkspaceName,
        names: &BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>,
    ) -> WorkspaceNameBuf {
        if let Some(name) = names.get(key) {
            return name.clone();
        }
        match workspaces::split_key(key.as_str()) {
            Some((machine, workspace)) if machine == self.machine.key() => workspace.into(),
            // A workspace the operation forgot, so its view doesn't name it.
            Some((machine, workspace)) => {
                format!("{}/{workspace}", workspaces::machine_name(machine)).into()
            }
            None => key.to_owned(),
        }
    }

    /// The per-machine fields a realization starts from: its parent's, or for a merge, the
    /// parents' merged three-way as jj merges them, as a local merge of the same operations
    /// would.
    fn inherited_per_machine(&self, parents: &[OperationId]) -> Result<Arc<PerMachine>, NodeError> {
        if let ([parent], Some((last, per_machine))) = (parents, &self.last_realized)
            && parent == last
        {
            return Ok(per_machine.clone());
        }
        let (first, rest) = parents.split_first().expect("operations have parents");
        let first_op = self.loader.load_operation(first).block_on()?;
        if rest.is_empty() {
            return Ok(Arc::new(fields_of(&first_op)?));
        }
        // jj's merge loads each parent's repository, and so its index, which for a join
        // operation, whose only ancestor is the root, means indexing all its commits anew: a
        // second or more for a large repository. Usually it isn't needed.
        if let Some(merged) = self.merged_trivially(&first_op, rest)? {
            debug_assert_eq!(*merged, *merged_by_jj(&self.loader, first_op, rest)?);
            return Ok(merged);
        }
        merged_by_jj(&self.loader, first_op, rest)
    }

    /// The per-machine fields of `first_op` and `rest` merged three-way, if at most one of
    /// them differs from its base, which the merge then takes: another machine's join
    /// operation's are its base's, the root's, as, usually, are those of other machines'
    /// operations. `None` where jj's merge must decide (`PerMachine::merged_trivially`), or
    /// where a merge has several bases.
    fn merged_trivially(
        &self,
        first_op: &Operation,
        rest: &[OperationId],
    ) -> Result<Option<Arc<PerMachine>>, NodeError> {
        let mut merged = fields_of(first_op)?;
        let mut ops = vec![first_op.clone()];
        for other in rest {
            let other_op = self.loader.load_operation(other).block_on()?;
            // Several bases would need jj's merge of them, which costs what this saves.
            let Some(base) = single_base(&self.loader, &ops, &other_op)? else {
                return Ok(None);
            };
            let (base, theirs) = (fields_of(&base)?, fields_of(&other_op)?);
            match PerMachine::merged_trivially(&base, merged, theirs) {
                Some(next) => merged = next,
                None => return Ok(None),
            }
            ops.push(other_op);
        }
        Ok(Some(Arc::new(merged)))
    }

    /// Realizes a canonical operation and publishes it as an op head, in place of the op
    /// heads it descends from (heads := max(heads ∪ {op})). In a colocated
    /// repository the realization first exports its refs to `.git`, holding jj's colocated
    /// import/export lock, so that no `jj` command sees the operation before `.git` matches
    /// it.
    pub fn advance(&mut self, canonical: &OperationId) -> Result<OperationId, NodeError> {
        let realized = self.realize(canonical)?;
        // Views made ahead inherit what this changes, in a colocated repository.
        self.prepared = None;
        let superseded = self.check_mergeable(&realized)?;
        let colocation = self.colocation();
        let _lock = colocation.map(Colocation::lock).transpose()?;
        let head = match colocation {
            Some(colocation) => {
                let exported = colocation
                    .export_refs(&self.loader, &realized, &|op| self.is_join_point(op))?;
                self.insert_map(exported.clone(), canonical.clone())?;
                exported
            }
            None => realized,
        };
        // The new head replaces those it descends from, as jj's own resolution of op heads
        // would: otherwise, after realizing several operations, the previous head stays, and
        // the next step merges it.
        let mut replaced = self
            .loader
            .op_store()
            .read_operation(&head)
            .block_on()?
            .parents;
        replaced.extend(superseded);
        self.loader
            .op_heads_store()
            .update_op_heads(&replaced, &head)
            .block_on()?;
        drop(_lock);
        self.replace_abandoned_working_copies()?;
        Ok(head)
    }

    /// Refuses to publish a realization that jj cannot merge with this machine's own
    /// concurrent operations. Published, it would be merged by every `jj` command here, and
    /// each would fail, or for some jj bugs panic, until someone reverted an operation by
    /// hand. Unpublished, jj keeps working, and the error says which operations to revert.
    /// Returns the op heads the realization descends from, beyond its parents, which are
    /// not concurrent with it: after a catch-up of several operations, the previous head.
    fn check_mergeable(&self, realized: &OperationId) -> Result<Vec<OperationId>, NodeError> {
        let realized_op = self.loader.load_operation(realized).block_on()?;
        let others: Vec<OperationId> = self
            .local_heads()?
            .into_iter()
            .filter(|head| head != realized && !realized_op.parent_ids().contains(head))
            .collect();
        let mut theirs = vec![];
        let mut superseded = vec![];
        for head in others {
            let op = self.loader.load_operation(&head).block_on()?;
            // Nothing of its own that the realization lacks: an ancestor.
            let beyond = std::pin::pin!(op_walk::walk_ancestors_range(
                std::slice::from_ref(&op),
                std::slice::from_ref(&realized_op),
            ))
            .try_next()
            .block_on()?;
            match beyond {
                None => superseded.push(head),
                Some(_) => theirs.push(op),
            }
        }
        if theirs.is_empty() {
            return Ok(superseded);
        }
        // This machine's operations that the hive doesn't have: one of them conflicts.
        let roots = realized_op.parents().block_on()?;
        let ours: Vec<OperationId> = op_walk::walk_ancestors_range(&theirs, &roots)
            .map_ok(|op| op.id().clone())
            .try_collect()
            .block_on()?;
        let mut operations = theirs;
        operations.push(realized_op);
        // jj merges op heads in order of their end times, and the result can depend on the
        // order, so try that order. Try the reverse too: equal times sort either way.
        operations.sort_by_key(|op| op.metadata().time.end.timestamp);
        let reversed: Vec<_> = operations.iter().rev().cloned().collect();
        for order in [operations, reversed] {
            let merged = catch_jj_panic(|| {
                self.loader
                    .merge_operations(order, None, Some("reconcile divergent operations"), [])
                    .block_on()
                    .map(|_| ())
                    .map_err(|err| format!("{err:#}"))
            });
            merged.map_err(|reason| self.unmergeable(&ours, reason))?;
        }
        Ok(superseded)
    }

    /// The error for operations of this machine's, `ours` (newest first), that jj can't
    /// merge with the hive's.
    pub(super) fn unmergeable(&self, ours: &[OperationId], reason: String) -> NodeError {
        const SHOWN: usize = 5;
        let mut listed: Vec<String> = ours
            .iter()
            .take(SHOWN)
            .map(|id| {
                let description = self
                    .loader
                    .load_operation(id)
                    .block_on()
                    .map(|op| op.metadata().description.clone())
                    .unwrap_or_default();
                format!("{} ({description})", &id.hex()[..12])
            })
            .collect();
        if ours.len() > SHOWN {
            listed.push(format!("and {} older", ours.len() - SHOWN));
        }
        NodeError::Unmergeable {
            ours: ours.to_vec(),
            listed: listed.join(", "),
            reason,
        }
    }
}

/// The per-machine fields of a local operation's view.
fn fields_of(op: &Operation) -> Result<PerMachine, NodeError> {
    Ok(PerMachine::of(op.view().block_on()?.store_view()))
}

/// The per-machine fields of `first_op` and `rest` merged three-way by jj.
pub(super) fn merged_by_jj(
    loader: &RepoLoader,
    first_op: Operation,
    rest: &[OperationId],
) -> Result<Arc<PerMachine>, NodeError> {
    let repo = loader.load_at(&first_op).block_on()?;
    let mut tx = repo.start_transaction();
    let mut merged = vec![first_op];
    for other in rest {
        let other_op = loader.load_operation(other).block_on()?;
        let base = merge_base(loader, &merged, &other_op)?;
        tx.merge_operation(&base, &other_op).block_on()?;
        merged.push(other_op);
    }
    Ok(Arc::new(PerMachine::of(tx.repo().view().store_view())))
}

/// The closest common ancestor of `ops` and `other`, or the root if they have none; `None`
/// if they have several.
fn single_base(
    loader: &RepoLoader,
    ops: &[Operation],
    other: &Operation,
) -> Result<Option<Operation>, NodeError> {
    let mut bases = op_walk::closest_common_ancestors(ops.to_vec(), [other.clone()]).block_on()?;
    Ok(match bases.len() {
        0 => Some(loader.root_operation().block_on()),
        1 => Some(bases.remove(0)),
        _ => None,
    })
}

/// The base a merge of `ops` with `other` merges three-way against, as jj's
/// `merge_operations` has it: their closest common ancestor, or where there are several,
/// as in a criss-cross merge, those merged first, recursively, into an operation that is
/// written but not published. Against the first of them instead, a merged record can be a
/// conflict that matches neither `.git` nor jj's merge, which the export can't correct and
/// the next import merges into the bookmark (`firstBase_reverts` in
/// formal/Musubi/Refs.lean).
pub(super) fn merge_base(
    loader: &RepoLoader,
    ops: &[Operation],
    other: &Operation,
) -> Result<Operation, NodeError> {
    let mut bases = op_walk::closest_common_ancestors(ops.to_vec(), [other.clone()]).block_on()?;
    match bases.len() {
        0 => return Ok(loader.root_operation().block_on()),
        1 => return Ok(bases.remove(0)),
        _ => {}
    }
    let first = bases[0].clone();
    // jj's merge rebases descendants, which can panic, as in `merge_heads`; jj's own merge
    // of these operations would too. Then the first base, as musubi had before.
    match catch_jj_panic(|| Ok(loader.merge_operations(bases, None, None, []).block_on())) {
        Ok(merged) => Ok(merged?.0.operation().clone()),
        Err(reason) => {
            tracing::warn!("merging the bases of a criss-cross merge: {reason}");
            Ok(first)
        }
    }
}
