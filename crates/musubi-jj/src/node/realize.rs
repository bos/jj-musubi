//! Realizing the hive's canonical operations here as local ones, writing them, and
//! advancing the op heads to them.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::sync::Arc;
use std::sync::PoisonError;
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
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use pollster::FutureExt as _;

use super::CANONICAL_ATTRIBUTE;
use super::NodeError;
use super::NodeRepo;
use super::UnmergeableSearch;
use super::catch_jj_panic;
use super::git::Colocation;
use super::translate::target_of;
use super::view::LocalView;
use super::view::PerMachine;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::Kind;
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
    local: LocalOp,
    canonical: CanonicalOp,
}

/// A realized operation, not yet written.
struct Realization {
    id: LocalOp,
    op: StoreOperation,
    view: View,
    per_machine: Arc<PerMachine>,
}

impl NodeRepo {
    /// Realizes a stored canonical operation, and any unrealized ancestors, without
    /// publishing it. Returns the local operation id.
    pub fn realize(&mut self, canonical: &CanonicalOp) -> Result<LocalOp, NodeError> {
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
        canonical: &CanonicalOp,
        next: &[CanonicalOp],
    ) -> Result<LocalOp, NodeError> {
        // Map everything reachable from the op heads first. Otherwise, after losing the
        // translation cache, an operation that already has a reachable realization would be
        // realized again, and two reachable local operations would share a canonical form.
        if !self.heads_mapped {
            // Noticing an abandon there reads every local operation it reaches.
            self.settle()?;
            self.canonical_heads()?;
            self.heads_mapped = true;
        }
        let order = self.unrealized(canonical)?;
        for (i, (id, op)) in order.iter().enumerate() {
            let parents: Vec<LocalOp> = CanonicalOp::parents_of(op)
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
        first: &CanonicalOp,
        op: &StoreOperation,
        later: impl Iterator<Item = &'a CanonicalOp>,
    ) -> Result<Vec<(CanonicalOp, StoreOperation)>, NodeError> {
        let mut run = vec![(first.clone(), op.clone())];
        for id in later.take(REALIZE_AT_ONCE - 1) {
            if !self.canonical.has_operation(id) || self.local_of(id).is_some() {
                break;
            }
            let op = self.canonical.read_operation(id)?;
            let (last, _) = run.last().expect("a run is never empty");
            if op.parents != std::slice::from_ref(&last.0) {
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
        canonical: &CanonicalOp,
    ) -> Result<Vec<(CanonicalOp, StoreOperation)>, NodeError> {
        let mut order = vec![];
        let mut ordered = HashSet::new();
        let mut stack: Vec<(CanonicalOp, Option<StoreOperation>)> = vec![(canonical.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if self.local_of(&id).is_some() || ordered.contains(&id) {
                continue;
            }
            if !self.canonical.has_operation(&id) {
                return Err(NodeError::NotRealizable(id.0.hex(), "operation not stored"));
            }
            let op = match loaded {
                Some(op) => op,
                None => self.canonical.read_operation(&id)?,
            };
            let missing: Vec<_> = CanonicalOp::parents_of(&op)
                .into_iter()
                .filter(|p| self.local_of(p).is_none() && !ordered.contains(p))
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
        ops: &[(CanonicalOp, StoreOperation)],
        per_machine: &PerMachine,
    ) -> Vec<Result<LocalView, NodeError>> {
        let make = |part: &[(CanonicalOp, StoreOperation)]| -> Vec<_> {
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
        canonical: CanonicalOp,
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
        self.remember_original(&canonical, &op)?;
        let store = self.loader.op_store().clone();
        let expected = id.clone();
        let write = thread::Builder::new()
            .name("write operation".to_owned())
            .spawn(move || {
                let view_id = store.write_view(&view).block_on()?;
                let written = store.write_operation(&op).block_on()?;
                if view_id != op.view_id || written != expected.0 {
                    return Err(NodeError::MisnamedWrite(expected.0.hex()));
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
    pub fn crash_before_settling(&mut self) -> Vec<LocalOp> {
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
    /// workspaces if it has none of them and the hive has forgotten this machine there: as the
    /// realization of its parent with the machine's latest work has them
    /// (`latest_work_parent`), following the operation's rewrites. They are still its working
    /// copies, and the hive shows them again with its next work. So too at work by this
    /// machine, where it is present: such an operation, realized here, is one another machine
    /// wrote for it, as a fix-up's (`write_fixup`), maybe where it had forgotten this machine
    /// and so without its workspaces; only this machine's own operations remove them. A view
    /// that has this machine's workspaces, or where it is otherwise present without any, is
    /// left as it is.
    fn with_own_workspaces(
        &mut self,
        canonical_id: &CanonicalOp,
        op: &StoreOperation,
        parents: &[LocalOp],
        local: LocalView,
    ) -> Result<LocalView, NodeError> {
        if local.names.keys().any(|key| self.is_own_key(key)) {
            return Ok(local);
        }
        let source = self.latest_work_parent(&CanonicalOp::parents_of(op))?;
        let mut own = match (parents.get(source), &self.last_own) {
            (None, _) => return Ok(local),
            (Some(parent), Some((last, own))) if parent == last => (**own).clone(),
            (Some(parent), _) => {
                // It may still be being written.
                self.settle()?;
                let op_store = self.loader.op_store();
                let parent_view = op_store
                    .read_view(&op_store.read_operation(&parent.0).block_on()?.view_id)
                    .block_on()?;
                let parent_canonical = self.canonical_of(parent).expect("parents realized first");
                self.own_of_view(parent_view.wc_commit_ids, &parent_canonical)?
            }
        };
        let own_work = Kind::of(&op.metadata).work.as_deref() == Some(self.machine.key());
        if own.is_empty()
            || !own_work && self.presence(canonical_id)?.is_present(self.machine.key())
        {
            return Ok(local);
        }
        workspaces::follow_rewrites(&mut own, op.commit_predecessors.as_ref());
        let LocalView {
            mut view,
            names,
            prefixes,
            ..
        } = local;
        let shown: HashSet<&WorkspaceNameBuf> = names.values().collect();
        for (name, commit) in own {
            if !shown.contains(&name) {
                view.wc_commit_ids.insert(name, commit);
            }
        }
        // The id the op store gives it, worked out as it does.
        let id = jj_lib::op_store::ViewId::new(blake2b_hash(&view).to_vec());
        Ok(LocalView {
            view,
            id,
            names,
            prefixes,
        })
    }

    /// Which of a canonical operation's parents has this machine's latest work in its history:
    /// one whose history has every other's (`Presence::worked`), so that a merge of a forget
    /// that saw the machine's latest work with an operation that saw only earlier work keeps
    /// the machine's workspaces as they are now. The first, if they agree or none has all.
    fn latest_work_parent(&self, parents: &[CanonicalOp]) -> Result<usize, NodeError> {
        if parents.len() < 2 {
            return Ok(0);
        }
        let key = self.machine.key();
        let worked: Vec<BTreeSet<crate::canonical::Work>> = parents
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
                    // Work an abandon dropped can't be placed: no parent is later for it.
                    if op.op.is_none() {
                        continue 'parents;
                    }
                    let mut seen = false;
                    for later in mine {
                        if op.below(&self.canonical, later)? {
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
        canonical_id: &CanonicalOp,
        op: &StoreOperation,
        parents: Vec<LocalOp>,
        local: LocalView,
        per_machine: Arc<PerMachine>,
    ) -> Result<Realization, NodeError> {
        let LocalView {
            view, id, prefixes, ..
        } = local;
        let mut metadata = op.metadata.clone();
        if let Some((prefix, target)) = target_of(&metadata.description)
            && let target = CanonicalOp(target)
            && self
                .canonical
                .is_ancestor(&target, &CanonicalOp::parents_of(op))?
        {
            let local = self.local_of(&target).expect("ancestors realized first");
            metadata.description = format!("{prefix}{}", local.0.hex());
        }
        metadata.workspace_name = metadata
            .workspace_name
            .map(|key| self.realized_workspace_name(&key, &prefixes));
        metadata
            .attributes
            .insert(CANONICAL_ATTRIBUTE.to_owned(), canonical_id.0.hex());
        // The id the op store gives it, worked out as it does.
        let local_op = StoreOperation {
            view_id: id,
            parents: parents.into_iter().map(|parent| parent.0).collect(),
            metadata,
            commit_predecessors: op.commit_predecessors.clone(),
        };
        Ok(Realization {
            id: LocalOp(OperationId::new(blake2b_hash(&local_op).to_vec())),
            op: local_op,
            per_machine,
            view,
        })
    }

    /// The local name of the workspace that made a canonical operation, as names go in the
    /// operation's view: `default` for this machine's own, `beta/default` for another's,
    /// even one the operation forgot, which the view doesn't name. jj's `undo` and `redo`
    /// refuse to undo another workspace's operation, and they tell workspaces apart only by
    /// name, so with the plain name `jj undo` here would undo beta's latest operation as if it
    /// were this machine's own; and so it would with `beta/default` if that were a workspace
    /// of this machine's own, as it can be where beta is shown as `beta-1a2b`.
    fn realized_workspace_name(
        &self,
        key: &WorkspaceName,
        prefixes: &BTreeMap<String, String>,
    ) -> WorkspaceNameBuf {
        self.local_name(key, prefixes)
            .unwrap_or_else(|| key.to_owned())
    }

    /// The per-machine fields a realization starts from: its parent's, or for a merge, the
    /// parents' merged three-way as jj merges them, as a local merge of the same operations
    /// would.
    fn inherited_per_machine(&self, parents: &[LocalOp]) -> Result<Arc<PerMachine>, NodeError> {
        if let ([parent], Some((last, per_machine))) = (parents, &self.last_realized)
            && parent == last
        {
            return Ok(per_machine.clone());
        }
        let (first, rest) = parents.split_first().expect("operations have parents");
        let first_op = self.loader.load_operation(&first.0).block_on()?;
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
        rest: &[LocalOp],
    ) -> Result<Option<Arc<PerMachine>>, NodeError> {
        let mut merged = fields_of(first_op)?;
        let mut ops = vec![first_op.clone()];
        for other in rest {
            let other_op = self.loader.load_operation(&other.0).block_on()?;
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
    /// it. There, too, a realization beside this machine's own concurrent op heads is
    /// published merged with them, as jj would merge them, and that merge exported first:
    /// published apart, the heads would be merged by whichever `jj` command loaded them
    /// first, which doesn't export, and whose import takes `.git` as the realization alone
    /// left it. While records are being taken, the heads it is published beside are those
    /// moving the op heads where the records name the history leaves beside it. Returns the
    /// realization as exported, which `canonical` translates to, not the merge.
    ///
    /// In the protocol model the head update and jj's merge are separate steps:
    /// `SyncStep.advance` followed by `EnvStep.merge` (`advance_merge_refines` in
    /// `formal/Musubi/Safety.lean`). The merge creates a canonical operation; realization
    /// alone does not. Working-copy cleanup below can load and merge the heads too, even
    /// in a non-colocated repository, and may write a separate working-copy repair.
    pub fn advance(&mut self, canonical: &CanonicalOp) -> Result<LocalOp, NodeError> {
        // One operation alone is never left out.
        self.advance_to(std::slice::from_ref(canonical))?
            .ok_or(NodeError::NotRealizable(
                String::new(),
                "nothing to advance to",
            ))
    }

    /// [`Self::advance`] to each of `canonicals` at once, as to what this machine's history
    /// has in place of an operation it dropped: `heads := max(heads ∪ canonicals)`. Where
    /// there are several, those at or below another of them, or at or below an op head, are
    /// left out, by the op heads as they are when it publishes; if none is left, there is
    /// nothing to do. Several left are published as one realization is beside this machine's
    /// concurrent op heads, but merged with each other too, in the one operation jj would make
    /// of them all as op heads: in a colocated repository, that merge, exported, is what is
    /// published; in one that isn't, they are published apart, and the working-copy cleanup
    /// at the end loads the repository, which merges them all at once. Merging them one at a
    /// time would make operations jj wouldn't, and could merge them in another order. Returns
    /// the first realization left, as exported, if one is.
    pub fn advance_to(&mut self, canonicals: &[CanonicalOp]) -> Result<Option<LocalOp>, NodeError> {
        if canonicals.is_empty() {
            return Err(NodeError::NotRealizable(
                String::new(),
                "nothing to advance to",
            ));
        }
        // Each realized first, so that those left can be worked out again from the op heads
        // under the lock below, without realizing anything while holding it.
        let all = canonicals
            .iter()
            .map(|canonical| self.realize(canonical))
            .collect::<Result<Vec<_>, _>>()?;
        // Views made ahead inherit what this changes, in a colocated repository.
        self.prepared = None;
        let mut heads = self.local_heads()?;
        let Some((mut left, mut realized)) = self.left_beside(canonicals, &all, &heads)? else {
            return Ok(None);
        };
        let (mut superseded, mut concurrent) = self.check_mergeable(&left, &realized, &heads)?;
        let colocation = self.colocation();
        let colocated = colocation.is_some();
        let _lock = colocation.map(Colocation::lock).transpose()?;
        // A `jj` command in the colocated workspace publishes only while holding the lock, so
        // none can until this publishes. One may have published since the op heads were read,
        // though, which the export and the merge must take in: published beside the merge, it
        // would be merged by the next `jj` command, which doesn't export. The heads are
        // checked again only if they changed, so that the first check, whose search for an
        // operation to revert where jj can't merge them can take a while, keeps `jj` commands
        // waiting for the lock only in that rare case. Which are left goes by the same heads.
        if colocated {
            let mut now = self.local_heads()?;
            heads.sort();
            now.sort();
            if now != heads {
                match self.left_beside(canonicals, &all, &now)? {
                    Some(again) => (left, realized) = again,
                    None => return Ok(None),
                }
                (superseded, concurrent) = self.check_mergeable(&left, &realized, &now)?;
            }
        }
        let (canonical, primary) = (left[0].clone(), realized[0].clone());
        // The others, merged with the first as op heads beside it would be.
        let others: Vec<Operation> = realized[1..]
            .iter()
            .map(|op| self.loader.load_operation(&op.0).block_on())
            .collect::<Result<_, _>>()?;
        // Records being taken move the op heads where they name the history, as they name the
        // realization: the heads it is published beside are those that leaves beside it,
        // renamed. The heads `check_mergeable` found name the history as it was, so most of
        // them only look concurrent with it, and the records may drop some.
        let taking = self.taking_unswitched();
        if taking {
            concurrent = self
                .taken_beside(&primary)?
                .iter()
                .map(|op| self.loader.load_operation(&op.0).block_on())
                .collect::<Result<_, _>>()?;
        }
        // Everything the realization is merged with, each once: jj doesn't merge an operation
        // with itself, and records being taken can leave another realization beside it too.
        let mut merging: Vec<Operation> = vec![];
        for op in concurrent.iter().chain(&others) {
            if op.id() != &primary.0 && merging.iter().all(|m| m.id() != op.id()) {
                merging.push(op.clone());
            }
        }
        let colocation = self.colocation();
        let pending = self.pending_expected();
        // Exported beside all it is merged with next, as one realization beside the op heads.
        let head = match colocation {
            Some(colocation) => colocation.export_refs(
                &self.loader,
                &primary,
                &|op| self.is_join_point(op),
                &merging,
                &pending,
            )?,
            None => primary,
        };
        let merged = match colocation {
            Some(colocation) if !merging.is_empty() => {
                match self.merge_unpublished(&head, &merging) {
                    Ok(merged) => Some(colocation.export_refs(
                        &self.loader,
                        &merged,
                        &|op| self.is_join_point(op),
                        &[],
                        &pending,
                    )?),
                    // `check_mergeable` merged them already, so this is a store error or a jj
                    // bug, unless records being taken renamed them, which leaves their views
                    // but changes what they merge against: the heads are published apart, for
                    // `replace_abandoned_working_copies` to merge as it would any others.
                    Err(reason) => {
                        tracing::warn!("merging a realization with this machine's heads: {reason}");
                        None
                    }
                }
            }
            _ => None,
        };
        if colocated {
            self.insert_map(head.clone(), canonical.clone())?;
        }
        // Published apart, where they weren't merged: the working-copy cleanup below merges
        // them all at once, as loading the repository does.
        let apart: Vec<&Operation> = if merged.is_none() {
            others.iter().collect()
        } else {
            vec![]
        };
        if taking {
            // The hub's head, named as records this machine is taking name the history: the
            // op heads move there, renamed, at once (`NodeRepo::switch_to_taken`).
            self.switch_to_taken(Some(&head), merged.as_ref())?;
            for other in &apart {
                self.loader
                    .op_heads_store()
                    .update_op_heads(&[], other.id())
                    .block_on()?;
            }
        } else {
            // The new head replaces those it descends from, as jj's own resolution of op
            // heads would: otherwise, after realizing several operations, the previous head
            // stays, and the next step merges it.
            let mut replaced = self
                .loader
                .op_store()
                .read_operation(&head.0)
                .block_on()?
                .parents;
            replaced.extend(superseded.into_iter().map(|op| op.0));
            if merged.is_some() {
                replaced.extend(merging.iter().map(|op| op.id().clone()));
            }
            // The new heads go in before the old come out, the last with them.
            for other in &apart {
                self.loader
                    .op_heads_store()
                    .update_op_heads(&[], other.id())
                    .block_on()?;
            }
            self.loader
                .op_heads_store()
                .update_op_heads(&replaced, &merged.as_ref().unwrap_or(&head).0)
                .block_on()?;
        }
        drop(_lock);
        self.move_taken_workspaces()?;
        self.replace_abandoned_working_copies()?;
        Ok(Some(head))
    }

    /// The realization `head` merged with this machine's concurrent op heads `theirs`, as
    /// jj merges op heads on loading them, in order of their end times, into an operation
    /// written but not published.
    fn merge_unpublished(&self, head: &LocalOp, theirs: &[Operation]) -> Result<LocalOp, String> {
        let mut operations = theirs.to_vec();
        operations.push(
            self.loader
                .load_operation(&head.0)
                .block_on()
                .map_err(|err| format!("{err:#}"))?,
        );
        operations.sort_by_key(|op| op.metadata().time.end.timestamp);
        catch_jj_panic(|| {
            self.loader
                .merge_operations(operations, None, Some("reconcile divergent operations"), [])
                .block_on()
                .map(|(repo, _)| LocalOp(repo.op_id().clone()))
                .map_err(|err| format!("{err:#}"))
        })
    }

    /// Refuses to publish a realization that jj cannot merge with this machine's own
    /// concurrent operations, the op heads `heads`, and, where there are several, with each
    /// other. Published, it would be merged by every `jj` command here, and each would fail,
    /// or for some jj bugs panic, until someone reverted an operation by hand. Unpublished, jj
    /// keeps working, and the error says which operations to revert. Returns the op heads the
    /// realizations descend from, beyond their parents, which are not concurrent with them:
    /// after a catch-up of several operations, the previous head; and those that are.
    fn check_mergeable(
        &self,
        canonicals: &[CanonicalOp],
        realized: &[LocalOp],
        heads: &[LocalOp],
    ) -> Result<(Vec<LocalOp>, Vec<Operation>), NodeError> {
        let realized_ops: Vec<Operation> = realized
            .iter()
            .map(|op| self.loader.load_operation(&op.0).block_on())
            .collect::<Result<_, _>>()?;
        let realized_op = realized_ops.first().expect("something to advance to");
        let mut heads = heads.to_vec();
        let others: Vec<LocalOp> = heads
            .iter()
            .filter(|head| {
                !realized.contains(head)
                    && !realized_ops
                        .iter()
                        .any(|op| op.parent_ids().contains(&head.0))
            })
            .cloned()
            .collect();
        let mut theirs = vec![];
        let mut superseded = vec![];
        for head in others {
            let op = self.loader.load_operation(&head.0).block_on()?;
            // Nothing of its own that the realizations lack: an ancestor.
            let beyond = std::pin::pin!(op_walk::walk_ancestors_range(
                std::slice::from_ref(&op),
                &realized_ops,
            ))
            .try_next()
            .block_on()?;
            match beyond {
                None => superseded.push(head),
                Some(_) => theirs.push(op),
            }
        }
        if theirs.is_empty() && realized_ops.len() == 1 {
            return Ok((superseded, theirs));
        }
        // This machine's operations that the hive doesn't have: one of them conflicts.
        let mut roots: Vec<Operation> = vec![];
        for op in &realized_ops {
            for parent in op.parents().block_on()? {
                if !roots.contains(&parent) {
                    roots.push(parent);
                }
            }
        }
        let ours: Vec<LocalOp> = op_walk::walk_ancestors_range(&theirs, &roots)
            .map_ok(|op| LocalOp(op.id().clone()))
            .try_collect()
            .block_on()?;
        let mut operations = theirs.clone();
        operations.extend(realized_ops.iter().cloned());
        if let Err(reason) = self.try_merge(operations) {
            // The search for the one to revert goes by a single realization: with several,
            // the advice lists this machine's operations instead.
            if realized_ops.len() > 1 {
                return Err(self.unmergeable(&ours, None, reason));
            }
            let canonical = &canonicals[0];
            // The same heads and the hive's same operation, as when the sync is retried,
            // give the same result. Failing to find it leaves the advice to list them.
            heads.sort();
            let mut memo = self
                .unmergeable
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            let culprit = match &memo.last {
                Some(last) if last.heads == heads && last.theirs == *canonical => {
                    last.culprit.clone()
                }
                _ => {
                    memo.searches += 1;
                    // An error, as reading the store, is no answer to keep.
                    // Failing a single revert that will do, one that will help.
                    let culprit = self
                        .op_to_revert(&theirs, &ours, realized_op)
                        .and_then(|found| match found {
                            Some(op) => Ok(Some(op)),
                            None => self.first_unmergeable(&ours, realized_op),
                        })
                        .ok();
                    if let Some(culprit) = &culprit {
                        memo.last = Some(UnmergeableSearch {
                            heads,
                            theirs: canonical.clone(),
                            culprit: culprit.clone(),
                        });
                    }
                    culprit.flatten()
                }
            };
            drop(memo);
            return Err(self.unmergeable(&ours, culprit, reason));
        }
        Ok((superseded, theirs))
    }

    /// Of `canonicals`, realized as `realized`, those [`Self::advance_to`] publishes beside
    /// the op heads `heads`, with their realizations: one alone; of several, each once, those
    /// at or below none of the others nor any of `heads`. None if none is left.
    #[expect(clippy::type_complexity)]
    fn left_beside(
        &self,
        canonicals: &[CanonicalOp],
        realized: &[LocalOp],
        heads: &[LocalOp],
    ) -> Result<Option<(Vec<CanonicalOp>, Vec<LocalOp>)>, NodeError> {
        if canonicals.len() == 1 {
            return Ok(Some((canonicals.to_vec(), realized.to_vec())));
        }
        let mut covering = vec![];
        for head in heads {
            covering.extend(self.canonical_at_or_below(head)?);
        }
        let mut left: (Vec<CanonicalOp>, Vec<LocalOp>) = (vec![], vec![]);
        for (canonical, local) in canonicals.iter().zip(realized) {
            if left.0.contains(canonical) {
                continue;
            }
            let mut covered = false;
            for above in &covering {
                if self.canonical.is_ancestor_of(canonical, above)? {
                    covered = true;
                    break;
                }
            }
            for other in canonicals {
                if covered {
                    break;
                }
                covered = other != canonical && self.canonical.is_ancestor_of(canonical, other)?;
            }
            if !covered {
                left.0.push(canonical.clone());
                left.1.push(local.clone());
            }
        }
        Ok((!left.0.is_empty()).then_some(left))
    }

    /// The canonical form of local operation `op`, or, for one not canonicalized yet, as a
    /// `jj` command's just published, those of the nearest operations below it that are:
    /// what is below it of the canonical history.
    fn canonical_at_or_below(&self, op: &LocalOp) -> Result<Vec<CanonicalOp>, NodeError> {
        let mut found = vec![];
        let mut seen = HashSet::new();
        let mut stack = vec![op.clone()];
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone()) {
                continue;
            }
            match self.canonical_of(&local) {
                Some(canonical) => found.push(canonical),
                None => {
                    let read = self.loader.op_store().read_operation(&local.0).block_on()?;
                    stack.extend(read.parents.into_iter().map(LocalOp));
                }
            }
        }
        Ok(found)
    }

    /// Whether jj can merge `operations` without failing or panicking. jj merges op heads in
    /// order of their end times, and the result can depend on the order, so this tries that
    /// order, and the reverse too: equal times sort either way.
    fn try_merge(&self, mut operations: Vec<Operation>) -> Result<(), String> {
        operations.sort_by_key(|op| op.metadata().time.end.timestamp);
        let reversed: Vec<_> = operations.iter().rev().cloned().collect();
        for order in [operations, reversed] {
            catch_jj_panic(|| {
                self.loader
                    .merge_operations(order, None, Some("reconcile divergent operations"), [])
                    .block_on()
                    .map(|_| ())
                    .map_err(|err| format!("{err:#}"))
            })?;
        }
        Ok(())
    }

    /// Of this machine's operations the hive doesn't have, `ours` (newest first), the newest
    /// whose revert lets jj merge the hive's operation `realized`: the one to revert. Each
    /// is reverted as `jj op revert` would, on top of this machine's op heads, `heads`,
    /// merged, into an operation written but not published (though it rebases immutable
    /// commits too, where `jj op revert` leaves them), and that merged with `realized`.
    /// Newest first, since reverting an operation whose result was rewritten since leaves
    /// it divergent, which can untie the loop where reverting the rewrite would be cleaner.
    /// Skips merges, which `jj op revert` refuses, operations already reverted, and those
    /// that leave the commit graph as it was, which can't make a loop. `None` if no single
    /// revert will do, as when several of this machine's operations each loop with the
    /// hive's.
    fn op_to_revert(
        &self,
        heads: &[Operation],
        ours: &[LocalOp],
        realized: &Operation,
    ) -> Result<Option<LocalOp>, NodeError> {
        // Where `jj op revert` starts: jj's merge of the op heads, in jj's order, as any
        // command loads them.
        let mut heads = heads.to_vec();
        heads.sort_by_key(|op| op.metadata().time.end.timestamp);
        let Ok(Ok(head)) = catch_jj_panic(|| {
            Ok(self
                .loader
                .merge_operations(heads, None, Some("reconcile divergent operations"), [])
                .block_on())
        }) else {
            return Ok(None);
        };
        let head = head.0;
        let mut ops = vec![];
        for id in ours {
            ops.push(self.loader.load_operation(&id.0).block_on()?);
        }
        let reverted = reverted_by(&ops);
        for op in &ops {
            if op.parent_ids().len() != 1 || reverted.contains(&op.id().hex()) {
                continue;
            }
            let parent = op.parents().block_on()?.remove(0);
            if op.view().block_on()?.heads() == parent.view().block_on()?.heads() {
                continue;
            }
            let (at_op, at_parent) = (
                self.loader.load_at(op).block_on()?,
                self.loader.load_at(&parent).block_on()?,
            );
            let revert_op = catch_jj_panic(|| {
                let mut tx = head.start_transaction();
                Ok(async {
                    tx.repo_mut().merge(&at_op, &at_parent).await?;
                    // `jj op revert` keeps git's refs as they are.
                    let mut view = tx.repo().view().store_view().clone();
                    view.git_refs = head.view().store_view().git_refs.clone();
                    view.git_heads = head.view().store_view().git_heads.clone();
                    tx.repo_mut().set_view(view);
                    tx.repo_mut().rebase_descendants().await?;
                    let reverted = tx
                        .write(format!("revert operation {}", op.id().hex()))
                        .await?;
                    Ok::<_, NodeError>(reverted.leave_unpublished().operation().clone())
                }
                .block_on())
            });
            let Ok(Ok(revert_op)) = revert_op else {
                continue;
            };
            if self.try_merge(vec![revert_op, realized.clone()]).is_ok() {
                return Ok(Some(LocalOp(op.id().clone())));
            }
        }
        Ok(None)
    }

    /// Of this machine's operations the hive doesn't have, `ours` (newest first), the oldest
    /// whose own change jj panics merging with the hive's operation `realized`: one to revert
    /// first where no single revert will do. Each operation's change, from its parent, is
    /// merged with `realized` alone, both ways round, since the result can depend on which
    /// side the merge starts from, in a transaction never committed (though the rebased
    /// commits are written). Merged whole instead, every operation after the one to revert
    /// would fail too, carrying its change, though reverting them wouldn't help. Skips
    /// merges, which `jj op revert` refuses, and operations already reverted. `None` if no
    /// change panics alone, as when the loop needs several of them.
    fn first_unmergeable(
        &self,
        ours: &[LocalOp],
        realized: &Operation,
    ) -> Result<Option<LocalOp>, NodeError> {
        let mut ops = vec![];
        for id in ours.iter().rev() {
            ops.push(self.loader.load_operation(&id.0).block_on()?);
        }
        let reverted = reverted_by(&ops);
        let at_realized = self.loader.load_at(realized).block_on()?;
        for op in &ops {
            if op.parent_ids().len() != 1 || reverted.contains(&op.id().hex()) {
                continue;
            }
            let parent = op.parents().block_on()?.remove(0);
            let at_op = self.loader.load_at(op).block_on()?;
            // A panic is jj failing on a loop. An error doesn't say which operation to
            // revert: from the parent, this machine's earlier work looks abandoned on the
            // hive's side, which can itself fail, as for a merge commit on the root. `None`
            // for an error, which passes over the operation: only a loop panics.
            let panics = |repo: &Arc<ReadonlyRepo>, other: &Operation| {
                let merged = catch_jj_panic(|| {
                    let mut tx = repo.start_transaction();
                    Ok(async {
                        tx.merge_operation(&parent, other).await?;
                        tx.repo_mut().rebase_descendants().await?;
                        Ok::<_, NodeError>(())
                    }
                    .block_on())
                });
                match merged {
                    Ok(Ok(())) => Some(false),
                    Ok(Err(_)) => None,
                    Err(_) => Some(true),
                }
            };
            let panicked = match panics(&at_op, realized) {
                Some(false) => panics(&at_realized, op),
                other => other,
            };
            if panicked == Some(true) {
                return Ok(Some(LocalOp(op.id().clone())));
            }
        }
        Ok(None)
    }

    /// The error for operations of this machine's, `ours` (newest first), that jj can't
    /// merge with the hive's, `culprit` being the one to revert if known.
    pub(super) fn unmergeable(
        &self,
        ours: &[LocalOp],
        culprit: Option<LocalOp>,
        reason: String,
    ) -> NodeError {
        const SHOWN: usize = 5;
        let describe = |id: &LocalOp| {
            let description = self
                .loader
                .load_operation(&id.0)
                .block_on()
                .map(|op| op.metadata().description.clone())
                .unwrap_or_default();
            format!("{} ({description})", &id.0.hex()[..12])
        };
        let advice = match &culprit {
            Some(op) => format!(
                "To go on, revert this machine's operation {} with `jj op revert {}`: \
                 musubi then catches up, or names another to revert",
                describe(op),
                &op.0.hex()[..12]
            ),
            None => {
                let mut listed: Vec<String> = ours.iter().take(SHOWN).map(describe).collect();
                if ours.len() > SHOWN {
                    listed.push(format!("and {} older", ours.len() - SHOWN));
                }
                format!(
                    "To go on, revert this machine's operation that conflicts with them, one \
                     of those the hive doesn't have yet (newest first: {}), with \
                     `jj op revert <id>`; musubi then catches up",
                    listed.join(", ")
                )
            }
        };
        NodeError::Unmergeable {
            ours: ours.to_vec(),
            culprit,
            advice,
            reason,
        }
    }
}

#[cfg(all(test, unix))]
mod advance_tests;

/// The operations that those of `ops` that `jj op revert` wrote reverted, by hex id: it
/// describes what it writes so.
fn reverted_by(ops: &[Operation]) -> HashSet<String> {
    ops.iter()
        .filter_map(|op| op.metadata().description.strip_prefix("revert operation "))
        .map(str::to_owned)
        .collect()
}

/// The per-machine fields of a local operation's view.
fn fields_of(op: &Operation) -> Result<PerMachine, NodeError> {
    Ok(PerMachine::of(op.view().block_on()?.store_view()))
}

/// The per-machine fields of `first_op` and `rest` merged three-way by jj.
pub(super) fn merged_by_jj(
    loader: &RepoLoader,
    first_op: Operation,
    rest: &[LocalOp],
) -> Result<Arc<PerMachine>, NodeError> {
    let repo = loader.load_at(&first_op).block_on()?;
    let mut tx = repo.start_transaction();
    let mut merged = vec![first_op];
    for other in rest {
        let other_op = loader.load_operation(&other.0).block_on()?;
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
