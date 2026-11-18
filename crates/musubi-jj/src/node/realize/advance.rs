//! Publishing realizations at an exact, revalidated native head frontier.
//!
//! Preparation runs outside the publication locks. Head and Git publication keep the same
//! captured frontier under both locks; cached native ancestry is invalidated explicitly when
//! translations or history change. Merge feasibility and diagnosis belong to `merge`.

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::lock::FileLock;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_heads_store::OpHeadsStore;
use jj_lib::op_heads_store::OpHeadsStoreLock;
use jj_lib::op_walk;
use jj_lib::operation::Operation;
use jj_lib::ref_name::WorkspaceNameBuf;
use pollster::FutureExt as _;

use super::super::NodeError;
use super::super::NodeRepo;
use super::super::git::Colocation;
#[cfg(test)]
use super::super::native_contract;
use super::super::translate::target_of;
use super::super::view::PerMachine;
use super::with_kept;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;

#[derive(Default)]
pub(in crate::node) struct PublishedHistoryCache(Option<PublishedHistory>);

impl PublishedHistoryCache {
    pub(in crate::node) fn contains(&self, local: &LocalOp) -> bool {
        self.0
            .as_ref()
            .is_some_and(|history| history.locals.contains(local))
    }
}

struct PublishedHistory {
    heads: Vec<LocalOp>,
    locals: HashSet<LocalOp>,
    canonicals: Arc<HashMap<CanonicalOp, LocalOp>>,
}

/// Realizations [`NodeRepo::advance_to`] prepared outside the publication locks.
struct Prepared {
    /// The op heads captured, which must still be the op heads under the locks.
    heads: Vec<LocalOp>,
    /// The operations left to publish, the first of them the one it returns.
    left: Vec<CanonicalOp>,
    /// Their realizations, in the same order.
    realized: Vec<LocalOp>,
    /// The op heads the realizations descend from, which they replace.
    superseded: Vec<LocalOp>,
    /// The op heads concurrent with them, as the history was named when captured.
    concurrent: Vec<Operation>,
    /// Whether records being taken are based at the root (`NodeRepo::taking_root_base`).
    root_base: bool,
}

/// What preparing to advance beside the op heads as they are came to.
enum Preparation {
    Ready(Prepared),
    /// A native command moved the op heads after the records being taken were prepared:
    /// prepare again.
    Retry,
    /// Every operation is at or below another of them or an op head: nothing to do.
    NothingLeft,
}

/// The publication locks: jj's colocated import/export lock, in a colocated repository, and
/// the op heads lock. Dropped, the op heads lock goes first, as [`Self::release`] does.
struct PublicationLocks<'a> {
    heads: Box<dyn OpHeadsStoreLock + 'a>,
    git: Option<FileLock>,
}

impl PublicationLocks<'_> {
    fn colocated(&self) -> bool {
        self.git.is_some()
    }

    fn release(self) {
        #[cfg(test)]
        let colocated = self.colocated();
        let Self { heads, git } = self;
        drop(heads);
        #[cfg(test)]
        native_contract::emit(native_contract::Event::HeadsUnlocked);
        drop(git);
        #[cfg(test)]
        if colocated {
            native_contract::emit(native_contract::Event::GitUnlocked);
        }
    }
}

/// What the realization [`NodeRepo::advance_to`] returns is published beside.
struct Beside {
    /// The other realizations left, merged with it as op heads beside it would be.
    others: Vec<Operation>,
    /// Everything it is merged with, each once.
    merging: Vec<Operation>,
    /// Whether records are being taken (`NodeRepo::taking_unswitched`).
    taking: bool,
}

/// The realization [`NodeRepo::advance_to`] returns, as exported, and its merge with what it
/// is published beside, if it was merged.
struct Exported {
    head: LocalOp,
    merged: Option<LocalOp>,
}

impl NodeRepo {
    /// Forgets ancestry whose recorded native identities no longer describe this repository.
    pub(in crate::node) fn invalidate_published_history(&mut self) {
        self.published.0 = None;
    }
}

impl NodeRepo {
    /// Whether `local` is a realization not yet published that was named clear of fewer of
    /// this machine's own names (`reserved_names`) than its op heads have now, as one made
    /// before a crash, or before a `jj` command published: merged with them, it may show
    /// another machine's workspace by a name that is a workspace of this machine's own there.
    fn realized_beside_other_heads(&mut self, local: &LocalOp) -> Result<bool, NodeError> {
        let op = self.loader.op_store().read_operation(&local.0).block_on()?;
        if OpAttrs(&op.metadata.attributes).canonical().is_none()
            || self
                .reserved_names()?
                .is_subset(&super::super::view::reserved_of(&op.metadata)?)
        {
            return Ok(false);
        }
        // Published already, as when records being taken leave the op heads at it, it is
        // merged with nothing new.
        let load = |op: &LocalOp| self.loader.load_operation(&op.0).block_on();
        let heads = self
            .local_heads()?
            .iter()
            .map(load)
            .collect::<Result<Vec<_>, _>>()?;
        let bases = op_walk::closest_common_ancestors([load(local)?], heads).block_on()?;
        Ok(!bases.iter().any(|base| base.id() == &local.0))
    }

    /// Realizes `canonical` again in place of `local`, its realization, not yet published,
    /// beside the op heads as they are now.
    fn realize_again(
        &mut self,
        canonical: &CanonicalOp,
        local: &LocalOp,
    ) -> Result<LocalOp, NodeError> {
        self.settle()?;
        // The old one stays unreachable, as after a crash: the map's file names the new one
        // after it, and the one named last counts.
        self.map.forget(local, canonical);
        self.realizing.clear_prepared();
        self.realize(canonical)
    }

    /// Actual native ancestry, not the cache's preferred unpublished aliases. Append-only
    /// moves extend only the new suffix; a trim or restore rebuilds the index.
    fn published_realizations(
        &mut self,
        heads: &[LocalOp],
    ) -> Result<Arc<HashMap<CanonicalOp, LocalOp>>, NodeError> {
        for head in heads {
            match self.canonicalize_unchecked(head) {
                Ok(_) | Err(NodeError::BeforeJoin(_)) => {}
                Err(err) => return Err(err),
            }
        }
        let mut heads = heads.to_vec();
        heads.sort();
        if let Some(history) = &self.published.0
            && history.heads == heads
        {
            return Ok(history.canonicals.clone());
        }
        let mut previous = self.published.0.take();
        loop {
            let mut pending = heads.clone();
            let mut added = vec![];
            let mut seen = HashSet::new();
            let mut boundaries = HashSet::new();
            while let Some(local) = pending.pop() {
                if !seen.insert(local.clone()) {
                    continue;
                }
                if previous
                    .as_ref()
                    .is_some_and(|old| old.locals.contains(&local))
                {
                    boundaries.insert(local);
                    continue;
                }
                let op = self.loader.op_store().read_operation(&local.0).block_on()?;
                pending.extend(LocalOp::parents_of(&op));
                added.push(local);
            }
            if previous
                .as_ref()
                .is_some_and(|old| old.heads.iter().any(|head| !boundaries.contains(head)))
            {
                previous = None;
                continue;
            }
            let (mut locals, mut canonicals) = previous.map_or_else(
                || (HashSet::new(), HashMap::new()),
                |old| (old.locals, Arc::unwrap_or_clone(old.canonicals)),
            );
            for local in added.into_iter().rev() {
                if let Some(canonical) = self.canonical_of(&local) {
                    canonicals.insert(canonical, local.clone());
                }
                locals.insert(local);
            }
            let canonicals = Arc::new(canonicals);
            self.published.0 = Some(PublishedHistory {
                heads,
                locals,
                canonicals: canonicals.clone(),
            });
            return Ok(canonicals);
        }
    }

    /// Re-render only unpublished suffixes against actual published parent aliases.
    /// Every operation validates its full inputs, so partial writes recover after restart.
    pub(super) fn current_realizations(
        &mut self,
        canonicals: &[CanonicalOp],
        published: &HashMap<CanonicalOp, LocalOp>,
        prepared: &HashMap<CanonicalOp, LocalOp>,
        root_own: &BTreeMap<WorkspaceNameBuf, CommitId>,
    ) -> Result<Vec<LocalOp>, NodeError> {
        let order = self.canonical.ancestors_until(canonicals, |id| {
            prepared.contains_key(id) || published.contains_key(id)
        })?;
        let order = order
            .into_iter()
            .map(|id| {
                let op = self.canonical.read_operation(&id)?;
                Ok((id, op))
            })
            .collect::<Result<Vec<_>, NodeError>>()?;
        // Bind the actual published frontier before choosing merge bases for kept names.
        for (_, op) in &order {
            let mut references = CanonicalOp::parents_of(op);
            if let Some((_, target)) = target_of(&op.metadata.description) {
                references.push(CanonicalOp(target));
            }
            for id in references {
                if let Some(local) = prepared.get(&id).or_else(|| published.get(&id)) {
                    self.insert_map(local.clone(), id)?;
                }
            }
        }
        let (reserved, kept) = self.reserved_for(&order)?;
        for (id, op) in &order {
            let old = self.local_of(id);
            let mut cached = None;
            if let Some(local) = &old {
                let raw = self.loader.op_store().read_operation(&local.0).block_on()?;
                // An original native operation is its own authority; only prepared
                // realizations can depend on stale parent aliases or private root context.
                if OpAttrs(&raw.metadata.attributes).canonical().is_none() {
                    continue;
                }
                cached = Some(raw);
            }
            let parents = CanonicalOp::parents_of(op)
                .iter()
                .map(|parent| {
                    prepared
                        .get(parent)
                        .or_else(|| published.get(parent))
                        .cloned()
                        .or_else(|| self.local_of(parent))
                        .ok_or_else(|| {
                            NodeError::NotRealizable(id.0.hex(), "a parent has no local operation")
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            if !matches!((parents.as_slice(), self.realizing.last_realized()), ([parent], Some((last, _))) if parent == last)
            {
                self.settle()?;
            }
            let fields = match cached.as_ref() {
                // An export can update a prepared realization's Git record. Preserve
                // that independently observed state while its physical parents are unchanged.
                Some(raw)
                    if raw
                        .parents
                        .iter()
                        .eq(parents.iter().map(|parent| &parent.0)) =>
                {
                    let view = self.loader.op_store().read_view(&raw.view_id).block_on()?;
                    Arc::new(PerMachine::of(&view))
                }
                _ => self.inherited_per_machine(&parents)?,
            };
            let view = self.local_view(id, op, &fields, &reserved)?;
            let view =
                self.with_own_workspaces(id, op, &parents, view, &reserved, Some(root_own))?;
            let own = self.own_of(&view);
            let view = with_kept(view, &kept);
            let expected =
                self.realize_one(id, op, parents, view, &own, &reserved, fields.clone())?;
            self.realizing.remember_own(expected.id.clone(), own);
            if old.as_ref() == Some(&expected.id) {
                self.realizing.remember_last(expected.id, fields);
            } else {
                self.write_later(expected, id.clone())?;
            }
        }
        self.settle()?;
        canonicals
            .iter()
            .map(|id| {
                prepared
                    .get(id)
                    .or_else(|| published.get(id))
                    .cloned()
                    .or_else(|| self.local_of(id))
                    .ok_or_else(|| {
                        NodeError::NotRealizable(id.0.hex(), "its local operation is missing")
                    })
            })
            .collect()
    }

    /// A local representation with the same shared view and parents, carrying `fields`
    /// and an explicit canonical identity. Written before publication, as an export is.
    pub(super) fn with_per_machine(
        &self,
        local: &LocalOp,
        fields: &PerMachine,
        canonical: &CanonicalOp,
    ) -> Result<LocalOp, NodeError> {
        let store = self.loader.op_store();
        let mut op = store.read_operation(&local.0).block_on()?;
        let mut view = store.read_view(&op.view_id).block_on()?;
        if PerMachine::of(&view) == *fields {
            return Ok(local.clone());
        }
        fields.apply_to(&mut view);
        op.view_id = store.write_view(&view).block_on()?;
        // This may be a local original rather than a received realization. Keep its
        // identity explicit across translation-cache loss and a later jj op abandon.
        OpAttrs(&mut op.metadata.attributes).set_canonical(canonical);
        Ok(LocalOp(store.write_operation(&op).block_on()?))
    }

    /// Realizes a canonical operation and publishes it as an op head, in place of the op
    /// heads it descends from (heads := max(heads ∪ {op})). In a colocated
    /// repository the realization first exports its refs to `.git`, holding jj's colocated
    /// import/export lock, so that no `jj` command sees the operation before `.git` matches
    /// it. There, too, a realization beside this machine's own concurrent op heads is
    /// published merged with them, as jj would merge them, and that merge exported first:
    /// published apart, the heads would be merged by whichever `jj` command loaded them
    /// first, without exporting before its import, which takes `.git` as the realization
    /// alone left it. While records are being taken, the heads it is published beside are those
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
        let op_heads_store = self.loader.op_heads_store().clone();
        // Prepare outside both publication locks. A native command can publish while this
        // runs, so compare the exact captured head set again under those locks.
        let (prepared, locks) = loop {
            let mut prepared = match self.prepare_advance(canonicals)? {
                Preparation::Ready(prepared) => prepared,
                Preparation::Retry => continue,
                Preparation::NothingLeft => return Ok(None),
            };
            if let Some(locks) = self.lock_if_unchanged(&mut prepared.heads, &*op_heads_store)? {
                break (prepared, locks);
            }
        };
        let Prepared {
            left,
            mut realized,
            superseded,
            concurrent,
            root_base,
            ..
        } = prepared;
        let current_git = self.carry_current_git(&left, &mut realized, root_base)?;
        let primary = realized[0].clone();
        let beside = self.beside(&primary, &realized, concurrent)?;
        let exported = self.export_and_merge(primary, &beside.merging, current_git)?;
        if locks.colocated() {
            self.insert_map(exported.head.clone(), left[0].clone())?;
        }
        self.move_heads_to(&exported, &beside, superseded)?;
        locks.release();
        #[cfg(test)]
        native_contract::emit(native_contract::Event::Cleanup);
        self.move_taken_workspaces()?;
        self.replace_abandoned_working_copies()?;
        #[cfg(test)]
        native_contract::emit(native_contract::Event::Complete);
        Ok(Some(exported.head))
    }

    /// Realizes `canonicals` beside the op heads as they are now, outside the publication
    /// locks, and finds which of them [`Self::advance_to`] publishes, and how.
    fn prepare_advance(&mut self, canonicals: &[CanonicalOp]) -> Result<Preparation, NodeError> {
        let root_base = self.taking_root_base()?;
        self.settle()?;
        if !self.heads_mapped {
            self.canonical_heads()?;
        }
        self.realizing.clear_prepared();
        let heads = self.local_heads()?;
        #[cfg(test)]
        native_contract::emit(native_contract::Event::Captured(heads.clone()));
        let published = self.published_realizations(&heads)?;
        let own = self.own_for_root(&heads)?;
        let Some(prepared) = self.prepared_realizations(&heads) else {
            return Ok(Preparation::Retry);
        };
        let all = self.current_realizations(canonicals, &published, &prepared, &own)?;
        let Some((left, mut realized)) = self.left_beside(canonicals, &all, &heads)? else {
            return Ok(Preparation::NothingLeft);
        };
        for (id, local) in left.iter().zip(&mut realized) {
            if self.realized_beside_other_heads(local)? {
                *local = self.realize_again(id, local)?;
            }
        }
        let (superseded, concurrent) = self.check_mergeable(&left, &realized, &heads)?;
        #[cfg(test)]
        native_contract::prepared(self, &left, &realized);
        Ok(Preparation::Ready(Prepared {
            heads,
            left,
            realized,
            superseded,
            concurrent,
            root_base,
        }))
    }

    /// Takes the publication locks, jj's colocated import/export lock first in a colocated
    /// repository, if the op heads are still those `captured`; otherwise releases them again.
    fn lock_if_unchanged<'a>(
        &self,
        captured: &mut [LocalOp],
        op_heads_store: &'a dyn OpHeadsStore,
    ) -> Result<Option<PublicationLocks<'a>>, NodeError> {
        let git = self.colocation().map(Colocation::lock).transpose()?;
        #[cfg(test)]
        if git.is_some() {
            native_contract::emit(native_contract::Event::GitLocked);
        }
        let heads = op_heads_store.lock().block_on()?;
        #[cfg(test)]
        native_contract::emit(native_contract::Event::HeadsLocked);
        let mut now = self.local_heads()?;
        captured.sort();
        now.sort();
        #[cfg(test)]
        native_contract::emit(native_contract::Event::Reread {
            captured: captured.to_vec(),
            actual: now.clone(),
        });
        if now[..] != captured[..] {
            #[cfg(test)]
            native_contract::emit(native_contract::Event::RevalidationRetry {
                captured: captured.to_vec(),
                actual: now.clone(),
            });
            drop(heads);
            drop(git);
            return Ok(None);
        }
        Ok(Some(PublicationLocks { heads, git }))
    }

    /// Under the publication locks, gives those of `realized`, the realizations of `left`,
    /// that need them this copy's current Git records, from its op heads as they are now.
    /// Returns whether any does.
    fn carry_current_git(
        &mut self,
        left: &[CanonicalOp],
        realized: &mut [LocalOp],
        root_base: bool,
    ) -> Result<bool, NodeError> {
        // Recheck the source under the colocated lock, after all realization work. A
        // root-based cached realization may have no Git fields, or ones from before a
        // concurrent command. Taking a trim must change neither this copy's record of Git
        // nor its physical Git state merely because that record's old ancestry disappeared.
        // So too for records that drop an op head, as another machine's `jj op abandon` of
        // this machine's latest operation does: the realization is on what was below it,
        // without the HEAD its commit recorded. A known forgotten copy with retained private
        // workspaces has the same missing shared authority even when its saved accepted base
        // is non-root. Use its actual current Git bookkeeping, and merge shared payloads
        // before the export.
        let sources = self.local_heads()?;
        #[cfg(test)]
        native_contract::emit(native_contract::Event::Sources(sources.clone()));
        let carried = root_base || self.taking_drops_a_head(&sources)?;
        let mut private = vec![false; left.len()];
        if !carried {
            let absent = left
                .iter()
                .map(|id| {
                    let presence = self.presence(id)?;
                    Ok(presence.known().contains(self.machine.key())
                        && !presence.is_present(self.machine.key()))
                })
                .collect::<Result<Vec<_>, NodeError>>()?;
            if absent.iter().any(|absent| *absent) {
                let own = self.own_at_heads(&sources)?;
                for (i, canonical) in left.iter().enumerate().filter(|(i, _)| absent[*i]) {
                    let raw = self
                        .loader
                        .op_store()
                        .read_operation(&realized[i].0)
                        .block_on()?;
                    let view = self.loader.op_store().read_view(&raw.view_id).block_on()?;
                    let target_own = self.own_of_view(view.wc_commit_ids, canonical, &raw)?;
                    private[i] = own.keys().any(|name| target_own.contains_key(name));
                }
            }
        }
        let current_git = carried || private.iter().any(|kept| *kept);
        if current_git {
            let fields = self.inherited_per_machine(&sources)?;
            for (i, (canonical, local)) in left.iter().zip(realized.iter_mut()).enumerate() {
                if carried || private[i] {
                    #[cfg(test)]
                    let source_before = native_contract::observer()
                        .map(|_| (local.clone(), self.native_identity_snapshot()));
                    *local = self.with_per_machine(local, &fields, canonical)?;
                    self.insert_map(local.clone(), canonical.clone())?;
                    #[cfg(test)]
                    if let Some((input, source_before)) = source_before {
                        native_contract::emit(native_contract::Event::CurrentGit {
                            canonical: canonical.clone(),
                            input,
                            output: local.clone(),
                            mapped: self.canonical_of(local),
                            preferred: self.local_of(canonical),
                            source_before,
                            source_after: self.native_identity_snapshot(),
                        });
                    }
                }
            }
        }
        Ok(current_git)
    }

    /// What `primary`, the first of `realized`, is published beside: the others, and the op
    /// heads `check_mergeable` found `concurrent` with it, or those records being taken leave
    /// beside it.
    fn beside(
        &mut self,
        primary: &LocalOp,
        realized: &[LocalOp],
        mut concurrent: Vec<Operation>,
    ) -> Result<Beside, NodeError> {
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
                .taken_beside(primary)?
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
        Ok(Beside {
            others,
            merging,
            taking,
        })
    }

    /// In a colocated repository, exports `primary` to `.git` and merges it with `merging`,
    /// exporting the merge too. `current_git` says whether a realization carries this copy's
    /// current Git records.
    fn export_and_merge(
        &self,
        primary: LocalOp,
        merging: &[Operation],
        current_git: bool,
    ) -> Result<Exported, NodeError> {
        let colocation = self.colocation();
        let pending = self.pending_expected();
        // A transition that carries the current heads' Git records, rather than a shared
        // ancestor's, merges its shared payload before exporting: exporting the incoming tip
        // first could move Git backward, then merge its record forward without writing Git
        // again. Other realizations export beside the heads as usual.
        let merge_before_export = current_git && !merging.is_empty();
        let head = match colocation {
            Some(colocation) if !merge_before_export => colocation.export_refs(
                &self.loader,
                &primary,
                &|op| self.is_join_point(op),
                merging,
                &pending,
            )?,
            _ => primary,
        };
        let merged = match colocation {
            Some(colocation) if !merging.is_empty() => {
                match self.merge_unpublished(&head, merging) {
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
                        if merge_before_export {
                            return Err(self.unmergeable(&self.local_heads()?, None, reason));
                        }
                        tracing::warn!("merging a realization with this machine's heads: {reason}");
                        None
                    }
                }
            }
            _ => None,
        };
        Ok(Exported { head, merged })
    }

    /// Moves the op heads to `exported`, beside what `beside` says, in place of the op heads
    /// it replaces, `superseded` among them.
    fn move_heads_to(
        &mut self,
        exported: &Exported,
        beside: &Beside,
        superseded: Vec<LocalOp>,
    ) -> Result<(), NodeError> {
        let Exported { head, merged } = exported;
        // Published apart, where they weren't merged: the working-copy cleanup at the end of
        // `advance_to` merges them all at once, as loading the repository does.
        let apart: Vec<&Operation> = if merged.is_none() {
            beside.others.iter().collect()
        } else {
            vec![]
        };
        if beside.taking {
            // The hub's head, named as records this machine is taking name the history: the
            // op heads move there, renamed, at once (`NodeRepo::switch_to_taken`).
            self.switch_to_taken(Some(head), merged.as_ref())?;
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
                replaced.extend(beside.merging.iter().map(|op| op.id().clone()));
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
                .update_op_heads(&replaced, &merged.as_ref().unwrap_or(head).0)
                .block_on()?;
        }
        Ok(())
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
}
