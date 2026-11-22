//! Publishing realizations at an exact, revalidated native head frontier.
//!
//! Preparation runs outside the publication locks. Head and Git publication keep the same
//! captured frontier under both locks; cached native ancestry is invalidated explicitly when
//! translations or history change. Merge feasibility and diagnosis belong to `merge`.

use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

use jj_lib::lock::FileLock;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_heads_store::OpHeadsStore;
use jj_lib::operation::Operation;
use pollster::FutureExt as _;

use super::super::NodeError;
use super::super::NodeRepo;
use super::super::git::Colocation;
use super::super::heads::HeadsLock;
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

/// The realization [`NodeRepo::advance`] prepared outside the publication locks.
struct Prepared {
    /// The op heads captured, which must still be the op heads under the locks.
    heads: Vec<LocalOp>,
    /// The realization.
    realized: LocalOp,
    /// The op heads the realization descends from, which it replaces.
    superseded: Vec<LocalOp>,
    /// The op heads concurrent with it.
    concurrent: Vec<Operation>,
}

/// The publication locks: jj's colocated import/export lock, in a colocated repository, and
/// the op heads lock. Dropped, the op heads lock goes first, as [`Self::release`] does.
struct PublicationLocks<'a> {
    heads: HeadsLock<'a>,
    git: Option<FileLock>,
}

impl PublicationLocks<'_> {
    fn colocated(&self) -> bool {
        self.git.is_some()
    }

    fn release(self) {
        let Self { heads, git } = self;
        drop(heads);
        drop(git);
    }
}

/// What the realization [`NodeRepo::advance`] returns is published beside.
struct Beside {
    /// Everything it is merged with, each once.
    merging: Vec<Operation>,
}

/// The realization [`NodeRepo::advance`] returns, as exported, and its merge with what it
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
    /// Actual native ancestry, not the cache's preferred unpublished aliases. Append-only
    /// moves extend only the new suffix; a trim or restore rebuilds the index.
    pub(in crate::node) fn published_realizations(
        &mut self,
        heads: &[LocalOp],
    ) -> Result<Arc<HashMap<CanonicalOp, LocalOp>>, NodeError> {
        for head in heads {
            match self.canonicalize(head) {
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
    /// Each shows other machines' workspaces clear of this machine's own names in the op heads
    /// as they are now (`reserved_for`), so one made before a crash, or before a `jj` command
    /// added such a name, is made again rather than published as it was.
    pub(super) fn current_realization(
        &mut self,
        canonical: &CanonicalOp,
        published: &HashMap<CanonicalOp, LocalOp>,
    ) -> Result<LocalOp, NodeError> {
        let order = self
            .canonical
            .ancestors_until(std::slice::from_ref(canonical), |id| {
                published.contains_key(id)
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
                if let Some(local) = published.get(&id) {
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
                // An original native operation is its own authority; only realizations not
                // yet published can depend on stale parent aliases.
                if OpAttrs(&raw.metadata.attributes).canonical().is_none() {
                    continue;
                }
                cached = Some(raw);
            }
            let parents = CanonicalOp::parents_of(op)
                .iter()
                .map(|parent| {
                    published
                        .get(parent)
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
                // An export can update an unpublished realization's Git record. Preserve
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
            let view = self.with_own_workspaces(id, op, &parents, view, &reserved)?;
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
        published
            .get(canonical)
            .cloned()
            .or_else(|| self.local_of(canonical))
            .ok_or_else(|| {
                NodeError::NotRealizable(canonical.0.hex(), "its local operation is missing")
            })
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
    /// alone left it. Returns the realization as exported, which `canonical` translates to,
    /// not the merge.
    ///
    /// In the protocol model the head update and jj's merge are separate steps:
    /// `SyncStep.advance` followed by `EnvStep.merge` (`advance_merge_refines` in
    /// `formal/Musubi/Safety.lean`). The merge creates a canonical operation; realization
    /// alone does not. Working-copy cleanup below can load and merge the heads too, even
    /// in a non-colocated repository, and may write a separate working-copy repair.
    pub fn advance(&mut self, canonical: &CanonicalOp) -> Result<LocalOp, NodeError> {
        let op_heads_store = self.loader.op_heads_store().clone();
        // Prepare outside both publication locks. A native command can publish while this
        // runs, so compare the exact captured head set again under those locks.
        let (prepared, locks) = loop {
            let mut prepared = self.prepare_advance(canonical)?;
            if let Some(locks) = self.lock_if_unchanged(&mut prepared.heads, &*op_heads_store)? {
                break (prepared, locks);
            }
        };
        let Prepared {
            mut realized,
            superseded,
            concurrent,
            ..
        } = prepared;
        let current_git = self.carry_current_git(canonical, &mut realized)?;
        let beside = self.beside(&realized, concurrent);
        let exported = self.export_and_merge(realized, &beside.merging, current_git)?;
        if locks.colocated() {
            self.insert_map(exported.head.clone(), canonical.clone())?;
        }
        self.move_heads_to(&exported, &beside, superseded)?;
        locks.release();
        self.replace_abandoned_working_copies()?;
        Ok(exported.head)
    }

    /// Realizes `canonical` beside the op heads as they are now, outside the publication
    /// locks, and finds how [`Self::advance`] publishes it.
    fn prepare_advance(&mut self, canonical: &CanonicalOp) -> Result<Prepared, NodeError> {
        self.settle()?;
        if !self.heads_mapped {
            self.canonical_heads()?;
        }
        self.realizing.clear_prepared();
        let heads = self.local_heads()?;
        let published = self.published_realizations(&heads)?;
        let realized = self.current_realization(canonical, &published)?;
        let (superseded, concurrent) = self.check_mergeable(canonical, &realized, &heads)?;
        Ok(Prepared {
            heads,
            realized,
            superseded,
            concurrent,
        })
    }

    /// Takes the publication locks, jj's colocated import/export lock first in a colocated
    /// repository, if the op heads are still those `captured`; otherwise releases them again.
    fn lock_if_unchanged<'a>(
        &self,
        captured: &mut [LocalOp],
        op_heads_store: &'a dyn OpHeadsStore,
    ) -> Result<Option<PublicationLocks<'a>>, NodeError> {
        self.race();
        let git = self.colocation().map(Colocation::lock).transpose()?;
        let heads = self.lock_heads(op_heads_store)?;
        let mut now = self.local_heads()?;
        captured.sort();
        now.sort();
        if now[..] != captured[..] {
            drop(heads);
            drop(git);
            return Ok(None);
        }
        Ok(Some(PublicationLocks { heads, git }))
    }

    /// Under the publication locks, gives `realized`, the realization of `canonical`, this
    /// copy's current Git records, from its op heads as they are now, if it needs them: where
    /// the hive has forgotten this machine, and it keeps private workspaces the realization
    /// would leave without the shared authority for them. Returns whether it did.
    fn carry_current_git(
        &mut self,
        canonical: &CanonicalOp,
        realized: &mut LocalOp,
    ) -> Result<bool, NodeError> {
        // Recheck the source under the colocated lock, after all realization work. A known
        // forgotten copy with retained private workspaces has the missing shared authority
        // even when its saved accepted base is non-root. Use its actual current Git
        // bookkeeping, and merge shared payloads before the export.
        let sources = self.local_heads()?;
        let presence = self.presence(canonical)?;
        let absent = presence.known().contains(self.machine.key())
            && !presence.is_present(self.machine.key());
        if !absent {
            return Ok(false);
        }
        let own = self.own_at_heads(&sources)?;
        let raw = self
            .loader
            .op_store()
            .read_operation(&realized.0)
            .block_on()?;
        let view = self.loader.op_store().read_view(&raw.view_id).block_on()?;
        let target_own = self.own_of_view(view.wc_commit_ids, canonical, &raw)?;
        if !own.keys().any(|name| target_own.contains_key(name)) {
            return Ok(false);
        }
        let fields = self.inherited_per_machine(&sources)?;
        *realized = self.with_per_machine(realized, &fields, canonical)?;
        self.insert_map(realized.clone(), canonical.clone())?;
        Ok(true)
    }

    /// What `realized` is published beside: the op heads `check_mergeable` found `concurrent`
    /// with it.
    fn beside(&self, realized: &LocalOp, concurrent: Vec<Operation>) -> Beside {
        // Everything the realization is merged with, each once: jj doesn't merge an operation
        // with itself.
        let mut merging: Vec<Operation> = vec![];
        for op in concurrent {
            if op.id() != &realized.0 && merging.iter().all(|m| m.id() != op.id()) {
                merging.push(op);
            }
        }
        Beside { merging }
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
                    )?),
                    // `check_mergeable` merged them already, so this is a store error or a jj
                    // bug.
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

    /// Moves the op heads to `exported`, in place of the op heads it replaces, `superseded`
    /// among them.
    fn move_heads_to(
        &mut self,
        exported: &Exported,
        beside: &Beside,
        superseded: Vec<LocalOp>,
    ) -> Result<(), NodeError> {
        let Exported { head, merged } = exported;
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
        self.loader
            .op_heads_store()
            .update_op_heads(&replaced, &merged.as_ref().unwrap_or(head).0)
            .block_on()?;
        Ok(())
    }
}
