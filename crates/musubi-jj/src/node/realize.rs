//! Constructing local operations from canonical history.
//!
//! This module plans parent-first batches and constructs their operations. `workspaces`
//! preserves local workspace ownership, `writes` owns prepared views and pending writes,
//! `advance` publishes a revalidated native frontier, and `merge` checks jj's merge behavior.

mod advance;
mod merge;
mod workspaces;
mod writes;

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::sync::Arc;
use std::thread;

use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::ref_name::WorkspaceNameBuf;

use super::NodeError;
use super::NodeRepo;
use super::translate::target_of;
use super::view::LocalView;
use super::view::PerMachine;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;

pub(super) use advance::PublishedHistoryCache;
pub(super) use merge::MergeDiagnosis;
#[cfg(test)]
use merge::fields_of;
#[cfg(test)]
pub(super) use merge::merged_by_jj;
#[cfg(test)]
use workspaces::latest_work_index;
use workspaces::with_kept;
pub(super) use writes::State;

/// How many linear descendants have their views prepared or written together.
pub const REALIZE_AT_ONCE: usize = writes::MAX_UNWRITTEN;

/// A constructed local operation, before the write queue takes ownership of it.
struct Realization {
    id: LocalOp,
    op: StoreOperation,
    view: View,
    per_machine: Arc<PerMachine>,
}

impl NodeRepo {
    /// Realizes a stored canonical operation, and any unrealized ancestors, without
    /// publishing it. Returns the local operation id after [`Self::settle`] completes the
    /// current write batch. Its error contract also applies here.
    pub fn realize(&mut self, canonical: &CanonicalOp) -> Result<LocalOp, NodeError> {
        let local = self.realize_pending(canonical, &[])?;
        self.settle()?;
        Ok(local)
    }

    /// Constructs local representations without publishing them, overlapping construction
    /// with native writes. The returned id and its ancestors are known to [`Self::local_of`]
    /// and [`Self::canonical_of`] immediately, but their native operations and views may
    /// still be unwritten, and their translations may exist only in memory.
    ///
    /// Call [`Self::settle`] before reading these results from the stores or relying on
    /// their translations after reopening. [`Self::realize`] and [`Self::advance`] settle
    /// automatically. Dropping the handle attempts to settle too, but only logs errors and
    /// skips settling during unwinding; it does not provide the same success guarantee.
    ///
    /// `next` is only a preparation hint: operations likely realized after this one, in
    /// order. It neither realizes nor publishes them. Making a view
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
        if order.is_empty() {
            return self.local_of(canonical).ok_or_else(|| {
                NodeError::NotRealizable(canonical.0.hex(), "its local operation is missing")
            });
        }
        let starts = self.starts_of(&order);
        let (reserved, kept) = self.reserved_for(&order)?;
        for (i, (id, op)) in order.iter().enumerate() {
            // `unrealized` puts parents first, so a parent missing here is a bug: refuse to
            // realize the operation rather than panic in the daemon.
            let parents: Vec<LocalOp> = CanonicalOp::parents_of(op)
                .iter()
                .map(|parent| {
                    self.local_of(parent).ok_or_else(|| {
                        NodeError::NotRealizable(id.0.hex(), "a parent has no local operation")
                    })
                })
                .collect::<Result<_, _>>()?;
            // Realizing it reads its parents from the store, unless its only parent is the
            // operation realized last.
            if !matches!(
                (parents.as_slice(), self.realizing.last_realized()),
                ([parent], Some((last, _))) if parent == last
            ) {
                self.settle()?;
            }
            let per_machine = self.inherited_per_machine(&parents)?;
            let prepared = self.realizing.take_prepared(id, &per_machine, &reserved);
            let view = match prepared {
                Some(view) => view,
                None => {
                    let later = order[i + 1..].iter().map(|(id, _)| id).chain(next);
                    let run = self.run_after(id, op, later)?;
                    // So that the threads making views each find the presence before theirs
                    // remembered, rather than each reading the history below it.
                    self.presence(id)?;
                    let mut views = self.local_views(&run, &per_machine, &reserved).into_iter();
                    let view = views
                        .next()
                        .expect("a run starts with its first operation")?;
                    // One that failed is made again when its turn comes.
                    let ahead = run[1..]
                        .iter()
                        .zip(views)
                        .filter_map(|((id, _), view)| Some((id.clone(), view.ok()?)))
                        .collect();
                    self.realizing
                        .prepare(per_machine.clone(), reserved.clone(), ahead);
                    view
                }
            };
            let view = self.with_own_workspaces(id, op, &parents, view, &reserved)?;
            let own = self.own_of(&view);
            let view = with_kept(view, &kept);
            let realization =
                self.realize_one(id, op, parents, view, &own, &reserved, per_machine)?;
            self.realizing.remember_own(realization.id.clone(), own);
            self.write_later(realization, id.clone())?;
        }
        let realized = self.local_of(canonical).ok_or_else(|| {
            NodeError::NotRealizable(canonical.0.hex(), "its local operation is missing")
        })?;
        // The next along this line starts from this one, beside the same op heads.
        self.realizing.advance_kept(&starts, &realized);
        Ok(realized)
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

    /// The local views of `ops`, which all inherit `per_machine`, made in parallel, with
    /// other machines' workspaces named clear of `reserved` (`reserved_names`).
    fn local_views(
        &self,
        ops: &[(CanonicalOp, StoreOperation)],
        per_machine: &PerMachine,
        reserved: &BTreeSet<WorkspaceNameBuf>,
    ) -> Vec<Result<LocalView, NodeError>> {
        let make = |part: &[(CanonicalOp, StoreOperation)]| -> Vec<_> {
            part.iter()
                .map(|(id, op)| self.local_view(id, op, per_machine, reserved))
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

    /// Realizes one canonical operation whose parents are realized, as `parents`, without
    /// writing it, from its local view, in which `own` are this machine's own workspaces and
    /// other machines' are shown clear of `reserved` (`reserved_for`).
    #[expect(clippy::too_many_arguments, reason = "each is part of the realization")]
    fn realize_one(
        &self,
        canonical_id: &CanonicalOp,
        op: &StoreOperation,
        parents: Vec<LocalOp>,
        local: LocalView,
        own: &BTreeMap<WorkspaceNameBuf, CommitId>,
        reserved: &BTreeSet<WorkspaceNameBuf>,
        per_machine: Arc<PerMachine>,
    ) -> Result<Realization, NodeError> {
        let LocalView {
            view, id, prefixes, ..
        } = local;
        let mut metadata = op.metadata.clone();
        self.record_private_workspaces(&mut metadata, own.keys().cloned(), canonical_id)?;
        super::view::record_reserved(&mut metadata, reserved);
        if let Some((prefix, target)) = target_of(&metadata.description)
            && let target = CanonicalOp(target)
            && self
                .canonical
                .is_ancestor(&target, &CanonicalOp::parents_of(op))?
        {
            // Realized already, as an ancestor of the parents.
            let local = self.local_of(&target).ok_or_else(|| {
                NodeError::NotRealizable(
                    canonical_id.0.hex(),
                    "the operation it restores or reverts has no local operation",
                )
            })?;
            metadata.description = format!("{prefix}{}", local.0.hex());
        }
        metadata.workspace_name = metadata
            .workspace_name
            .map(|key| self.realized_workspace_name(&key, &prefixes));
        OpAttrs(&mut metadata.attributes).set_canonical(canonical_id);
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
}

#[cfg(all(test, unix))]
mod advance_tests;

#[cfg(all(test, unix))]
mod concurrent_tests;

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]
    use std::collections::BTreeSet;

    use musubi_testutil::TestEnv;

    use super::latest_work_index;
    use crate::canonical::Work;
    use crate::node::NodeRepo;

    #[test]
    fn forgetting_a_workspace_merges_its_git_head_as_jj() {
        use super::{LocalOp, fields_of, merged_by_jj};
        use jj_lib::op_store::RefTarget;
        use jj_lib::ref_name::WorkspaceName;
        use pollster::FutureExt as _;

        let env = TestEnv::new();
        let repo = env.init_repo("owner");
        let node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
        let loaded = node.loader().load_at_head(None).block_on().unwrap();
        let workspace = WorkspaceName::new("owner");
        let target = loaded.view().get_wc_commit_id(workspace).unwrap().clone();
        let mut tx = loaded.start_transaction();
        tx.repo_mut()
            .set_git_head_target(workspace, RefTarget::normal(target));
        let base = tx.commit("record HEAD").block_on().unwrap();
        let ours = base
            .start_transaction()
            .commit("keep workspace")
            .block_on()
            .unwrap();
        // A realization inherits this copy's Git records separately from its shared
        // workspace map. Its HEAD can therefore survive the workspace's removal.
        let mut view = base.view().store_view().clone();
        view.wc_commit_ids.remove(workspace);
        let mut tx = base.start_transaction();
        tx.repo_mut().set_view(view);
        let theirs = tx.commit("realize forgotten workspace").block_on().unwrap();
        assert_eq!(
            fields_of(ours.operation()).unwrap(),
            fields_of(theirs.operation()).unwrap()
        );
        let rest = [LocalOp(theirs.operation().id().clone())];
        assert!(
            node.merged_trivially(ours.operation(), &rest)
                .unwrap()
                .is_none()
        );
        let merged = merged_by_jj(node.loader(), ours.operation().clone(), &rest).unwrap();
        let mut expected = base.view().store_view().clone();
        expected.git_heads.clear();
        assert_eq!(*merged, super::PerMachine::of(&expected));
        assert_eq!(
            *node
                .inherited_per_machine(&[LocalOp(ours.operation().id().clone()), rest[0].clone()])
                .unwrap(),
            *merged
        );
    }

    #[test]
    fn concrete_work_keeps_the_namespace_after_a_deletion() {
        let env = TestEnv::new();
        let repo = env.init_repo("owner");
        repo.jj(&[
            "workspace",
            "add",
            "--name",
            "second",
            env.root().join("second").to_str().unwrap(),
        ]);
        let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
        let old = node.canonical_heads().unwrap().pop().unwrap();
        repo.jj(&["workspace", "forget", "second"]);
        let current = node.canonical_heads().unwrap().pop().unwrap();
        let store = node.canonical_store();
        let second = format!("{}/second", node.machine().key());
        let old_op = store.read_operation(&old).unwrap();
        let current_op = store.read_operation(&current).unwrap();
        assert!(
            store
                .read_view(&old_op.view_id)
                .unwrap()
                .wc_commit_ids
                .keys()
                .any(|key| key.as_str() == second)
        );
        assert!(
            !store
                .read_view(&current_op.view_id)
                .unwrap()
                .wc_commit_ids
                .keys()
                .any(|key| key.as_str() == second)
        );
        let mut dropped = Work::of(store, &old).unwrap();
        // Contraction retains the original identity while removing its operation.
        dropped.op = None;
        let concrete = Work::of(store, &current).unwrap();
        let old_names = BTreeSet::from([dropped.clone()]);
        let deleted = BTreeSet::from([concrete]);
        assert_eq!(
            latest_work_index(
                store,
                &[old.clone(), current.clone()],
                &[old_names.clone(), deleted.clone()]
            )
            .unwrap(),
            1
        );
        assert_eq!(
            latest_work_index(
                store,
                &[current.clone(), old.clone()],
                &[deleted, old_names.clone()]
            )
            .unwrap(),
            0
        );
        let mut other_dropped = Work::of(store, &current).unwrap();
        other_dropped.op = None;
        assert_eq!(
            latest_work_index(
                store,
                &[old.clone(), current.clone()],
                &[old_names, BTreeSet::from([other_dropped])]
            )
            .unwrap(),
            0,
            "two erased operations provide no ordering evidence"
        );
        // Newer work an abandon dropped, on a line that saw the older concrete work, as
        // a forget that saw a rename: that line has the newer workspaces.
        let older = BTreeSet::from([Work::of(store, &old).unwrap()]);
        let mut newer = Work::of(store, &current).unwrap();
        newer.op = None;
        let newer = BTreeSet::from([newer]);
        assert_eq!(
            latest_work_index(
                store,
                &[old.clone(), current.clone()],
                &[older.clone(), newer.clone()]
            )
            .unwrap(),
            1
        );
        assert_eq!(
            latest_work_index(store, &[current, old], &[newer, older]).unwrap(),
            0
        );
    }
}
