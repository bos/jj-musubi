//! Preserving this copy's workspace ownership while preparing received operations.
//!
//! Reserved and kept names are selected against the current native heads. The write state
//! remembers their preparation context; this module computes the views without publishing.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_walk;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;
use pollster::FutureExt as _;

use super::super::NodeError;
use super::super::NodeRepo;
use super::super::view::LocalView;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::Kind;
use crate::workspaces;

pub(super) type Kept = BTreeMap<WorkspaceNameBuf, CommitId>;

impl NodeRepo {
    /// What realizing `order`, parents first, keeps clear of: this machine's own names in its
    /// op heads (`reserved_names`), which other machines' workspaces are shown clear of; and
    /// those of them that a merge with the heads would merge against, in the views of the
    /// closest common ancestors of the heads and the operations it starts from, at their
    /// commits. Showing another machine's workspaces under a longer name drops the names they
    /// had, which the merge would take for removals, and a removal wins over the heads' own
    /// workspace of that name, as after `jj workspace forget beta/default` and `jj workspace
    /// add --name beta/default`. So a realization keeps such a name as the merge's base has it,
    /// which leaves the merge the heads' own workspace.
    pub(super) fn reserved_for(
        &mut self,
        order: &[(CanonicalOp, StoreOperation)],
    ) -> Result<(Arc<BTreeSet<WorkspaceNameBuf>>, Kept), NodeError> {
        let reserved = self.reserved_names()?;
        if reserved.is_empty() {
            return Ok((reserved, Kept::new()));
        }
        // Only a name one of the machines these views show could be shown under renames them.
        let mut machines = BTreeSet::new();
        for (id, op) in order {
            let view = self.canonical.read_view(&op.view_id)?;
            machines.extend(self.machines_of(&view, self.presence(id)?.known()));
        }
        let renaming: BTreeSet<WorkspaceNameBuf> = reserved
            .iter()
            .filter(|name| self.names_other_machine(name, &machines))
            .cloned()
            .collect();
        let starts = self.starts_of(order);
        if renaming.is_empty() || starts.is_empty() {
            return Ok((reserved, Kept::new()));
        }
        let mut heads = self.local_heads()?;
        heads.sort();
        // A line of realizations beside the same op heads merges against the same base.
        if let [start] = starts.as_slice()
            && let Some(kept) = self.realizing.kept(&heads, start, &renaming)
        {
            return Ok((reserved, kept));
        }
        // The operations it starts from may still be being written.
        if self.realizing.pending_among(&starts) {
            self.settle()?;
        }
        let load = |op: &LocalOp| self.loader.load_operation(&op.0).block_on();
        let start_ops = starts.iter().map(load).collect::<Result<Vec<_>, _>>()?;
        let head_ops = heads.iter().map(load).collect::<Result<Vec<_>, _>>()?;
        let mut kept = Kept::new();
        for base in op_walk::closest_common_ancestors(start_ops, head_ops).block_on()? {
            for (name, commit) in base.view().block_on()?.wc_commit_ids() {
                if renaming.contains(name) {
                    kept.entry(name.clone()).or_insert_with(|| commit.clone());
                }
            }
        }
        if let [start] = starts.as_slice() {
            self.realizing
                .remember_kept(heads, start.clone(), renaming, kept.clone());
        }
        Ok((reserved, kept))
    }

    /// The local operations realizing `order`, parents first, starts from: the realizations
    /// of its operations' parents that aren't in it.
    pub(super) fn starts_of(&self, order: &[(CanonicalOp, StoreOperation)]) -> Vec<LocalOp> {
        let realizing: HashSet<&CanonicalOp> = order.iter().map(|(id, _)| id).collect();
        let mut starts: Vec<LocalOp> = vec![];
        for parent in order.iter().flat_map(|(_, op)| CanonicalOp::parents_of(op)) {
            if !realizing.contains(&parent)
                && let Some(local) = self.local_of(&parent)
                && !starts.contains(&local)
            {
                starts.push(local);
            }
        }
        starts
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
    /// left as it is. Other machines' workspaces stay named clear of `reserved` too.
    pub(super) fn with_own_workspaces(
        &mut self,
        canonical_id: &CanonicalOp,
        op: &StoreOperation,
        parents: &[LocalOp],
        local: LocalView,
        reserved: &BTreeSet<WorkspaceNameBuf>,
        root_own: Option<&BTreeMap<WorkspaceNameBuf, CommitId>>,
    ) -> Result<LocalView, NodeError> {
        if local.names.keys().any(|key| self.is_own_key(key)) {
            return Ok(local);
        }
        let canonical_parents = CanonicalOp::parents_of(op);
        let source = self.latest_work_parent(&canonical_parents)?;
        let mut own = match (parents.get(source), self.realizing.last_own()) {
            (None, _) => return Ok(local),
            (Some(parent), Some((last, own))) if parent == last => (**own).clone(),
            (Some(parent), _) => {
                // It may still be being written.
                self.settle()?;
                let op_store = self.loader.op_store();
                let parent_op = op_store.read_operation(&parent.0).block_on()?;
                let parent_view = op_store.read_view(&parent_op.view_id).block_on()?;
                // `parents` are the realizations of `canonical_parents`, in the same order.
                self.own_of_view(
                    parent_view.wc_commit_ids,
                    &canonical_parents[source],
                    &parent_op,
                )?
            }
        };
        if own.is_empty() && parents.get(source) == Some(self.root_op_id()) {
            own = match root_own {
                Some(own) => own.clone(),
                None => {
                    let heads = self.local_heads()?;
                    self.own_for_root(&heads)?
                }
            };
        }
        let own_work = Kind::of(&op.metadata).work.as_deref() == Some(self.machine.key());
        let fixup = OpAttrs(&op.metadata.attributes).is_fixup();
        if own.is_empty()
            || !own_work && !fixup && self.presence(canonical_id)?.is_present(self.machine.key())
        {
            return Ok(local);
        }
        workspaces::follow_rewrites(&mut own, op.commit_predecessors.as_ref());
        let LocalView {
            mut view,
            mut names,
            mut prefixes,
            ..
        } = local;
        let private: BTreeSet<WorkspaceNameBuf> = own.keys().chain(reserved).cloned().collect();
        let canonical_view = self.canonical.read_view(&op.view_id)?;
        let adjusted =
            self.prefixes_with_own(&canonical_view, &*self.presence(canonical_id)?, &private)?;
        if adjusted != prefixes {
            let adjusted_names = self.names_of(&canonical_view, &adjusted);
            let mut bindings = vec![];
            for (key, old) in &names {
                if !self.is_own_key(key)
                    && let Some(commit) = view.wc_commit_ids.remove(old)
                    && let Some(name) = adjusted_names.get(key)
                {
                    bindings.push((name.clone(), commit));
                }
            }
            view.wc_commit_ids.extend(bindings);
            prefixes = adjusted;
            names = adjusted_names;
        }
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

    pub(super) fn own_for_root(
        &mut self,
        heads: &[LocalOp],
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        match self.own_before_taking(heads) {
            Some(own) => Ok(own.clone()),
            None => self.own_at_heads(heads),
        }
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
        latest_work_index(&self.canonical, parents, &worked)
    }

    /// This machine's own workspaces in a local view: every one but those named for another
    /// machine's.
    pub(super) fn own_of(&self, local: &LocalView) -> BTreeMap<WorkspaceNameBuf, CommitId> {
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

    /// The local name of the workspace that made a canonical operation, as names go in the
    /// operation's view: `default` for this machine's own, `beta/default` for another's,
    /// even one the operation forgot, which the view doesn't name. jj's `undo` and `redo`
    /// refuse to undo another workspace's operation, and they tell workspaces apart only by
    /// name, so with the plain name `jj undo` here would undo beta's latest operation as if it
    /// were this machine's own; and so it would with `beta/default` if that were a workspace
    /// of this machine's own, as it can be where beta is shown as `beta-1a2b`.
    pub(super) fn realized_workspace_name(
        &self,
        key: &WorkspaceName,
        prefixes: &BTreeMap<String, String>,
    ) -> WorkspaceNameBuf {
        self.local_name(key, prefixes)
            .unwrap_or_else(|| key.to_owned())
    }
}

/// `local` with each of `kept` it lacks, at its commit in the base of the realization's merge
/// with the op heads (`reserved_for`).
pub(super) fn with_kept(mut local: LocalView, kept: &Kept) -> LocalView {
    let mut changed = false;
    for (name, commit) in kept {
        if !local.view.wc_commit_ids.contains_key(name) {
            local
                .view
                .wc_commit_ids
                .insert(name.clone(), commit.clone());
            changed = true;
        }
    }
    if changed {
        // The id the op store gives it, worked out as it does.
        local.id = jj_lib::op_store::ViewId::new(blake2b_hash(&local.view).to_vec());
    }
    local
}

/// Pick the branch of `parents` whose work includes every other branch's, given each one's
/// latest work, `worked`. A parent whose history has every other's latest work, none of it its
/// own latest, did later work, even work an abandon dropped since: as a forget's line that saw
/// a rename the abandon dropped, beside a line that saw only the work before it. Otherwise
/// the branch whose concrete work includes every other's; dropped work is compared there by
/// the same relation as presence, rather than given a separate ordering.
pub(super) fn latest_work_index(
    store: &crate::canonical::CanonicalStore,
    parents: &[CanonicalOp],
    worked: &[BTreeSet<crate::canonical::Work>],
) -> Result<usize, NodeError> {
    if worked.iter().all(|ops| *ops == worked[0]) {
        return Ok(0);
    }
    'seen: for (index, (parent, mine)) in parents.iter().zip(worked).enumerate() {
        for theirs in worked {
            for work in theirs.difference(mine) {
                let Some(op) = &work.op else {
                    continue 'seen;
                };
                if !store.is_ancestor_of(op, parent)? {
                    continue 'seen;
                }
            }
        }
        return Ok(index);
    }
    'parents: for (index, mine) in worked.iter().enumerate() {
        for theirs in worked {
            for op in theirs.difference(mine) {
                // Work an abandon dropped is below surviving concrete work, as
                // presence defines it. Rejecting it here would prefer an older
                // private namespace and resurrect names its owner removed.
                let mut seen = false;
                for later in mine {
                    if op.below(store, later)? {
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
