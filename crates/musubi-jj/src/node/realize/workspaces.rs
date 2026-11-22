//! Preserving this copy's workspace ownership while preparing received operations. This
//! module computes the views without publishing.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;

use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;
use pollster::FutureExt as _;

use super::super::NodeError;
use super::super::NodeRepo;
use super::super::view::LocalView;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::Kind;
use crate::workspaces;

impl NodeRepo {
    /// `local`, the local view of canonical operation `canonical_id`, with this machine's own
    /// workspaces if it has none of them and the hive has forgotten this machine there: as the
    /// realization of its parent with the machine's latest work has them
    /// (`latest_work_parent`), following the operation's rewrites. They are still its working
    /// copies, and the hive shows them again with its next work. So too at work by this
    /// machine, where it is present: such an operation, realized here, is one another machine
    /// wrote for it, as an earlier release's fix-up, maybe where it had forgotten this machine
    /// and so without its workspaces; only this machine's own operations remove them. A view
    /// that has this machine's workspaces, or where it is otherwise present without any, is
    /// left as it is, but for this machine's workspaces with a `/` in their names, which no
    /// canonical view has (`view::is_publishable`): those it keeps as the parent has them, as
    /// it keeps the others while forgotten.
    pub(super) fn with_own_workspaces(
        &mut self,
        canonical_id: &CanonicalOp,
        op: &StoreOperation,
        parents: &[LocalOp],
        local: LocalView,
    ) -> Result<LocalView, NodeError> {
        let published = local.names.keys().any(|key| self.is_own_key(key));
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
        if own.is_empty() {
            return Ok(local);
        }
        let own_work = Kind::of(&op.metadata).work.as_deref() == Some(self.machine.key());
        if published || !own_work && self.presence(canonical_id)?.is_present(self.machine.key()) {
            own.retain(|name, _| !super::super::view::is_publishable(name));
            if own.is_empty() {
                return Ok(local);
            }
        }
        workspaces::follow_rewrites(&mut own, op.commit_predecessors.as_ref());
        let LocalView {
            mut view,
            mut names,
            mut prefixes,
            ..
        } = local;
        let private: BTreeSet<WorkspaceNameBuf> = own.keys().cloned().collect();
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
