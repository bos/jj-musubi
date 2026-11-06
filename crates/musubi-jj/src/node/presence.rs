//! Which copies are present at canonical operations (see `crate::presence`), and forgetting
//! copies: another machine's, as `musubi forget` does, or this one's, as `musubi leave` does.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;
use std::sync::PoisonError;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::View;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::index_err;
use crate::canonical::Work;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::FORGET_ATTRIBUTE;
use crate::presence::Presence;
use crate::workspaces;

/// This machine's own workspace names as of its latest work (`Presence::worked`), the last
/// asked about.
pub(super) type WorkedNames = Option<(Vec<Option<CanonicalOp>>, Arc<BTreeSet<WorkspaceNameBuf>>)>;

/// The names of this machine's own workspaces in a canonical view.
fn own_keys(node: &NodeRepo, view: &View) -> BTreeSet<WorkspaceNameBuf> {
    view.wc_commit_ids
        .keys()
        .filter(|key| node.is_own_key(key))
        .map(|key| WorkspaceNameBuf::from(super::view::key_workspace(key)))
        .collect()
}

impl NodeRepo {
    /// The copies present at canonical operation `op`. Unless an ancestor's presence is
    /// remembered, this reads the history below `op`, once.
    pub fn presence(&self, op: &CanonicalOp) -> Result<Arc<Presence<Work>>, NodeError> {
        if op != self.canonical.root_operation_id() && !self.canonical.has_operation(op) {
            return Err(NodeError::NotRealizable(op.0.hex(), "operation not stored"));
        }
        Ok(self.presences.presence(&self.canonical, op)?)
    }

    /// Presence before an operation's own effect, from its parents'.
    pub(super) fn merge_presence(
        &self,
        parents: &[(CanonicalOp, Arc<Presence<Work>>)],
    ) -> Result<Presence<Work>, NodeError> {
        Ok(crate::canonical::merge_presence(&self.canonical, parents)?)
    }

    /// Remembers the presence at canonical operation `op`, just written.
    pub(super) fn remember_presence(&self, op: CanonicalOp, presence: Presence<Work>) {
        self.presences.remember(op, presence);
    }

    /// The copies present as of this machine's (merged) op head, and the canonical form of
    /// that head.
    pub fn present_copies(&mut self) -> Result<(CanonicalOp, Arc<Presence<Work>>), NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        let presence = self.presence(&canonical)?;
        Ok((canonical, presence))
    }

    /// The key of the other machine shown here as `name`, as of this machine's op head: the
    /// machine whose workspaces are `name/...`, as in `name/default@`. Any other name it could
    /// be shown under (`workspaces::could_be_shown_as`), as the hub, which names machines
    /// among every machine, may list it, or its plain name (`laptop` for one shown as
    /// `laptop-1a2b`), or a whole machine key (`laptop#1a2b3c4d`), names it too, if no other
    /// machine shown here has it.
    pub fn machine_named(&mut self, name: &str) -> Result<Option<String>, NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        let shown = self.shown_names(&canonical)?;
        let only = |matches: Vec<&String>| match matches.as_slice() {
            [one] => Some((*one).clone()),
            _ => None,
        };
        Ok(only(
            shown
                .iter()
                .filter(|(machine, prefix)| *prefix == name || *machine == name)
                .map(|(machine, _)| machine)
                .collect(),
        )
        .or_else(|| {
            only(
                shown
                    .keys()
                    .filter(|machine| workspaces::could_be_shown_as(machine, name))
                    .collect(),
            )
        })
        .or_else(|| {
            only(
                shown
                    .keys()
                    .filter(|machine| workspaces::machine_name(machine) == name)
                    .collect(),
            )
        }))
    }

    /// Forgets another machine's copy, `copy` (its machine key), as `musubi forget` does: an
    /// operation that removes its workspaces from the view, as `jj workspace forget` would,
    /// abandoning each working-copy commit that is empty, and that the hive takes as a forget
    /// of the copy. Writes nothing, and returns false, if the copy isn't present.
    pub fn forget_copy(&mut self, copy: &str, display: &str) -> Result<bool, NodeError> {
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(&LocalOp(repo.op_id().clone()))?;
        if !self.presence(&canonical)?.is_present(copy) {
            return Ok(false);
        }
        let names: Vec<WorkspaceNameBuf> = self
            .other_names(&canonical)?
            .into_iter()
            .filter(|(_, key)| workspaces::split_key(key.as_str()).is_some_and(|(m, _)| m == copy))
            .map(|(name, _)| name)
            .collect();
        forget_workspaces(&repo, &names, copy, &format!("musubi: forget {display}"))?;
        Ok(true)
    }

    /// Forgets, in one operation, every copy present here but this one that `keep` doesn't
    /// name, as [`Self::forget_copy`] forgets one: as a copy does when it joins a hive whose
    /// head lacks copies its history brings from another hive (docs/internals/copies.md,
    /// R8). Returns the keys it forgot, writing nothing if there are none.
    pub fn forget_copies_except(
        &mut self,
        keep: &BTreeSet<String>,
    ) -> Result<Vec<String>, NodeError> {
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(&LocalOp(repo.op_id().clone()))?;
        let own = self.machine.key().to_owned();
        let forgotten: Vec<String> = self
            .presence(&canonical)?
            .copies()
            .filter(|copy| *copy != own && !keep.contains(*copy))
            .map(str::to_owned)
            .collect();
        if forgotten.is_empty() {
            return Ok(forgotten);
        }
        let names: Vec<WorkspaceNameBuf> = self
            .other_names(&canonical)?
            .into_iter()
            .filter(|(_, key)| {
                workspaces::split_key(key.as_str())
                    .is_some_and(|(machine, _)| forgotten.iter().any(|copy| copy == machine))
            })
            .map(|(name, _)| name)
            .collect();
        forget_workspaces(
            &repo,
            &names,
            &forgotten.join(" "),
            "musubi: forget copies of another hive",
        )?;
        Ok(forgotten)
    }

    /// Forgets this machine's copy, as `musubi leave` does before it stops syncing: an
    /// operation that removes this machine's workspaces, abandoning each working-copy commit
    /// that is empty, and that the hive takes as a forget of this copy. Returns the
    /// workspaces it removed, for [`Self::restore_workspaces`] to put back here once the
    /// hive has the forget, or `None`, writing nothing, if the copy isn't present.
    pub fn forget_self(&mut self) -> Result<Option<Vec<(WorkspaceNameBuf, CommitId)>>, NodeError> {
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(&LocalOp(repo.op_id().clone()))?;
        if !self.presence(&canonical)?.is_present(self.machine.key()) {
            return Ok(None);
        }
        let own = self.own_workspaces(&repo, &canonical)?;
        let mut tx = repo.start_transaction();
        for name in own.keys() {
            tx.repo_mut()
                .remove_workspace(name)
                .block_on()
                .map_err(index_err)?;
        }
        tx.repo_mut().rebase_descendants().block_on()?;
        tx.set_attribute(FORGET_ATTRIBUTE.to_owned(), self.machine.key().to_owned());
        tx.commit("musubi: leave").block_on()?;
        Ok(Some(own.into_iter().collect()))
    }

    /// Puts back the workspaces [`Self::forget_self`] removed, each at its commit, which may
    /// be hidden now: one the forget abandoned gets a new commit with this copy's next work,
    /// or with [`Self::give_back_working_copies`] if it leaves.
    pub fn restore_workspaces(
        &mut self,
        removed: &[(WorkspaceNameBuf, CommitId)],
    ) -> Result<(), NodeError> {
        let repo = self.merged_repo()?;
        let mut tx = repo.start_transaction();
        for (name, commit) in removed {
            if tx.repo().view().get_wc_commit_id(name).is_none() {
                tx.repo_mut()
                    .set_wc_commit(name.clone(), commit.clone())
                    .map_err(index_err)?;
            }
        }
        tx.commit("musubi: keep this copy's working copies after leaving")
            .block_on()?;
        Ok(())
    }

    /// Gives each of this machine's workspaces whose working-copy commit is hidden a visible
    /// one, as [`Self::replace_abandoned_working_copies`] does, even if the hive has forgotten
    /// this machine: for a copy leaving its hive, which no next work of its will show again.
    pub fn give_back_working_copies(&mut self) -> Result<Vec<String>, NodeError> {
        self.replace_hidden_working_copies(true)
    }

    /// This machine's own workspaces in `repo`'s view, whose canonical form is `canonical`.
    pub(super) fn own_workspaces(
        &self,
        repo: &ReadonlyRepo,
        canonical: &CanonicalOp,
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        self.own_of_view(
            repo.view().wc_commit_ids().clone(),
            canonical,
            repo.operation().store_operation(),
        )
    }

    /// This machine's own of `workspaces`, a local view's, whose canonical form is
    /// `canonical`: every one but those the canonical view gives other machines, and other
    /// machines' under names the hive no longer gives them (`names_other_machine`).
    pub(super) fn own_of_view(
        &self,
        workspaces: BTreeMap<WorkspaceNameBuf, CommitId>,
        canonical: &CanonicalOp,
        op: &jj_lib::op_store::Operation,
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        if canonical == self.canonical.root_operation_id() {
            return Ok(workspaces);
        }
        let private = self.private_workspace_names(op, &workspaces)?;
        let canonical_view = self.canonical.read_operation_view(canonical)?;
        let prefixes =
            self.prefixes_with_own(&canonical_view, &*self.presence(canonical)?, &private)?;
        let others: BTreeSet<_> = self
            .names_of(&canonical_view, &prefixes)
            .into_iter()
            .filter(|(key, _)| !self.is_own_key(key))
            .map(|(_, name)| name)
            .collect();
        let machines = self.known_machines(canonical)?;
        let own = self.own_names(canonical)?;
        Ok(workspaces
            .into_iter()
            .filter(|(name, _)| {
                !others.contains(name)
                    && (private.contains(name)
                        || own.contains(name)
                        || !self.names_other_machine(name, &machines))
            })
            .collect())
    }

    /// Merges this copy's bindings over the actual native heads and native merge bases.
    /// Canonical operations can omit them while the copy is forgotten.
    pub(super) fn merged_local_workspaces(
        &self,
        ops: &[jj_lib::operation::Operation],
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        let of = |op: &jj_lib::operation::Operation| {
            let local = LocalOp(op.id().clone());
            // A prejoin branch has no shared namespace: as at the join boundary,
            // its native slots belong to this copy. It must not block taking a trim.
            let canonical = self
                .canonical_of(&local)
                .unwrap_or_else(|| self.canonical.root_operation_id().clone());
            let view = op.view().block_on()?;
            self.own_of_view(
                view.wc_commit_ids().clone(),
                &canonical,
                op.store_operation(),
            )
        };
        let Some((first, rest)) = ops.split_first() else {
            return Ok(BTreeMap::new());
        };
        let mut merged = of(first)?;
        let mut parents = vec![first.clone()];
        for other in rest {
            let bases = jj_lib::op_walk::closest_common_ancestors(parents.clone(), [other.clone()])
                .block_on()?;
            let base = match bases.as_slice() {
                [] => BTreeMap::new(),
                [one] => of(one)?,
                several => self.merged_local_workspaces(several)?,
            };
            let theirs = of(other)?;
            let keys: BTreeSet<_> = merged
                .keys()
                .chain(base.keys())
                .chain(theirs.keys())
                .cloned()
                .collect();
            merged = keys
                .into_iter()
                .filter_map(|key| {
                    workspaces::merge_working_copy(
                        merged.get(&key),
                        base.get(&key),
                        theirs.get(&key),
                    )
                    .cloned()
                    .map(|value| (key, value))
                })
                .collect();
            parents.push(other.clone());
        }
        Ok(merged)
    }

    /// The names of this machine's own workspaces as of a canonical operation: those in its
    /// view where this machine is present, and where the hive has forgotten it, those it had
    /// at its latest work, still its own here.
    pub(super) fn own_names(
        &self,
        canonical: &CanonicalOp,
    ) -> Result<BTreeSet<WorkspaceNameBuf>, NodeError> {
        if canonical == self.canonical.root_operation_id() {
            return Ok(BTreeSet::new());
        }
        let view = self.canonical.read_operation_view(canonical)?;
        // A view with workspaces of this machine's has them because it is present: no need to
        // work out presence, which for an old operation reads the history below it.
        let own = own_keys(self, &view);
        if !own.is_empty() {
            return Ok(own);
        }
        self.own_names_in(&view, &*self.presence(canonical)?)
    }

    /// [`Self::own_names`] of a canonical operation with this view and presence.
    pub(super) fn own_names_in(
        &self,
        view: &View,
        presence: &Presence<Work>,
    ) -> Result<BTreeSet<WorkspaceNameBuf>, NodeError> {
        let key = self.machine.key();
        let worked = match presence.worked(key) {
            Some(worked) if !presence.is_present(key) => worked,
            _ => return Ok(own_keys(self, view)),
        };
        let memo = || {
            self.worked_names
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
        };
        // By the operations that stand for the work: work an abandon dropped has none here, and
        // no view, so its names went with it.
        let ops: Vec<Option<CanonicalOp>> = worked.iter().map(|work| work.op.clone()).collect();
        if let Some((remembered, names)) = &*memo()
            && *remembered == ops
        {
            return Ok((**names).clone());
        }
        let mut names = BTreeSet::new();
        for op in ops.iter().flatten() {
            names.extend(own_keys(self, &self.canonical.read_operation_view(op)?));
        }
        *memo() = Some((ops, Arc::new(names.clone())));
        Ok(names)
    }

    /// Every machine a canonical operation's history has known (`machines_of`).
    pub(super) fn known_machines(
        &self,
        canonical: &CanonicalOp,
    ) -> Result<BTreeSet<String>, NodeError> {
        if canonical == self.canonical.root_operation_id() {
            return Ok(BTreeSet::new());
        }
        let view = self.canonical.read_operation_view(canonical)?;
        Ok(self.machines_of(&view, self.presence(canonical)?.known()))
    }

    /// Whether jj's workspace store records a working copy here for `name`, or can't say:
    /// a guard against dropping a workspace of this machine's own whose name looks like
    /// another machine's. Never what decides whose a workspace is, since repositories from
    /// before the store have none of theirs in it.
    pub(super) fn may_be_registered(&self, name: &jj_lib::ref_name::WorkspaceName) -> bool {
        !matches!(
            self.loader.workspace_store().get_workspace_path(name),
            Ok(None)
        )
    }

    /// The local names of other machines' workspaces in a canonical operation's view, with
    /// their keys.
    pub(super) fn other_names(
        &self,
        canonical: &CanonicalOp,
    ) -> Result<BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>, NodeError> {
        if canonical == self.canonical.root_operation_id() {
            return Ok(BTreeMap::new());
        }
        let view = self.canonical.read_operation_view(canonical)?;
        let prefixes = self.machine_prefixes(canonical, &view)?;
        Ok(self
            .names_of(&view, &prefixes)
            .into_iter()
            .filter(|(key, _)| !self.is_own_key(key))
            .map(|(key, name)| (name, key))
            .collect())
    }

    /// Machine prefixes reserve local workspace names even when a copy currently has no
    /// workspace. Membership, rather than workspace existence, determines who can be named.
    pub(super) fn machine_prefixes(
        &self,
        canonical: &CanonicalOp,
        view: &View,
    ) -> Result<BTreeMap<String, String>, NodeError> {
        let private = if let Some(local) = self.local_of(canonical) {
            let op = self.loader.op_store().read_operation(&local.0).block_on()?;
            let local_view = self.loader.op_store().read_view(&op.view_id).block_on()?;
            self.private_workspace_names(&op, &local_view.wc_commit_ids)?
        } else {
            BTreeSet::new()
        };
        self.prefixes_with_own(view, &*self.presence(canonical)?, &private)
    }
}

/// Removes the selected workspaces and records the copies forgotten, in one operation.
fn forget_workspaces(
    repo: &Arc<ReadonlyRepo>,
    names: &[WorkspaceNameBuf],
    copies: &str,
    description: &str,
) -> Result<(), NodeError> {
    let mut tx = repo.start_transaction();
    for name in names {
        if tx.repo().view().get_wc_commit_id(name).is_some() {
            tx.repo_mut()
                .remove_workspace(name)
                .block_on()
                .map_err(index_err)?;
        }
    }
    tx.repo_mut().rebase_descendants().block_on()?;
    tx.set_attribute(FORGET_ATTRIBUTE.to_owned(), copies.to_owned());
    tx.commit(description).block_on()?;
    Ok(())
}
