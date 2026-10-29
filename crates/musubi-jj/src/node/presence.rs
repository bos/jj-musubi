//! Which copies are present at canonical operations (see `crate::presence`), and forgetting
//! copies: another machine's, as `musubi forget` does, or this one's, as `musubi leave` does.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::PoisonError;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::Repo as _;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::index_err;
use crate::presence::FORGET_ATTRIBUTE;
use crate::presence::Kind;
use crate::presence::Presence;
use crate::workspaces;

/// How many operations' presence to remember: those computed last, which the next
/// operations' parents mostly are.
const REMEMBERED: usize = 256;

/// This machine's own workspace names as of its latest work (`Presence::worked`), the last
/// asked about.
pub(super) type WorkedNames = Option<(BTreeSet<OperationId>, Arc<BTreeSet<WorkspaceNameBuf>>)>;

/// The names of this machine's own workspaces in a canonical view.
fn own_keys(node: &NodeRepo, view: &View) -> BTreeSet<WorkspaceNameBuf> {
    view.wc_commit_ids
        .keys()
        .filter(|key| node.is_own_key(key))
        .map(|key| WorkspaceNameBuf::from(super::view::key_workspace(key)))
        .collect()
}

/// Presence at canonical operations, for the last [`REMEMBERED`] computed.
#[derive(Default)]
pub(super) struct PresenceMemo {
    presences: HashMap<OperationId, Arc<Presence<OperationId>>>,
    order: VecDeque<OperationId>,
}

impl PresenceMemo {
    fn get(&self, op: &OperationId) -> Option<Arc<Presence<OperationId>>> {
        self.presences.get(op).cloned()
    }

    fn insert(&mut self, op: OperationId, presence: Arc<Presence<OperationId>>) {
        if self.presences.insert(op.clone(), presence).is_none() {
            self.order.push_back(op);
        }
        while self.order.len() > REMEMBERED {
            if let Some(old) = self.order.pop_front() {
                self.presences.remove(&old);
            }
        }
    }
}

impl NodeRepo {
    /// The copies present at canonical operation `op`. Unless an ancestor's presence is
    /// remembered, this reads the history below `op`, once.
    pub fn presence(&self, op: &OperationId) -> Result<Arc<Presence<OperationId>>, NodeError> {
        let root = self.canonical.root_operation_id();
        if op == root {
            return Ok(Arc::default());
        }
        if !self.canonical.has_operation(op) {
            return Err(NodeError::NotRealizable(op.hex(), "operation not stored"));
        }
        let memo = || {
            self.presences
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
        };
        if let Some(presence) = memo().get(op) {
            return Ok(presence);
        }
        // The operations whose presence isn't known, ancestors first, each read once, then each
        // one's from its parents', keeping each only until the last of its children in the
        // walk needs it.
        let mut ops: Vec<(OperationId, Vec<OperationId>, Kind)> = vec![];
        let mut seen: HashSet<OperationId> = HashSet::new();
        let mut stack: Vec<(OperationId, Option<jj_lib::op_store::Operation>)> =
            vec![(op.clone(), None)];
        while let Some((id, stored)) = stack.pop() {
            match stored {
                Some(stored) => ops.push((id, stored.parents, Kind::of(&stored.metadata))),
                None => {
                    if !seen.insert(id.clone()) || id == *root || memo().get(&id).is_some() {
                        continue;
                    }
                    let stored = self.canonical.read_operation(&id)?;
                    let parents: Vec<OperationId> = stored
                        .parents
                        .iter()
                        .filter(|parent| !seen.contains(*parent))
                        .cloned()
                        .collect();
                    stack.push((id, Some(stored)));
                    stack.extend(parents.into_iter().map(|parent| (parent, None)));
                }
            }
        }
        // Another thread worked it out meanwhile.
        if ops.last().map(|(id, _, _)| id) != Some(op) {
            let remembered = memo().get(op);
            return remembered.map_or_else(|| self.presence(op), Ok);
        }
        let mut children: HashMap<OperationId, usize> = HashMap::new();
        for (_, parents, _) in &ops {
            for parent in parents {
                *children.entry(parent.clone()).or_default() += 1;
            }
        }
        let mut walked: HashMap<OperationId, Arc<Presence<OperationId>>> = HashMap::new();
        let mut presence = Arc::default();
        for (id, parents, kind) in ops {
            self.canonical.note_generation(&id, &parents);
            let mut of_parents = Vec::with_capacity(parents.len());
            for parent in &parents {
                let known = match walked.get(parent) {
                    Some(known) => known.clone(),
                    None if parent == root => Arc::default(),
                    None => {
                        // Not under the lock: working it out takes it.
                        let remembered = memo().get(parent);
                        match remembered {
                            Some(known) => known,
                            None => self.presence(parent)?,
                        }
                    }
                };
                of_parents.push((parent.clone(), known));
            }
            presence = if let ([(_, only)], None, true) =
                (of_parents.as_slice(), &kind.work, kind.forgets.is_empty())
            {
                only.clone()
            } else {
                Arc::new(self.merge_presence(&of_parents)?.apply(&id, &kind))
            };
            for parent in &parents {
                if let Some(left) = children.get_mut(parent) {
                    *left -= 1;
                    if *left == 0 {
                        walked.remove(parent);
                    }
                }
            }
            if children.get(&id).is_some_and(|&left| left > 0) {
                walked.insert(id, presence.clone());
            }
        }
        memo().insert(op.clone(), presence.clone());
        Ok(presence)
    }

    /// Presence before an operation's own effect, from its parents'.
    pub(super) fn merge_presence(
        &self,
        parents: &[(OperationId, Arc<Presence<OperationId>>)],
    ) -> Result<Presence<OperationId>, NodeError> {
        let parents: Vec<(OperationId, &Presence<OperationId>)> = parents
            .iter()
            .map(|(op, presence)| (op.clone(), presence.as_ref()))
            .collect();
        Ok(Presence::merge(&parents, |a, b| {
            self.canonical.is_ancestor_of(a, b)
        })?)
    }

    /// Remembers the presence at canonical operation `op`, just written.
    pub(super) fn remember_presence(&self, op: OperationId, presence: Presence<OperationId>) {
        self.presences
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(op, Arc::new(presence));
    }

    /// The copies present as of this machine's (merged) op head, and the canonical form of
    /// that head.
    pub fn present_copies(
        &mut self,
    ) -> Result<(OperationId, Arc<Presence<OperationId>>), NodeError> {
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
        let own = self.machine.key().to_owned();
        let shown: BTreeMap<String, String> = self
            .other_names(&canonical)?
            .into_iter()
            .filter_map(|(local, key)| {
                let (machine, _) = workspaces::split_key(key.as_str())?;
                let (prefix, _) = local.as_str().split_once('/')?;
                (machine != own).then(|| (machine.to_owned(), prefix.to_owned()))
            })
            .collect();
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
        let canonical = self.canonicalize(repo.op_id())?;
        if !self.presence(&canonical)?.is_present(copy) {
            return Ok(false);
        }
        let names: Vec<WorkspaceNameBuf> = self
            .other_names(&canonical)?
            .into_iter()
            .filter(|(_, key)| workspaces::split_key(key.as_str()).is_some_and(|(m, _)| m == copy))
            .map(|(name, _)| name)
            .collect();
        let mut tx = repo.start_transaction();
        for name in &names {
            if tx.repo().view().get_wc_commit_id(name).is_some() {
                tx.repo_mut()
                    .remove_workspace(name)
                    .block_on()
                    .map_err(index_err)?;
            }
        }
        tx.repo_mut().rebase_descendants().block_on()?;
        tx.set_attribute(FORGET_ATTRIBUTE.to_owned(), copy.to_owned());
        tx.commit(format!("musubi: forget {display}")).block_on()?;
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
        let canonical = self.canonicalize(repo.op_id())?;
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
        let mut tx = repo.start_transaction();
        for name in &names {
            if tx.repo().view().get_wc_commit_id(name).is_some() {
                tx.repo_mut()
                    .remove_workspace(name)
                    .block_on()
                    .map_err(index_err)?;
            }
        }
        tx.repo_mut().rebase_descendants().block_on()?;
        tx.set_attribute(FORGET_ATTRIBUTE.to_owned(), forgotten.join(" "));
        tx.commit("musubi: forget copies of another hive")
            .block_on()?;
        Ok(forgotten)
    }

    /// Forgets this machine's copy, as `musubi leave` does before it stops syncing: an
    /// operation that removes this machine's workspaces, abandoning each working-copy commit
    /// that is empty, and that the hive takes as a forget of this copy. Returns the
    /// workspaces it removed, for [`Self::restore_workspaces`] to put back here once the
    /// hive has the forget, or `None`, writing nothing, if the copy isn't present.
    pub fn forget_self(&mut self) -> Result<Option<Vec<(WorkspaceNameBuf, CommitId)>>, NodeError> {
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(repo.op_id())?;
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
        repo: &jj_lib::repo::ReadonlyRepo,
        canonical: &OperationId,
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        self.own_of_view(repo.view().wc_commit_ids().clone(), canonical)
    }

    /// This machine's own of `workspaces`, a local view's, whose canonical form is
    /// `canonical`: every one but those the canonical view gives other machines, and other
    /// machines' under names the hive no longer gives them (`names_other_machine`).
    pub(super) fn own_of_view(
        &self,
        workspaces: BTreeMap<WorkspaceNameBuf, CommitId>,
        canonical: &OperationId,
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        let others = self.other_names(canonical)?;
        let machines = self.known_machines(canonical)?;
        let own = self.own_names(canonical)?;
        Ok(workspaces
            .into_iter()
            .filter(|(name, _)| {
                !others.contains_key(name)
                    && (own.contains(name) || !self.names_other_machine(name, &machines))
            })
            .collect())
    }

    /// The names of this machine's own workspaces as of a canonical operation: those in its
    /// view where this machine is present, and where the hive has forgotten it, those it had
    /// at its latest work, still its own here.
    pub(super) fn own_names(
        &self,
        canonical: &OperationId,
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
        presence: &Presence<OperationId>,
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
        if let Some((ops, names)) = &*memo()
            && ops == worked
        {
            return Ok((**names).clone());
        }
        let mut names = BTreeSet::new();
        for op in worked {
            names.extend(own_keys(self, &self.canonical.read_operation_view(op)?));
        }
        *memo() = Some((worked.clone(), Arc::new(names.clone())));
        Ok(names)
    }

    /// Every machine a canonical operation's history has known (`machines_of`).
    pub(super) fn known_machines(
        &self,
        canonical: &OperationId,
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
        canonical: &OperationId,
    ) -> Result<BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>, NodeError> {
        if canonical == self.canonical.root_operation_id() {
            return Ok(BTreeMap::new());
        }
        let view = self.canonical.read_operation_view(canonical)?;
        Ok(self
            .local_names(&view, &*self.presence(canonical)?)?
            .into_iter()
            .filter(|(key, _)| !self.is_own_key(key))
            .map(|(key, name)| (name, key))
            .collect())
    }
}
