//! Views between their local and canonical forms: this machine's records of its own `.git`,
//! and workspaces' names here and in the hive.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::RemoteView;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::ref_name::GitRefNameBuf;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::Repo as _;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::is_visible;
use crate::workspaces;

/// Per-machine fields of a view that a realization inherits: this machine's record of its
/// own `.git` (`git_refs`, the `git` pseudo-remote, and each workspace's `git_heads`). The
/// working copies come from the canonical view instead. See "Per-machine state in a
/// replicated view" in docs/internals/design.md.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct PerMachine {
    git_refs: BTreeMap<GitRefNameBuf, RefTarget>,
    git_remote: Option<RemoteView>,
    git_heads: BTreeMap<WorkspaceNameBuf, RefTarget>,
}

impl PerMachine {
    pub(super) fn of(view: &View) -> Self {
        Self {
            git_refs: view.git_refs.clone(),
            // An empty `git` remote, which jj leaves when the last ref it exported goes,
            // counts as none, as it does when jj merges views.
            git_remote: view
                .remote_views
                .get(REMOTE_NAME_FOR_LOCAL_GIT_REPO)
                .filter(|remote| **remote != RemoteView::default())
                .cloned(),
            git_heads: view.git_heads.clone(),
        }
    }

    /// Removes these fields from `view`.
    fn strip(view: &mut View) {
        view.git_refs.clear();
        view.remote_views.remove(REMOTE_NAME_FOR_LOCAL_GIT_REPO);
        view.git_heads.clear();
    }

    /// Gives `view` these fields, in place of any it has.
    fn apply_to(&self, view: &mut View) {
        Self::strip(view);
        view.git_refs = self.git_refs.clone();
        if let Some(remote) = &self.git_remote {
            view.remote_views
                .insert(REMOTE_NAME_FOR_LOCAL_GIT_REPO.to_owned(), remote.clone());
        }
        view.git_heads = self.git_heads.clone();
    }
}

/// A canonical operation's view made local, with its id and the local names of the
/// canonical view's workspaces.
pub(super) struct LocalView {
    pub(super) view: View,
    pub(super) id: ViewId,
    pub(super) names: BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>,
}

impl NodeRepo {
    /// The canonical form of a local view: no records of this machine's `.git`, and every
    /// machine's workspaces under machine-qualified keys. This machine's come from `view`.
    /// The others' come from the canonical parents, except where this operation moved them:
    /// they are workspaces in `view` too, which jj moves when it rewrites or abandons their
    /// commits, or restores an older view. Adding, forgetting or renaming another machine's
    /// workspace here changes nothing: its workspaces are its own. Depends only on its
    /// arguments, so canonicalizing again after a crash gives the same result.
    pub(super) fn canonical_view(
        &self,
        local_op: &OperationId,
        mut view: View,
        canonical_parents: &[OperationId],
        predecessors: Option<&BTreeMap<CommitId, Vec<CommitId>>>,
    ) -> Result<View, NodeError> {
        // The names under which this machine showed the parents' other workspaces, exactly
        // as `realize_one` named them.
        let mut others: BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf> = BTreeMap::new();
        let mut parent_heads: BTreeSet<CommitId> = BTreeSet::new();
        for parent in canonical_parents {
            if parent == self.canonical.root_operation_id() {
                continue;
            }
            let parent_view = self.canonical.read_operation_view(parent)?;
            parent_heads.extend(parent_view.head_ids.iter().cloned());
            for (key, name) in self.local_names(&parent_view) {
                if !self.is_own_key(&key) {
                    others.insert(name, key);
                }
            }
        }
        let mut workspaces_by_key = self.merged_workspaces(canonical_parents)?;
        workspaces_by_key.retain(|key, _| !self.is_own_key(key));
        let mut local = std::mem::take(&mut view.wc_commit_ids);
        let mut moved_here = BTreeSet::new();
        for (name, key) in &others {
            if let Some(commit) = local.remove(name)
                && let Some(entry) = workspaces_by_key.get_mut(key)
            {
                *entry = commit;
                moved_here.insert(key.clone());
            }
        }
        // Another machine's workspace forgotten here can't be moved by jj; follow the
        // rewrites this operation records instead.
        let mut forgotten: BTreeMap<WorkspaceNameBuf, CommitId> = workspaces_by_key
            .iter()
            .filter(|(key, _)| !moved_here.contains(*key))
            .map(|(key, commit)| (key.clone(), commit.clone()))
            .collect();
        workspaces::follow_rewrites(&mut forgotten, predecessors);
        // Forgetting a workspace abandons its working-copy commit if it's empty, as
        // `jj workspace forget` does. Forgetting another machine's workspace here mustn't
        // abandon that machine's working copy: keep the commit visible, in the operation
        // that forgot the workspace and in every later one. But not once this machine
        // abandons the commit itself, as it can while the commit is visible here: had the
        // workspace been here, jj would have given it a new commit. And only while its
        // parents are visible here: jj, no longer seeing the commit, doesn't rebase it when
        // this machine rewrites or abandons them, and keeping it would bring them back.
        // Either way, its machine then replaces it, as if jj had abandoned it here
        // (`replace_abandoned_working_copies`).
        let mut repo = None;
        let mut before = None;
        for (key, commit) in &forgotten {
            if !parent_heads.contains(commit) || view.head_ids.contains(commit) {
                continue;
            }
            let (names, heads) = match &before {
                Some(before) => before,
                None => before.insert(self.parents_names_and_heads(local_op)?),
            };
            let forgotten_here = others
                .iter()
                .any(|(name, other)| other == key && names.contains(name));
            // Forgotten before, and visible until this operation abandoned it.
            if !forgotten_here && heads.contains(commit) {
                continue;
            }
            let repo = match &repo {
                Some(repo) => repo,
                None => repo.insert(self.repo_at(local_op)?),
            };
            let parents = repo.store().get_commit_async(commit).block_on()?;
            let mut parents_visible = true;
            for parent in parents.parent_ids() {
                parents_visible &= is_visible(repo, parent)?;
            }
            if parents_visible {
                view.head_ids.insert(commit.clone());
            }
        }
        workspaces_by_key.extend(forgotten);
        for (workspace, commit) in local {
            workspaces_by_key.insert(
                workspaces::workspace_key(self.machine.key(), workspace.as_str()),
                commit,
            );
        }
        PerMachine::strip(&mut view);
        view.wc_commit_ids = workspaces_by_key;
        Ok(view)
    }

    /// The workspaces, by local name, and the heads of the views of a local operation's
    /// parents, all together.
    fn parents_names_and_heads(
        &self,
        local_op: &OperationId,
    ) -> Result<(BTreeSet<WorkspaceNameBuf>, BTreeSet<CommitId>), NodeError> {
        let op_store = self.loader.op_store();
        let mut names = BTreeSet::new();
        let mut heads = BTreeSet::new();
        for parent in op_store.read_operation(local_op).block_on()?.parents {
            let parent = op_store.read_operation(&parent).block_on()?;
            let view = op_store.read_view(&parent.view_id).block_on()?;
            names.extend(view.wc_commit_ids.into_keys());
            heads.extend(view.head_ids);
        }
        Ok((names, heads))
    }

    pub(super) fn is_own_key(&self, key: &WorkspaceName) -> bool {
        workspaces::split_key(key.as_str())
            .is_some_and(|(machine, _)| machine == self.machine.key())
    }

    /// The local name of each workspace in a canonical view: this machine's own keep their
    /// names, and another machine's are prefixed with the machine's name, as in
    /// `beta/default`, or with its name and part of its id when two machines share a name
    /// or the prefix would make a name of this machine's own.
    pub(super) fn local_names(
        &self,
        canonical_view: &View,
    ) -> BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf> {
        let keys = &canonical_view.wc_commit_ids;
        let machines: BTreeSet<String> = keys
            .keys()
            .filter_map(|key| workspaces::split_key(key.as_str()))
            .map(|(machine, _)| machine.to_owned())
            .filter(|machine| machine != self.machine.key())
            .collect();
        let own: Vec<&str> = keys
            .keys()
            .filter(|key| self.is_own_key(key))
            .map(|key| key_workspace(key))
            .collect();
        let prefixes = workspaces::display_names(&machines, |name| {
            own.iter()
                .any(|workspace| workspace.starts_with(&format!("{name}/")))
        });
        keys.keys()
            .filter_map(|key| {
                let (machine, workspace) = workspaces::split_key(key.as_str())?;
                let name = if machine == self.machine.key() {
                    workspace.to_owned()
                } else {
                    format!("{}/{workspace}", prefixes.get(machine)?)
                };
                Some((key.clone(), WorkspaceNameBuf::from(name)))
            })
            .collect()
    }

    /// Where every machine's workspaces were, as of the canonical form of this machine's
    /// (merged) op head: each workspace's name here, as jj shows it (`default`, or
    /// `beta/default` for another machine's), and its commit. This machine's come first.
    pub fn machine_workspaces(&mut self) -> Result<Vec<(String, CommitId)>, NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        if canonical == *self.canonical.root_operation_id() {
            return Ok(vec![]);
        }
        let view = self.canonical.read_operation_view(&canonical)?;
        let names = self.local_names(&view);
        let mut workspaces: Vec<(bool, String, CommitId)> = view
            .wc_commit_ids
            .iter()
            .filter_map(|(key, commit)| {
                let name = names.get(key)?;
                Some((
                    !self.is_own_key(key),
                    name.as_str().to_owned(),
                    commit.clone(),
                ))
            })
            .collect();
        workspaces.sort();
        Ok(workspaces
            .into_iter()
            .map(|(_, name, commit)| (name, commit))
            .collect())
    }

    /// The machine-qualified workspaces of a canonical view.
    pub(super) fn workspaces_of(
        &self,
        op: &OperationId,
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        if op == self.canonical.root_operation_id() {
            return Ok(BTreeMap::new());
        }
        let view = self.canonical.read_operation_view(op)?;
        Ok(view.wc_commit_ids)
    }

    /// The parents' machine-qualified workspaces merged three-way, as jj merges views
    /// (`workspaces::merge_working_copy`). A removal wins over a move, which matters here:
    /// only a workspace's own machine removes it, and its removal must win over another
    /// machine moving it meanwhile.
    fn merged_workspaces(
        &self,
        parents: &[OperationId],
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        let Some((first, rest)) = parents.split_first() else {
            return Ok(BTreeMap::new());
        };
        let mut merged = self.workspaces_of(first)?;
        let mut merged_parents = vec![first.clone()];
        for other in rest {
            let base = match self
                .canonical
                .closest_common_ancestors(&merged_parents, std::slice::from_ref(other))?
                .first()
            {
                Some(base) => self.workspaces_of(base)?,
                None => BTreeMap::new(),
            };
            let theirs = self.workspaces_of(other)?;
            let keys: BTreeSet<WorkspaceNameBuf> = merged
                .keys()
                .chain(theirs.keys())
                .chain(base.keys())
                .cloned()
                .collect();
            let mut next = BTreeMap::new();
            for key in keys {
                let value = workspaces::merge_working_copy(
                    merged.get(&key),
                    base.get(&key),
                    theirs.get(&key),
                );
                if let Some(commit) = value {
                    next.insert(key, commit.clone());
                }
            }
            merged = next;
            merged_parents.push(other.clone());
        }
        Ok(merged)
    }

    /// A canonical operation's view, made local with `per_machine`.
    pub(super) fn local_view(
        &self,
        op: &StoreOperation,
        per_machine: &PerMachine,
    ) -> Result<LocalView, NodeError> {
        let mut view = self.canonical.read_view(&op.view_id)?;
        // Every machine's working copies become workspaces here: this machine's under their
        // own names, the others' as `beta/default`. This machine's own may have moved: when
        // another machine rewrites, abandons or restores a working-copy commit, its jj moves
        // the workspace, and the canonical view records where to.
        let names = self.local_names(&view);
        view.wc_commit_ids = std::mem::take(&mut view.wc_commit_ids)
            .into_iter()
            .filter_map(|(key, commit)| Some((names.get(&key)?.clone(), commit)))
            .collect();
        per_machine.apply_to(&mut view);
        debug_assert_eq!(PerMachine::of(&view), *per_machine);
        // The id the op store gives it, worked out as it does.
        let id = ViewId::new(blake2b_hash(&view).to_vec());
        Ok(LocalView { view, id, names })
    }
}

/// The workspace part of a machine-qualified key.
pub(super) fn key_workspace(key: &WorkspaceName) -> &str {
    workspaces::split_key(key.as_str()).map_or(key.as_str(), |(_, workspace)| workspace)
}
