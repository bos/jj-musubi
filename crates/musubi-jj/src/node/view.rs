//! Views between their local and canonical forms: this machine's records of its own `.git`,
//! and workspaces' names here and in the hive.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

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
use super::translate::target_of;
use crate::presence::Kind;
use crate::presence::Presence;
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

    /// Whether the `git` remote has a ref with no target, as jj keeps a tracked one while
    /// its local bookmark is there.
    pub(super) fn has_absent_remote_ref(&self) -> bool {
        self.git_remote.as_ref().is_some_and(|remote| {
            remote
                .bookmarks
                .values()
                .chain(remote.tags.values())
                .any(|remote_ref| remote_ref.target.is_absent())
        })
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
    /// The canonical form of a local view, of an operation of `kind`: no records of this
    /// machine's `.git`, and the workspaces of every machine present (see `crate::presence`)
    /// under machine-qualified keys. This machine's come from `view`, if it is present. The
    /// others' come from the canonical parents where their machine is present, except where
    /// this operation moved them: they are workspaces in `view` too, which jj moves when it
    /// rewrites or abandons their commits, or restores an older view. Adding, forgetting or
    /// renaming another machine's workspace here changes nothing: its workspaces are its own.
    /// Only a forget of the machine removes them. Depends only on its arguments, so
    /// canonicalizing again after a crash gives the same result. Returns the presence the
    /// parents give the operation too, before its own effect.
    pub(super) fn canonical_view(
        &self,
        local_op: &OperationId,
        mut view: View,
        canonical_parents: &[OperationId],
        predecessors: Option<&BTreeMap<CommitId, Vec<CommitId>>>,
        kind: &Kind,
    ) -> Result<(View, Presence<OperationId>), NodeError> {
        let parent_presences = canonical_parents
            .iter()
            .map(|parent| Ok((parent.clone(), self.presence(parent)?)))
            .collect::<Result<Vec<_>, NodeError>>()?;
        let merged = self.merge_presence(&parent_presences)?;
        let present = |machine: &str| {
            !kind.forgets.contains(machine)
                && (kind.work.as_deref() == Some(machine) || merged.is_present(machine))
        };
        // The names under which this machine showed the parents' other workspaces, exactly
        // as `realize_one` named them, and every machine their histories have known.
        let mut others: BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf> = BTreeMap::new();
        let mut parent_heads: BTreeSet<CommitId> = BTreeSet::new();
        let mut machines: BTreeSet<String> = BTreeSet::new();
        let mut own_names: BTreeSet<WorkspaceNameBuf> = BTreeSet::new();
        for (parent, presence) in &parent_presences {
            if parent == self.canonical.root_operation_id() {
                continue;
            }
            let parent_view = self.canonical.read_operation_view(parent)?;
            parent_heads.extend(parent_view.head_ids.iter().cloned());
            machines.extend(self.machines_of(&parent_view, presence.known()));
            own_names.extend(self.own_names_in(&parent_view, presence)?);
            for (key, name) in self.local_names(&parent_view, presence)? {
                if !self.is_own_key(&key) {
                    others.insert(name, key);
                }
            }
        }
        let mut workspaces_by_key = self.present_workspaces(&parent_presences, &present)?;
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
        // (`replace_abandoned_working_copies`). Nor at a merge where a parent hid it, having
        // had it at the merge base: a rewrite there, before a forget of the machine, moved
        // the workspace in a view the merge leaves out (`present_workspaces`), and keeping
        // the commit would show it beside its rewrite (`merged_heads`).
        let mut repo = None;
        let mut before = None;
        let mut merged_heads = None;
        for (key, commit) in &forgotten {
            if !parent_heads.contains(commit) || view.head_ids.contains(commit) {
                continue;
            }
            if canonical_parents.len() > 1 {
                let merged = match &merged_heads {
                    Some(merged) => merged,
                    None => merged_heads.insert(self.merged_heads(canonical_parents)?),
                };
                if !merged.contains(commit) {
                    continue;
                }
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
        // What's left is this machine's own, but for other machines' workspaces under names
        // the hive no longer gives them, as `jj undo` brings back. They are not this
        // machine's to publish. A name this machine's own already had stays its own; and so
        // does one this operation made, there in none of its parents' views. An operation
        // that restores an older view makes none: its names are its own if they were in the
        // view it restores, or, for a revert, in that operation's parents'.
        let stale: Vec<WorkspaceNameBuf> = local
            .keys()
            .filter(|name| !own_names.contains(*name) && self.names_other_machine(name, &machines))
            .cloned()
            .collect();
        if !stale.is_empty() {
            let op = self.loader.op_store().read_operation(local_op).block_on()?;
            let restored = match target_of(&op.metadata.description) {
                Some((_, target)) => Some(self.restored_own_names(&target)?),
                None => None,
            };
            let (names, _) = match &before {
                Some(before) => before,
                None => before.insert(self.parents_names_and_heads(local_op)?),
            };
            for name in stale {
                let own = match &restored {
                    Some(restored) => restored.contains(&name),
                    None => !names.contains(&name),
                };
                if !own {
                    local.remove(&name);
                }
            }
        }
        if present(self.machine.key()) {
            for (workspace, commit) in local {
                workspaces_by_key.insert(
                    workspaces::workspace_key(self.machine.key(), workspace.as_str()),
                    commit,
                );
            }
        }
        PerMachine::strip(&mut view);
        view.wc_commit_ids = workspaces_by_key;
        Ok((view, merged))
    }

    /// The workspaces of the machines `present` accepts, other than this one's, each machine's
    /// merged three-way over the parents where it is present: a parent where it isn't lacks
    /// its workspaces because a forget saw its work, not because it removed them.
    fn present_workspaces(
        &self,
        parents: &[(OperationId, Arc<Presence<OperationId>>)],
        present: &impl Fn(&str) -> bool,
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        // Machines grouped by the parents where they are present, usually all of them.
        let mut groups: BTreeMap<Vec<usize>, BTreeSet<&str>> = BTreeMap::new();
        for machine in parents.iter().flat_map(|(_, presence)| presence.copies()) {
            if machine == self.machine.key() || !present(machine) {
                continue;
            }
            let at: Vec<usize> = (0..parents.len())
                .filter(|&i| parents[i].1.is_present(machine))
                .collect();
            groups.entry(at).or_default().insert(machine);
        }
        let mut workspaces = BTreeMap::new();
        for (at, machines) in groups {
            let ops: Vec<OperationId> = at.iter().map(|&i| parents[i].0.clone()).collect();
            workspaces.extend(
                self.merged_workspaces(&ops)?
                    .into_iter()
                    .filter(|(key, _)| {
                        workspaces::split_key(key.as_str())
                            .is_some_and(|(machine, _)| machines.contains(machine))
                    }),
            );
        }
        Ok(workspaces)
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

    /// The local name of each workspace in a canonical view, whose operation has `presence`:
    /// this machine's own keep their names, and another machine's are prefixed with the
    /// machine's name, as in `beta/default`, or with its name and part of its id when two
    /// machines share a name or the prefix would make a name of this machine's own
    /// (`own_names_in`, which the hive having forgotten this machine doesn't change). The
    /// names are chosen among every machine the view's history has known
    /// (`Presence::known`), so that a machine's name doesn't change as others are forgotten
    /// and come back, and a forgotten machine's is never another's.
    pub(super) fn local_names(
        &self,
        canonical_view: &View,
        presence: &Presence<OperationId>,
    ) -> Result<BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>, NodeError> {
        let keys = &canonical_view.wc_commit_ids;
        let mut machines = self.machines_of(canonical_view, presence.known());
        machines.remove(self.machine.key());
        let own = self.own_names_in(canonical_view, presence)?;
        let prefixes = workspaces::display_names(&machines, |name| {
            own.iter()
                .any(|workspace| workspace.as_str().starts_with(&format!("{name}/")))
        });
        Ok(keys
            .keys()
            .filter_map(|key| {
                let (machine, workspace) = workspaces::split_key(key.as_str())?;
                let name = if machine == self.machine.key() {
                    workspace.to_owned()
                } else {
                    format!("{}/{workspace}", prefixes.get(machine)?)
                };
                Some((key.clone(), WorkspaceNameBuf::from(name)))
            })
            .collect())
    }

    /// The machines a canonical view's history has known: `known`, and those with
    /// workspaces in the view, as one that joined before joining was recorded as work.
    pub(super) fn machines_of(&self, view: &View, known: &BTreeSet<String>) -> BTreeSet<String> {
        let mut machines = known.clone();
        machines.extend(
            view.wc_commit_ids
                .keys()
                .filter_map(|key| workspaces::split_key(key.as_str()))
                .map(|(machine, _)| machine.to_owned()),
        );
        machines
    }

    /// This machine's own names as of a local operation that `jj op restore` or `jj undo`
    /// goes back to, and as of its parents, which a revert of it goes back to: those of each
    /// one's canonical form (`own_names`), where it has one yet.
    fn restored_own_names(
        &self,
        target: &OperationId,
    ) -> Result<BTreeSet<WorkspaceNameBuf>, NodeError> {
        let op_store = self.loader.op_store();
        let mut names = BTreeSet::new();
        let Ok(op) = op_store.read_operation(target).block_on() else {
            return Ok(names);
        };
        // Parents first: working out presence at the target then stops at theirs.
        for local in op.parents.iter().chain(std::iter::once(target)) {
            if let Some(canonical) = self.canonical_of(local) {
                names.extend(self.own_names(&canonical)?);
            }
        }
        Ok(names)
    }

    /// Whether `name`, a workspace in this machine's view, is one this machine shows, or
    /// once showed, another machine's under: `<prefix>/<workspace>`, with either of the
    /// prefixes one of `machines` other than this one can have (`workspaces::display_forms`).
    /// `jj undo` and `jj op restore` bring back older views, with names the hive no longer
    /// gives: a forgotten machine's, or one shown by another name since a machine of the same
    /// name joined. Such a name is this machine's own only if the hive has it so already, or
    /// this machine just made it (`canonical_view`). Depends only on its arguments.
    pub(super) fn names_other_machine(
        &self,
        name: &WorkspaceName,
        machines: &BTreeSet<String>,
    ) -> bool {
        let Some((prefix, _)) = name.as_str().split_once('/') else {
            return false;
        };
        machines
            .iter()
            .filter(|machine| machine.as_str() != self.machine.key())
            .any(|machine| {
                workspaces::display_forms(machine)
                    .iter()
                    .any(|form| form == prefix)
            })
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
        let names = self.local_names(&view, &*self.presence(&canonical)?)?;
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
            let base = self.base_of(
                &merged_parents,
                other,
                |op| self.workspaces_of(op),
                |ops| self.merged_workspaces(ops),
            )?;
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

    /// The base a merge of `ours` with `theirs` merges three-way against, as jj merges
    /// operations: what `of` gives for their closest common ancestor, or where there are
    /// several, as in a criss-cross merge, those merged by `merge`, as jj merges them into one
    /// base first; nothing, if they have none.
    fn base_of<T: Default>(
        &self,
        ours: &[OperationId],
        theirs: &OperationId,
        of: impl Fn(&OperationId) -> Result<T, NodeError>,
        merge: impl Fn(&[OperationId]) -> Result<T, NodeError>,
    ) -> Result<T, NodeError> {
        let ancestors = self
            .canonical
            .closest_common_ancestors(ours, std::slice::from_ref(theirs))?;
        match ancestors.as_slice() {
            [] => Ok(T::default()),
            [one] => of(one),
            several => merge(several),
        }
    }

    /// The heads of a canonical operation's view.
    fn heads_of(&self, op: &OperationId) -> Result<BTreeSet<CommitId>, NodeError> {
        if op == self.canonical.root_operation_id() {
            return Ok(BTreeSet::new());
        }
        let view = self.canonical.read_operation_view(op)?;
        Ok(view.head_ids.into_iter().collect())
    }

    /// The heads of canonical operations' views merged three-way, as jj merges views: a head
    /// that a parent dropped since their merge base is gone, and one a parent added is there.
    fn merged_heads(&self, parents: &[OperationId]) -> Result<BTreeSet<CommitId>, NodeError> {
        let heads_of = |op: &OperationId| self.heads_of(op);
        let Some((first, rest)) = parents.split_first() else {
            return Ok(BTreeSet::new());
        };
        let mut merged = heads_of(first)?;
        let mut merged_parents = vec![first.clone()];
        for other in rest {
            let base = self.base_of(&merged_parents, other, heads_of, |ops| {
                self.merged_heads(ops)
            })?;
            let theirs = heads_of(other)?;
            let all: BTreeSet<&CommitId> = merged.iter().chain(&theirs).chain(&base).collect();
            let next = all
                .into_iter()
                .filter(|head| {
                    let ours = merged.contains(*head);
                    if ours == base.contains(*head) {
                        theirs.contains(*head)
                    } else {
                        ours
                    }
                })
                .cloned()
                .collect();
            merged = next;
            merged_parents.push(other.clone());
        }
        Ok(merged)
    }

    /// A canonical operation's view, made local with `per_machine`.
    pub(super) fn local_view(
        &self,
        id: &OperationId,
        op: &StoreOperation,
        per_machine: &PerMachine,
    ) -> Result<LocalView, NodeError> {
        let mut view = self.canonical.read_view(&op.view_id)?;
        // Every machine's working copies become workspaces here: this machine's under their
        // own names, the others' as `beta/default`. This machine's own may have moved: when
        // another machine rewrites, abandons or restores a working-copy commit, its jj moves
        // the workspace, and the canonical view records where to.
        let names = self.local_names(&view, &*self.presence(id)?)?;
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
