//! Views between their local and canonical forms: this machine's records of its own `.git`,
//! and workspaces' names here and in the hive.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::op_store::Operation as StoreOperation;
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
use crate::canonical::Work;
use crate::presence::Kind;
use crate::presence::Presence;
use crate::workspaces;

/// The names with a `/` that earlier releases recorded on realizations, and on the commands
/// they rewrote, as this machine's own where the canonical view didn't give them to it.
/// Nothing reads it now: a name with a `/` is this machine's only where jj's workspace store
/// records a directory for it (`own_of_view`). Local to this copy: canonicalizing drops it,
/// as it drops the other local attributes (`OpAttrs::remove_private_workspaces`).
pub(crate) const LOCAL_WORKSPACES: &str = "musubi.local-workspaces";

/// The names a realization showed other machines' workspaces clear of beyond its canonical
/// view's own, which earlier releases recorded. Local to this copy, like [`LOCAL_WORKSPACES`]:
/// canonicalizing drops it.
pub(crate) const RESERVED_WORKSPACES: &str = "musubi.reserved-workspaces";

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

    /// These fields merged with `theirs` against `base`, if at most one of the two differs
    /// from `base`: that one, as jj's merge has it. `None` where jj's merge must decide:
    /// where both differ, or where any has a tracked remote ref with no target. jj keeps one
    /// only while its local bookmark is there, which these fields don't say: merging, it may
    /// drop one, then merge a side that brings it back as from nothing, untracked (#56).
    /// This is `shortcut` in formal/Musubi/Refs.lean, which agrees with jj's merge wherever it
    /// applies (`shortcut_agrees`).
    pub(super) fn merged_trivially(base: &Self, merged: Self, theirs: Self) -> Option<Self> {
        if [base, &merged, &theirs]
            .iter()
            .any(|fields| fields.has_absent_remote_ref())
        {
            return None;
        }
        if theirs == *base {
            Some(merged)
        } else if merged == *base {
            Some(theirs)
        } else {
            None
        }
    }

    /// Whether the `git` remote has a ref with no target, as jj keeps a tracked one while
    /// its local bookmark is there.
    fn has_absent_remote_ref(&self) -> bool {
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
    pub(super) fn apply_to(&self, view: &mut View) {
        Self::strip(view);
        view.git_refs = self.git_refs.clone();
        if let Some(remote) = &self.git_remote {
            view.remote_views
                .insert(REMOTE_NAME_FOR_LOCAL_GIT_REPO.to_owned(), remote.clone());
        }
        view.git_heads = self.git_heads.clone();
    }
}

/// A canonical operation's view made local, with its id, the local names of the canonical
/// view's workspaces, and the prefix of every other machine its history has known.
pub(super) struct LocalView {
    pub(super) view: View,
    pub(super) id: ViewId,
    pub(super) names: BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>,
    pub(super) prefixes: BTreeMap<String, String>,
}

/// The local parents of an operation being canonicalized, read for `NodeRepo::canonical_view`.
struct LocalParents {
    /// The workspaces in the view of the parent canonicalized just before, if one was.
    last: Option<Arc<BTreeMap<WorkspaceNameBuf, CommitId>>>,
    /// The other parents.
    ops: Vec<StoreOperation>,
}

impl LocalParents {
    /// The workspaces in the parents' views, all together, each with its commits there.
    fn workspaces(
        &self,
        node: &NodeRepo,
    ) -> Result<BTreeMap<WorkspaceNameBuf, BTreeSet<CommitId>>, NodeError> {
        let mut workspaces: BTreeMap<WorkspaceNameBuf, BTreeSet<CommitId>> = BTreeMap::new();
        let mut add = |view: &BTreeMap<WorkspaceNameBuf, CommitId>| {
            for (name, commit) in view {
                workspaces
                    .entry(name.clone())
                    .or_default()
                    .insert(commit.clone());
            }
        };
        if let Some(last) = &self.last {
            add(last);
        }
        for parent in &self.ops {
            let view = node
                .loader
                .op_store()
                .read_view(&parent.view_id)
                .block_on()?;
            add(&view.wc_commit_ids);
        }
        Ok(workspaces)
    }
}

/// The views a `jj` command started from, each with its canonical form: for each, its
/// workspaces by name, and the canonical form's by key, with their commits. A name stands for
/// another machine's workspace only where every one of them that has the name has it at a
/// commit its own canonical form gives that workspace.
struct StartedFrom(Vec<Source>);

/// One of the views of [`StartedFrom`].
#[derive(Default)]
struct Source {
    here: BTreeMap<WorkspaceNameBuf, BTreeSet<CommitId>>,
    there: BTreeMap<WorkspaceNameBuf, BTreeSet<CommitId>>,
}

impl StartedFrom {
    /// Whether `name` stands for the other machine's workspace `key`.
    fn stands_for(&self, name: &WorkspaceName, key: &WorkspaceName) -> bool {
        let mut having = self
            .0
            .iter()
            .filter_map(|source| Some((source.here.get(name)?, source.there.get(key))))
            .peekable();
        having.peek().is_some()
            && having.all(|(here, there)| there.is_some_and(|there| !here.is_disjoint(there)))
    }
}

/// What an operation's canonical parents say of the names in its local view, for
/// `NodeRepo::canonical_view`.
#[derive(Default)]
struct Inherited {
    /// The names under which this machine showed the parents' other workspaces, exactly as
    /// `realize_one` named them, with their keys.
    others: BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>,
    /// The commits the parents give each other machine's workspace, by key.
    commits: BTreeMap<WorkspaceNameBuf, BTreeSet<CommitId>>,
    /// The heads of the parents' views.
    parent_heads: BTreeSet<CommitId>,
}

/// The workspace names and heads of a local operation's parents' views, read when first
/// needed (`NodeRepo::parents_names_and_heads`).
struct ParentsBefore<'a> {
    local_op: &'a LocalOp,
    read: Option<(BTreeSet<WorkspaceNameBuf>, BTreeSet<CommitId>)>,
}

impl<'a> ParentsBefore<'a> {
    fn new(local_op: &'a LocalOp) -> Self {
        Self {
            local_op,
            read: None,
        }
    }

    fn get(
        &mut self,
        node: &NodeRepo,
    ) -> Result<&(BTreeSet<WorkspaceNameBuf>, BTreeSet<CommitId>), NodeError> {
        let read = match self.read.take() {
            Some(read) => read,
            None => node.parents_names_and_heads(self.local_op)?,
        };
        Ok(self.read.insert(read))
    }
}

/// The workspaces of `workspaces_by_key` that this operation didn't move, `moved_here`.
/// Another machine's workspace forgotten here can't be moved by jj; follow the rewrites this
/// operation records instead.
fn forgotten_workspaces(
    workspaces_by_key: &BTreeMap<WorkspaceNameBuf, CommitId>,
    moved_here: &BTreeSet<WorkspaceNameBuf>,
    predecessors: Option<&BTreeMap<CommitId, Vec<CommitId>>>,
) -> BTreeMap<WorkspaceNameBuf, CommitId> {
    let mut forgotten: BTreeMap<WorkspaceNameBuf, CommitId> = workspaces_by_key
        .iter()
        .filter(|(key, _)| !moved_here.contains(*key))
        .map(|(key, commit)| (key.clone(), commit.clone()))
        .collect();
    workspaces::follow_rewrites(&mut forgotten, predecessors);
    forgotten
}

impl NodeRepo {
    /// The canonical form of a local view, of an operation of `kind`: no records of this
    /// machine's `.git`, and the workspaces of every machine present (see `crate::presence`)
    /// under machine-qualified keys. This machine's come from `view`, if it is present, those
    /// with no `/` in their names (`is_publishable`). The
    /// others' come from the canonical parents where their machine is present, except where
    /// this operation moved them: they are workspaces in `view` too, which jj moves when it
    /// rewrites or abandons their commits, or restores an older view. Adding, forgetting or
    /// renaming another machine's workspace here changes nothing: its workspaces are its own.
    /// Only a forget of the machine removes them. Depends only on its arguments, so
    /// canonicalizing again after a crash gives the same result. Returns the presence the
    /// parents give the operation too, before its own effect.
    pub(super) fn canonical_view(
        &self,
        local_op: &LocalOp,
        mut view: View,
        canonical_parents: &[CanonicalOp],
        predecessors: Option<&BTreeMap<CommitId, Vec<CommitId>>>,
        kind: &Kind,
    ) -> Result<(View, Presence<Work>), NodeError> {
        let parent_presences = canonical_parents
            .iter()
            .map(|parent| Ok((parent.clone(), self.presence(parent)?)))
            .collect::<Result<Vec<_>, NodeError>>()?;
        let merged = self.merge_presence(&parent_presences)?;
        let present = |machine: &str| {
            !kind.forgets.contains(machine)
                && (kind.work.as_deref() == Some(machine) || merged.is_present(machine))
        };
        let raw = self
            .loader
            .op_store()
            .read_operation(&local_op.0)
            .block_on()?;
        // Operations are canonicalized parents first, so the one before is usually the parent:
        // its names are known, and it is no realization.
        let last = self
            .names
            .last_view
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        let names_here = Arc::new(view.wc_commit_ids.clone());
        let local_parents = self.read_local_parents(&raw, last)?;
        let inherited = self.inherited_from_parents(&parent_presences)?;

        let mut workspaces_by_key = self.present_workspaces(&parent_presences, &present)?;
        workspaces_by_key.retain(|key, _| !self.is_own_key(key));
        let mut local = std::mem::take(&mut view.wc_commit_ids);
        let moved_here = self.move_others_here(
            &raw,
            &local_parents,
            &inherited,
            &mut local,
            &mut workspaces_by_key,
        )?;
        let forgotten = forgotten_workspaces(&workspaces_by_key, &moved_here, predecessors);
        let mut before = ParentsBefore::new(local_op);
        self.keep_forgotten_visible(
            local_op,
            canonical_parents,
            &inherited,
            &forgotten,
            &mut view,
            &mut before,
        )?;
        workspaces_by_key.extend(forgotten);
        // What is left is this machine's, but only a name with no `/` is its own to publish:
        // other machines' workspaces show here as `beta/x`, so a name of that form, whatever
        // made it, is never this machine's own (design.md, "Which workspaces are this
        // machine's own").
        local.retain(|name, _| is_publishable(name));
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
        *self
            .names
            .last_view
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) =
            Some((local_op.0.clone(), names_here));
        Ok((view, merged))
    }

    /// The local parents of `raw`, but `last`, the one canonicalized just before, if it is
    /// one.
    fn read_local_parents(
        &self,
        raw: &StoreOperation,
        last: Option<(
            jj_lib::op_store::OperationId,
            Arc<BTreeMap<WorkspaceNameBuf, CommitId>>,
        )>,
    ) -> Result<LocalParents, NodeError> {
        let mut ops = vec![];
        for parent in &raw.parents {
            if last.as_ref().is_some_and(|(id, _)| id == parent) {
                continue;
            }
            ops.push(self.loader.op_store().read_operation(parent).block_on()?);
        }
        let last = last.and_then(|(id, names)| raw.parents.contains(&id).then_some(names));
        Ok(LocalParents { last, ops })
    }

    /// What the canonical parents say of an operation's names: each parent's other machines'
    /// workspaces, named as a realization of it names them (`local_view`).
    fn inherited_from_parents(
        &self,
        parent_presences: &[(CanonicalOp, Arc<Presence<Work>>)],
    ) -> Result<Inherited, NodeError> {
        let mut inherited = Inherited::default();
        for (parent, presence) in parent_presences {
            if parent == self.canonical.root_operation_id() {
                continue;
            }
            let parent_view = self.canonical.read_operation_view(parent)?;
            inherited
                .parent_heads
                .extend(parent_view.head_ids.iter().cloned());
            let prefixes = self.prefixes_with_own(&parent_view, presence, &BTreeSet::new())?;
            for (key, name) in self.names_of(&parent_view, &prefixes) {
                if !self.is_own_key(&key) {
                    if let Some(commit) = parent_view.wc_commit_ids.get(&key) {
                        inherited
                            .commits
                            .entry(key.clone())
                            .or_default()
                            .insert(commit.clone());
                    }
                    inherited.others.insert(name, key);
                }
            }
        }
        Ok(inherited)
    }

    /// Moves other machines' workspaces that this operation moved from `local` to
    /// `workspaces_by_key`, returning their keys. A name in a `jj` command's view stands for
    /// another machine's workspace only where a view it started from had the name at the
    /// commit the canonical parents give that workspace, as a realization shows it and as an
    /// earlier command that moved it left it: otherwise it is a workspace this machine added
    /// under the name, as after forgetting the other machine's here and adding one of that
    /// name, which `jj workspace add` moves to its commit in a second operation. Adding changes
    /// nothing of another machine's. A command that goes back to an older operation (`jj
    /// undo`, `jj op restore`, `jj op revert`) starts from the view it brings back, and the
    /// commits that view's canonical form gives other machines' workspaces: a workspace of this
    /// machine's by such a name, brought back with it, stands for none of theirs.
    /// musubi's own operations add none, but show the others' again under their names.
    fn move_others_here(
        &self,
        raw: &StoreOperation,
        local_parents: &LocalParents,
        inherited: &Inherited,
        local: &mut BTreeMap<WorkspaceNameBuf, CommitId>,
        workspaces_by_key: &mut BTreeMap<WorkspaceNameBuf, CommitId>,
    ) -> Result<BTreeSet<WorkspaceNameBuf>, NodeError> {
        let started_from = if raw.metadata.workspace_name.is_some()
            && inherited.others.keys().any(|name| local.contains_key(name))
        {
            Some(self.started_from(raw, local_parents, inherited)?)
        } else {
            None
        };
        let mut moved_here = BTreeSet::new();
        for (name, key) in &inherited.others {
            let stands_for_it = match &started_from {
                None => true,
                Some(started_from) => started_from.stands_for(name, key),
            };
            if !stands_for_it {
                continue;
            }
            if let Some(commit) = local.remove(name)
                && let Some(entry) = workspaces_by_key.get_mut(key)
            {
                *entry = commit;
                moved_here.insert(key.clone());
            }
        }
        Ok(moved_here)
    }

    /// Keeps visible in `view` the working-copy commits of the `forgotten` workspaces that
    /// forgetting them here would abandon.
    ///
    /// Forgetting a workspace abandons its working-copy commit if it's empty, as
    /// `jj workspace forget` does. Forgetting another machine's workspace here mustn't
    /// abandon that machine's working copy: keep the commit visible, in the operation
    /// that forgot the workspace and in every later one. But not once this machine
    /// abandons the commit itself, as it can while the commit is visible here: had the
    /// workspace been here, jj would have given it a new commit. And only while its
    /// parents are visible here: jj, no longer seeing the commit, doesn't rebase it when
    /// this machine rewrites or abandons them, and keeping it would bring them back.
    /// Either way, its machine then replaces it, as if jj had abandoned it here
    /// (`replace_abandoned_working_copies`). Nor at a merge where a parent hid it, having
    /// had it at the merge base: a rewrite there, before a forget of the machine, moved
    /// the workspace in a view the merge leaves out (`present_workspaces`), and keeping
    /// the commit would show it beside its rewrite (`merged_heads`).
    fn keep_forgotten_visible(
        &self,
        local_op: &LocalOp,
        canonical_parents: &[CanonicalOp],
        inherited: &Inherited,
        forgotten: &BTreeMap<WorkspaceNameBuf, CommitId>,
        view: &mut View,
        before: &mut ParentsBefore<'_>,
    ) -> Result<(), NodeError> {
        let mut repo = None;
        let mut merged_heads = None;
        for (key, commit) in forgotten {
            if !inherited.parent_heads.contains(commit) || view.head_ids.contains(commit) {
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
            let (names, heads) = before.get(self)?;
            let forgotten_here = inherited
                .others
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
        Ok(())
    }

    /// The workspaces of the machines `present` accepts, other than this one's, each machine's
    /// merged three-way over the parents where it is present: a parent where it isn't lacks
    /// its workspaces because a forget saw its work, not because it removed them.
    fn present_workspaces(
        &self,
        parents: &[(CanonicalOp, Arc<Presence<Work>>)],
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
            let ops: Vec<CanonicalOp> = at.iter().map(|&i| parents[i].0.clone()).collect();
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
        local_op: &LocalOp,
    ) -> Result<(BTreeSet<WorkspaceNameBuf>, BTreeSet<CommitId>), NodeError> {
        let op_store = self.loader.op_store();
        let mut names = BTreeSet::new();
        let mut heads = BTreeSet::new();
        for parent in op_store.read_operation(&local_op.0).block_on()?.parents {
            let parent = op_store.read_operation(&parent).block_on()?;
            let view = op_store.read_view(&parent.view_id).block_on()?;
            names.extend(view.wc_commit_ids.into_keys());
            heads.extend(view.head_ids);
        }
        Ok((names, heads))
    }

    /// The views local operation `op` started from, and their canonical forms: its parents',
    /// or, for one that goes back to an older operation, the view it brings back (for a revert,
    /// the reverted operation's parents', with its parents').
    fn started_from(
        &self,
        op: &StoreOperation,
        local_parents: &LocalParents,
        inherited: &Inherited,
    ) -> Result<StartedFrom, NodeError> {
        let op_store = self.loader.op_store();
        let target = target_of(&op.metadata.description).and_then(|(prefix, target)| {
            let target_op = op_store.read_operation(&target).block_on().ok()?;
            Some((prefix.contains("revert operation"), target, target_op))
        });
        let parents = || -> Result<Source, NodeError> {
            Ok(Source {
                here: local_parents.workspaces(self)?,
                there: inherited.commits.clone(),
            })
        };
        let (mut started_from, sources) = match target {
            // An old target may have been collected: then only the parents say anything.
            None => (vec![parents()?], vec![]),
            Some((true, _, target_op)) => (vec![parents()?], target_op.parents),
            Some((false, target, _)) => (vec![], vec![target]),
        };
        for source in sources {
            let op = op_store.read_operation(&source).block_on()?;
            let view = op_store.read_view(&op.view_id).block_on()?;
            let mut from = Source::default();
            for (name, commit) in view.wc_commit_ids {
                from.here.entry(name).or_default().insert(commit);
            }
            // One from before this repository joined has no other machines' workspaces.
            if let Some(canonical) = self.canonical_of(&LocalOp(source))
                && canonical != *self.canonical.root_operation_id()
            {
                let view = self.canonical.read_operation_view(&canonical)?;
                for (key, commit) in view.wc_commit_ids {
                    from.there.entry(key).or_default().insert(commit);
                }
            }
            started_from.push(from);
        }
        Ok(StartedFrom(started_from))
    }

    pub(super) fn is_own_key(&self, key: &WorkspaceName) -> bool {
        workspaces::split_key(key.as_str())
            .is_some_and(|(machine, _)| machine == self.machine.key())
    }

    /// The local name of each workspace in the view of canonical operation `canonical`: this
    /// machine's own keep their names, and another machine's are prefixed with the machine's
    /// name, as in `beta/default`, or with its name and part or all of its id when two
    /// machines share a name or the prefix would start a name of this machine's
    /// (`workspaces::display_names`; `machine_prefixes`). The
    /// names are chosen among every machine the view's history has known
    /// (`Presence::known`), so that a machine's name doesn't change as others are forgotten
    /// and come back, and a forgotten machine's is never another's.
    pub(super) fn local_names(
        &self,
        canonical: &CanonicalOp,
        canonical_view: &View,
    ) -> Result<BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>, NodeError> {
        let prefixes = self.machine_prefixes(canonical, canonical_view)?;
        Ok(self.names_of(canonical_view, &prefixes))
    }

    pub(super) fn prefixes_with_own(
        &self,
        canonical_view: &View,
        presence: &Presence<Work>,
        private: &BTreeSet<WorkspaceNameBuf>,
    ) -> Result<BTreeMap<String, String>, NodeError> {
        let mut machines = self.machines_of(canonical_view, presence.known());
        machines.insert(self.machine.key().to_owned());
        let mut own = self.own_names_in(canonical_view, presence)?;
        own.extend(private.iter().cloned());
        Ok(workspaces::display_names(&machines, |name| {
            own.iter()
                .any(|workspace| workspace.as_str().starts_with(&format!("{name}/")))
        }))
    }

    /// The local names of a canonical view's workspaces, given the other machines' prefixes.
    pub(super) fn names_of(
        &self,
        canonical_view: &View,
        prefixes: &BTreeMap<String, String>,
    ) -> BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf> {
        canonical_view
            .wc_commit_ids
            .keys()
            .filter_map(|key| Some((key.clone(), self.local_name(key, prefixes)?)))
            .collect()
    }

    /// The local name of the workspace a machine-qualified key names, given the other
    /// machines' prefixes: its own name for this machine's, `<prefix>/<workspace>` for
    /// another's. None for a machine with no prefix.
    pub(super) fn local_name(
        &self,
        key: &WorkspaceName,
        prefixes: &BTreeMap<String, String>,
    ) -> Option<WorkspaceNameBuf> {
        workspaces::local_name(self.machine.key(), key.as_str(), prefixes)
            .map(WorkspaceNameBuf::from)
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
        let names = self.local_names(&canonical, &view)?;
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
        op: &CanonicalOp,
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
        parents: &[CanonicalOp],
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        let of = |op: &CanonicalOp| self.workspaces_of(op);
        let Some((first, rest)) = parents.split_first() else {
            return Ok(BTreeMap::new());
        };
        let mut merged = of(first)?;
        let mut merged_parents = vec![first.clone()];
        for other in rest {
            let base = self.base_of(&merged_parents, other, of, |ops| {
                self.merged_workspaces(ops)
            })?;
            let theirs = of(other)?;
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
        ours: &[CanonicalOp],
        theirs: &CanonicalOp,
        of: impl Fn(&CanonicalOp) -> Result<T, NodeError>,
        merge: impl Fn(&[CanonicalOp]) -> Result<T, NodeError>,
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
    fn heads_of(&self, op: &CanonicalOp) -> Result<BTreeSet<CommitId>, NodeError> {
        if op == self.canonical.root_operation_id() {
            return Ok(BTreeSet::new());
        }
        let view = self.canonical.read_operation_view(op)?;
        Ok(view.head_ids.into_iter().collect())
    }

    /// The heads of canonical operations' views merged three-way, as jj merges views: a head
    /// that a parent dropped since their merge base is gone, and one a parent added is there.
    fn merged_heads(&self, parents: &[CanonicalOp]) -> Result<BTreeSet<CommitId>, NodeError> {
        let heads_of = |op: &CanonicalOp| self.heads_of(op);
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
        id: &CanonicalOp,
        op: &StoreOperation,
        per_machine: &PerMachine,
    ) -> Result<LocalView, NodeError> {
        let mut view = self.canonical.read_view(&op.view_id)?;
        // Every machine's working copies become workspaces here: this machine's under their
        // own names, the others' as `beta/default`. This machine's own may have moved: when
        // another machine rewrites, abandons or restores a working-copy commit, its jj moves
        // the workspace, and the canonical view records where to.
        let prefixes = self.prefixes_with_own(&view, &*self.presence(id)?, &BTreeSet::new())?;
        let names = self.names_of(&view, &prefixes);
        view.wc_commit_ids = std::mem::take(&mut view.wc_commit_ids)
            .into_iter()
            .filter_map(|(key, commit)| Some((names.get(&key)?.clone(), commit)))
            .collect();
        per_machine.apply_to(&mut view);
        debug_assert_eq!(PerMachine::of(&view), *per_machine);
        // The id the op store gives it, worked out as it does.
        let id = ViewId::new(blake2b_hash(&view).to_vec());
        Ok(LocalView {
            view,
            id,
            names,
            prefixes,
        })
    }
}

/// Whether this machine publishes a workspace of its own named `name`: only if the name has no
/// `/`. Other machines' workspaces show here as `<machine>/<workspace>`, so a name of that form
/// is never this machine's own, whatever made it.
pub(crate) fn is_publishable(name: &WorkspaceName) -> bool {
    !name.as_str().contains('/')
}

/// The workspace part of a machine-qualified key.
pub(super) fn key_workspace(key: &WorkspaceName) -> &str {
    workspaces::split_key(key.as_str()).map_or(key.as_str(), |(_, workspace)| workspace)
}

// The Lean oracle, and the model of one ref's slot it answers, for the tests.
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
#[cfg(test)]
use crate::oracle;
#[cfg(test)]
#[path = "../../tests/support/refs_model.rs"]
#[allow(dead_code, clippy::unwrap_used)]
mod refs_model;

#[cfg(test)]
mod tests {
    //! jj's merge of one bookmark's views, against `TSlot.merge` in formal/Musubi/Refs.lean
    //! as the oracle computes it, and `PerMachine::merged_trivially` against jj's merge
    //! wherever it applies (`shortcut_agrees`). docs/internals/conformance.md, "Per-machine
    //! refs".

    use hegel::TestCase;
    use hegel::generators as gs;
    use jj_lib::default_backend_factories::default_backend_factories;
    use jj_lib::op_store::RemoteRef;
    use jj_lib::op_store::RemoteRefState;
    use jj_lib::operation::Operation;
    use jj_lib::ref_name::GitRefName;
    use jj_lib::ref_name::RefName;
    use jj_lib::repo::ReadonlyRepo;
    use jj_lib::repo::RepoLoader;
    use musubi_testutil::TestEnv;

    use super::*;

    use std::cell::RefCell;

    use super::refs_model::RefsModel;
    use super::refs_model::Slot;

    const X: &str = "refs/heads/x";

    /// A slot for `x`: the bookmark, `x@git` and whether it is tracked, and
    /// `git_refs["refs/heads/x"]`.
    impl Slot {
        /// `repo`'s view with `x` as this slot has it, verbatim.
        fn view(&self, repo: &ReadonlyRepo) -> View {
            let mut view = repo.view().store_view().clone();
            let name = RefName::new("x").to_owned();
            if self.l.is_present() {
                view.local_bookmarks.insert(name.clone(), self.l.clone());
            }
            if self.r.is_present() || self.tr {
                let state = if self.tr {
                    RemoteRefState::Tracked
                } else {
                    RemoteRefState::New
                };
                let remote_ref = RemoteRef {
                    target: self.r.clone(),
                    state,
                };
                view.remote_views
                    .entry(REMOTE_NAME_FOR_LOCAL_GIT_REPO.to_owned())
                    .or_default()
                    .bookmarks
                    .insert(name, remote_ref);
            }
            if self.k.is_present() {
                view.git_refs.insert(X.into(), self.k.clone());
            }
            view
        }

        /// `x` in `view`.
        fn of(view: &View) -> Self {
            let name = RefName::new("x");
            let remote = view
                .remote_views
                .get(REMOTE_NAME_FOR_LOCAL_GIT_REPO)
                .and_then(|remote| remote.bookmarks.get(name));
            Self {
                l: view
                    .local_bookmarks
                    .get(name)
                    .cloned()
                    .unwrap_or_else(RefTarget::absent),
                r: remote.map_or_else(RefTarget::absent, |remote| remote.target.clone()),
                tr: remote.is_some_and(|remote| remote.state == RemoteRefState::Tracked),
                k: view
                    .git_refs
                    .get(GitRefName::new(X))
                    .cloned()
                    .unwrap_or_else(RefTarget::absent),
            }
        }
    }

    /// A repository with a commit `one` on the root, and `two`, `three` and `four` beside
    /// each other on `one`, so that jj's merge resolves no conflict of them by ancestry.
    /// The commits are made in process, which starts no `jj`.
    fn repository() -> (TestEnv, Arc<ReadonlyRepo>, [CommitId; 4]) {
        let env = TestEnv::new();
        let repo = env.init_repo("alpha");
        let loader = RepoLoader::init_from_file_system(
            &repo.settings(),
            &repo.repo_path(),
            &default_backend_factories(),
        )
        .unwrap();
        let loaded = loader.load_at_head(None).block_on().unwrap();
        let tree = loaded.store().empty_merged_tree();
        let mut tx = loaded.start_transaction();
        let mut commit = |parent: &CommitId, name: &str| {
            tx.repo_mut()
                .new_commit(vec![parent.clone()], tree.clone())
                .set_description(name)
                .write()
                .block_on()
                .unwrap()
                .id()
                .clone()
        };
        let one = commit(loaded.store().root_commit_id(), "one");
        let [two, three, four] = ["two", "three", "four"].map(|name| commit(&one, name));
        let loaded = tx.commit("commits").block_on().unwrap();
        (env, loaded, [one, two, three, four])
    }

    /// An operation with `parents` and `repo`'s view with `x` as `slot` has it, ending `ms`
    /// milliseconds after `repo`'s.
    fn op_at(
        repo: &ReadonlyRepo,
        parents: &[&Operation],
        slot: &Slot,
        name: &str,
        ms: i64,
    ) -> Operation {
        let mut store_op = repo.operation().store_operation().clone();
        store_op.parents = parents.iter().map(|op| op.id().clone()).collect();
        store_op.metadata.description = name.to_owned();
        store_op.metadata.time.end.timestamp.0 += ms;
        store_op.view_id = repo
            .op_store()
            .write_view(&slot.view(repo))
            .block_on()
            .unwrap();
        let id = repo
            .op_store()
            .write_operation(&store_op)
            .block_on()
            .unwrap();
        repo.loader().load_operation(&id).block_on().unwrap()
    }

    /// jj's merge of `v` with `w` against `b`, each an operation of its own, as
    /// `realize::merged_by_jj` merges them; and the per-machine fields of all four.
    fn jj_merge(repo: &ReadonlyRepo, b: &Slot, v: &Slot, w: &Slot) -> (Slot, [PerMachine; 4]) {
        let head = repo.operation();
        let (b, v, w) = (
            op_at(repo, &[head], b, "b", 0),
            op_at(repo, &[head], v, "v", 0),
            op_at(repo, &[head], w, "w", 0),
        );
        let mut tx = repo
            .loader()
            .load_at(&v)
            .block_on()
            .unwrap()
            .start_transaction();
        tx.merge_operation(&b, &w).block_on().unwrap();
        let merged = tx.repo().view().store_view();
        let fields = |op: &Operation| PerMachine::of(op.view().block_on().unwrap().store_view());
        (
            Slot::of(merged),
            [fields(&b), fields(&v), fields(&w), PerMachine::of(merged)],
        )
    }

    /// Checks jj's merge of `v` with `w` against `b`: it is the model's, and the shortcut,
    /// where it applies, is jj's. Returns jj's merge, and what the shortcut gave.
    fn check(repo: &Arc<ReadonlyRepo>, b: &Slot, v: &Slot, w: &Slot) -> (Slot, Option<PerMachine>) {
        let (merged, [base, ours, theirs, jj]) = jj_merge(repo, b, v, w);
        let model = MODEL.with(|model| {
            model
                .borrow_mut()
                .get_or_insert_with(|| RefsModel::new(repo.clone()))
                .merge_slots(b, v, w)
        });
        assert_eq!(
            merged, model,
            "TSlot.merge of {v:?} with {w:?} against {b:?}"
        );
        let shortcut = PerMachine::merged_trivially(&base, ours, theirs);
        if let Some(fields) = &shortcut {
            assert_eq!(
                *fields, jj,
                "the shortcut, of {v:?} with {w:?} against {b:?}"
            );
        }
        (merged, shortcut)
    }

    thread_local!(static REPO: (TestEnv, Arc<ReadonlyRepo>, [CommitId; 4]) = repository());
    // The model for every case on this thread, merging with `REPO`'s index.
    thread_local!(
        #[cfg_attr(
            any(target_os = "illumos", target_os = "solaris"),
            allow(
                clippy::missing_const_for_thread_local,
                reason = "clippy wrongly reports this on illumos, but only when the \
                          rust-src component is installed, so it's allowed rather than expected"
            )
        )]
        static MODEL: RefCell<Option<RefsModel>> = const { RefCell::new(None) }
    );

    /// A slot: the bookmark absent or at either commit; `x@git` none, tracked with no
    /// target, or at either commit, tracked or not; and `git_refs` absent or at the first
    /// commit. Not every one is a view jj makes, but musubi's realization makes some that
    /// jj doesn't (`realize_not_WF`).
    ///
    /// A composite, so a failure prints each slot it drew once, as the slot.
    #[hegel::composite]
    fn slot(tc: &TestCase, commits: [CommitId; 4]) -> Slot {
        let target = |n: usize| match n {
            0 => RefTarget::absent(),
            n => RefTarget::normal(commits[n - 1].clone()),
        };
        let l = target(tc.draw(gs::integers::<usize>().max_value(2)));
        let r = target(tc.draw(gs::integers::<usize>().max_value(2)));
        Slot {
            l,
            r,
            tr: tc.draw(gs::booleans()),
            k: target(tc.draw(gs::integers::<usize>().max_value(1))),
        }
    }

    /// Which side, if either, keeps the base's per-machine fields, so that the shortcut applies.
    #[derive(Clone, Copy, Debug)]
    enum Keeps {
        Neither,
        Theirs,
        Ours,
    }

    #[hegel::test(test_cases = 200)]
    fn merges_conform_to_refs_model(tc: TestCase) {
        REPO.with(|(_, repo, commits)| {
            let b = tc.draw(slot(commits.clone()));
            // Often one side keeps the base's per-machine fields, where the shortcut applies.
            let mut v = tc.draw(slot(commits.clone()));
            let mut w = tc.draw(slot(commits.clone()));
            let keeps = tc.draw(gs::sampled_from(vec![
                Keeps::Neither,
                Keeps::Theirs,
                Keeps::Ours,
            ]));
            match keeps {
                Keeps::Theirs => {
                    w = Slot {
                        l: w.l,
                        ..b.clone()
                    }
                }
                Keeps::Ours => {
                    v = Slot {
                        l: v.l,
                        ..b.clone()
                    }
                }
                Keeps::Neither => {}
            }
            check(repo, &b, &v, &w);
        });
    }

    /// #56: a tracked `x@git` with no target, kept while `x` exists, where the other side
    /// deleted `x` and kept the base's per-machine fields. jj drops it; the shortcut took it
    /// (`shortcutUnguarded_keeps_absent`).
    #[test]
    fn merge_drops_tracked_absent_remote_ref() {
        REPO.with(|(_, repo, [one, ..])| {
            let one = RefTarget::normal(one.clone());
            let none = || RefTarget::absent();
            let b = Slot {
                l: one.clone(),
                r: none(),
                tr: false,
                k: none(),
            };
            let v = Slot {
                l: one,
                r: none(),
                tr: true,
                k: none(),
            };
            let w = Slot {
                l: none(),
                r: none(),
                tr: false,
                k: none(),
            };
            let (merged, shortcut) = check(repo, &b, &v, &w);
            assert_eq!(
                merged,
                Slot {
                    l: none(),
                    r: none(),
                    tr: false,
                    k: none()
                }
            );
            assert_eq!(shortcut, None);
        });
    }

    /// #56: the base and one side have a tracked `x@git` with no target; the other has no
    /// `x` and `x@git` at `two`, as after importing git's creation of `refs/heads/x` there and
    /// then deleting `x`, the export of that failing. jj drops the absent ref with `x`, then
    /// merges the other's as from nothing, untracked; the shortcut took it tracked
    /// (`shortcutUnguarded_untracks`).
    #[test]
    fn merge_untracks_remote_ref() {
        REPO.with(|(_, repo, [one, two, ..])| {
            let (one, two) = (
                RefTarget::normal(one.clone()),
                RefTarget::normal(two.clone()),
            );
            let none = || RefTarget::absent();
            let b = Slot {
                l: one,
                r: none(),
                tr: true,
                k: none(),
            };
            let w = Slot {
                l: none(),
                r: two.clone(),
                tr: true,
                k: two.clone(),
            };
            let (merged, shortcut) = check(repo, &b, &b, &w);
            assert_eq!(
                merged,
                Slot {
                    l: none(),
                    r: two.clone(),
                    tr: false,
                    k: two
                }
            );
            assert_eq!(shortcut, None);
        });
    }

    /// A criss-cross merge, whose heads have two closest common ancestors: jj merges against
    /// the two merged, and so must musubi (`firstBase_reverts`). This machine moved the
    /// bookmark to `two` in one ancestor, which the other kept the base's; both were merged
    /// twice; then this machine moved it to `three`, exporting it, and another to `four`,
    /// whose export failed. Against the ancestors merged the record is at `three`, as `.git`
    /// is; against the one that kept the base's it would be a conflict, which jj resolves
    /// only where the commits are in a line, so here they are beside each other.
    #[test]
    fn criss_cross_merges_per_machine_fields_as_jj() {
        REPO.with(|(_, repo, [one, two, three, four])| {
            let at = |id: &CommitId| RefTarget::normal(id.clone());
            let slot = |l: &CommitId, r: &CommitId| Slot {
                l: at(l),
                r: at(r),
                tr: true,
                k: at(r),
            };
            for swap in [false, true] {
                let head = repo.operation();
                let name = |n: &str| format!("{n} {swap}");
                // Each ancestor ends first once, as jj orders them by end time.
                let (kept_ms, moved_ms) = if swap { (2, 1) } else { (1, 2) };
                let base = op_at(repo, &[head], &slot(one, one), &name("base"), 0);
                let kept = op_at(repo, &[&base], &slot(one, one), &name("kept"), kept_ms);
                let moved = op_at(repo, &[&base], &slot(two, two), &name("moved"), moved_ms);
                let parents = [&kept, &moved];
                let merge1 = op_at(repo, &parents, &slot(two, two), &name("merge1"), 3);
                let merge2 = op_at(repo, &parents, &slot(two, two), &name("merge2"), 3);
                let ours = op_at(repo, &[&merge1], &slot(three, three), &name("ours"), 4);
                let theirs = op_at(repo, &[&merge2], &slot(four, two), &name("theirs"), 4);
                let (jj, _) = repo
                    .loader()
                    .merge_operations(vec![ours.clone(), theirs.clone()], None, None, [])
                    .block_on()
                    .unwrap();
                assert_eq!(Slot::of(jj.view().store_view()).r, at(three));
                let jj = PerMachine::of(jj.view().store_view());
                let merged = super::super::realize::merged_by_jj(
                    repo.loader(),
                    ours,
                    &[LocalOp(theirs.id().clone())],
                )
                .unwrap();
                assert_eq!(*merged, jj);
            }
        });
    }
}
