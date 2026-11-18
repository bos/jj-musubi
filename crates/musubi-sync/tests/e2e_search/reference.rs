//! The reference that divergence and bookmark and tag conflicts are judged against: the
//! hive's history rebuilt in one jj repository, in which every merge is jj's own.
//!
//! The hub's canonical history is a graph of operations: each machine's commands (and the
//! operations musubi writes for it, such as a forget), and the merges that nodes and `jj`
//! commands made of concurrent ones. The reference takes the same operations, with the same
//! parents, into one jj repository. An operation with one parent is taken as it is, its view
//! the canonical one, while the reference agrees with the hive at its parent. A merge is jj's
//! own merge of the same parents, in the same order, by `RepoLoader::merge_operations`, as
//! concurrent processes on one machine would have it merged. A merge made on a machine, rather
//! than realized there, agrees too where it is jj's merge of the parents as that machine had
//! them when it made it, though `jj op abandon` or musubi has since moved it onto others keeping
//! its view, lacking the working-copy commit or local alias of another machine's workspace.
//! An alias omission with the same visible commits requires an exact captured native
//! input and an independently certified foreign binding (`merged_as_made`). A native replay
//! can also use that same copy's actual owned bindings in the base and ordered parents,
//! for certified names only, including a realized merge. Its full structural result must
//! match the hive's; the realization's marker supplies no such evidence.
//!
//! Where jj's merge gives what the hive's did, the reference takes the hive's operation
//! itself, so that it goes on agreeing exactly. Where it doesn't, the reference goes its own
//! way from there: each later operation of one parent is applied to the reference's parent as
//! jj applies a concurrent operation, three-way against the hive's parent, and each later
//! merge merges the reference's operations, until an operation brings the two back into
//! agreement, and every later operation descending from where they parted descends from it
//! too. Agreement compares visible commits, bookmarks, tags and remote bookmarks, commits by
//! their contents, change ids and parents rather than their ids, since a commit a merge
//! rebases records when it was made, and without the author's time where jj resets it; a
//! commit of a change new to the operation, like the empty working-copy commit jj makes for an
//! abandoned one, by all but its change id. Workspaces aren't compared: which workspaces a
//! view has is musubi's (docs/internals/design.md, "Copies that go away").
//!
//! Divergence or a conflict that the hive has beyond the reference is musubi's: at its head,
//! and at any merge whose parents the two agree on, where jj's merge is exact. So that the
//! hive's history can stand for one repository's, every machine's realization of each
//! operation must have the hive's view of it, and no operation but a merge may make anything
//! diverge or conflict unless what it did explains it (`explained`).
//!
//! [`Reference::build`] walks that history and chooses when a native result is an
//! admissible explanation. The supporting contracts have separate homes:
//! - `adjudication`: source validation, native witnesses and the replay frontier;
//! - `comparison`: structural equality and divergence/conflicts beyond jj's;
//! - `workspaces`: independent historical evidence for workspace names and targets;
//! - `replay`: native jj execution from those authenticated inputs;
//! - `rewrites`: independent duplicate rebases versus certified serial native rebases.
//!
//! The negative controls below exercise those boundaries without changing the search's rules.

mod adjudication;
mod comparison;
mod replay;
mod rewrites;
mod witnesses;
mod workspaces;

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Write as _;
use std::fs;
use std::process::Command;
use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::backend::ChangeId;
use jj_lib::backend::CommitId;
use jj_lib::backend::MillisSinceEpoch;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::config::StackedConfig;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::repo::RepoLoader;
use jj_lib::settings::UserSettings;
use jj_lib::workspace::Workspace;
use musubi_jj::op_id::CanonicalOp;
use tempfile::TempDir;

use crate::identity::NativeOperation;
use crate::identity::SourceKey;
use crate::world::World;
use crate::world::merge_key;
use adjudication::{HistoryEntry, ReplayHistory};
use comparison::Facts;
use comparison::Summary;
use comparison::refs;
use replay::CertifiedParent;
use replay::project_private_workspaces;
use rewrites::MergeRewrite;
use rewrites::native_rebase_matches;
use rewrites::repeated_rebase;
use workspaces::WorkspaceCertificate;
use workspaces::foreign_alias_absent;

pub struct Reference {
    _dir: TempDir,
    loader: RepoLoader,
    facts: HashMap<CommitId, Facts>,
    /// The commits visible at each set of heads (`heads_key`).
    visible: HashMap<Vec<u8>, Arc<HashSet<CommitId>>>,
    /// The hive's head, as copied into the reference, and the reference's own operation for
    /// it.
    head_copy: Operation,
    head_replay: Operation,
    /// Each operation where the reference parted from the hive or came back to it, oldest
    /// first, for failure messages.
    pub deviations: Vec<String>,
    /// Every rewrite the hive's merges record: the merge, the new commit, and its
    /// predecessors.
    rewrites: Vec<MergeRewrite>,
    /// Operations other than merges that made a change diverge or a bookmark or tag
    /// conflict, where nothing the operation did explains it (`explained`), and merges that
    /// did more of either than jj's merge of the same parents.
    pub unexplained: Vec<String>,
    /// The hive's history, but for the root.
    history: Vec<CanonicalOp>,
    workspace_certificates: HashMap<CanonicalOp, WorkspaceCertificate>,
    workspace_in_progress: HashSet<CanonicalOp>,
    workspace_copies: HashMap<CanonicalOp, Operation>,
    pub workspace_unmapped: BTreeSet<(String, OperationId)>,
    /// Captured commands by copy and native id, for the number of commands it indexes.
    workspace_command_index: (usize, HashMap<(String, OperationId), SourceKey>),
    /// The keys of every operation in the hive's history, for the head they were read at.
    workspace_history_keys: Option<(CanonicalOp, HashSet<SourceKey>)>,
}

/// Settings for the reference's merges. The user is the tests' user; a seed of its own for
/// the change ids of commits jj makes keeps them clear of the hive's.
pub(crate) fn settings() -> UserSettings {
    let mut config = StackedConfig::with_defaults();
    let text = r#"
user.name = "Test User"
user.email = "test@example.com"
operation.hostname = "reference"
operation.username = "test"
debug.randomness-seed = 9000000000000000000
"#;
    config.add_layer(ConfigLayer::parse(ConfigSource::User, text).unwrap());
    UserSettings::from_config_and_home_dir(config, None).unwrap()
}

impl Reference {
    /// Rebuilds the hub's canonical history, up to its head, in a new repository whose git
    /// store borrows machine 0's objects and the recorded command sources', with jj's
    /// record of their change ids and conflicts. A raw source base can contain commits
    /// absent from the contracted canonical history, which machine 0 never fetched.
    pub fn build(world: &World) -> Self {
        let dir = musubi_testutil::tempdir();
        let git = dir.path().join("git");
        let status = Command::new("git")
            .args(["init", "--bare", "-q"])
            .arg(&git)
            .status()
            .unwrap();
        assert!(status.success(), "git init failed");
        let machine = world.fx.repo(0);
        let mut sources = world.evidence.command_sources.clone();
        sources.insert(
            machine.path().join(".git/objects"),
            machine.repo_path().join("store/extra"),
        );
        let mut alternates = String::new();
        for path in sources.keys() {
            writeln!(alternates, "{}", path.display()).unwrap();
        }
        fs::write(git.join("objects/info/alternates"), alternates).unwrap();
        let settings = settings();
        let root = dir.path().join("repo");
        fs::create_dir(&root).unwrap();
        block_on(Workspace::init_external_git(
            &settings,
            &root,
            WorkspaceName::DEFAULT,
            &git,
        ))
        .unwrap();
        let repo_path = root.join(".jj/repo");
        let extra = repo_path.join("store/extra");
        fs::remove_dir_all(&extra).unwrap();
        for source in sources.values() {
            musubi_testutil::copy_tree(source, &extra);
        }
        let loader =
            RepoLoader::init_from_file_system(&settings, &repo_path, &default_backend_factories())
                .unwrap();

        // The hub's history, parents first.
        let store = world.fx.hive.hub.store();
        let canonical = store.canonical();
        let head = CanonicalOp(store.head().1.clone());
        let mut ops: BTreeMap<CanonicalOp, op_store::Operation> = BTreeMap::new();
        let mut pending = vec![head.clone()];
        while let Some(id) = pending.pop() {
            if ops.contains_key(&id) || id == *canonical.root_operation_id() {
                continue;
            }
            let op = canonical.read_operation(&id).unwrap();
            pending.extend(CanonicalOp::parents_of(&op));
            ops.insert(id, op);
        }
        // Concurrent operations of a generation in the order they ended, which is the same
        // on every run of a case, unlike their ids: jj records each command's arguments,
        // temporary paths and all.
        let mut order: Vec<(u64, MillisSinceEpoch, String, CanonicalOp)> = ops
            .iter()
            .map(|(id, op)| {
                (
                    canonical.generation(id).unwrap(),
                    op.metadata.time.end.timestamp,
                    op.view_id.hex(),
                    id.clone(),
                )
            })
            .collect();
        order.sort();

        let root_op = block_on(loader.root_operation());
        let mut reference = Self {
            _dir: dir,
            loader,
            facts: HashMap::new(),
            visible: HashMap::new(),
            head_copy: root_op.clone(),
            head_replay: root_op.clone(),
            deviations: vec![],
            rewrites: vec![],
            unexplained: vec![],
            history: order.iter().map(|(.., id)| id.clone()).collect(),
            workspace_certificates: HashMap::new(),
            workspace_in_progress: HashSet::new(),
            workspace_copies: HashMap::new(),
            workspace_unmapped: BTreeSet::new(),
            workspace_command_index: (0, HashMap::new()),
            workspace_history_keys: None,
        };
        let root_view = canonical
            .read_operation_view(canonical.root_operation_id())
            .unwrap();
        let mut history =
            ReplayHistory::new(&ops, canonical.root_operation_id(), root_op, root_view);
        for (.., id) in order {
            let op = &ops[&id];
            let view = canonical.read_view(&op.view_id).unwrap();
            let entry = HistoryEntry::new(world, &id, op, view);
            reference.validate_source(world, &entry, &history);
            let copy = reference.copy_operation(&entry, &history);
            let replay = reference.replay_operation(world, &entry, &copy, &mut history);
            history.record(entry, copy, replay);
        }
        (reference.head_copy, reference.head_replay) = history.heads(&head);
        reference
    }

    /// The changes that diverge into more commits in `after` than in `before`, and the
    /// bookmarks and tags that conflict in `after` but not `before`, but for a bookmark on a
    /// commit `after` abandons, which jj moves to the commit's parents, so conflicts if it
    /// was a merge.
    fn made_divergent_or_conflicted(&mut self, before: &View, after: &View) -> Vec<Made> {
        let mut made = vec![];
        let (old, new) = (self.change_counts(before), self.change_counts(after));
        for (change, n) in &new {
            if *n > 1 && old.get(change).copied().unwrap_or(0) < *n {
                made.push(Made::Diverges(change.clone()));
            }
        }
        let visible = self.visible(after);
        let before_refs = refs(before);
        for (name, target) in refs(after) {
            if name.starts_with("remote ") || target.is_resolved() {
                continue;
            }
            let was = before_refs.get(&name);
            if was.is_some_and(|was| !was.is_resolved()) {
                continue;
            }
            let abandoned = was
                .and_then(|was| was.as_normal().cloned())
                .filter(|commit| !visible.contains(commit))
                .is_some_and(|commit| {
                    let parents: BTreeSet<CommitId> =
                        self.facts(&commit).parents.iter().cloned().collect();
                    target.adds().flatten().cloned().collect::<BTreeSet<_>>() == parents
                });
            if !abandoned {
                made.push(Made::Conflicts(name));
            }
        }
        made
    }

    /// A native command can itself make a change diverge. Its recorded result bounds what
    /// translation may add: compare versions and conflict terms, not just their counts.
    pub fn unexplained_command_changes(
        &mut self,
        before: &View,
        native: &View,
        canonical: &View,
    ) -> Vec<String> {
        let mut made: Vec<_> = self
            .made_divergent_or_conflicted(before, canonical)
            .iter()
            .map(Made::to_string)
            .collect();
        if !made.is_empty() {
            let known = self
                .visible(native)
                .iter()
                .map(|commit| self.facts(commit).change.clone())
                .collect();
            let beyond = self.beyond(canonical, native, &known);
            made.retain(|change| beyond.contains(change));
        }
        made
    }

    /// Every machine's realization of each of the hive's operations, the operation another
    /// machine made or a merge, has the canonical view's visible commits, bookmarks and tags:
    /// a machine's commands run where the hive's history says they did. A machine's own
    /// operations have the canonical view's bookmarks and tags, and its visible commits but
    /// for those the canonical view keeps visible for other machines (`canonical_view`):
    /// whether keeping them makes anything diverge or conflict is judged against the
    /// canonical parent, as for any operation. Returns those that differ.
    pub fn check_realizations(&mut self, world: &World) -> Vec<String> {
        let store = world.fx.hive.hub.store();
        let canonical = store.canonical();
        let mut differ = vec![];
        for (m, member) in world.fx.hive.members.iter().enumerate() {
            let node = member.adapter.repo();
            let op_store = node.loader().op_store();
            for id in self.history.clone() {
                let Some(local) = node.local_of(&id) else {
                    differ.push(format!(
                        "{} hasn't realized {}",
                        world.machine(m),
                        &id.0.hex()[..12]
                    ));
                    continue;
                };
                let local_op = block_on(op_store.read_operation(&local.0)).unwrap();
                let ours = block_on(op_store.read_view(&local_op.view_id)).unwrap();
                let theirs = canonical.read_operation_view(&id).unwrap();
                let realized = world.realized(m, &id, &local_op);
                let mut why = vec![];
                if realized {
                    if ours.head_ids != theirs.head_ids {
                        why.push("heads differ".to_owned());
                    }
                } else {
                    if !self.visible(&ours).is_subset(&self.visible(&theirs)) {
                        why.push("commits visible here are hidden in the hive".to_owned());
                    }
                }
                if ours.local_bookmarks != theirs.local_bookmarks {
                    why.push("bookmarks differ".to_owned());
                }
                if ours.local_tags != theirs.local_tags {
                    why.push("tags differ".to_owned());
                }
                if !why.is_empty() {
                    differ.push(format!(
                        "{}'s {} {} of {} \"{}\": {}",
                        world.machine(m),
                        if realized { "realization" } else { "operation" },
                        &local.0.hex()[..12],
                        &id.0.hex()[..12],
                        local_op
                            .metadata
                            .description
                            .lines()
                            .next()
                            .unwrap_or_default(),
                        why.join(", ")
                    ));
                }
            }
        }
        differ
    }
}

/// Whether every operation descending from one of `deviated` is an ancestor or a
/// descendant of `id` (or `id`), in the history `ops` with `children`.
fn dominates(
    ops: &BTreeMap<CanonicalOp, op_store::Operation>,
    children: &HashMap<CanonicalOp, Vec<CanonicalOp>>,
    deviated: &BTreeSet<CanonicalOp>,
    id: &CanonicalOp,
) -> bool {
    if deviated.is_empty() {
        return true;
    }
    let walk = |start: &CanonicalOp, next: &dyn Fn(&CanonicalOp) -> Vec<CanonicalOp>| {
        let mut found: HashSet<CanonicalOp> = HashSet::new();
        let mut pending = vec![start.clone()];
        while let Some(op) = pending.pop() {
            if found.insert(op.clone()) {
                pending.extend(next(&op));
            }
        }
        found
    };
    let parents = |op: &CanonicalOp| ops.get(op).map_or(vec![], CanonicalOp::parents_of);
    let kids = |op: &CanonicalOp| children.get(op).cloned().unwrap_or_default();
    let related: HashSet<CanonicalOp> = walk(id, &parents)
        .into_iter()
        .chain(walk(id, &kids))
        .collect();
    deviated
        .iter()
        .all(|d| walk(d, &kids).iter().all(|op| related.contains(op)))
}

/// What a single operation did that would make a change diverge or a name conflict, as
/// `Reference::made_divergent_or_conflicted` finds it.
enum Made {
    Diverges(String),
    Conflicts(String),
}

impl std::fmt::Display for Made {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Diverges(change) => write!(f, "{change} diverges"),
            Self::Conflicts(name) => write!(f, "{name} conflicts"),
        }
    }
}

/// Whether what `op` did explains `made`, as jj would do it on one machine: a fetch brings
/// back a pushed commit beside its rewrite, or conflicts a bookmark with the remote's; an
/// undo, redo, restore or revert brings back an older view; and an import of git refs takes
/// what `.git` has where jj's record of it differs, which happens without anyone moving a
/// branch, as when an undo restores an older record and a conflicted bookmark can't be
/// exported over it. An import of git's HEAD likewise moves the working copy onto what
/// `.git`'s HEAD has, bringing back a rewritten commit there, as after a command at an older
/// operation wrote HEAD and jj's merge with the operations since conflicted its record of it.
/// (Whether musubi keeps those records as jj would is for the per-machine refs' conformance
/// test, docs/internals/conformance.md, and the check of every import, `imports`.) Anything
/// else must be bounded by a captured native command's actual result, or it is musubi's:
/// an operation of its own, or a realization or canonical form that differs from that result.
fn explained(op: &op_store::Operation) -> bool {
    NativeOperation::of(op).explains_reintroduced_work()
}

/// A canonical operation, for messages: its description, id and machine.
fn describe(id: &CanonicalOp, op: &op_store::Operation) -> String {
    format!(
        "\"{}\" ({} on {})",
        op.metadata.description.lines().next().unwrap_or_default(),
        &id.0.hex()[..12],
        op.metadata.hostname
    )
}

// Negative controls: the reference must reject unproven inputs and excess effects.

#[test]
fn private_projection_requires_a_current_name_and_an_actual_owned_slot() {
    let id = |n| CommitId::new(vec![n; 20]);
    let mut canonical = View::make_root(id(0));
    canonical
        .wc_commit_ids
        .insert("alpha/default".into(), id(1));
    canonical.wc_commit_ids.insert("beta/default".into(), id(3));
    let mut native = View::make_root(id(0));
    native.wc_commit_ids.insert("default".into(), id(2));
    native.wc_commit_ids.insert("beta/default".into(), id(4));
    let names = BTreeSet::from(["alpha/default".to_owned()]);
    let empty = BTreeSet::new();
    for (source, frontier, absent, has_raw, expected) in [
        (true, false, false, true, true),
        (false, true, true, true, true),
        (false, true, false, true, false),
        (false, false, true, true, false),
        (false, true, true, false, false),
    ] {
        let mut view = canonical.clone();
        let mut raw = native.clone();
        if !has_raw {
            raw.wc_commit_ids.remove(WorkspaceName::new("default"));
        }
        project_private_workspaces(
            &mut view,
            &raw,
            "alpha",
            if source { &names } else { &empty },
            if frontier { &names } else { &empty },
            absent,
        );
        assert_eq!(
            view.wc_commit_ids.get(WorkspaceName::new("alpha/default")),
            expected.then(|| id(2)).as_ref()
        );
        assert_eq!(
            view.wc_commit_ids.get(WorkspaceName::new("beta/default")),
            Some(&id(3)),
            "raw foreign aliases cannot override canonical bindings"
        );
    }
    let mut view = canonical;
    let literal = BTreeSet::from(["alpha/beta/default".to_owned()]);
    project_private_workspaces(&mut view, &native, "alpha", &literal, &names, true);
    assert_eq!(
        view.wc_commit_ids[WorkspaceName::new("alpha/beta/default")],
        id(4)
    );
    assert_eq!(
        view.wc_commit_ids[WorkspaceName::new("beta/default")],
        id(3)
    );
}

#[test]
fn foreign_commands_keep_bindings_after_their_local_aliases_are_forgotten() {
    let commit = |byte| CommitId::new(vec![byte; 20]);
    let mut command = crate::world::CommandSnapshot {
        id: OperationId::new(vec![1; 64]),
        copy: "alpha".to_owned(),
        copies: BTreeSet::from(["alpha".to_owned(), "beta".to_owned()]),
        parent: OperationId::new(vec![2; 64]),
        input: None,
        predecessors: None,
        base: View::make_root(commit(0)),
        made: View::make_root(commit(0)),
    };
    let mut proof = WorkspaceCertificate::default();
    proof
        .entry("beta/default".to_owned())
        .remember_binding(commit(1));
    proof.entry("beta/default".to_owned()).authenticate_name();
    let old = commit(1);
    let new = commit(2);
    let visible = HashSet::from([new.clone()]);
    let carried = |proof: &WorkspaceCertificate,
                   command: &crate::world::CommandSnapshot,
                   target: &CommitId,
                   visible: &HashSet<CommitId>| {
        proof.foreign_binding_carried_by_command(command, "beta/default", target, visible)
    };
    assert!(carried(&proof, &command, &old, &visible));
    command.predecessors = Some(BTreeMap::from([(new.clone(), vec![old.clone()])]));
    assert!(carried(&proof, &command, &new, &visible));
    assert!(!carried(&proof, &command, &old, &visible));
    assert!(!carried(&proof, &command, &commit(3), &visible));
    assert!(!carried(&proof, &command, &new, &HashSet::new()));
    proof.entry("beta/default".to_owned()).mark_dormant();
    assert!(!carried(&proof, &command, &new, &visible));
    proof.clear_dormancy();
    proof.clear_bindings();
    assert!(!carried(&proof, &command, &new, &visible));
    proof
        .entry("beta/default".to_owned())
        .remember_binding(old.clone());
    command.copy = "beta".to_owned();
    assert!(!carried(&proof, &command, &new, &visible));
    command.copy = "alpha".to_owned();
    command
        .predecessors
        .as_mut()
        .unwrap()
        .insert(commit(3), vec![old.clone()]);
    assert!(!carried(
        &proof,
        &command,
        &new,
        &HashSet::from([new.clone(), commit(3)])
    ));
}

#[test]
fn only_an_abandoned_owner_command_adds_a_name_to_a_retained_command() {
    use jj_lib::ref_name::{WorkspaceName, WorkspaceNameBuf};

    use crate::world::CommandSnapshot;

    let op = |byte| OperationId::new(vec![byte; 64]);
    let view = |work: Option<u8>| {
        let mut view = View::make_root(CommitId::new(vec![0; 20]));
        if let Some(byte) = work {
            view.wc_commit_ids.insert(
                WorkspaceNameBuf::from("work"),
                CommitId::new(vec![byte; 20]),
            );
        }
        view
    };
    let command = |id, parent, base, made| CommandSnapshot {
        id: op(id),
        copy: "alpha".to_owned(),
        copies: BTreeSet::from(["alpha".to_owned()]),
        parent: op(parent),
        input: None,
        predecessors: None,
        base: view(base),
        made: view(made),
    };
    let key = |n: u8| SourceKey::from_template(&n.to_string());
    let name = WorkspaceName::new("work");
    // The rename (1) on 0 created `work`; the retained command (2) ran on it.
    let rename = command(1, 0, None, Some(1));
    let retained = command(2, 1, Some(1), Some(2));
    let check = |commands: &[(u8, &CommandSnapshot)],
                 retained: &CommandSnapshot,
                 in_history: Option<u8>,
                 parents_have: bool| {
        let commands: BTreeMap<_, _> = commands.iter().map(|(n, c)| (key(*n), *c)).collect();
        workspaces::abandoned_creation(
            |copy, id| {
                commands
                    .iter()
                    .find(|(_, c)| c.copy == copy && c.id == *id)
                    .map(|(key, c)| (key, *c))
            },
            retained,
            name,
            |chain| in_history.is_some_and(|n| chain.contains(&&key(n))),
            || parents_have,
        )
    };
    assert!(check(&[(1, &rename)], &retained, None, false));
    // A parent in the hive's history that has the name: the command adds nothing.
    assert!(!check(&[(1, &rename)], &retained, None, true));
    // The creating command is still in the hive's history.
    assert!(!check(&[(1, &rename)], &retained, Some(1), false));
    // Broken chains: no captured command, another copy's, or one that made another base.
    assert!(!check(&[], &retained, None, false));
    let mut foreign = rename.clone();
    foreign.copy = "beta".to_owned();
    assert!(!check(&[(1, &foreign)], &retained, None, false));
    assert!(!check(
        &[(1, &rename)],
        &command(2, 1, Some(3), Some(2)),
        None,
        false
    ));
    // A base that already had the name from anything but a captured command.
    let kept = command(1, 0, Some(1), Some(1));
    assert!(!check(&[(1, &kept)], &retained, None, false));
    // A longer abandoned chain reaches its creator, and every link must be gone.
    let created = command(3, 0, None, Some(1));
    let kept = command(1, 3, Some(1), Some(1));
    let chain = [(1, &kept), (3, &created)];
    assert!(check(&chain, &retained, None, false));
    assert!(!check(&chain, &retained, Some(1), false));
    assert!(!check(&chain, &retained, Some(3), false));
    // The store-reading checks run only when the cheap walk succeeds.
    assert!(!workspaces::abandoned_creation(
        |_, _| None,
        &retained,
        name,
        |_| unreachable!(),
        || unreachable!(),
    ));
}

#[test]
fn native_foreign_alias_omissions_do_not_erase_owned_names() {
    let commit = CommitId::new(vec![1; 20]);
    let mut command = crate::world::CommandSnapshot {
        id: OperationId::new(vec![1; 64]),
        copy: "alpha#aaaa".to_owned(),
        copies: BTreeSet::from(["alpha#aaaa".to_owned(), "beta#bbbb".to_owned()]),
        parent: OperationId::new(vec![2; 64]),
        input: None,
        predecessors: None,
        base: View::make_root(commit.clone()),
        made: View::make_root(commit.clone()),
    };
    let key = "beta#bbbb/default";
    let mut source_names = BTreeSet::new();
    assert!(foreign_alias_absent(
        &command,
        |name| source_names.contains(name),
        key
    ));
    assert!(!foreign_alias_absent(
        &command,
        |name| source_names.contains(name),
        "alpha#aaaa/default"
    ));
    for alias in ["beta/default", "beta-bbbb/default", "beta-bbbb--/default"] {
        command.made.wc_commit_ids.clear();
        command
            .made
            .wc_commit_ids
            .insert(alias.into(), commit.clone());
        assert!(
            !foreign_alias_absent(&command, |name| source_names.contains(name), key),
            "{alias}"
        );
    }
    command.made.wc_commit_ids.clear();
    command
        .made
        .wc_commit_ids
        .insert("beta/second".into(), commit.clone());
    assert!(foreign_alias_absent(
        &command,
        |name| source_names.contains(name),
        key
    ));
    command
        .made
        .wc_commit_ids
        .insert("beta/default".into(), commit);
    // A later birth does not prove that this earlier slot was owned at this source.
    let later_births = BTreeSet::from(["alpha#aaaa/beta/default".to_owned()]);
    assert!(!foreign_alias_absent(
        &command,
        |name| source_names.contains(name),
        key
    ));
    source_names.extend(later_births);
    assert!(foreign_alias_absent(
        &command,
        |name| source_names.contains(name),
        key
    ));
}

#[test]
fn native_aliases_carry_only_authenticated_workspace_names() {
    let commit = |byte| CommitId::new(vec![byte; 20]);
    let mut base = View::make_root(commit(0));
    base.wc_commit_ids.insert("default".into(), commit(1));
    base.wc_commit_ids.insert("beta/default".into(), commit(2));
    let mut command = crate::world::CommandSnapshot {
        id: OperationId::new(vec![1; 64]),
        copy: "alpha".to_owned(),
        copies: BTreeSet::from(["alpha".to_owned(), "beta".to_owned()]),
        parent: OperationId::new(vec![2; 64]),
        input: None,
        predecessors: None,
        base: base.clone(),
        made: base,
    };
    command
        .made
        .wc_commit_ids
        .insert("beta/default".into(), commit(3));
    let mut input = WorkspaceCertificate::default();
    for name in ["alpha/default", "beta/default"] {
        input.entry(name.to_owned()).authenticate_name();
    }
    input
        .entry("beta/default".to_owned())
        .remember_binding(commit(4));
    let mut births: BTreeSet<_> = input.names().cloned().collect();
    assert!(
        input
            .names_carried_by_command(&command, &births)
            .any(|name| name == "beta/default")
    );
    assert_eq!(input.binding("beta/default"), Some(&commit(4)));

    // Neither a historical birth nor a matching existing raw alias supplies a missing
    // input certificate. The target and the global birth remain unchanged in this control.
    input.remove_name("beta/default");
    input.remove_binding("beta/default");
    assert!(
        !input
            .names_carried_by_command(&command, &births)
            .any(|name| name == "beta/default")
    );
    input.entry("beta/default".to_owned()).authenticate_name();
    births.insert("alpha/beta/default".to_owned());
    assert!(
        !input
            .names_carried_by_command(&command, &births)
            .any(|name| name == "beta/default")
    );

    command
        .made
        .wc_commit_ids
        .remove(WorkspaceName::new("default"));
    command
        .made
        .wc_commit_ids
        .insert("second".into(), commit(1));
    assert!(
        !input
            .names_carried_by_command(&command, &births)
            .any(|name| name == "alpha/default")
    );
}

#[test]
fn a_clones_workspace_witness_is_its_native_join_input() {
    use crate::world::{Naming, Setup};

    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: false,
    });
    world.forget_copy(0, 1);
    world.sync(0);
    world.clone_copy(1);
    world.converge();
    let (key, bindings) = world.evidence.workspace_joins.iter().next().unwrap();
    let store = world.fx.hive.members[1].adapter.repo().canonical_store();
    let join = store
        .operation_ids()
        .unwrap()
        .into_iter()
        .find(|id| merge_key(&store.read_operation(id).unwrap()) == *key)
        .unwrap();
    let own = format!("{}/default", world.fx.machine_key(1));
    let mut reference = Reference::build(&world);
    assert_eq!(
        reference.workspace_certificate(&world, &join).binding(&own),
        bindings.get(&own)
    );
    assert!(bindings.contains_key(&own));

    // A matching join timestamp and description do not certify another owner's name or
    // an owned name at a target the native join never had.
    let mut operation = store.read_operation(&join).unwrap();
    let mut view = store.read_view(&operation.view_id).unwrap();
    let foreign = format!("{}/default", world.fx.machine_key(0));
    let wrong = world.fx.hive.members[0]
        .adapter
        .repo()
        .loader()
        .store()
        .root_commit_id()
        .clone();
    view.wc_commit_ids
        .insert(foreign.clone().into(), wrong.clone());
    view.wc_commit_ids.insert(own.clone().into(), wrong);
    operation.view_id = store.write_view(&view).unwrap();
    let forged = store.write_operation(&operation).unwrap();
    let certificate = reference.workspace_certificate(&world, &forged);
    assert!(certificate.binding(&foreign).is_none());
    assert!(certificate.binding(&own).is_none());

    world.evidence.workspace_joins.clear();
    reference.workspace_certificates.clear();
    assert!(
        !reference
            .workspace_certificate(&world, &join)
            .has_name(&own)
    );
}

#[test]
fn native_payloads_allow_only_foreign_working_copies_retained_from_their_inputs() {
    use crate::world::{Naming, Setup};

    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: false,
    });
    let key = format!("{}/default", world.fx.machine_key(1));
    let base = CanonicalOp(world.fx.hive.hub.store().head().1.clone());
    let store = world.fx.hive.members[0].adapter.repo().canonical_store();
    let template = store.read_operation(&base).unwrap();
    let source_view = store.read_view(&template.view_id).unwrap();
    let old = source_view.wc_commit_ids[WorkspaceName::new(&key)].clone();
    let native_base = world.latest_op_head(0);
    world.jj(0, &["describe", &old.hex(), "-m", "first foreign rewrite"]);
    let first = OperationId::try_from_hex(world.latest_op_head(0)).unwrap();
    world.jj_at_op(
        0,
        &native_base,
        &["describe", &old.hex(), "-m", "second foreign rewrite"],
    );
    let second = OperationId::try_from_hex(world.latest_op_head(0)).unwrap();
    let snapshot = |id: &OperationId| {
        world
            .evidence
            .commands
            .values()
            .find(|c| c.id == *id)
            .unwrap()
    };
    let replacement = |id: &OperationId| {
        snapshot(id)
            .predecessors
            .as_ref()
            .unwrap()
            .iter()
            .find(|(_, predecessors)| predecessors.contains(&old))
            .unwrap()
            .0
            .clone()
    };
    let (first_version, second_version) = (replacement(&first), replacement(&second));
    let mut command = snapshot(&first).clone();
    command.made.head_ids = HashSet::from([first_version.clone()]);
    let mut reference = Reference::build(&world);
    let store = world.fx.hive.members[0].adapter.repo().canonical_store();
    let root = world.fx.hive.members[0]
        .adapter
        .repo()
        .loader()
        .store()
        .root_commit_id()
        .clone();
    for case in [
        "retained",
        "missing proof",
        "dormant",
        "missing slot",
        "hidden",
        "new target",
        "own",
    ] {
        let mut source = source_view.clone();
        let mut certificate = WorkspaceCertificate::default();
        certificate.entry(key.clone()).remember_binding(old.clone());
        certificate.entry(key.clone()).authenticate_name();
        if case == "missing proof" {
            certificate.clear_bindings();
        }
        if case == "dormant" {
            certificate.entry(key.clone()).mark_dormant();
        }
        if case == "missing slot" {
            source.wc_commit_ids.remove(WorkspaceName::new(&key));
        }
        if case == "hidden" {
            source.head_ids = HashSet::from([root.clone()]);
        }
        let mut input = template.clone();
        input.metadata.attributes.clear();
        input.metadata.description = format!("foreign visibility input: {case}");
        input.parents = vec![base.0.clone()];
        input.view_id = store.write_view(&source).unwrap();
        let input_id = store.write_operation(&input).unwrap();
        reference
            .workspace_certificates
            .insert(input_id.clone(), certificate);
        command.input = Some(input_id.clone());
        command.copy = world.fx.machine_key(if case == "own" { 1 } else { 0 });
        let mut output = input;
        output.parents = vec![input_id.0];
        let mut canonical = command.made.clone();
        canonical.head_ids.insert(old.clone());
        canonical.wc_commit_ids.insert(
            key.clone().into(),
            if case == "new target" {
                second_version.clone()
            } else {
                old.clone()
            },
        );
        let protected = reference.retained_foreign_targets(
            &world,
            &command.copy,
            command.input.as_ref(),
            &output,
            &canonical,
        );
        assert_eq!(protected.contains(&old), case == "retained", "{case}");
        let mut expected = command.made.clone();
        expected.head_ids.extend(protected);
        let unexpected =
            reference.unexplained_command_changes(&command.base, &expected, &canonical);
        assert_eq!(
            unexpected.is_empty(),
            case == "retained",
            "{case}: {unexpected:?}"
        );
        if case == "retained" {
            canonical.head_ids.insert(second_version.clone());
            assert!(
                !reference
                    .unexplained_command_changes(&command.base, &expected, &canonical)
                    .is_empty(),
                "a third version is still extra"
            );
            canonical.head_ids.remove(&first_version);
            assert!(
                !reference
                    .unexplained_command_changes(&command.base, &expected, &canonical)
                    .is_empty(),
                "equal counts cannot hide a different version"
            );
        }
    }
}

#[test]
fn workspace_witnesses_walk_deep_histories_without_recursing() {
    use crate::world::{Naming, Setup};

    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: false,
    });
    let store = world.fx.hive.members[0].adapter.repo().canonical_store();
    let mut head = CanonicalOp(world.fx.hive.hub.store().head().1.clone());
    let mut operation = store.read_operation(&head).unwrap();
    let mut reference = Reference::build(&world);
    let original = reference.workspace_certificate(&world, &head);
    assert!(original.bindings().next().is_some());
    operation.metadata.attributes.clear();
    operation.metadata.workspace_name = None;
    operation.commit_predecessors = None;
    for n in 0..512 {
        operation.parents = vec![head.0];
        operation.metadata.description = format!("unchanged workspace source {n}");
        head = store.write_operation(&operation).unwrap();
    }
    let certificate = reference.workspace_certificate(&world, &head);
    assert_eq!(
        certificate.bindings().collect::<BTreeMap<_, _>>(),
        original.bindings().collect::<BTreeMap<_, _>>()
    );
    assert_eq!(
        certificate.names().collect::<BTreeSet<_>>(),
        original.names().collect::<BTreeSet<_>>()
    );
    assert_eq!(
        certificate.merge_births().collect::<BTreeSet<_>>(),
        original.merge_births().collect::<BTreeSet<_>>()
    );
    assert_eq!(
        certificate.dormant_names().collect::<BTreeSet<_>>(),
        original.dormant_names().collect::<BTreeSet<_>>()
    );
    assert_eq!(
        reference.workspace_copy(&world, &head).unwrap().id(),
        &head.0
    );
    // A trim witness can refer outside its new root-parent graph. These dependencies
    // must be preloaded too, rather than recursing once per earlier trim.
    let owner = world.fx.machine_key(1);
    let key = format!("{owner}/default");
    let target = original.binding(&key).unwrap().clone();
    operation.parents = vec![store.root_operation_id().0.clone()];
    operation
        .metadata
        .attributes
        .insert("musubi.work".to_owned(), owner);
    for n in 0..512 {
        operation.metadata.description = format!("trim workspace source {n}");
        let next = store.write_operation(&operation).unwrap();
        world
            .evidence
            .workspace_fixup_inputs
            .insert(merge_key(&operation), (world.fx.machine_key(0), head));
        head = next;
    }
    let certificate = reference.workspace_certificate(&world, &head);
    assert_eq!(certificate.binding(&key), Some(&target));
    assert!(certificate.has_name(&key));
    assert_eq!(
        certificate.has_merge_birth(&key),
        original.has_merge_birth(&key)
    );
    assert!(!certificate.is_dormant(&key));
}

#[test]
fn workspace_certificates_require_each_sources_existing_binding() {
    use crate::world::{Naming, Setup};

    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: false,
    });
    let key = format!("{}/default", world.fx.machine_key(0));
    let store = world.fx.hive.members[0].adapter.repo().canonical_store();
    let (base, mut operation, original) = store
        .operation_ids()
        .unwrap()
        .into_iter()
        .filter_map(|id| {
            let op = store.read_operation(&id).unwrap();
            let view = store.read_view(&op.view_id).unwrap();
            (world.baseline_operation(&merge_key(&op))
                && view.wc_commit_ids.contains_key(WorkspaceName::new(&key)))
            .then_some((id, op, view))
        })
        .max_by_key(|(_, op, _)| op.metadata.time.end.timestamp)
        .unwrap();
    let old = original.wc_commit_ids[WorkspaceName::new(&key)].clone();
    let native_base = world.latest_op_head(1);
    world.jj(1, &["describe", &old.hex(), "-m", "rewritten elsewhere"]);
    world.sync(1);
    let replacement = CommitId::try_from_hex(
        world
            .raw_jj(
                1,
                &[
                    "log",
                    "-r",
                    "description(substring:rewritten)",
                    "--no-graph",
                    "-T",
                    "commit_id",
                ],
            )
            .trim(),
    )
    .unwrap();
    assert_eq!(replacement.as_bytes().len(), 20);
    world.jj_at_op(
        1,
        &native_base,
        &["describe", &old.hex(), "-m", "second rewrite"],
    );
    let second = CommitId::try_from_hex(
        world
            .raw_jj(
                1,
                &[
                    "log",
                    "-r",
                    "description(substring:second)",
                    "--no-graph",
                    "-T",
                    "commit_id",
                ],
            )
            .trim(),
    )
    .unwrap();
    assert_eq!(second.as_bytes().len(), 20);
    let root = world.fx.hive.members[0]
        .adapter
        .repo()
        .loader()
        .store()
        .root_commit_id()
        .clone();
    world.forget_copy(1, 0);
    world.sync(1);
    let departed = world.fx.hive.members[1]
        .adapter
        .repo()
        .canonical_store()
        .operation_ids()
        .unwrap()
        .into_iter()
        .find(|id| {
            let presence = world.fx.hive.members[1]
                .adapter
                .repo()
                .presence(id)
                .unwrap();
            presence.known().contains(&world.fx.machine_key(0))
                && !presence.is_present(&world.fx.machine_key(0))
        })
        .unwrap();
    world.sync(0);
    world.jj(0, &["new", "-m", "renewed private work"]);
    let renewed = CommitId::try_from_hex(world.working_copies(0)["default"].trim()).unwrap();
    let store = world.fx.hive.members[0].adapter.repo().canonical_store();
    let departure_store = world.fx.hive.members[1].adapter.repo().canonical_store();
    let departure_op = departure_store.read_operation(&departed).unwrap();
    let departure_view = departure_store.read_view(&departure_op.view_id).unwrap();
    assert_eq!(
        store.write_view(&departure_view).unwrap(),
        departure_op.view_id
    );
    assert_eq!(store.write_operation(&departure_op).unwrap(), departed);
    operation.metadata.attributes.clear();
    operation.metadata.workspace_name = None;
    operation.commit_predecessors = None;
    operation.metadata.description = "certificate source".to_owned();
    operation.metadata.time.end.timestamp.0 += 10_000;
    operation.parents = vec![base.0.clone()];
    // These are the certificate checker's inputs, not simulated musubi output: a proven
    // name can still point at the hidden old commit before its owner repairs it.
    for case in [
        "unique",
        "missing",
        "visible",
        "divergent",
        "wrong",
        "dormant",
        "merge",
        "omitted",
        "all dormant",
        "deleted",
        "conflicting",
        "output only",
        "absent",
        "renewed",
        "renewed wrong",
        "renewed missing",
        "foreign alias forgotten",
        "foreign alias already gone",
        "foreign name missing",
        "owner alias gone",
    ] {
        let mut reference = Reference::build(&world);
        let renewal = case.starts_with("renewed");
        operation.parents = vec![if case == "absent" || renewal {
            departed.0.clone()
        } else {
            base.0.clone()
        }];
        let mut source = original.clone();
        source.head_ids = HashSet::from([replacement.clone()]);
        if case == "visible" {
            source.head_ids.insert(old.clone());
        }
        if case == "divergent" {
            source.head_ids.insert(second.clone());
        }
        if case == "conflicting" {
            source
                .wc_commit_ids
                .insert(key.clone().into(), root.clone());
        }
        if case == "output only" {
            source.head_ids = HashSet::from([root.clone()]);
        }
        let target = if renewal {
            if case == "renewed wrong" {
                old.clone()
            } else {
                renewed.clone()
            }
        } else if case == "omitted" || case == "all dormant" || case == "deleted" {
            old.clone()
        } else if case == "wrong" {
            root.clone()
        } else {
            replacement.clone()
        };
        let mut proof = WorkspaceCertificate::default();
        proof.entry(key.clone()).remember_binding(old.clone());
        proof.entry(key.clone()).authenticate_name();
        proof.entry(key.clone()).witness_merge_birth();
        let opaque_command = case.starts_with("foreign ") || case == "owner alias gone";
        if opaque_command {
            proof.clear_bindings();
        }
        if case == "foreign name missing" {
            proof.clear_names();
            proof.clear_merge_births();
        }
        if case == "missing" || case == "deleted" {
            proof.clear_bindings();
            proof.clear_names();
        }
        if renewal || ["dormant", "omitted", "all dormant", "deleted"].contains(&case) {
            source.wc_commit_ids.remove(WorkspaceName::new(&key));
            if case != "deleted" {
                proof.entry(key.clone()).mark_dormant();
            }
        }
        operation.view_id = store.write_view(&source).unwrap();
        let parent = store.write_operation(&operation).unwrap();
        reference
            .workspace_certificates
            .insert(parent.clone(), proof);
        let mut output = operation.clone();
        output.metadata.description = format!("certificate result: {case}");
        output.parents = vec![parent.0.clone()];
        let mut made = source.clone();
        made.wc_commit_ids
            .insert(key.clone().into(), target.clone());
        if case == "output only" {
            made.head_ids.insert(replacement.clone());
        }
        if renewal || ["merge", "omitted", "all dormant", "deleted"].contains(&case) {
            let mut other = operation.clone();
            other.metadata.description = format!("certificate other input: {case}");
            let live_target = if renewal {
                renewed.clone()
            } else {
                target.clone()
            };
            if renewal {
                other.parents = vec![base.0.clone()];
                other
                    .metadata
                    .attributes
                    .insert("musubi.work".to_owned(), world.fx.machine_key(0));
            }
            let mut live = original.clone();
            live.head_ids.insert(live_target.clone());
            live.wc_commit_ids
                .insert(key.clone().into(), live_target.clone());
            if case == "all dormant" {
                live.wc_commit_ids.remove(WorkspaceName::new(&key));
            }
            other.view_id = store.write_view(&live).unwrap();
            let other = store.write_operation(&other).unwrap();
            let mut proof = WorkspaceCertificate::default();
            proof.entry(key.clone()).remember_binding(live_target);
            if case == "renewed missing" {
                proof.clear_bindings();
            }
            proof.entry(key.clone()).authenticate_name();
            if case == "all dormant" {
                proof.entry(key.clone()).mark_dormant();
            }
            reference
                .workspace_certificates
                .insert(other.clone(), proof);
            output.parents.push(other.0);
        }
        if opaque_command {
            let maker = if case == "owner alias gone" { 0 } else { 1 };
            output.metadata.workspace_name =
                Some(format!("{}/default", world.fx.machine_key(maker)).into());
            let mut native = original.clone();
            native.wc_commit_ids.clear();
            let mut base = native.clone();
            if case == "foreign alias forgotten" {
                base.wc_commit_ids
                    .insert("alpha/default".into(), old.clone());
            }
            world.evidence.commands.insert(
                merge_key(&output),
                crate::world::CommandSnapshot {
                    id: OperationId::new(vec![42; 64]),
                    copy: world.fx.machine_key(maker),
                    copies: (0..world.nodes())
                        .map(|m| world.fx.machine_key(m))
                        .collect(),
                    parent: OperationId::new(vec![43; 64]),
                    input: Some(parent.clone()),
                    predecessors: None,
                    base,
                    made: native,
                },
            );
        }
        output.view_id = store.write_view(&made).unwrap();
        let result = store.write_operation(&output).unwrap();
        let certified = reference.workspace_certificate(&world, &result);
        if output.parents.len() == 1 {
            assert_eq!(
                certified.has_merge_birth(&key),
                ![
                    "missing",
                    "deleted",
                    "foreign name missing",
                    "owner alias gone"
                ]
                .contains(&case),
                "the name's independent birth survives payload changes: {case}"
            );
        }
        if case == "renewed" {
            assert!(
                certified.has_merge_birth(&key),
                "a forgotten branch cannot veto new live work"
            );
            assert_ne!(
                reference.facts(&old).change.clone(),
                reference.facts(&renewed).change.clone()
            );
        }
        assert_eq!(
            certified.binding(&key),
            ["unique", "merge", "omitted", "renewed"]
                .contains(&case)
                .then_some(&target),
            "{case}"
        );
    }
}

#[test]
fn native_merge_replay_requires_its_source_and_complete_shared_inputs() {
    use crate::world::{Naming, Setup};
    use witnesses::{RejectionCause, WitnessKind};

    fn run(observe: bool) -> (Vec<ChangeId>, String) {
        let mut world = World::new(Setup {
            nodes: 2,
            naming: Naming::Default,
            prejoin: false,
            secondary: false,
        });
        let base = world.fx.hive.members[0]
            .adapter
            .repo()
            .local_heads()
            .unwrap()[0]
            .0
            .hex();
        world.jj(
            0,
            &[
                "--ignore-working-copy",
                "--at-op",
                &base,
                "new",
                "--no-edit",
                "-m",
                "left",
            ],
        );
        world.jj(
            0,
            &[
                "--ignore-working-copy",
                "--at-op",
                &base,
                "new",
                "--no-edit",
                "-m",
                "right",
            ],
        );
        world.jj(0, &["status"]);
        world.converge();
        let node = world.fx.hive.members[0].adapter.repo();
        let store = node.canonical_store();
        let id = store
            .operation_ids()
            .unwrap()
            .into_iter()
            .find(|id| {
                let Some(local) = node.local_of(id) else {
                    return false;
                };
                let op = block_on(node.loader().op_store().read_operation(&local.0)).unwrap();
                op.parents.len() == 2
                    && !op
                        .metadata
                        .attributes
                        .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
            })
            .expect("the native command must reconcile the two heads");
        let op = store.read_operation(&id).unwrap();
        let parents = CanonicalOp::parents_of(&op);
        let views: HashMap<_, _> = store
            .operation_ids()
            .unwrap()
            .into_iter()
            .chain([store.root_operation_id().clone()])
            .map(|id| {
                let view = store.read_operation_view(&id).unwrap();
                (id, view)
            })
            .collect();
        let output = views[&id].clone();
        let before = world.observer_state();
        if !observe {
            return (world.next_actor_randomness(), world.fingerprint());
        }
        let mut reference = Reference::build(&world);
        let copies: Vec<_> = parents
            .iter()
            .map(|id| reference.workspace_copy(&world, id).unwrap())
            .collect();
        let known = reference.changes_of(copies.iter());
        assert!(
            reference
                .native_merge_matches(&world, &id, &parents, &output, &known, &views)
                .is_ok()
        );
        world.assert_observer_state(&before);
        let mut wrong = output.clone();
        wrong.local_bookmarks.insert(
            "invented".into(),
            RefTarget::normal(output.head_ids.iter().next().unwrap().clone()),
        );
        let rejected =
            reference.native_merge_matches(&world, &id, &parents, &wrong, &known, &views);
        assert!(rejected.is_err());
        let rejected = rejected.unwrap_err();
        assert!(
            rejected.contains(
                WitnessKind::NativeDag,
                &RejectionCause::StructuralResultDiffers
            ),
            "{rejected}"
        );
        let mut reversed = parents.clone();
        reversed.reverse();
        let rejected =
            reference.native_merge_matches(&world, &id, &reversed, &output, &known, &views);
        assert!(rejected.is_err());
        let rejected = rejected.unwrap_err();
        assert!(
            rejected.contains(
                WitnessKind::NativeDag,
                &RejectionCause::OrderedParentsDiffer
            ),
            "{rejected}"
        );
        let mut wrong_inputs = views.clone();
        wrong_inputs.get_mut(&parents[0]).unwrap().local_bookmarks = wrong.local_bookmarks;
        let rejected =
            reference.native_merge_matches(&world, &id, &parents, &output, &known, &wrong_inputs);
        assert!(rejected.is_err());
        let rejected = rejected.unwrap_err();
        assert!(
            rejected.contains(WitnessKind::NativeDag, &RejectionCause::SharedInputDiffers),
            "{rejected}"
        );
        let mut missing_workspace = views.clone();
        missing_workspace
            .get_mut(&parents[0])
            .unwrap()
            .wc_commit_ids
            .pop_first()
            .unwrap();
        let rejected = reference.native_merge_matches(
            &world,
            &id,
            &parents,
            &output,
            &known,
            &missing_workspace,
        );
        assert!(
            rejected.is_err(),
            "matching shared summaries cannot excuse different workspace bindings"
        );
        let rejected = rejected.unwrap_err();
        assert!(
            rejected.contains(
                WitnessKind::NativeDag,
                &RejectionCause::CertifiedInputBindingsDiffer
            ),
            "{rejected}"
        );
        world.assert_observer_state(&before);
        let result = (world.next_actor_randomness(), world.fingerprint());
        // Replacing the maker leaves only marked renderings of this operation. Those
        // cannot turn the product's output into independent native evidence.
        world.clone_copy(0);
        let rejected =
            reference.native_merge_matches(&world, &id, &parents, &output, &known, &views);
        assert!(rejected.is_err());
        let rejected = rejected.unwrap_err();
        assert!(
            rejected.contains(
                WitnessKind::NativeDag,
                &RejectionCause::RealizationIsNotMaker
            ),
            "{rejected}"
        );
        result
    }
    assert_eq!(run(false), run(true));
}

/// `jj op abandon` of the snapshot below a `jj commit` moves the commit's operation onto the
/// snapshot's parent, keeping its view, so the commit's new working copy follows no binding of
/// its new parent's. The operation's certificate still has the maker's working copies, as the
/// commit made them, so a native merge over it qualifies. Before, the merge was refused, its
/// base's workspace bindings uncertified. Where the merge itself can't qualify, an earlier
/// version of it on earlier versions of its parents, as a reparenting leaves, witnesses it; a
/// version on parents standing for no canonical parent, or for them in another order, or over a
/// base not below both, witnesses nothing.
#[test]
fn a_native_merge_qualifies_over_a_command_jj_op_abandon_reparented() {
    use crate::world::{Naming, Setup};
    use witnesses::{RejectionCause, WitnessKind};

    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.commit(0, 0, 1);
    let commit = OperationId::try_from_hex(world.latest_op_head(0)).unwrap();
    let snapshot = {
        let store = world.fx.node(0).loader().op_store().clone();
        block_on(store.read_operation(&commit)).unwrap().parents[0].hex()
    };
    world.op_abandon(0, &snapshot);
    let base = world.latest_op_head(0);
    for side in ["left", "right"] {
        world.jj(
            0,
            &[
                "--ignore-working-copy",
                "--at-op",
                &base,
                "new",
                "--no-edit",
                "-m",
                side,
            ],
        );
    }
    world.jj(0, &["status"]);
    world.converge();
    let node = world.fx.hive.members[0].adapter.repo();
    let store = node.canonical_store();
    let reparented = node
        .canonical_of(&musubi_jj::op_id::LocalOp(
            OperationId::try_from_hex(&base).unwrap(),
        ))
        .unwrap();
    let id = store
        .operation_ids()
        .unwrap()
        .into_iter()
        .find(|id| {
            let Some(local) = node.local_of(id) else {
                return false;
            };
            let op = block_on(node.loader().op_store().read_operation(&local.0)).unwrap();
            op.parents.len() == 2
                && !op
                    .metadata
                    .attributes
                    .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
        })
        .expect("the native command must reconcile the two heads");
    let op = store.read_operation(&id).unwrap();
    let parents = CanonicalOp::parents_of(&op);
    let views: HashMap<_, _> = store
        .operation_ids()
        .unwrap()
        .into_iter()
        .chain([store.root_operation_id().clone()])
        .map(|id| {
            let view = store.read_operation_view(&id).unwrap();
            (id, view)
        })
        .collect();
    let output = views[&id].clone();
    let mut reference = Reference::build(&world);
    let copies: Vec<_> = parents
        .iter()
        .map(|id| reference.workspace_copy(&world, id).unwrap())
        .collect();
    let known = reference.changes_of(copies.iter());
    let matched = reference.native_merge_matches(&world, &id, &parents, &output, &known, &views);
    assert!(matched.is_ok(), "{}", matched.unwrap_err());
    let own = format!("{}/", world.fx.machine_key(0));
    let certificate = reference.workspace_certificate(&world, &reparented);
    for (key, target) in &views[&reparented].wc_commit_ids {
        if key.as_str().starts_with(&own) {
            assert_eq!(certificate.binding(key.as_str()), Some(target), "{key:?}");
        }
    }

    // An earlier version of the merge, on earlier versions of its parents over the operation
    // below the reparented commit's, as a reparenting leaves them. It witnesses the merge where
    // the merge itself can't, here for a base whose checked bindings are made to differ.
    let ops = node.loader().op_store().clone();
    let read = |id: &OperationId| block_on(ops.read_operation(id)).unwrap();
    let write = |op: &op_store::Operation| block_on(ops.write_operation(op)).unwrap();
    let native = read(&node.local_of(&id).unwrap().0);
    let [left, right] = native.parents.clone().try_into().unwrap();
    let version_on = |parents: Vec<OperationId>| {
        let mut version = native.clone();
        version.parents = parents;
        write(&version)
    };
    let moved = |id: &OperationId, onto: &OperationId| {
        let mut op = read(id);
        op.parents = vec![onto.clone()];
        write(&op)
    };
    let below = read(&OperationId::try_from_hex(&base).unwrap()).parents[0].clone();
    version_on(vec![moved(&left, &below), moved(&right, &below)]);
    let mut unchecked = views.clone();
    unchecked
        .get_mut(&reparented)
        .unwrap()
        .wc_commit_ids
        .pop_first()
        .unwrap();
    let matched =
        reference.native_merge_matches(&world, &id, &parents, &output, &known, &unchecked);
    assert!(matched.is_ok(), "{}", matched.unwrap_err());

    // Versions on wrong parents, or over a base above the merge, are tried too once the merge
    // fails, here against a changed result, and are refused for those reasons.
    let unmapped = {
        let mut left = read(&left);
        left.metadata.description = "not the left parent".to_owned();
        write(&left)
    };
    let native_id = node.local_of(&id).unwrap().0;
    version_on(vec![right.clone(), left.clone()]);
    version_on(vec![unmapped, right.clone()]);
    version_on(vec![moved(&left, &native_id), moved(&right, &native_id)]);
    let mut wrong = output.clone();
    wrong.local_bookmarks.insert(
        "invented".into(),
        RefTarget::normal(output.head_ids.iter().next().unwrap().clone()),
    );
    let rejected = reference
        .native_merge_matches(&world, &id, &parents, &wrong, &known, &views)
        .unwrap_err();
    for cause in [
        RejectionCause::StructuralResultDiffers,
        RejectionCause::OrderedParentsDiffer,
        RejectionCause::ParentMappingMissing,
        RejectionCause::BaseNotShared,
    ] {
        assert!(
            rejected.contains(WitnessKind::NativeDag, &cause),
            "{rejected}"
        );
    }

    // Without a retained source that records the commit's own input, the maker's binding must
    // be the commit's base, as for any other command, and so is not certified.
    let key = merge_key(&store.read_operation(&reparented).unwrap());
    let own_key = format!("{}/{}", world.fx.machine_key(0), world.machine(0));
    assert!(
        views[&reparented]
            .wc_commit_ids
            .contains_key(WorkspaceName::new(&own_key))
    );
    let mut other_input = world.evidence.kept_operations[&key].clone();
    other_input.parent = Some(other_input.view.clone());
    for kept in [None, Some(other_input)] {
        match kept {
            None => world.evidence.kept_operations.remove(&key),
            Some(kept) => world.evidence.kept_operations.insert(key.clone(), kept),
        };
        let mut reference = Reference::build(&world);
        let certificate = reference.workspace_certificate(&world, &reparented);
        assert_eq!(certificate.binding(&own_key), None);
    }
}

#[test]
fn private_workspace_replay_merges_all_native_bases() {
    use crate::world::{Naming, Setup};

    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: true,
    });
    let baseline = CanonicalOp(world.fx.hive.hub.store().head().1.clone());
    let (left, right, first, second, final_merge, view) = {
        let store = world.fx.hive.members[0].adapter.repo().canonical_store();
        let mut op = store.read_operation(&baseline).unwrap();
        let view = store.read_view(&op.view_id).unwrap();
        op.metadata.attributes.clear();
        op.metadata.workspace_name = None;
        op.commit_predecessors = None;
        let mut write = |description: &str, parents: &[CanonicalOp]| {
            op.metadata.description = description.to_owned();
            op.parents = parents.iter().map(|id| id.0.clone()).collect();
            store.write_operation(&op).unwrap()
        };
        let left = write("private base left", std::slice::from_ref(&baseline));
        let right = write("private base right", std::slice::from_ref(&baseline));
        let first = write("private first merge", &[left.clone(), right.clone()]);
        let second = write("private second merge", &[right.clone(), left.clone()]);
        let final_merge = write("private final merge", &[first.clone(), second.clone()]);
        (left, right, first, second, final_merge, view)
    };
    for id in [&left, &right, &first, &second, &final_merge] {
        world.fx.node(0).realize(id).unwrap();
    }
    world.fx.node(0).advance(&final_merge).unwrap();
    world.sync(0);
    world.sync(1);
    let native_id = world.fx.hive.members[0]
        .adapter
        .repo()
        .local_of(&final_merge)
        .unwrap();
    world.crash(0, true, 0);
    let node = world.fx.hive.members[0].adapter.repo();
    let native = block_on(node.loader().load_operation(&native_id.0)).unwrap();
    let parents = block_on(native.parents()).unwrap();
    let bases = block_on(jj_lib::op_walk::closest_common_ancestors(
        vec![parents[0].clone()],
        [parents[1].clone()],
    ))
    .unwrap();
    assert_eq!(bases.len(), 2, "the native fixture must be criss-cross");
    let mut reference = Reference::build(&world);
    let certificate = reference.workspace_certificate(&world, &baseline);
    for id in [&left, &right, &first, &second] {
        reference
            .workspace_certificates
            .insert(id.clone(), certificate.clone());
    }
    let replays = reference.workspace_private_replays(
        &world,
        &final_merge,
        &[
            CertifiedParent {
                canonical: &first,
                certificate: &certificate,
            },
            CertifiedParent {
                canonical: &second,
                certificate: &certificate,
            },
        ],
    );
    let replay = replays
        .iter()
        .find(|r| r.private.as_ref().unwrap().0 == world.fx.machine_key(0))
        .expect("native private replay must merge both bases");
    assert_eq!(replay.parents.len(), 2);
    assert_eq!(replay.view.wc_commit_ids, view.wc_commit_ids);
    // An optional base may be clear itself while its source ancestry reaches an active
    // conclusion. Refusing that candidate must not cache an empty substitute proof.
    reference.workspace_certificates.clear();
    reference.workspace_in_progress.insert(baseline.clone());
    assert!(!reference.workspace_dependencies_available(&world, std::slice::from_ref(&first)));
    assert!(reference.workspace_certificates.is_empty());
    assert_eq!(
        reference.workspace_in_progress,
        HashSet::from([baseline.clone()])
    );
    reference.workspace_in_progress.clear();
    assert!(reference.workspace_dependencies_available(&world, std::slice::from_ref(&first)));
    // A completed certificate is an independent proof barrier, even during a later proof.
    reference
        .workspace_certificates
        .insert(baseline.clone(), WorkspaceCertificate::default());
    reference.workspace_in_progress.insert(baseline);
    assert!(reference.workspace_dependencies_available(&world, std::slice::from_ref(&first)));
    // Captured command inputs are required proof edges too. An internal cycle must
    // refuse the optional witness even when no outer certificate is active.
    reference.workspace_certificates.clear();
    reference.workspace_in_progress.clear();
    let op = world.fx.hive.members[0]
        .adapter
        .repo()
        .canonical_store()
        .read_operation(&first)
        .unwrap();
    world.evidence.commands.insert(
        merge_key(&op),
        crate::world::CommandSnapshot {
            id: OperationId::new(vec![42; 64]),
            copy: world.fx.machine_key(0),
            copies: (0..world.nodes())
                .map(|m| world.fx.machine_key(m))
                .collect(),
            parent: OperationId::new(vec![43; 64]),
            input: Some(first.clone()),
            predecessors: None,
            base: view.clone(),
            made: view,
        },
    );
    assert!(!reference.workspace_dependencies_available(&world, std::slice::from_ref(&first)));
    assert!(reference.workspace_certificates.is_empty());
    assert!(reference.workspace_in_progress.is_empty());
}

#[test]
fn a_native_serial_merge_can_repeat_a_rebase_after_abandon() {
    let env = musubi_testutil::TestEnv::new();
    // No Git working tree or branch import: this is unrelated to the snapshot/import
    // divergence when Git points a branch at an unsnapshotted working copy (#41).
    let repo = env.init_non_colocated_repo("native");
    let op = || {
        repo.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n",
            "1",
            "-T",
            "id",
        ])
        .trim()
        .to_owned()
    };
    let commit = || {
        CommitId::try_from_hex(
            repo.jj(&[
                "--ignore-working-copy",
                "log",
                "--no-graph",
                "-r",
                "@",
                "-T",
                "commit_id",
            ])
            .trim(),
        )
        .unwrap()
    };
    repo.jj(&["describe", "-m", "parent"]);
    let parent = commit();
    let base = op();
    repo.jj(&["new", "-m", "child"]);
    let original = commit();
    let left = op();
    repo.jj(&[
        "--at-op",
        &base,
        "describe",
        &parent.hex(),
        "-m",
        "rewritten parent",
    ]);
    repo.jj(&["status"]);
    let first = commit();
    let first_merge = op();

    // The retained merge keeps its result after its child-creation parent disappears.
    // A delayed command still has the old operation: native jj integrates that history.
    repo.jj(&["op", "abandon", &left]);
    repo.jj(&[
        "--at-op",
        &left,
        "bookmark",
        "create",
        "delayed",
        "-r",
        &original.hex(),
    ]);
    repo.jj(&["status"]);
    let serial_merge = op();
    let visible: Vec<_> = repo
        .jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            "description(substring:\"child\")",
            "-T",
            "commit_id ++ \"\\n\"",
        ])
        .lines()
        .map(|id| CommitId::try_from_hex(id).unwrap())
        .collect();
    assert_eq!(
        visible.len(),
        2,
        "notice when jj no longer makes this divergence"
    );
    let second = visible.iter().find(|id| **id != first).unwrap().clone();

    let loader = RepoLoader::init_from_file_system(
        &repo.settings(),
        &repo.repo_path(),
        &default_backend_factories(),
    )
    .unwrap();
    let load = |id: &str| {
        block_on(loader.load_operation(&OperationId::try_from_hex(id).unwrap())).unwrap()
    };
    let first_op = load(&first_merge);
    let serial_op = load(&serial_merge);
    let event = |op: &Operation, new: &CommitId| {
        let native_inputs = block_on(op.parents())
            .unwrap()
            .iter()
            .flat_map(|parent| {
                block_on(parent.view())
                    .unwrap()
                    .store_view()
                    .head_ids
                    .clone()
            })
            .collect();
        MergeRewrite {
            operation: op.id().clone(),
            new: new.clone(),
            predecessors: op.store_operation().commit_predecessors.as_ref().unwrap()[new].clone(),
            native_inputs: Arc::new(native_inputs),
        }
    };
    let mut events = vec![event(&first_op, &first), event(&serial_op, &second)];
    assert_eq!(events[0].predecessors, std::slice::from_ref(&original));
    assert_eq!(events[1].predecessors, std::slice::from_ref(&original));
    assert!(events[1].native_inputs.contains(&first));
    assert!(!events[0].native_inputs.contains(&second));

    // A second independent native merge of the first inputs is still the forbidden
    // duplicate. It has neither result in its inputs, even beside the serial pair.
    let (independent, rebased) = block_on(loader.merge_operations(
        block_on(first_op.parents()).unwrap(),
        None,
        Some("independent merge"),
        [],
    ))
    .unwrap();
    assert_eq!(rebased, 1);
    let duplicate = independent
        .operation()
        .store_operation()
        .commit_predecessors
        .as_ref()
        .unwrap()
        .iter()
        .find(|(_, predecessors)| *predecessors == &vec![original.clone()])
        .unwrap()
        .0
        .clone();
    assert_ne!(duplicate, first);
    assert_ne!(duplicate, second);
    let expected = loader.store().get_commit(&first).unwrap();
    for id in [&second, &duplicate] {
        let actual = loader.store().get_commit(id).unwrap();
        assert_eq!(actual.change_id(), expected.change_id());
        assert_eq!(actual.parent_ids(), expected.parent_ids());
        assert_eq!(actual.tree_ids(), expected.tree_ids());
        assert_eq!(actual.description(), expected.description());
        assert_eq!(actual.author(), expected.author());
    }
    let keys = HashMap::from([
        (first.clone(), 0),
        (second.clone(), 0),
        (duplicate.clone(), 0),
    ]);

    // In this native result, both children have structural key 0 and their common
    // parent has key 1. Its only shared reference is the delayed bookmark at a child.
    let native_refs = refs(block_on(serial_op.view()).unwrap().store_view());
    assert_eq!(native_refs.len(), 1);
    let (name, target) = native_refs.into_iter().next().unwrap();
    assert!(visible.contains(target.as_normal().unwrap()));
    let shared = Summary {
        visible: BTreeMap::from([(0, visible.len()), (1, 1)]),
        refs: BTreeMap::from([(name, (vec![Some(0)], vec![]))]),
    };
    let certify = |replayed: &Summary, relation: Option<&[CommitId]>| {
        native_rebase_matches(
            (&shared, replayed),
            keys[&second],
            &events[1].predecessors,
            relation
                .into_iter()
                .map(|predecessors| (keys[&second], predecessors)),
        )
    };
    let native_relation = events[1].predecessors.as_slice();
    assert!(certify(&shared, Some(native_relation)));
    assert!(events[1].native_inputs.contains(&first));
    assert!(
        !certify(&shared, Some(std::slice::from_ref(&parent))),
        "a matching child with a different native predecessor cannot be certified"
    );
    assert!(
        !certify(&shared, None),
        "missing native predecessor evidence cannot be certified"
    );
    for changed in [
        Summary {
            visible: BTreeMap::from([(0, 1), (1, 1)]),
            refs: shared.refs.clone(),
        },
        Summary {
            visible: shared.visible.clone(),
            refs: BTreeMap::new(),
        },
    ] {
        assert!(
            !certify(&changed, Some(native_relation)),
            "a changed shared result cannot be certified even with the earlier result in the inputs"
        );
    }

    assert!(!repeated_rebase(&events, &keys));
    events.reverse();
    assert!(
        !repeated_rebase(&events, &keys),
        "collection order does not grant evidence"
    );
    events[0].native_inputs = Arc::default();
    assert!(
        repeated_rebase(&events, &keys),
        "missing native evidence must not forgive"
    );
    events[0] = event(&serial_op, &second);
    events.push(event(independent.operation(), &duplicate));
    assert!(
        repeated_rebase(&events, &keys),
        "independent merges remain forbidden"
    );

    repo.jj(&["abandon", &second.hex()]);
    let remaining = repo.jj(&[
        "--ignore-working-copy",
        "log",
        "--no-graph",
        "-r",
        "description(substring:\"child\")",
        "-T",
        "commit_id ++ \"\\n\"",
    ]);
    assert_eq!(remaining.trim(), first.hex());
}
