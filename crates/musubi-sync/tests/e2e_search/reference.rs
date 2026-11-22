//! The reference that divergence and bookmark and tag conflicts are judged against: the
//! hive's history rebuilt in one jj repository, in which every merge is jj's own.
//!
//! The hub's canonical history is a graph of operations: each machine's commands (and the
//! operations musubi writes for it, such as a forget), and the merges that nodes and `jj`
//! commands made of concurrent ones. The reference takes the same operations, with the same
//! parents, into one jj repository. An operation with one parent is taken as it is, its view
//! the canonical one, while the reference agrees with the hive at its parent. A merge is jj's
//! own merge of the same parents, in the same order, by `RepoLoader::merge_operations`, as
//! concurrent processes on one machine would have it merged.
//!
//! Where jj's merge gives what the hive's did, the reference takes the hive's operation
//! itself, so that it goes on agreeing exactly. Where it doesn't, the reference records a
//! deviation. A merge can differ from jj's for reasons that aren't musubi's, such as a machine
//! that merged its parents without another machine's workspace it forgot
//! (docs/internals/races.md, "Known jj limitations"); the reference doesn't try to prove such a
//! merge jj's own, and fails it only for what it does beyond jj's merge of the same parents.
//! Where no other line has parted, it then goes on from the hive's merge, so that the merges
//! after it are judged against jj's too. Otherwise, as after an operation of one parent that
//! jj applies differently, the reference goes its own way: each later operation of one parent
//! is applied to the reference's parent as jj applies a concurrent operation, three-way
//! against the hive's parent, and each later merge merges the reference's operations, until an
//! operation brings the two back into agreement, and every later operation descending from
//! where they parted descends from it too. Agreement compares
//! visible commits, bookmarks, tags and remote bookmarks, commits by their contents, change ids
//! and parents rather than their ids, since a commit a merge rebases records when it was made,
//! and without the author's time where jj resets it; a commit of a change new to the
//! operation, like the empty working-copy commit jj makes for an abandoned one, by all but its
//! change id. Workspaces aren't compared: which workspaces a view has is musubi's
//! (docs/internals/design.md, "Copies that go away").
//!
//! Divergence or a conflict that the hive has beyond the reference is musubi's: at its head,
//! and at any merge whose parents the two agree on. So that the hive's history can stand for
//! one repository's, every machine's realization of each operation must have the hive's view of
//! it, and no operation but a merge may make anything diverge or conflict unless what it did
//! explains it (`explained`).
//!
//! [`Reference::build`] walks that history. `adjudication` checks each operation against its
//! recorded source and compares the replay with the hive; `comparison` holds structural
//! equality and what one view has beyond another; `replay` holds jj's merge and application of
//! operations; `rewrites` finds independent merges that did the same rebase twice, telling
//! them from jj's own repeat of a rebase after `jj op abandon`, which jj's merge of the same
//! parents makes too.

mod adjudication;
mod comparison;
mod replay;
mod rewrites;

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Write as _;
use std::fs;
use std::process::Command;
use std::sync::Arc;

use futures::executor::block_on;
use jj_lib::backend::CommitId;
use jj_lib::backend::MillisSinceEpoch;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::config::StackedConfig;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::operation::Operation;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::repo::RepoLoader;
use jj_lib::settings::UserSettings;
use jj_lib::workspace::Workspace;
use musubi_jj::op_id::CanonicalOp;
use tempfile::TempDir;

use crate::identity::NativeOperation;
use crate::world::World;
use adjudication::{HistoryEntry, ReplayHistory};
use comparison::Facts;
use comparison::refs;
use rewrites::MergeRewrite;
pub use rewrites::RebaseTwice;

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
    /// first, for failure messages (`deviation_report`).
    deviations: Vec<String>,
    /// Every rewrite the hive's merges record: the merge, the new commit, and its
    /// predecessors.
    rewrites: Vec<MergeRewrite>,
    /// For each merge the reference replayed, the changes jj's own merge of its parents left
    /// with two alike commits (`alike_changes`).
    jj_alike: HashMap<OperationId, BTreeSet<String>>,
    /// Operations other than merges that made a change diverge or a bookmark or tag
    /// conflict, where nothing the operation did explains it (`explained`), and merges that
    /// did more of either than jj's merge of the same parents.
    pub unexplained: Vec<String>,
    /// The hive's history, but for the root.
    history: Vec<CanonicalOp>,
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
    /// absent from the canonical history, which machine 0 never fetched.
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
            jj_alike: HashMap::new(),
            unexplained: vec![],
            history: order.iter().map(|(.., id)| id.clone()).collect(),
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
            let replay = reference.replay_operation(&entry, &copy, &mut history);
            history.record(entry, copy, replay);
        }
        (reference.head_copy, reference.head_replay) = history.heads(&head);
        reference
    }

    /// Where jj's merges differed from the hive's, oldest first, for a failure message. A
    /// merge can differ for a reason that isn't musubi's, such as a machine merging without a
    /// workspace it forgot; what fails is only what the hive has beyond jj's merge.
    pub fn deviation_report(&self) -> String {
        if self.deviations.is_empty() {
            return "jj's merges agree with the hive's everywhere".to_owned();
        }
        let mut report = "where jj's merges differ from the hive's, oldest first:".to_owned();
        for deviation in &self.deviations {
            write!(report, "\n- {deviation}").unwrap();
        }
        report
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
