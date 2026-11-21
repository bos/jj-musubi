//! The world a generated sequence acts on: a hive of real colocated repositories sharing a
//! bare `origin`, plus what the test remembers about them, and every action a rule can
//! take. Every action is something a user, git, a remote, or the musubi daemon can do.
//!
//! The implementations follow their roles: `commands` runs user actions, `sync` runs daemon
//! and network actions, and `copies` handles membership. `observations` reads actor state;
//! `evidence` captures native inputs before later actions can rewrite them; `history` tracks
//! identity across abandonment; `recovery` follows supported refusals. The property assertions
//! live in `checks`, `imports` and `reference`. Tests here pin the independence of their
//! evidence and the behavior of the actors they judge.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_jj::node::NodeError;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_sync::OpId;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

use crate::fixture::Fixture;
use crate::identity::HistoryKey;
use crate::identity::MERGE_KEY_TEMPLATE;
use crate::identity::OP_KEY_TEMPLATE;
use crate::identity::SourceHeader;
use crate::identity::SourceKey;
use crate::imports::Imports;
use crate::ledger::Ledger;
use crate::ledger::Seen;
use crate::origin::Origin;
use crate::view::View;

mod commands;
mod copies;
mod evidence;
mod history;
mod observations;
mod recovery;
mod sync;

use self::evidence::NativeEvidence;

/// Machine directories. Their hostnames are the same, unless the setup shares one.
pub const MACHINES: [&str; 4] = ["alpha", "beta", "gamma", "delta"];
/// How many machines a search's hive grows to: the fourth is for the dropped merge's setup
/// only (`World::hold_dropped_merge`).
pub const SEARCH_MACHINES: usize = 3;
/// Small pools, so that machines collide on names.
pub const BOOKMARKS: [&str; 3] = ["main", "feature", "topic"];
pub const TAGS: [&str; 2] = ["v1", "v2"];
pub const WORKSPACES: [&str; 4] = ["default", "work", "second", "third"];
/// What the trace says when jj fails with its known duplicate-commit bug (races.md, "Known
/// jj limitations") and the world runs the command again.
pub const JJ_DUPLICATE_COMMIT_BUG: &str = "jj hit its known duplicate-commit bug";
/// Shared files, so that rebases and merges produce content conflicts.
pub const FILES: [&str; 3] = ["a.txt", "b.txt", "dir/c.txt"];

/// A read-only observation also preserves the command seeds its native probes took.
#[derive(Debug, PartialEq, Eq)]
struct StaleObservation {
    stale: bool,
    command_seeds: u64,
}

/// The native head before joining: the fixture has not introduced concurrency yet.
fn native_head(repo: &TestRepo) -> OpId {
    let heads: Vec<_> = fs::read_dir(repo.repo_path().join("op_heads/heads"))
        .unwrap()
        .map(|entry| entry.unwrap().file_name())
        .collect();
    assert_eq!(heads.len(), 1);
    OpId::try_from_hex(heads[0].to_str().unwrap()).unwrap()
}

/// A native abandon changes an operation's parents but preserves the rest of its identity.
fn join_fingerprint(op: &jj_lib::op_store::Operation) -> OpId {
    let mut op = op.clone();
    op.parents.clear();
    OpId::new(jj_lib::content_hash::blake2b_hash(&op).to_vec())
}

/// The one id of `ids`, if it has exactly one.
fn single(ids: Option<&BTreeSet<String>>) -> Option<&String> {
    match ids.map(|ids| ids.iter().collect::<Vec<_>>()).as_deref() {
        Some([id]) => Some(id),
        _ => None,
    }
}

/// An operation's key, as `MERGE_KEY_TEMPLATE` gives it.
pub fn merge_key(op: &jj_lib::op_store::Operation) -> SourceKey {
    SourceKey::of(op)
}

/// Reparenting preserves the source body; local identity and ownership annotations may
/// be added afterward. In particular its view and workspace identity are never stripped.
pub fn same_source_body(a: &jj_lib::op_store::Operation, b: &jj_lib::op_store::Operation) -> bool {
    let strip = |mut op: jj_lib::op_store::Operation| {
        op.parents.clear();
        for key in [
            musubi_jj::node::CANONICAL_ATTRIBUTE,
            "musubi.workspace-context",
            "musubi.local-workspaces",
        ] {
            op.metadata.attributes.remove(key);
        }
        op
    };
    strip(a.clone()) == strip(b.clone())
}

#[derive(Clone, Copy, Debug)]
pub enum Naming {
    /// Each machine names its workspace after itself.
    Own,
    /// Every machine keeps `default`.
    Default,
    /// Every machine has the same hostname, and keeps `default`.
    SharedHostname,
}

#[derive(Clone, Copy, Debug)]
pub struct Setup {
    pub nodes: usize,
    pub naming: Naming,
    /// Each repository has history of its own, with a `main` bookmark, before joining.
    pub prejoin: bool,
    /// Each machine has a secondary workspace, `second`, from the start.
    pub secondary: bool,
}

pub struct AbandonedOperation {
    pub by: usize,
    pub key: HistoryKey,
    pub merge: SourceKey,
    native: OpId,
    copy: String,
    /// Whether this command could already denote a shared operation. A private command
    /// removed before publication does not forbid later versions with different parents.
    shared: bool,
    /// Copy-qualified native versions kept by an abandon or introduced by a later native
    /// command from a history where that version was absent. Only exact native parent
    /// rewrites extend these witnesses. First learned identities stay fixed; sync adds none.
    native_witnesses: BTreeMap<(String, OpId), Option<OpId>>,
    header: SourceHeader,
    /// The immutable identity known before the native abandon. Different native
    /// reparentings can share metadata while naming different original operations.
    pub originals: Option<BTreeSet<OpId>>,
}

impl AbandonedOperation {
    fn qualify_native(&mut self, id: &(String, OpId), original: OpId) {
        let known = self
            .native_witnesses
            .get_mut(id)
            .expect("a frozen native survivor");
        if let Some(previous) = known {
            assert_eq!(
                *previous, original,
                "an immutable native survivor changed original identity"
            );
        } else {
            *known = Some(original);
        }
    }
}

#[derive(Default)]
pub(crate) struct OperationHistory {
    copy: Option<String>,
    native: BTreeSet<OpId>,
    native_by_header: BTreeMap<SourceHeader, BTreeSet<OpId>>,
    native_originals: BTreeMap<OpId, OpId>,
    headers: BTreeSet<SourceHeader>,
    originals: BTreeSet<OpId>,
    originals_by_header: BTreeMap<SourceHeader, BTreeSet<OpId>>,
    unknown: BTreeSet<SourceHeader>,
}

impl OperationHistory {
    pub(crate) fn may_contain(&self, op: &AbandonedOperation) -> bool {
        match &op.originals {
            Some(_) => self.proves_present(op) || self.unknown.contains(&op.header),
            None => {
                self.has_native_source(op)
                    || (self.headers.contains(&op.header)
                        && (self.unknown.contains(&op.header)
                            || self.originals_by_header.get(&op.header).is_none_or(|ids| {
                                ids.iter().any(|id| {
                                    !op.native_witnesses
                                        .values()
                                        .any(|known| known.as_ref() == Some(id))
                                })
                            })))
            }
        }
    }

    pub(crate) fn explain(&self, op: &AbandonedOperation) -> String {
        format!(
            "wanted originals={:?}, wanted native={}, retained native={}, matching originals={:?}, unknown matching metadata={}",
            op.originals,
            op.native.hex(),
            self.has_native_source(op),
            self.originals
                .iter()
                .filter(|id| op
                    .originals
                    .as_ref()
                    .is_some_and(|wanted| wanted.contains(*id)))
                .collect::<Vec<_>>(),
            self.unknown.contains(&op.header)
        )
    }

    fn has_native_source(&self, op: &AbandonedOperation) -> bool {
        self.copy.as_deref() == Some(op.copy.as_str()) && self.native.contains(&op.native)
    }

    fn proves_present(&self, op: &AbandonedOperation) -> bool {
        self.has_native_source(op)
            || op
                .originals
                .as_ref()
                .is_some_and(|ids| ids.iter().any(|id| self.originals.contains(id)))
    }
}

fn operation_header(op: &jj_lib::op_store::Operation) -> SourceHeader {
    SourceHeader::of(op)
}

pub struct Workspace {
    pub name: String,
    /// `None` for the repository's own directory.
    pub path: Option<PathBuf>,
    /// Files were written in it since a recorded `jj` command last ran there, so the next
    /// one there snapshots them.
    pub edited: bool,
}

/// An operation a rule may act on, printed by what it did and how far back it is, which are
/// the same from one run of a case to the next, and by id, which is not: jj records each
/// command's arguments in its operation, temporary paths and all.
#[derive(Clone)]
pub struct PastOp {
    pub id: String,
    /// The first line of the operation's description.
    pub description: String,
    /// How many operations before the machine's head it is.
    pub back: usize,
}

/// An operation a full trim to the root left on a machine, from before the node handled the
/// trim, or a late command or merge written on one: jj can still load it by its id, though no
/// op head reaches it (`World::late_ops`).
#[derive(Clone)]
pub struct LateOp {
    pub id: String,
    /// The first line of the operation's description.
    pub description: String,
    /// How many full trims the machine had made when it was written.
    pub trim: usize,
    /// Whether it has more than one parent.
    pub merge: bool,
}

impl std::fmt::Debug for LateOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let merge = if self.merge { ", a merge" } else { "" };
        write!(
            f,
            "{:?}, after trim {}{merge} (op {})",
            self.description,
            self.trim,
            &self.id[..12]
        )
    }
}

impl std::fmt::Debug for PastOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?}, {} back (op {})",
            self.description,
            self.back,
            &self.id[..12]
        )
    }
}

/// What an actual jj command read and wrote, before canonicalization or abandonment can
/// expand its parent. This is independent source evidence for the reference replay.
#[derive(Clone)]
pub struct CommandSnapshot {
    /// The native operation, before contraction or a per-machine export changes it.
    pub id: jj_lib::op_store::OperationId,
    pub copy: String,
    pub copies: BTreeSet<String>,
    pub parent: jj_lib::op_store::OperationId,
    pub input: Option<CanonicalOp>,
    pub predecessors: Option<BTreeMap<CommitId, Vec<CommitId>>>,
    pub base: jj_lib::op_store::View,
    pub made: jj_lib::op_store::View,
}

/// Native source capture includes failed invocations; only successful ones qualify for
/// race coverage. This never controls the reference oracle's evidence capture.
#[derive(Clone, Copy)]
pub(super) enum CommandOutcome {
    Succeeded,
    Failed,
}

/// How many recovery commands a sequence may make before a repeated refusal is a finding.
const MAX_RECOVERIES: usize = 10;

/// An operation observed before replication can reparent it, independently of the eventual
/// canonical view. Its source view remains the oracle for a later contraction's survivor.
struct OperationSource {
    operation: jj_lib::op_store::Operation,
    retained: RetainedOperation,
}

/// Independent source data for a native operation whose parents later change.
#[derive(Clone)]
pub struct RetainedOperation {
    pub copy: String,
    pub native: bool,
    pub view: jj_lib::op_store::View,
    pub realized: bool,
    /// The original input, when the operation had one parent.
    pub parent: Option<jj_lib::op_store::View>,
}

impl RetainedOperation {
    fn capture(
        copy: String,
        op: &jj_lib::op_store::Operation,
        view: jj_lib::op_store::View,
        realized: bool,
        parent: Option<jj_lib::op_store::View>,
    ) -> Self {
        Self {
            copy,
            native: !op
                .metadata
                .attributes
                .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE),
            view,
            realized,
            parent,
        }
    }
}

#[test]
fn retained_sources_do_not_infer_native_ownership_from_a_shared_hostname() {
    use jj_lib::op_store::{Operation, View as RawView, ViewId};
    use jj_lib::ref_name::WorkspaceNameBuf;

    let view = RawView::make_root(CommitId::new(vec![1; 20]));
    let parent = RawView::make_root(CommitId::new(vec![2; 20]));
    for copy in ["mac#first", "mac#second"] {
        for workspace in [None, Some(WorkspaceNameBuf::from("default"))] {
            for marker in [None, Some("invalid-id"), Some("abcd")] {
                let mut op = Operation::make_root(ViewId::new(vec![0; 64]));
                op.metadata.hostname = "mac".to_owned();
                op.metadata.workspace_name = workspace.clone();
                // Neither a shared hostname nor another copy's work marker owns the input.
                op.metadata.attributes.insert(
                    musubi_jj::presence::WORK_ATTRIBUTE.to_owned(),
                    "mac#other".to_owned(),
                );
                if let Some(marker) = marker {
                    op.metadata.attributes.insert(
                        musubi_jj::node::CANONICAL_ATTRIBUTE.to_owned(),
                        marker.to_owned(),
                    );
                }
                let source = RetainedOperation::capture(
                    copy.to_owned(),
                    &op,
                    view.clone(),
                    false,
                    Some(parent.clone()),
                );
                assert_eq!(
                    source.native,
                    marker.is_none(),
                    "{copy}, {workspace:?}, {marker:?}"
                );
                assert_eq!(source.copy, copy);
                assert_eq!(source.view, view);
                assert_eq!(source.parent, Some(parent.clone()));
                assert!(!source.realized);
            }
        }
    }
}

/// Why a published carrier may preserve an independently observed Git frontier.
#[derive(Debug, PartialEq, Eq)]
enum GitRecordAuthorization {
    RootTransition,
    /// The carrier must retain one of these independently witnessed private names.
    PrivateWorkspaces(BTreeSet<String>),
}

struct GitRecordInput {
    copy: String,
    target: OpId,
    heads: Vec<OpId>,
    before: BTreeSet<OpId>,
    authorization: GitRecordAuthorization,
}

#[derive(Default)]
struct NativeOrigins {
    copy: String,
    seen: BTreeSet<OpId>,
    pending: BTreeMap<OpId, (jj_lib::op_store::Operation, jj_lib::op_store::View)>,
    known: BTreeMap<OpId, Vec<NativeOrigin>>,
}

struct NativeOrigin {
    header: SourceHeader,
    view: jj_lib::op_store::View,
}

fn shared_origin_view(mut view: jj_lib::op_store::View) -> jj_lib::op_store::View {
    view.wc_commit_ids.clear();
    view.git_refs.clear();
    view.git_heads.clear();
    view.remote_views
        .remove(jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO);
    view
}

struct WorkspaceTrim {
    copy: String,
    input: CanonicalOp,
    wrote_fixup: bool,
    seen: BTreeSet<jj_lib::op_store::OperationId>,
    before: BTreeSet<SourceKey>,
}

pub struct World {
    pub fx: Fixture,
    pub origin: Origin,
    /// Native inputs and identity witnesses, captured independently of the resulting hive.
    pub evidence: NativeEvidence,
    naming: Naming,
    /// Machines with file edits that no `jj` command has snapshotted yet.
    dirty: Vec<bool>,
    /// Each machine's workspaces; the first is the primary.
    pub workspaces: Vec<Vec<Workspace>>,
    /// Logical names with a live independent merge witness, without physical directories.
    pub logical_extras: Vec<BTreeSet<String>>,
    /// The key of each operation a `jj op abandon` dropped, with the machine that ran it and
    /// its `merge_key`: none comes back, unless jj brings it back there.
    pub abandoned: Vec<AbandonedOperation>,
    /// The key of every copy a machine forgot, with the forget's `merge_key`, until the hub's
    /// history has the forget and shows the copy again, by work it did since: an abandon can
    /// drop the forget from the history, but not its effect (docs/internals/design.md,
    /// "Presence through an abandon").
    forgot: BTreeMap<String, SourceKey>,
    /// What each machine saw at its op heads, when it last looked.
    seen: Vec<Option<(Vec<String>, Seen)>>,
    pub ledger: Ledger,
    /// What the no-spurious-revert check knows of each machine (`imports`).
    pub imports: Imports,
    /// Machines whose repository changed in ways no recorded command has loaded since.
    pub touched: BTreeSet<usize>,
    /// Recovery commands run so far after a supported refusal.
    recovery_actions: usize,
    /// Those operations, and the ones reverting them wrote, which reverting again would
    /// only undo the recovery: hex ids.
    recovery_ops: BTreeSet<String>,
    integrated_history: BTreeSet<(String, String)>,
    /// The change of every commit seen so far, for `fingerprint`.
    change_of: BTreeMap<String, String>,
    /// Whether the hub has restarted since it last pruned, for coverage.
    restarted_since_prune: bool,
    /// Per machine, newest first, the operations its full trims to the root left, and the
    /// late commands and merges written on them: a command can still run `--at-op` any of
    /// them (`World::late_ops`).
    late_ops: Vec<Vec<LateOp>>,
    /// Per machine, how many full trims to the root it has made.
    trims: Vec<usize>,
    /// The late operations written with the clock stepped back, each at a time of its own.
    stepped_back: BTreeSet<String>,
    counter: usize,
    pub trace: Vec<String>,
}

impl World {
    pub fn new(setup: Setup) -> Self {
        let env = TestEnv::new();
        let mut origin = Origin::new(env.root());
        origin.advance();
        let machines = &MACHINES[..setup.nodes];
        let repos: Vec<TestRepo> = machines
            .iter()
            .map(|machine| {
                let repo = match setup.naming {
                    Naming::Own => env.init_repo(machine),
                    Naming::Default => env.init_repo_with_workspace(machine, "default"),
                    Naming::SharedHostname => env.init_repo_with_hostname(machine, "mac"),
                };
                repo.jj(&[
                    "git",
                    "remote",
                    "add",
                    "origin",
                    origin.bare.to_str().unwrap(),
                ]);
                if setup.prejoin {
                    repo.write_file("pre", machine);
                    repo.jj(&["commit", "-m", &format!("pre-join work on {machine}")]);
                    repo.jj(&["bookmark", "create", "main", "-r", "@-"]);
                }
                repo
            })
            .collect();
        let primary = |machine: &str| match setup.naming {
            Naming::Own => machine.to_owned(),
            Naming::Default | Naming::SharedHostname => "default".to_owned(),
        };
        let workspaces: Vec<Vec<Workspace>> = machines
            .iter()
            .zip(&repos)
            .map(|(machine, repo)| {
                let mut workspaces = vec![Workspace {
                    name: primary(machine),
                    path: None,
                    edited: false,
                }];
                if setup.secondary {
                    let path = env.root().join(format!("{machine}-second"));
                    repo.jj(&[
                        "workspace",
                        "add",
                        "--name",
                        "second",
                        path.to_str().unwrap(),
                    ]);
                    workspaces.push(Workspace {
                        name: "second".to_owned(),
                        path: Some(path),
                        edited: false,
                    });
                }
                workspaces
            })
            .collect();
        let join_inputs: Vec<_> = repos.iter().map(native_head).collect();
        let fx = Fixture::join(env, repos);
        let join_points = join_inputs
            .iter()
            .zip(&fx.hive.members)
            .map(|(head, member)| {
                let store = member.adapter.repo().loader().op_store();
                let op = futures::executor::block_on(store.read_operation(head)).unwrap();
                join_fingerprint(&op)
            })
            .collect();
        let workspace_births: BTreeSet<String> = workspaces
            .iter()
            .enumerate()
            .flat_map(|(m, workspaces)| {
                workspaces
                    .iter()
                    .map(|ws| format!("{}/{}", fx.machine_key(m), ws.name))
                    .collect::<Vec<_>>()
            })
            .collect();
        let mut world = Self {
            logical_extras: vec![BTreeSet::new(); setup.nodes],
            evidence: NativeEvidence {
                initial_workspace_keys: workspace_births.clone(),
                workspace_births,
                baseline_ids: vec![],
                baseline_keys: vec![],
                join_points,
                join_inputs,
                hive_baseline: BTreeSet::new(),
                baseline_merge_keys: BTreeSet::new(),
                kept_operations: BTreeMap::new(),
                operation_sources: BTreeMap::new(),
                operation_seen: vec![],
                native_origins: vec![],
                published_seen: BTreeSet::new(),
                published_headers: BTreeSet::new(),
                commands: BTreeMap::new(),
                workspace_trim_inputs: BTreeMap::new(),
                workspace_fixup_inputs: BTreeMap::new(),
                workspace_joins: BTreeMap::new(),
                command_sources: BTreeMap::new(),
            },
            fx,
            origin,
            naming: setup.naming,
            dirty: vec![false; setup.nodes],
            workspaces,
            abandoned: vec![],
            forgot: BTreeMap::new(),
            seen: vec![None; setup.nodes],
            ledger: Ledger::default(),
            imports: Imports::default(),
            touched: BTreeSet::new(),
            recovery_actions: 0,
            recovery_ops: BTreeSet::new(),
            integrated_history: BTreeSet::new(),
            change_of: BTreeMap::new(),
            restarted_since_prune: false,
            late_ops: vec![vec![]; setup.nodes],
            trims: vec![0; setup.nodes],
            stepped_back: BTreeSet::new(),
            counter: 0,
            trace: vec![],
        };
        for m in 0..setup.nodes {
            let ids = world
                .raw_jj(m, &["op", "log", "--no-graph", "-T", "id ++ \"\\n\""])
                .lines()
                .map(str::to_owned)
                .collect();
            world.evidence.baseline_ids.push(ids);
            let keys = world.op_keys(m);
            world.evidence.baseline_keys.push(keys);
        }
        // Each machine's history from before it joined is its own, and a later copy has none
        // of it; and its join is its own last operation from then, under its own key there.
        world.evidence.hive_baseline = world
            .evidence
            .baseline_keys
            .iter()
            .flatten()
            .cloned()
            .collect();
        world.evidence.baseline_merge_keys = (0..world.nodes())
            .flat_map(|m| world.merge_keys(m))
            .collect();
        let view = world.view_at_head(0);
        world.ledger.reset(&view);
        world.start_imports();
        world.observe_published_operations();
        for m in 0..world.nodes() {
            world.observe_operation_sources(m);
        }
        world
    }

    pub fn baseline_operation(&self, key: &SourceKey) -> bool {
        self.evidence.baseline_merge_keys.contains(key)
    }

    pub fn nodes(&self) -> usize {
        self.fx.repos.len()
    }

    pub fn machine(&self, m: usize) -> &'static str {
        MACHINES[m]
    }

    pub fn record(&mut self, entry: String) {
        self.trace.push(entry);
    }

    pub fn next(&mut self) -> usize {
        self.counter += 1;
        self.counter
    }

    pub fn fail(&self, message: &str) -> ! {
        panic!("{message}\ntrace:\n{}", self.trace.join("\n"));
    }

    fn learn(&mut self, view: &View) {
        for commit in &view.commits {
            self.change_of
                .insert(commit.id.clone(), commit.change.clone());
        }
    }

    /// The trace without what differs from run to run even when a case replays exactly:
    /// commit ids become change ids; operation ids, which hold the test's directory in the
    /// arguments jj records, are masked, and so is the directory.
    pub fn fingerprint(&self) -> String {
        let root = self.fx.env.root().to_string_lossy().into_owned();
        let mut out = String::new();
        for line in &self.trace {
            let line = line.replace(&root, "<root>");
            let words: Vec<String> = line
                .split(' ')
                .map(|word| {
                    word.split("..")
                        .map(|part| match self.change_of.get(part) {
                            Some(change) => change.clone(),
                            None if part.len() >= 12
                                && part.chars().all(|c| c.is_ascii_hexdigit()) =>
                            {
                                "<id>".to_owned()
                            }
                            None => part.to_owned(),
                        })
                        .collect::<Vec<_>>()
                        .join("..")
                })
                .collect();
            out.push_str(&words.join(" "));
            out.push('\n');
        }
        out
    }

    // Invariants after every rule.

    /// Every op head of every repository a sync or fault touched loads, read-only. (A full
    /// `jj status` would also snapshot, import git refs, and merge concurrent operations,
    /// erasing the very states the sequence is meant to leave around. Recorded commands
    /// load every op head after they run, and the final check runs `jj status`
    /// everywhere.)
    pub fn check_loads(&mut self) {
        let touched = std::mem::take(&mut self.touched);
        for m in touched {
            self.check_loads_of(m);
        }
    }

    /// Every op head of machine `m` loads, read-only.
    fn check_loads_of(&self, m: usize) {
        for head in self.op_heads(m) {
            let output = self.fx.repo(m).jj_output(&[
                "--at-op",
                &head,
                "log",
                "--no-graph",
                "-r",
                "visible_heads()",
                "-T",
                "commit_id ++ \"\\n\"",
            ]);
            if !output.status.success() {
                self.fail(&format!(
                    "{} does not load at op head {head}:\n{}",
                    self.machine(m),
                    String::from_utf8_lossy(&output.stderr)
                ));
            }
        }
    }
}

#[test]
fn workspace_fixup_witnesses_require_the_native_source() {
    let mut world = World::new(Setup {
        nodes: 3,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.rename_workspace(2, 0, "default");
    world.sync(2);
    world.sync(0);
    let (base, dropped) = world.trim_range(0);
    world.rename_workspace(2, 0, "work");
    let foreign = world
        .foreign_workspace_names(0)
        .into_iter()
        .find(|name| name.ends_with("/default"))
        .unwrap();
    world.jj(0, &["workspace", "forget", &foreign]);
    world.jj(0, &["new", "-m", "after forgetting a foreign workspace"]);
    world.abandon_ops(0, &format!("..{base}"), &dropped);
    world.sync(0);
    world.sync(2);
    world.sync(0);
    let native: BTreeSet<_> = world
        .evidence
        .workspace_fixup_inputs
        .keys()
        .cloned()
        .collect();
    assert!(!native.is_empty(), "the trim must create native fix-ups");
    assert!(!world.evidence.workspace_trim_inputs.contains_key(&0));
    let gamma = format!("{}/default", world.fx.machine_key(2));
    let mut reference = crate::reference::Reference::build(&world);
    assert!(reference.witnessed_workspace_names(&world).contains(&gamma));

    let operations = |world: &World, m: usize| {
        let node = world.fx.hive.members[m].adapter.repo();
        let store = node.loader().op_store();
        fs::read_dir(node.repo_path().join("op_store/operations"))
            .unwrap()
            .map(|file| file.unwrap())
            .filter_map(|file| file.file_name().to_str().and_then(OpId::try_from_hex))
            .map(|id| {
                let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
                (id, op)
            })
            .collect::<Vec<_>>()
    };
    let (id, old) = operations(&world, 0)
        .into_iter()
        .find(|(_, op)| {
            native.contains(&merge_key(op))
                && op.metadata.attributes.get("musubi.work") == Some(&world.fx.machine_key(2))
                && !op
                    .metadata
                    .attributes
                    .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
        })
        .unwrap();
    let old_key = merge_key(&old);
    let parent = old.parents[0].hex();
    world.evidence.workspace_fixup_inputs.clear();
    world.jj(
        0,
        &[
            "--ignore-working-copy",
            "--at-op",
            &id.hex(),
            "new",
            "-m",
            "above old fix-up",
        ],
    );
    world.abandon_ops(0, &parent, std::slice::from_ref(&parent));
    assert!(
        operations(&world, 0).iter().any(|(now, op)| {
            *now != id
                && merge_key(op) == old_key
                && !op
                    .metadata
                    .attributes
                    .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
        }),
        "jj must actually reparent the old native fix-up"
    );
    world.observe_workspace_fixups(0);
    assert!(!world.evidence.workspace_fixup_inputs.contains_key(&old_key));

    // Lose the sender's witness, then give the receiver an older accepted baseline.
    // Receiving a marked realization must not turn that baseline into source evidence.
    world.evidence.workspace_fixup_inputs.clear();
    world.begin_workspace_trim(1);
    world.sync(1);
    let received = operations(&world, 1).iter().any(|(_, op)| {
        native.contains(&merge_key(op))
            && op
                .metadata
                .attributes
                .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
    });
    assert!(received, "the receiver must actually realize a fix-up");
    assert!(world.evidence.workspace_fixup_inputs.is_empty());
    assert!(!world.evidence.workspace_trim_inputs.contains_key(&1));
    world.begin_workspace_trim(1);
    world.clone_copy(1);
    assert!(!world.evidence.workspace_trim_inputs.contains_key(&1));
}

/// After `jj op abandon` of a rename, the operation above it adds the new name. When the
/// owner then renames it away and another copy trims its whole history, jj's merge against
/// the root brings the old name back, so the reference must witness it: but only from the
/// owner's own captured rename, not from the name merely being in the retained base.
#[test]
fn an_abandoned_rename_witnesses_the_name_a_full_trim_brings_back() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.rename_workspace(0, 0, "work");
    let rename = world
        .jj(
            0,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                "id",
            ],
        )
        .trim()
        .to_owned();
    world.jj(0, &["new", "-m", "above the rename"]);
    world.abandon_ops(0, &rename, std::slice::from_ref(&rename));
    world.sync(0);
    world.sync(1);
    world.rename_workspace(0, 0, "third");
    let (base, dropped) = world.trim_range(1);
    world.jj(1, &["new", "-m", "before the trim"]);
    world.abandon_ops(1, &format!("..{base}"), &dropped);
    world.sync(1);
    world.sync(0);
    world.sync(1);
    let work = format!("{}/work", world.fx.machine_key(0));
    let mut reference = crate::reference::Reference::build(&world);
    assert!(reference.witnessed_workspace_names(&world).contains(&work));

    // Without the owner's captured rename, the retained base alone proves nothing.
    world
        .evidence
        .commands
        .retain(|_, command| command.id.hex() != rename);
    let mut reference = crate::reference::Reference::build(&world);
    assert!(!reference.witnessed_workspace_names(&world).contains(&work));
}

#[test]
fn private_git_inputs_require_a_known_birth_and_a_retained_name() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: true,
        secondary: false,
    });
    assert!(
        world.private_git_names(1).is_none(),
        "a present copy is not private"
    );
    world.forget_copy(0, 1);
    world.sync(0);
    let birth = format!("{}/default", world.fx.machine_key(1));
    assert!(world.evidence.workspace_births.remove(&birth));
    assert!(
        world.private_git_names(1).is_none(),
        "a plain name needs its birth"
    );
    world.evidence.workspace_births.insert(birth);

    let before = world.observer_state();
    assert_eq!(world.root_record_transition(1), Some(false));
    let initial = world.git_record_input(1).unwrap();
    assert_eq!(
        initial.authorization,
        GitRecordAuthorization::PrivateWorkspaces(BTreeSet::from(["default".to_owned()]))
    );
    world.assert_observer_state(&before);

    // The current input has a newly renamed private slot, but an older representation
    // of this target retains only default. The target label alone cannot bind the input.
    world.rename_workspace(1, 0, "private");
    assert_eq!(
        world.private_git_names(1),
        Some(BTreeSet::from(["private".to_owned()]))
    );
    let input = world.git_record_input(1).unwrap();
    let target = input.target.hex();
    let old = input.before.clone();
    world.sync(1);
    let store = world.fx.hive.members[1].adapter.repo().loader().op_store();
    let mut todo: Vec<_> = world
        .op_heads(1)
        .iter()
        .map(|id| OpId::try_from_hex(id).unwrap())
        .collect();
    let mut seen = old;
    let mut carriers = vec![];
    while let Some(id) = todo.pop() {
        if !seen.insert(id.clone()) {
            continue;
        }
        let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
        todo.extend(op.parents.iter().cloned());
        if op
            .metadata
            .attributes
            .get(musubi_jj::node::CANONICAL_ATTRIBUTE)
            == Some(&target)
        {
            let view = futures::executor::block_on(store.read_view(&op.view_id)).unwrap();
            if !view
                .wc_commit_ids
                .keys()
                .any(|name| name.as_str() == "private")
            {
                carriers.push(id);
            }
        }
    }
    assert!(
        !carriers.is_empty(),
        "the real target publication must be reached"
    );
    assert!(
        carriers
            .iter()
            .all(|id| !world.imports.preserved_heads[1].contains_key(id))
    );
    world.finish_git_record_input(1, Some(input));
    assert!(
        carriers
            .iter()
            .all(|id| !world.imports.preserved_heads[1].contains_key(id))
    );
}

#[test]
fn git_record_inputs_distinguish_lost_work_from_an_opaque_prefix() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: true,
        secondary: false,
    });
    assert!(world.git_record_input(0).is_none());
    world.fx.hive.pruning = false;
    let initial = world.hub_seq();
    world.trim_below_accepted_push(1);
    world.sync(0);
    assert!(
        !world.fx.hive.members[0]
            .adapter
            .repo()
            .applied_records()
            .is_empty()
    );
    world.hub_goes_back(usize::try_from(world.hub_seq() - initial).unwrap());
    let input = world.git_record_input(0).unwrap();
    assert_eq!(input.copy, world.fx.machine_key(0));
    assert_eq!(&input.target, world.fx.hive.hub.store().head().1);
    assert_eq!(
        input.heads.iter().map(|id| id.hex()).collect::<Vec<_>>(),
        world.op_heads(0)
    );
    world.fx.hive.sync_all().unwrap();
    world.fx.hive.pruning = true;
    world.an_hour_passes();
    world.fx.hive.sync_all().unwrap();
    assert!(world.fx.hive.hub.store().pruned() > 0);
    world.clone_copy(world.nodes());
    let m = world.nodes() - 1;
    assert!(
        world.fx.hive.members[m]
            .adapter
            .repo()
            .record_prefix()
            .count
            > 0
    );
    assert!(
        world.fx.hive.members[m]
            .adapter
            .repo()
            .applied_records()
            .is_empty()
    );
    world.remake_hub();
    assert!(
        world.git_record_input(m).is_none(),
        "an opaque prefix is no lost applied suffix"
    );
}

#[test]
fn abandoned_originals_do_not_include_other_native_parent_versions() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: false,
    });
    world.jj(0, &["bookmark", "create", "ancestor", "-r", "@"]);
    let ancestor = world.latest_op_head(0);
    world.jj(0, &["bookmark", "create", "survivor", "-r", "@"]);
    let old = world.latest_op_head(0);
    world.fx.node(0).canonical_heads().unwrap();
    let old_original = world
        .known_original(0, &OpId::try_from_hex(&old).unwrap())
        .unwrap();
    let store = world.fx.hive.members[0].adapter.repo().loader().op_store();
    let body =
        futures::executor::block_on(store.read_operation(&OpId::try_from_hex(&old).unwrap()))
            .unwrap();
    let merge = merge_key(&body);
    world.op_abandon(0, &ancestor);
    world.sync(0);
    world.sync(1);
    // Resume the older immutable branch locally while only the reparented version has
    // been shared. Both native versions have the same command metadata and view.
    world.jj_at_op(0, &old, &["bookmark", "create", "old-branch", "-r", "@"]);
    world.jj(1, &["bookmark", "create", "after", "-r", "@"]);
    let versions = &world.ops_by_key(1)[&merge];
    assert_eq!(versions.len(), 1);
    let shared = versions.iter().next().unwrap().clone();
    world.crash(1, true, 0);
    world.op_abandon(1, &shared);
    let dropped = world
        .abandoned
        .iter()
        .find(|op| op.by == 1 && op.merge == merge)
        .unwrap();
    let originals = dropped.originals.clone().unwrap();
    assert!(!originals.contains(&old_original));
    // Before the drop reaches the first copy, its exact original is still reachable.
    let rejected =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| world.check_operations()))
            .unwrap_err();
    let message = rejected.downcast_ref::<String>().unwrap();
    assert!(
        message.contains("has the operation") && message.contains("which beta abandoned"),
        "{message}"
    );
    world.converge();
    assert!(
        world
            .replicated_history(0)
            .keys()
            .any(|id| world.known_original(0, id) == Some(old_original.clone()))
    );
    assert!(!world.replicated_history(0).keys().any(|id| {
        world
            .known_original(0, id)
            .is_some_and(|id| originals.contains(&id))
    }));
    let dropped = world
        .abandoned
        .iter()
        .find(|op| op.by == 1 && op.merge == merge)
        .unwrap();
    let alternate = world.operation_history(0, true);
    assert!(
        !alternate.proves_present(dropped),
        "an alternate original proves no native return"
    );
    assert!(
        !alternate.may_contain(dropped),
        "known alternate metadata is not uncertain source identity"
    );
    let mut foreign = OperationHistory {
        copy: Some("another-copy".to_owned()),
        ..OperationHistory::default()
    };
    foreign.native.insert(dropped.native.clone());
    assert!(
        !foreign.proves_present(dropped),
        "equal native bytes on a different copy prove no return"
    );
    let mut unknown = OperationHistory::default();
    unknown.unknown.insert(dropped.header.clone());
    assert!(
        unknown.may_contain(dropped),
        "uncertain matching metadata prevents absence proof"
    );
    assert!(
        !unknown.proves_present(dropped),
        "uncertain metadata cannot suppress or discharge a drop"
    );
    world.clone_copy(1);
    let at = world
        .abandoned
        .iter()
        .position(|op| op.by == 1 && op.merge == merge)
        .unwrap();
    world.abandoned[at].originals = None;
    let rejected =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| world.check_operations()))
            .unwrap_err();
    let message = rejected.downcast_ref::<String>().unwrap();
    assert!(
        message.contains("has the operation") && message.contains("which beta abandoned"),
        "matching metadata is rejected without an exact original witness: {message}"
    );
}

#[test]
fn private_abandons_still_reject_their_first_published_rendering() {
    for lose_cache in [false, true] {
        let mut world = World::new(Setup {
            nodes: 2,
            naming: Naming::Default,
            prejoin: false,
            secondary: false,
        });
        world.jj(0, &["bookmark", "create", "private", "-r", "@"]);
        let source = world.latest_op_head(0);
        let native = LocalOp(OpId::try_from_hex(&source).unwrap());
        let cached = lose_cache.then(|| world.fx.node(0).canonicalize(&native).unwrap());
        world.jj(0, &["bookmark", "create", "after", "-r", "@"]);
        if lose_cache {
            world.crash(0, true, 0);
        }
        world.op_abandon(0, &source);
        let at = world
            .abandoned
            .iter()
            .position(|op| op.native.hex() == source)
            .unwrap();
        assert!(!world.abandoned[at].shared);
        assert!(world.abandoned[at].originals.is_none());
        // Negative control: publish the discarded source with the real adapter, without
        // a native command that legitimately resumes old history. In the cache-loss case,
        // use its stored canonical form without asking the adapter to translate the source.
        let canonical = cached.unwrap_or_else(|| world.fx.node(0).canonicalize(&native).unwrap());
        world.fx.node(0).advance(&canonical).unwrap();
        world.sync(0);
        world.sync(1);
        if lose_cache {
            assert!(
                world.abandoned[at].originals.is_none(),
                "the stored rendering must not requalify the removed native source"
            );
        }
        let rejected =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| world.check_operations()))
                .unwrap_err();
        let message = rejected.downcast_ref::<String>().unwrap();
        assert!(
            message.contains("has the operation") && message.contains("which alpha abandoned"),
            "{message}"
        );
    }
}

#[test]
fn a_native_return_allows_only_the_parent_version_jj_brought_back() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: false,
    });
    world.jj(0, &["bookmark", "create", "ancestor", "-r", "@"]);
    let ancestor = world.latest_op_head(0);
    world.jj(0, &["bookmark", "create", "survivor", "-r", "@"]);
    let old = world.latest_op_head(0);
    world.op_abandon(0, &ancestor);
    let removed = world.latest_op_head(0);
    assert_ne!(removed, old);
    world.jj(0, &["bookmark", "create", "after", "-r", "@"]);
    world.op_abandon(0, &removed);
    world.jj_at_op(0, &old, &["bookmark", "create", "resumed", "-r", "@"]);
    world.converge();
    let dropped = world
        .abandoned
        .iter_mut()
        .find(|op| op.native.hex() == removed)
        .unwrap();
    assert!(dropped.originals.is_none());
    // Exact native-return proof also applies when a published source's identity was lost.
    dropped.shared = true;
    world.check_operations();
    // The older version was restored by jj. Republishing the other parent version through
    // the adapter still violates its own abandon, despite the matching command metadata.
    let canonical = world
        .fx
        .node(0)
        .canonicalize(&LocalOp(OpId::try_from_hex(&removed).unwrap()))
        .unwrap();
    world.fx.node(0).advance(&canonical).unwrap();
    world.sync(0);
    world.sync(1);
    let rejected =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| world.check_operations()))
            .unwrap_err();
    let message = rejected.downcast_ref::<String>().unwrap();
    assert!(
        message.contains("has the operation") && message.contains("which alpha abandoned"),
        "{message}"
    );
}

#[test]
fn marked_native_repairs_keep_their_author_after_cache_loss() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::SharedHostname,
        prejoin: false,
        secondary: false,
    });
    let parent = OpId::try_from_hex(world.latest_op_head(0)).unwrap();
    let loader = world.fx.hive.members[0].adapter.repo().loader().clone();
    let store = loader.op_store().clone();
    let mut op = futures::executor::block_on(store.read_operation(&parent)).unwrap();
    let view = futures::executor::block_on(store.read_view(&op.view_id)).unwrap();
    op.parents = vec![parent];
    op.metadata.attributes.clear();
    op.metadata.workspace_name = None;
    op.metadata.description = "native repair carrying another copy's work".to_owned();
    op.metadata.time.start.timestamp.0 += 1000;
    op.metadata.time.end.timestamp.0 += 1000;
    op.metadata
        .attributes
        .insert("musubi.fixup".to_owned(), "1".to_owned());
    op.metadata
        .attributes
        .insert("musubi.work".to_owned(), world.fx.machine_key(1));
    op.metadata.attributes.insert(
        "musubi.worked-at".to_owned(),
        op.metadata.time.end.timestamp.0.to_string(),
    );
    let raw = futures::executor::block_on(store.write_operation(&op)).unwrap();
    // Creating the fixture's operation is an actor action; observing it below must
    // neither canonicalize another source nor write a new native operation.
    let canonical = world.fx.node(0).canonicalize(&LocalOp(raw)).unwrap();
    world.observe_native_origins(0);
    let data = world.fx.hive.members[0].adapter.repo().canonical_store();
    let canonical_op = data.read_operation(&canonical).unwrap();
    let canonical_view = data.read_view(&canonical_op.view_id).unwrap();
    // A second copy can already hold immutable staged data before advancing to it.
    let receiver = world.fx.hive.members[1].adapter.repo().canonical_store();
    assert_eq!(
        receiver.write_view(&canonical_view).unwrap(),
        canonical_op.view_id
    );
    assert_eq!(receiver.write_operation(&canonical_op).unwrap(), canonical);
    let mut alias = op.clone();
    alias.metadata.attributes.insert(
        musubi_jj::node::CANONICAL_ATTRIBUTE.to_owned(),
        canonical.0.hex(),
    );
    assert!(
        !world.realized(0, &canonical, &alias),
        "work ownership is not the native author"
    );
    assert!(
        world.realized(1, &canonical, &alias),
        "a shared hostname and own-work marker prove no local creation"
    );
    let mut private = view.clone();
    private.wc_commit_ids.clear();
    private.git_heads.clear();
    private.git_refs.clear();
    private
        .remote_views
        .remove(jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO);
    alias.view_id = futures::executor::block_on(store.write_view(&private)).unwrap();
    assert!(
        !world.realized(0, &canonical, &alias),
        "private export/projection changes do not change authorship"
    );
    let mut wrong = private.clone();
    wrong.head_ids.clear();
    let mut changed = alias.clone();
    changed.view_id = futures::executor::block_on(store.write_view(&wrong)).unwrap();
    assert!(
        world.realized(0, &canonical, &changed),
        "native origin cannot excuse changed shared heads"
    );
    let mut wrong = private;
    let mut remote = jj_lib::op_store::RemoteView::default();
    remote.bookmarks.insert(
        "extra".into(),
        jj_lib::op_store::RemoteRef {
            target: jj_lib::op_store::RefTarget::normal(
                view.head_ids.iter().next().unwrap().clone(),
            ),
            state: jj_lib::op_store::RemoteRefState::Tracked,
        },
    );
    wrong.remote_views.insert("other".into(), remote);
    changed.view_id = futures::executor::block_on(store.write_view(&wrong)).unwrap();
    assert!(
        world.realized(0, &canonical, &changed),
        "non-Git remote changes remain shared payload"
    );
    let mut unknown = op;
    unknown.metadata.description = "unpublished unknown native source".to_owned();
    let unknown = futures::executor::block_on(store.write_operation(&unknown)).unwrap();
    let before: BTreeSet<_> = world.fx.hive.members[0]
        .adapter
        .repo()
        .canonical_store()
        .operation_ids()
        .unwrap()
        .into_iter()
        .collect();
    world.observe_native_origins(0);
    assert!(
        world.fx.hive.members[0]
            .adapter
            .repo()
            .canonical_of(&LocalOp(unknown))
            .is_none()
    );
    assert_eq!(
        world.fx.hive.members[0]
            .adapter
            .repo()
            .canonical_store()
            .operation_ids()
            .unwrap()
            .into_iter()
            .collect::<BTreeSet<_>>(),
        before
    );
    world.crash(0, true, 0);
    assert!(
        !world.realized(0, &canonical, &alias),
        "qualified native origin survives cache loss"
    );
    world.clone_copy(0);
    assert!(
        world.realized(0, &canonical, &alias),
        "a replacement cannot inherit the old copy's native origin"
    );
}

/// Tested repositories, their shared hub, retained copies and hermetic home. Replay's own
/// temporary directories and the harness's in-memory evidence maps are outside this state.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct ObserverState {
    files: BTreeMap<PathBuf, Vec<u8>>,
    heads: Vec<Vec<String>>,
    clock: std::time::SystemTime,
}

#[test]
fn stale_observation_matches_native_without_consuming_actor_state() {
    let run = |native| {
        let mut world = World::new(Setup {
            nodes: 1,
            naming: Naming::Own,
            prejoin: false,
            secondary: true,
        });
        let check = |world: &World, ws, stale, command_seeds| {
            let before = world.observer_state();
            let observed = world.stale_observation(0, ws);
            world.assert_observer_state(&before);
            assert_eq!(
                observed,
                StaleObservation {
                    stale,
                    command_seeds,
                }
            );
            if native {
                assert_eq!(observed, world.native_stale_observation(0, ws));
            } else {
                assert_eq!(observed.stale, world.is_stale(0, ws));
            }
        };
        world.jj_in(0, 1, &["status"]);
        world.jj(0, &["status"]);
        check(&world, 0, false, 3);
        check(&world, 1, false, 3);
        world.jj(
            0,
            &["describe", "-r", "second@", "-m", "rewritten from primary"],
        );
        check(&world, 1, true, 3);
        world.rename_workspace(0, 1, "renamed");
        check(&world, 1, false, 3);
        // A forgotten workspace can still have a physical checkout recording its old
        // binding. A later user command in it must be judged against the current view.
        world.jj(0, &["workspace", "forget", "renamed"]);
        check(&world, 1, true, 3);
        fs::remove_dir_all(world.workspaces[0][1].path.as_ref().unwrap()).unwrap();
        check(&world, 1, true, 1);
        let fork = native_head(world.fx.repo(0));
        world.jj(0, &["describe", "-m", "first concurrent operation"]);
        world.jj_at_op(
            0,
            &fork.hex(),
            &["describe", "-m", "second concurrent operation"],
        );
        assert_eq!(world.op_heads(0).len(), 2);
        check(&world, 0, true, 0);
        check(&world, 1, true, 0);
        // The actual native commands and the replacement must leave later actors with
        // identical times, seeds and randomness, not just agree on the stale verdict.
        (
            world.fingerprint(),
            world.fx.env.clock().now(),
            world.next_actor_randomness(),
        )
    };
    assert_eq!(run(false), run(true));
}

impl World {
    pub(crate) fn assert_observer_state(&self, before: &ObserverState) {
        let after = self.observer_state();
        assert_eq!(
            after.clock, before.clock,
            "observer consumed an actor seed/clock tick"
        );
        assert_eq!(
            after.heads, before.heads,
            "observer changed native op heads"
        );
        let paths: BTreeSet<_> = before.files.keys().chain(after.files.keys()).collect();
        for path in paths {
            assert!(
                before.files.get(path) == after.files.get(path),
                "observer changed source bytes or paths at {}",
                path.display()
            );
        }
    }

    pub(crate) fn observer_state(&self) -> ObserverState {
        fn collect(
            root: &std::path::Path,
            path: &std::path::Path,
            out: &mut BTreeMap<PathBuf, Vec<u8>>,
        ) {
            let metadata = fs::symlink_metadata(path).unwrap();
            if metadata.file_type().is_symlink() {
                out.insert(
                    path.strip_prefix(root).unwrap().to_path_buf(),
                    fs::read_link(path)
                        .unwrap()
                        .as_os_str()
                        .as_encoded_bytes()
                        .to_vec(),
                );
            } else if metadata.is_dir() {
                for entry in fs::read_dir(path).unwrap() {
                    collect(root, &entry.unwrap().path(), out);
                }
            } else {
                out.insert(
                    path.strip_prefix(root).unwrap().to_path_buf(),
                    fs::read(path).unwrap(),
                );
            }
        }
        let mut files = BTreeMap::new();
        collect(self.fx.env.root(), self.fx.env.root(), &mut files);
        ObserverState {
            files,
            heads: (0..self.nodes()).map(|m| self.op_heads(m)).collect(),
            clock: self.fx.env.clock().now(),
        }
    }

    /// A destructive probe, only after an observation window. Compare with a separate
    /// fixture running the identical actor prefix without that observer, never rewind it.
    pub(crate) fn next_actor_randomness(&self) -> Vec<jj_lib::backend::ChangeId> {
        self.fx
            .hive
            .members
            .iter()
            .map(|member| {
                member
                    .adapter
                    .repo()
                    .loader()
                    .settings()
                    .get_rng()
                    .new_change_id(16)
            })
            .collect()
    }
}

#[test]
fn replicated_history_stops_at_the_captured_join_after_native_reparenting() {
    use futures::executor::block_on;

    fn ancestry(world: &World, heads: Vec<OpId>) -> BTreeMap<OpId, jj_lib::op_store::Operation> {
        let store = world.fx.hive.members[0].adapter.repo().loader().op_store();
        let mut pending = heads;
        let mut operations = BTreeMap::new();
        while let Some(id) = pending.pop() {
            if operations.contains_key(&id) {
                continue;
            }
            let op = block_on(store.read_operation(&id)).unwrap();
            pending.extend(op.parents.iter().cloned());
            operations.insert(id, op);
        }
        operations
    }
    let mut fingerprints = vec![];
    for _ in 0..2 {
        // One joined copy isolates the cut: native abandon can also reparent a
        // foreign shared branch onto private ancestors, legitimately bypassing it.
        let mut world = World::new(Setup {
            nodes: 1,
            naming: Naming::Own,
            prejoin: true,
            secondary: false,
        });
        let join = world.evidence.join_inputs[0].clone();
        let store = world.fx.hive.members[0]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let join_body = block_on(store.read_operation(&join)).unwrap();
        let private = ancestry(&world, join_body.parents.clone());
        let parent = join_body.parents[0].clone();
        let grandparent = private[&parent].parents[0].clone();
        assert!(
            private.contains_key(&grandparent),
            "the cut must hide surviving private history"
        );
        world.jj(0, &["describe", "-m", "known post-join work"]);
        let first = native_head(world.fx.repo(0));
        world.jj(0, &["bookmark", "create", "after-join", "-r", "@"]);
        let second = native_head(world.fx.repo(0));
        let heads = || {
            world
                .op_heads(0)
                .iter()
                .map(|id| OpId::try_from_hex(id).unwrap())
                .collect()
        };
        let original = ancestry(&world, heads());
        let expected: BTreeSet<_> = original
            .keys()
            .filter(|id| !private.contains_key(*id))
            .cloned()
            .collect();
        assert!(expected.is_superset(&BTreeSet::from([
            join.clone(),
            first.clone(),
            second.clone()
        ])));
        assert_eq!(
            world
                .replicated_history(0)
                .into_keys()
                .collect::<BTreeSet<_>>(),
            expected
        );
        // Remove only the join's immediate parent. Its earlier ancestors remain, so
        // walking through a join whose parents changed is observably wrong.
        world.jj(
            0,
            &["--ignore-working-copy", "op", "abandon", &parent.hex()],
        );
        let rewritten = ancestry(
            &world,
            world
                .op_heads(0)
                .iter()
                .map(|id| OpId::try_from_hex(id).unwrap())
                .collect(),
        );
        assert!(rewritten.contains_key(&grandparent));
        for old in [&join, &first, &second] {
            let mut body = original[old].clone();
            body.parents.clear();
            let matches: Vec<_> = rewritten
                .iter()
                .filter(|(_, op)| {
                    let mut candidate = (*op).clone();
                    candidate.parents.clear();
                    candidate == body
                })
                .collect();
            let [(id, actual)] = matches.as_slice() else {
                panic!("one exact reparented source body required");
            };
            assert_ne!(*id, old);
            assert_ne!(actual.parents, original[old].parents);
        }
        let expected: BTreeSet<_> = rewritten
            .keys()
            .filter(|id| !private.contains_key(*id))
            .cloned()
            .collect();
        let actual: BTreeSet<_> = world.replicated_history(0).into_keys().collect();
        assert_eq!(actual, expected);
        assert!(!expected.contains(&grandparent));
        fingerprints.push(world.fingerprint());
    }
    assert_eq!(fingerprints[0], fingerprints[1]);
}

#[test]
fn raw_source_collectors_leave_pending_and_known_native_operations_untouched() {
    let run = |observe| {
        let mut world = World::new(Setup {
            nodes: 2,
            naming: Naming::Default,
            prejoin: false,
            secondary: true,
        });
        world.jj(0, &["describe", "-m", "known source"]);
        world.sync(0);
        world.sync(1);
        world.jj(0, &["describe", "-m", "unpublished source"]);
        let pending = LocalOp(native_head(world.fx.repo(0)));
        assert!(
            world.fx.hive.members[0]
                .adapter
                .repo()
                .canonical_of(&pending)
                .is_none()
        );
        let before = world.observer_state();
        if observe {
            // Run twice: both discovering evidence and revisiting it must be passive.
            for _ in 0..2 {
                for m in 0..world.nodes() {
                    world.observe_operation_sources(m);
                    world.check_imports(m);
                }
                world.observe_published_operations();
            }
            assert!(!world.evidence.operation_sources.is_empty());
            assert!(
                world.fx.hive.members[0]
                    .adapter
                    .repo()
                    .canonical_of(&pending)
                    .is_none()
            );
        }
        world.assert_observer_state(&before);
        (world.fingerprint(), world.next_actor_randomness())
    };
    assert_eq!(run(false), run(true));
}

/// `musubi forget` refuses as a sync does where jj's reparenting recreated an abandoned
/// operation's exact id, so that which of the hive's operations was dropped can't be told:
/// abandoning the snapshot below a commit rewrites the commit, a stale working copy brings
/// the original back, and abandoning that puts the rewrite on the snapshot, the original's
/// bytes. The search follows the refusal's hint, as a user would, and forgets again.
#[test]
fn forget_follows_an_ambiguous_abandon_hint() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.commit(0, 0, 1);
    let commit = world.latest_op_head(0);
    let store = world.fx.node(0).loader().op_store().clone();
    let id = OpId::try_from_hex(&commit).unwrap();
    let snapshot = futures::executor::block_on(store.read_operation(&id))
        .unwrap()
        .parents[0]
        .hex();
    world.forget_copy(0, 1);
    world.op_abandon(0, &snapshot);
    world.sync(0);
    world.sync(0);
    world.commit(0, 0, 0);
    world.op_abandon(0, &commit);
    world.commit(0, 0, 2);
    let (trace, credit) = (world.trace.len(), world.recovery_actions);
    world.forget_copy(0, 1);
    assert_eq!(world.recovery_actions, credit + 1);
    let [(copy, target)] = Vec::from_iter(world.integrated_history.clone())
        .try_into()
        .unwrap();
    assert_eq!(copy, world.fx.machine_key(0));
    assert_eq!(
        &world.trace[trace..],
        &[
            "alpha: musubi forget beta".to_owned(),
            format!("alpha: jj op integrate {target}"),
            "alpha: musubi forget beta".to_owned(),
        ]
    );
}

#[test]
fn ambiguous_abandon_recovery_integrates_the_real_hint_once() {
    use std::path::Path;

    let mut fingerprints = vec![];
    for _ in 0..2 {
        let mut world = World::new(Setup {
            nodes: 2,
            naming: Naming::Own,
            prejoin: false,
            secondary: false,
        });
        let target = native_head(world.fx.repo(0));
        // The pinned native regression: two restores with identical metadata/views,
        // separated by real work, become indistinguishable after native contraction.
        let restore = |world: &mut World| {
            crate::coverage::interrupt_races();
            let history = world.command_history(0);
            let before = world.seen(0);
            let present = world.abandoned_present(0);
            let stale = world.is_stale(0, 0);
            world.record(format!(
                "alpha: jj op restore {} (fixed native timestamp)",
                target.hex()
            ));
            let output = world
                .fx
                .repo(0)
                .program(Path::new("jj"))
                .args(["--ignore-working-copy", "op", "restore", &target.hex()])
                .env("JJ_OP_TIMESTAMP", "2001-02-03T04:05:06Z")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            world.record_commands(0, &history, CommandOutcome::Succeeded);
            let after = world.seen(0);
            let what = world.trace.last().unwrap().clone();
            world.ledger.record(0, &what, &before, &after, stale);
            world.forgive_jj_returns(0, present);
            native_head(world.fx.repo(0))
        };
        world.jj(0, &["describe", "-m", "before"]);
        let a = restore(&mut world);
        world.jj(0, &["describe", "-m", "between"]);
        let x = restore(&mut world);
        assert_ne!(a, x);
        world.sync(0);
        world.jj(
            0,
            &[
                "--ignore-working-copy",
                "op",
                "abandon",
                &format!("{}-..{}-", a.hex(), x.hex()),
            ],
        );
        assert_eq!(native_head(world.fx.repo(0)), a);
        let err = world
            .try_sync_partial(0, 100, None, None)
            .unwrap_err()
            .context("native restore/abandon prefix");
        let hint = err
            .chain()
            .find_map(|err| match err.downcast_ref::<NodeError>() {
                Some(NodeError::AmbiguousAbandon(target)) => Some(target.clone()),
                _ => None,
            })
            .expect("context must retain the typed ambiguous-abandon hint");
        assert_eq!(hint, x.hex());
        let trace = world.trace.len();
        let credit = world.recovery_actions;
        world.recover(0, "sync", &err);
        assert_eq!(world.recovery_actions, credit + 1);
        assert_eq!(
            &world.trace[trace..],
            &[format!("alpha: jj op integrate {hint}")]
        );
        assert_eq!(
            world.integrated_history,
            BTreeSet::from([(world.fx.machine_key(0), hint.clone())])
        );
        world.try_sync_partial(0, 100, None, None).unwrap();
        // These are driver-negative inputs reusing the captured real error, not a
        // claim that the repaired native repository produces it again.
        for exhausted in [false, true] {
            if exhausted {
                world.integrated_history.clear();
                world.recovery_actions = MAX_RECOVERIES;
            }
            let before = world.observer_state();
            let trace = world.trace.clone();
            let credit = world.recovery_actions;
            let stopped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                world.recover(0, "replayed driver hint", &err);
            }));
            assert!(stopped.is_err());
            assert_eq!(world.trace, trace);
            assert_eq!(world.recovery_actions, credit);
            world.assert_observer_state(&before);
        }
        // The general trace normalizer masks bare ids, not the trailing parent
        // selectors in this fixed range. Normalize these two captured ids explicitly.
        let range = format!("{}-..{}-", a.hex(), x.hex());
        fingerprints.push(world.fingerprint().replace(&range, "<id>-..<id>-"));
    }
    assert_eq!(fingerprints[0], fingerprints[1]);
}
