//! The world a generated sequence acts on: a hive of real colocated repositories sharing a
//! bare `origin`, plus what the test remembers about them, and every action a rule can
//! take. Every action is something a user, git, a remote, or the musubi daemon can do.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::repo::Repo as _;
use musubi_core::hub::HubStorage as _;
use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::Step;
use musubi_jj::node::NodeError;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_sync::Attachment;
use musubi_sync::OpId;
use musubi_sync::hub::WAIT_AFTER_OPENING;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

use crate::coverage::fired;
use crate::fixture::Fixture;
use crate::imports::Imports;
use crate::ledger::Ledger;
use crate::ledger::Seen;
use crate::origin::Origin;
use crate::view::TEMPLATE;
use crate::view::View;

/// Machine directories. Their hostnames are the same, unless the setup shares one.
pub const MACHINES: [&str; 4] = ["alpha", "beta", "gamma", "delta"];
/// How many machines a search's hive grows to: the fourth is for the dropped merge's setup
/// only (`World::hold_dropped_merge`).
pub const SEARCH_MACHINES: usize = 3;
/// Small pools, so that machines collide on names.
pub const BOOKMARKS: [&str; 3] = ["main", "feature", "topic"];
pub const TAGS: [&str; 2] = ["v1", "v2"];
pub const WORKSPACES: [&str; 4] = ["default", "work", "second", "third"];
/// Shared files, so that rebases and merges produce content conflicts.
pub const FILES: [&str; 3] = ["a.txt", "b.txt", "dir/c.txt"];

/// Operation metadata, which a realization shares with the operation it realizes, so it
/// identifies an operation across machines even though local ids differ.
const OP_KEY_TEMPLATE: &str = r#"time.start().format("%Y-%m-%dT%H:%M:%S%.f") ++ " " ++ time.end().format("%Y-%m-%dT%H:%M:%S%.f") ++ " " ++ user ++ " " ++ description.first_line() ++ "\n""#;

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

/// What identifies an operation across rewrites and canonicalizing, as `merge_key` has it:
/// its times, to the millisecond, and description.
const MERGE_KEY_TEMPLATE: &str = r#"time.start().format("%s%3f") ++ " " ++ time.end().format("%s%3f") ++ " " ++ description.first_line()"#;

/// Whether `op`, an operation of `node`'s, is a realization of another machine's. musubi marks
/// a realization with the canonical operation it realizes, but marks so too every rewrite of
/// the machine's own operations: whose it is, the canonical operation's work says, or for
/// one that is no copy's work, as a merge, its host (machines can share a host here, which
/// then takes a realization for the machine's own: a weaker check, not a false failure). A
/// fix-up's work, which another machine may write for a copy, counts as that copy's; and an
/// operation whose canonical one can't be read, as a realization.
pub fn realized(op: &jj_lib::op_store::Operation, node: &musubi_jj::node::NodeRepo) -> bool {
    let Some(canonical) = op
        .metadata
        .attributes
        .get("musubi.canonical")
        .and_then(jj_lib::op_store::OperationId::try_from_hex)
    else {
        return false;
    };
    let key = node.machine().key();
    match node
        .canonical_store()
        .read_operation(&CanonicalOp(canonical))
    {
        Ok(canonical) => match musubi_jj::presence::Kind::of(&canonical.metadata).work {
            Some(work) => work != key,
            None => op.metadata.hostname != musubi_jj::workspaces::machine_name(key),
        },
        Err(_) => true,
    }
}

/// An operation's key, as `MERGE_KEY_TEMPLATE` gives it.
pub fn merge_key(op: &jj_lib::op_store::Operation) -> String {
    let metadata = &op.metadata;
    format!(
        "{} {} {}",
        metadata.time.start.timestamp.0,
        metadata.time.end.timestamp.0,
        metadata.description.lines().next().unwrap_or_default()
    )
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

pub struct Workspace {
    pub name: String,
    /// `None` for the repository's own directory.
    pub path: Option<PathBuf>,
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

struct RootRecordInput {
    copy: String,
    target: OpId,
    heads: Vec<OpId>,
    before: BTreeSet<OpId>,
}

struct WorkspaceTrim {
    copy: String,
    input: CanonicalOp,
    wrote_fixup: bool,
    seen: BTreeSet<jj_lib::op_store::OperationId>,
    before: BTreeSet<String>,
}

pub struct World {
    pub fx: Fixture,
    pub origin: Origin,
    naming: Naming,
    /// Machines with file edits that no `jj` command has snapshotted yet.
    dirty: Vec<bool>,
    /// Each machine's workspaces; the first is the primary.
    pub workspaces: Vec<Vec<Workspace>>,
    /// Names actually created in each copy, independent of the resulting hive namespace.
    pub workspace_births: BTreeSet<String>,
    pub initial_workspace_keys: BTreeSet<String>,
    /// Logical names with a live independent merge witness, without physical directories.
    pub logical_extras: Vec<BTreeSet<String>>,
    /// Each machine's operation ids and keys once the hive was set up.
    baseline_ids: Vec<BTreeSet<String>>,
    pub baseline_keys: Vec<BTreeSet<String>>,
    /// Each copy's join point, observed before joining, apart from its parents.
    join_points: Vec<OpId>,
    /// The keys of every machine's operations once the hive was set up: what a copy made
    /// later has of them is its baseline too.
    hive_baseline: BTreeSet<String>,
    baseline_merge_keys: BTreeSet<String>,
    /// The key of each operation a `jj op abandon` dropped, with the machine that ran it and
    /// its `merge_key`: none comes back, unless jj brings it back there.
    pub abandoned: Vec<(usize, String, String)>,
    /// The key of every copy a machine forgot, with the forget's `merge_key`, until the hub's
    /// history has the forget and shows the copy again, by work it did since: an abandon can
    /// drop the forget from the history, but not its effect (docs/internals/design.md,
    /// "Presence through an abandon").
    forgot: BTreeMap<String, String>,
    /// Operations a `jj op abandon` rewrote, by `merge_key`, with their preserved views
    /// and whether each was a realization. Their new parents need not explain those views.
    pub kept_operations: BTreeMap<String, RetainedOperation>,
    operation_sources: BTreeMap<(usize, String), Option<OperationSource>>,
    operation_seen: Vec<BTreeSet<jj_lib::op_store::OperationId>>,
    pub commands: BTreeMap<String, CommandSnapshot>,
    /// The accepted history observed before a native trim, independent of its later fix-up.
    workspace_trim_inputs: BTreeMap<usize, WorkspaceTrim>,
    pub workspace_fixup_inputs: BTreeMap<String, (String, CanonicalOp)>,
    /// Owned native bindings observed before each replacement copy joins. Its synthetic
    /// join has different metadata from the native prejoin head.
    pub workspace_joins: BTreeMap<String, BTreeMap<String, CommitId>>,
    /// The object and jj metadata stores of command sources, including copies later
    /// replaced. The fixture retains their directories until the case ends.
    pub command_sources: BTreeMap<PathBuf, PathBuf>,
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
                    });
                }
                workspaces
            })
            .collect();
        let join_points: Vec<_> = repos.iter().map(native_head).collect();
        let fx = Fixture::join(env, repos);
        let join_points = join_points
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
            initial_workspace_keys: workspace_births.clone(),
            workspace_births,
            logical_extras: vec![BTreeSet::new(); setup.nodes],
            fx,
            origin,
            naming: setup.naming,
            dirty: vec![false; setup.nodes],
            workspaces,
            baseline_ids: vec![],
            baseline_keys: vec![],
            join_points,
            hive_baseline: BTreeSet::new(),
            baseline_merge_keys: BTreeSet::new(),
            abandoned: vec![],
            forgot: BTreeMap::new(),
            kept_operations: BTreeMap::new(),
            operation_sources: BTreeMap::new(),
            operation_seen: vec![],
            commands: BTreeMap::new(),
            workspace_trim_inputs: BTreeMap::new(),
            workspace_fixup_inputs: BTreeMap::new(),
            workspace_joins: BTreeMap::new(),
            command_sources: BTreeMap::new(),
            seen: vec![None; setup.nodes],
            ledger: Ledger::default(),
            imports: Imports::default(),
            touched: BTreeSet::new(),
            recovery_actions: 0,
            recovery_ops: BTreeSet::new(),
            integrated_history: BTreeSet::new(),
            change_of: BTreeMap::new(),
            restarted_since_prune: false,
            counter: 0,
            trace: vec![],
        };
        for m in 0..setup.nodes {
            let ids = world
                .raw_jj(m, &["op", "log", "--no-graph", "-T", "id ++ \"\\n\""])
                .lines()
                .map(str::to_owned)
                .collect();
            world.baseline_ids.push(ids);
            let keys = world.op_keys(m);
            world.baseline_keys.push(keys);
        }
        // Each machine's history from before it joined is its own, and a later copy has none
        // of it; and its join is its own last operation from then, under its own key there.
        world.hive_baseline = world.baseline_keys.iter().flatten().cloned().collect();
        world.baseline_merge_keys = (0..world.nodes())
            .flat_map(|m| world.merge_keys(m))
            .collect();
        let view = world.view_at_head(0);
        world.ledger.reset(&view);
        world.start_imports();
        for m in 0..world.nodes() {
            world.observe_operation_sources(m);
        }
        world
    }

    pub fn baseline_operation(&self, key: &str) -> bool {
        self.baseline_merge_keys.contains(key)
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

    /// Runs `jj`, which must succeed, recording nothing.
    pub fn raw_jj(&self, m: usize, args: &[&str]) -> String {
        let output = self.fx.repo(m).jj_output(args);
        if !output.status.success() {
            self.fail(&format!(
                "`jj {}` failed on {}:\n{}",
                args.join(" "),
                self.machine(m),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        String::from_utf8(output.stdout).unwrap()
    }

    // What machines see.

    /// The local op heads, read from the op heads store without loading the repository.
    pub fn op_heads(&self, m: usize) -> Vec<String> {
        let dir = self.fx.repo(m).repo_path().join("op_heads/heads");
        let mut heads: Vec<String> = fs::read_dir(&dir)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        heads.sort();
        heads
    }

    /// What machine `m` saw at an operation, read-only: no snapshot, import, or merge.
    pub fn view_at(&self, m: usize, op: &str) -> View {
        View::parse(&self.raw_jj(
            m,
            &[
                "--at-op",
                op,
                "log",
                "--no-graph",
                "-r",
                "all()",
                "-T",
                TEMPLATE,
            ],
        ))
    }

    /// The view at machine `m`'s latest op head, without perturbing anything.
    pub fn view_at_head(&self, m: usize) -> View {
        let head = self.latest_op_head(m);
        self.view_at(m, &head)
    }

    /// Machine `m`'s op head that ended last, by its view where two ended together. Not
    /// the first by id: jj records each command's arguments in its operation, temporary
    /// paths and all, so ids differ from one run of a case to the next.
    pub fn latest_op_head(&self, m: usize) -> String {
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let key = |head: &String| {
            let id = jj_lib::op_store::OperationId::try_from_hex(head).unwrap();
            match futures::executor::block_on(store.read_operation(&id)) {
                Ok(op) => (op.metadata.time.end.timestamp, op.view_id.hex()),
                Err(err) => self.fail(&format!(
                    "reading {}'s op head {head}: {err}",
                    self.machine(m)
                )),
            }
        };
        self.op_heads(m)
            .into_iter()
            .max_by_key(key)
            .expect("a repository has an op head")
    }

    /// What machine `m` sees at all its op heads, remembered while they do not change.
    fn seen(&mut self, m: usize) -> Seen {
        let heads = self.op_heads(m);
        if let Some((cached, seen)) = &self.seen[m]
            && *cached == heads
        {
            return seen.clone();
        }
        let views: Vec<View> = heads.iter().map(|h| self.view_at(m, h)).collect();
        for view in &views {
            self.learn(view);
        }
        let seen = Seen::of(&views);
        self.seen[m] = Some((heads, seen.clone()));
        seen
    }

    /// What machine `m` sees, through a `jj` command: like the command the rule is about to
    /// run, it snapshots, imports, and merges first, so the commits it lists are exactly
    /// those the next command can see. Recorded, since it may change things.
    pub fn observe(&mut self, m: usize) -> View {
        let history_before = self.command_history(m);
        let before = self.seen(m);
        self.dirty[m] = false;
        let present = self.abandoned_present(m);
        let view =
            View::parse(&self.raw_jj(m, &["log", "--no-graph", "-r", "all()", "-T", TEMPLATE]));
        self.record_commands(m, &history_before);
        self.forgive_jj_returns(m, present);
        self.learn(&view);
        let after = Seen::of(std::slice::from_ref(&view));
        let what = format!("{}: (looking)", self.machine(m));
        self.ledger.record(m, &what, &before, &after, false);
        let heads = self.op_heads(m);
        self.seen[m] = Some((heads, after));
        view
    }

    /// Has each machine with edits no `jj` command has snapshotted look, snapshotting them.
    /// Returns whether any did.
    pub fn snapshot_pending(&mut self) -> bool {
        let pending: Vec<usize> = (0..self.nodes()).filter(|&m| self.dirty[m]).collect();
        for &m in &pending {
            self.observe(m);
        }
        !pending.is_empty()
    }

    // Local work.

    /// Runs a `jj` command as a user would, in workspace `ws` of machine `m`; it must
    /// succeed. Records which changes, bookmarks, and tags it changed.
    pub fn jj_in(&mut self, m: usize, ws: usize, args: &[&str]) -> String {
        match self.try_jj_in(m, ws, args, &[]) {
            Ok(out) => out,
            Err(stderr) => self.fail(&stderr),
        }
    }

    pub fn jj(&mut self, m: usize, args: &[&str]) -> String {
        self.jj_in(m, 0, args)
    }

    /// Machine `m` forgets machine `o`'s copy, as `musubi forget` does, which abandons its
    /// working-copy commits that are empty. Records what changed.
    pub fn forget_copy(&mut self, m: usize, o: usize) {
        let before = self.seen(m);
        let key = self.fx.machine_key(o);
        let name = self.machine(o);
        self.record(format!("{}: musubi forget {name}", self.machine(m)));
        match self.fx.node(m).forget_copy(&key, name) {
            Ok(true) => {
                let forget = self.newest_key(m);
                self.forgot.insert(key, forget);
            }
            Ok(false) => {}
            Err(err) => self.fail(&format!(
                "musubi forget {name} failed on {}: {err}",
                self.machine(m)
            )),
        }
        let after = self.seen(m);
        let what = self.trace.last().cloned().unwrap_or_default();
        self.ledger.record(m, &what, &before, &after, false);
    }

    /// Machine `m` sets its copy's `musubi.forget-after` to `value`, as `musubi join` does,
    /// and records it in the hive, as its daemon does once idle. Records what changed.
    pub fn set_forget_after(&mut self, m: usize, value: &str) {
        let before = self.seen(m);
        self.record(format!(
            "{}: jj config set --repo musubi.forget-after {value}",
            self.machine(m)
        ));
        self.fx
            .repo(m)
            .jj(&["config", "set", "--repo", "musubi.forget-after", value]);
        if let Err(err) = self.fx.node(m).record_forget_after() {
            self.fail(&format!(
                "recording musubi.forget-after failed on {}: {err}",
                self.machine(m)
            ));
        }
        let after = self.seen(m);
        let what = self.trace.last().cloned().unwrap_or_default();
        self.ledger.record(m, &what, &before, &after, false);
    }

    /// Machine `m`'s daemon, two hours on by the environment's clock, forgets every other
    /// copy that has gone unused for longer than its `musubi.forget-after`. Records what
    /// changed.
    pub fn expire_idle(&mut self, m: usize) {
        let before = self.seen(m);
        self.record(format!(
            "{}: forget the copies unused two hours on",
            self.machine(m)
        ));
        let later = self.fx.env.clock().now() + std::time::Duration::from_secs(2 * 3600);
        let present = |world: &mut Self| -> BTreeSet<String> {
            match world.fx.node(m).activity() {
                Ok(active) => active.into_iter().map(|activity| activity.key).collect(),
                Err(err) => world.fail(&format!(
                    "listing copies' activity failed on {}: {err}",
                    world.machine(m)
                )),
            }
        };
        let active = present(self);
        if let Err(err) = self
            .fx
            .node(m)
            .expire_idle(later, std::time::Duration::ZERO)
        {
            self.fail(&format!(
                "forgetting unused copies failed on {}: {err}",
                self.machine(m)
            ));
        }
        let gone: Vec<String> = active.difference(&present(self)).cloned().collect();
        if !gone.is_empty() {
            let forget = self.newest_key(m);
            for key in gone {
                self.forgot.insert(key, forget.clone());
            }
        }
        let after = self.seen(m);
        let what = self.trace.last().cloned().unwrap_or_default();
        self.ledger.record(m, &what, &before, &after, false);
    }

    /// Like `jj_in`, but a failure whose message contains one of `refusals` (a refusal jj
    /// makes before changing anything) is returned rather than failing the test.
    pub fn try_jj_in(
        &mut self,
        m: usize,
        ws: usize,
        args: &[&str],
        refusals: &[&str],
    ) -> Result<String, String> {
        let history_before = self.command_history(m);
        let before = self.seen(m);
        let present = self.abandoned_present(m);
        let stale = self.is_stale(m, ws);
        let path = self.workspaces[m][ws]
            .path
            .as_ref()
            .map(|p| p.to_string_lossy().into_owned());
        let mut full: Vec<&str> = vec![];
        match &path {
            Some(path) => full.extend(["-R", path.as_str()]),
            None => self.dirty[m] = false,
        }
        full.extend_from_slice(args);
        let place = match &path {
            Some(_) => format!("{} ({})", self.machine(m), self.workspaces[m][ws].name),
            None => self.machine(m).to_owned(),
        };
        self.record(format!("{place}: jj {}", args.join(" ")));
        let output = self.fx.repo(m).jj_output(&full);
        self.record_commands(m, &history_before);
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        if !output.status.success() {
            if refusals.iter().any(|r| stderr.contains(r)) {
                let first = stderr.lines().next().unwrap_or("").to_owned();
                self.record(format!("  (refused: {first})"));
                return Err(stderr);
            }
            // A command imports before it fails: judge that first.
            self.check_imports(m);
            self.fail(&format!(
                "`jj {}` failed on {place}:\n{stderr}",
                full.join(" ")
            ));
        }
        let after = self.seen(m);
        let what = self.trace.last().cloned().unwrap_or_default();
        // In a stale workspace, jj snapshots the files at the operation the working copy
        // was last updated at, before updating it: a command at an older operation, which
        // can leave the working-copy change divergent, as on one machine.
        self.ledger.record(m, &what, &before, &after, stale);
        self.forgive_jj_returns(m, present);
        Ok(String::from_utf8(output.stdout).unwrap())
    }

    /// Whether workspace `ws` of machine `m` is stale: its working-copy commit has changed
    /// since the operation its working copy was last updated at. With several op heads,
    /// assumed so.
    fn is_stale(&self, m: usize, ws: usize) -> bool {
        let heads = self.op_heads(m);
        let [head] = heads.as_slice() else {
            return true;
        };
        let mut place = vec![];
        if let Some(path) = &self.workspaces[m][ws].path {
            place.extend(["-R".to_owned(), path.to_string_lossy().into_owned()]);
        }
        let jj = |args: &[&str]| {
            let mut full: Vec<&str> = place.iter().map(String::as_str).collect();
            full.extend_from_slice(args);
            let output = self.fx.repo(m).jj_output(&full);
            String::from_utf8_lossy(&output.stdout).into_owned()
        };
        let state = jj(&["--ignore-working-copy", "debug", "working-copy"]);
        let Some(updated_at) = state
            .split_once("Current operation: OperationId(\"")
            .and_then(|(_, rest)| rest.split_once('"'))
            .map(|(op, _)| op.to_owned())
        else {
            return true;
        };
        let wc = format!("{}@", self.workspaces[m][ws].name);
        let at = |op: &str| {
            jj(&[
                "--ignore-working-copy",
                "--at-op",
                op,
                "log",
                "--no-graph",
                "-r",
                &wc,
                "-T",
                "commit_id",
            ])
        };
        at(&updated_at) != at(head)
    }

    /// Runs a command at an older operation `op` of machine `m`, creating a concurrent
    /// operation, and records what it changed relative to `op`.
    pub fn jj_at_op(&mut self, m: usize, op: &str, args: &[&str]) {
        let before = Seen::of(&[self.view_at(m, op)]);
        let present = self.abandoned_present(m);
        let heads_before = self.op_heads(m);
        let history_before = self.command_history(m);
        let mut full = vec!["--at-op", op];
        full.extend_from_slice(args);
        self.record(format!(
            "{}: jj --at-op {} {}",
            self.machine(m),
            &op[..12],
            args.join(" ")
        ));
        let output = self.fx.repo(m).jj_output(&full);
        self.record_commands(m, &history_before);
        if !output.status.success() {
            self.fail(&format!(
                "`jj {}` failed on {}:\n{}",
                full.join(" "),
                self.machine(m),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let new_heads: Vec<String> = self
            .op_heads(m)
            .into_iter()
            .filter(|h| !heads_before.contains(h))
            .collect();
        let views: Vec<View> = new_heads.iter().map(|h| self.view_at(m, h)).collect();
        let after = Seen::of(&views);
        let what = self.trace.last().cloned().unwrap_or_default();
        self.ledger.record(m, &what, &before, &after, true);
        self.forgive_jj_returns(m, present);
    }

    /// The source history before a command. Keys also recognize operations an abandon
    /// rewrites without changing their metadata, so those are not mistaken for new work.
    fn command_history(&self, m: usize) -> BTreeSet<String> {
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let mut pending = self.op_heads(m);
        let mut seen = BTreeSet::new();
        let mut keys = BTreeSet::new();
        while let Some(head) = pending.pop() {
            if !seen.insert(head.clone()) {
                continue;
            }
            let id = jj_lib::op_store::OperationId::try_from_hex(&head).unwrap();
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            keys.insert(merge_key(&op));
            pending.extend(op.parents.iter().map(jj_lib::object_id::ObjectId::hex));
        }
        keys
    }

    fn record_commands(&mut self, m: usize, history_before: &BTreeSet<String>) {
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let mut pending = self.op_heads(m);
        let mut seen = BTreeSet::new();
        while let Some(head) = pending.pop() {
            if !seen.insert(head.clone()) {
                continue;
            }
            let id = jj_lib::op_store::OperationId::try_from_hex(&head).unwrap();
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            if history_before.contains(&merge_key(&op)) {
                continue;
            }
            // A command can first write a snapshot or import, then its requested work.
            // Record the complete new interval, not just its final operation head.
            pending.extend(op.parents.iter().map(jj_lib::object_id::ObjectId::hex));
            let [parent] = op.parents.as_slice() else {
                continue;
            };
            // A command can trigger jj's automatic reconciliation before doing no work.
            // Such a merge must still be compared with jj, never trusted as a payload.
            if op.metadata.description == "reconcile divergent operations" {
                continue;
            }
            let snapshot = futures::executor::block_on(async {
                let parent_id = parent.clone();
                let parent = store.read_operation(&parent_id).await.unwrap();
                let input = self.fx.hive.members[m]
                    .adapter
                    .repo()
                    .canonical_of(&LocalOp(parent_id.clone()))
                    .filter(|input| {
                        self.fx.hive.members[m]
                            .adapter
                            .repo()
                            .canonical_store()
                            .read_operation(input)
                            .is_ok_and(|canonical| merge_key(&canonical) == merge_key(&parent))
                            || self.baseline_operation(&merge_key(&parent))
                    });
                CommandSnapshot {
                    parent: parent_id,
                    input,
                    predecessors: op.commit_predecessors.clone(),
                    id: id.clone(),
                    copy: self.fx.machine_key(m),
                    copies: self
                        .workspace_births
                        .iter()
                        .filter_map(|key| key.split_once('/').map(|(copy, _)| copy.to_owned()))
                        .collect(),
                    base: store.read_view(&parent.view_id).await.unwrap(),
                    made: store.read_view(&op.view_id).await.unwrap(),
                }
            });
            let repo = self.fx.repo(m);
            self.command_sources.insert(
                repo.path().join(".git/objects"),
                repo.repo_path().join("store/extra"),
            );
            // Later rewrites keep the same key; retain the actual command's first input.
            self.commands.entry(merge_key(&op)).or_insert(snapshot);
        }
    }

    /// Operations made since setup that machine `m` can run a command at, other than its
    /// current head. (`jj op log` merges concurrent operations first, like any command.)
    pub fn older_ops(&mut self, m: usize) -> Vec<String> {
        // Through a recorded command: it merges concurrent operations first.
        self.jj(m, &["op", "log", "--no-graph", "-n", "8", "-T", "id"]);
        self.op_ids_and_keys(m, Some(8))
            .into_iter()
            .skip(1)
            .filter(|(id, key)| {
                !self.baseline_ids[m].contains(id) && !self.baseline_keys[m].contains(key)
            })
            .map(|(id, _)| id)
            .collect()
    }

    /// Those of `older_ops` that `jj op abandon` can abandon: not merges, which it refuses.
    pub fn abandonable_ops(&mut self, m: usize) -> Vec<String> {
        let older = self.older_ops(m);
        let merges: BTreeSet<String> = self
            .raw_jj(
                m,
                &[
                    "--ignore-working-copy",
                    "op",
                    "log",
                    "--no-graph",
                    "-n",
                    "8",
                    "-T",
                    r#"if(parents.len() > 1, id ++ "\n")"#,
                ],
            )
            .lines()
            .map(str::to_owned)
            .collect();
        older
            .into_iter()
            .filter(|op| !merges.contains(op))
            .collect()
    }

    /// Machine `m`'s operations, newest first, or only the first `limit`, by id with their
    /// keys, as `op_keys` has them.
    fn op_ids_and_keys(&self, m: usize, limit: Option<usize>) -> Vec<(String, String)> {
        let template = format!(r#"id ++ " " ++ {OP_KEY_TEMPLATE}"#);
        let limit = limit.map(|n| n.to_string());
        let mut args = vec![
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-T",
            &template,
        ];
        if let Some(limit) = &limit {
            args.extend(["-n", limit]);
        }
        self.raw_jj(m, &args)
            .lines()
            .filter_map(|line| line.split_once(' '))
            .map(|(id, key)| (id.to_owned(), without_op_ids(key)))
            .collect()
    }

    /// Whether `jj undo` on machine `m` would undo an ordinary operation made since setup:
    /// one op head, not a merge (jj refuses to undo those), not itself an undo or redo
    /// (repeated undos walk further back, eventually into the setup), not a workspace
    /// operation, and no pending edit (whose snapshot would be undone instead).
    pub fn can_undo(&self, m: usize) -> bool {
        if self.dirty[m] {
            return false;
        }
        let heads = self.op_heads(m);
        if heads.len() != 1 || self.baseline_ids[m].contains(&heads[0]) {
            return false;
        }
        let info = self.raw_jj(
            m,
            &[
                "--at-op",
                &heads[0],
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                r#"parents.len() ++ " " ++ description"#,
            ],
        );
        let (parents, description) = info.split_once(' ').unwrap_or((&info, ""));
        // Undoing a workspace operation strands a working copy: after undoing a rename,
        // the working copy's recorded name is no longer in the view, and jj says the
        // command "requires a working copy". jj's own behavior; jj refuses it too unless
        // told `--allow-cross-workspace`, which the `undo` rule uses after checking that
        // jj refuses other workspaces' and machines' operations.
        parents == "1"
            && !description.starts_with("undo")
            && !description.starts_with("redo")
            && !description.to_lowercase().contains("workspace")
    }

    /// The workspace that made the head operation, as `jj op log` shows it: `default@`,
    /// `beta/default@` for another machine's, or nothing for an operation musubi made.
    pub fn head_op_workspace(&self, m: usize) -> String {
        let head = self.latest_op_head(m);
        let template = "workspace_name";
        self.raw_jj(
            m,
            &[
                "--at-op",
                &head,
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                template,
            ],
        )
    }

    /// If machine `m`'s latest operation is an undo, the workspace that made the operation
    /// it undid, as `jj op log` shows it. (Without anything to change, `jj undo` writes no
    /// operation.)
    pub fn undone_workspace(&self, m: usize) -> Option<String> {
        let template =
            r#"description.first_line() ++ "\t" ++ parents.map(|p| p.workspace_name()).join(",")"#;
        let latest = self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                template,
            ],
        );
        let (description, parents) = latest.split_once('\t')?;
        description
            .starts_with("undo: restore to operation")
            .then(|| parents.trim().to_owned())
    }

    pub fn write(&mut self, m: usize, ws: usize, file: &str, contents: &str) {
        let dir = self.workspaces[m][ws]
            .path
            .clone()
            .unwrap_or_else(|| self.fx.repo(m).path().to_owned());
        let path = dir.join(file);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    pub fn commit(&mut self, m: usize, ws: usize, file: usize) {
        let n = self.next();
        let message = format!("c{n} on {}", self.machine(m));
        self.write(m, ws, FILES[file], &format!("{message}\n"));
        self.record(format!("{}: write {}", self.machine(m), FILES[file]));
        self.jj_in(m, ws, &["commit", "-m", &message]);
    }

    /// Edits a file without running `jj`, so the edit is not snapshotted yet.
    pub fn edit(&mut self, m: usize, file: usize) {
        let n = self.next();
        let contents = format!("edit {n} on {}\n", self.machine(m));
        self.write(m, 0, FILES[file], &contents);
        self.dirty[m] = true;
        self.record(format!(
            "{}: write {} (not snapshotted)",
            self.machine(m),
            FILES[file]
        ));
    }

    /// A fresh description.
    pub fn message(&mut self, m: usize) -> String {
        let n = self.next();
        format!("d{n} on {}", self.machine(m))
    }

    // Git-side work.

    pub fn git(&mut self, m: usize, args: &[&str]) -> String {
        self.record(format!("{}: git {}", self.machine(m), args.join(" ")));
        self.fx.repo(m).git(args)
    }

    pub fn git_branches(&self, m: usize) -> Vec<String> {
        self.fx
            .repo(m)
            .git(&["for-each-ref", "--format=%(refname:lstrip=2)", "refs/heads"])
            .lines()
            .map(str::to_owned)
            .collect()
    }

    // Sync and faults.

    /// A node's first policy step merges its op heads if there are several (`NodeCore::step`).
    /// Before a sync, they are all this machine's own concurrent operations (from `--at-op`),
    /// so the merge is this machine's work, and the ledger records it as such; this takes
    /// that first step through the same code, and records it. Later merges, with operations
    /// from the hub, are musubi's and are not recorded.
    pub fn merge_local_heads(&mut self, m: usize) {
        if self.op_heads(m).len() < 2 {
            return;
        }
        let before = self.seen(m);
        if let Err(err) = self.fx.node(m).merge_heads() {
            self.fail(&format!(
                "merging {}'s op heads failed: {err}",
                self.machine(m)
            ));
        }
        let after = self.seen(m);
        let what = format!("{}: merge own op heads before sync", self.machine(m));
        self.ledger.record(m, &what, &before, &after, false);
        self.observe_operation_sources(m);
    }

    /// Lets node `m` poll the hub and run its policy until idle.
    pub fn sync(&mut self, m: usize) {
        self.record(format!("{}: sync", self.machine(m)));
        self.sync_counted(m);
    }

    /// Syncs node `m` until idle and returns how many steps it took.
    pub fn sync_counted(&mut self, m: usize) -> usize {
        self.observe_operation_sources(m);
        self.touched.insert(m);
        self.merge_local_heads(m);
        let pruned = self.fx.hive.hub.store().pruned();
        let forgotten = self.forgotten_working_copies(m);
        let steps = loop {
            let input = self.root_record_input(m);
            let result = self.fx.hive.sync(m);
            self.finish_root_record_input(m, input);
            match result {
                Ok(steps) => break steps,
                Err(err) => self.recover(m, "sync", &err),
            }
        };
        self.note_pruning(pruned);
        self.note_forgotten_rebase(m, forgotten);
        self.record_merges(m);
        // A fully driven sync also finishes an unpublished-only trim, which produces
        // no shared drop or fix-up at all.
        if self.fx.hive.members[m]
            .adapter
            .repo()
            .pending_drops()
            .is_empty()
        {
            self.workspace_trim_inputs.remove(&m);
        }
        self.note_shown_again();
        steps
    }

    /// Machine `m`'s own working-copy commits, by workspace, each with its change id and
    /// whether it is visible, read in process, where the hive has forgotten the machine:
    /// `None` where it shows it.
    fn forgotten_working_copies(
        &self,
        m: usize,
    ) -> Option<BTreeMap<String, (String, String, bool)>> {
        if self.fx.shown_machines().contains(&self.fx.machine_key(m)) {
            return None;
        }
        let repo = self.fx.load(m);
        let index = repo.index();
        let heads = repo.view().heads();
        let visible = |id: &CommitId| {
            futures::executor::block_on(index.has_id(id)).unwrap()
                && heads
                    .iter()
                    .any(|head| futures::executor::block_on(index.is_ancestor(id, head)).unwrap())
        };
        Some(
            repo.view()
                .wc_commit_ids()
                .iter()
                // The search names workspaces without a `/`: those with one are others'.
                .filter(|(name, _)| !name.as_str().contains('/'))
                .map(|(name, id)| {
                    let commit =
                        futures::executor::block_on(repo.store().get_commit_async(id)).unwrap();
                    let change = commit.change_id().hex();
                    (name.as_str().to_owned(), (id.hex(), change, visible(id)))
                })
                .collect(),
        )
    }

    /// Notes, for coverage, a sync of machine `m`, forgotten before it and after, that moved
    /// a working copy of its own from one hidden commit to another of the same change: as a
    /// forgotten copy rebases one whose parents other machines rewrote or abandoned
    /// (`replace_abandoned_working_copies`).
    fn note_forgotten_rebase(
        &self,
        m: usize,
        before: Option<BTreeMap<String, (String, String, bool)>>,
    ) {
        let (Some(before), Some(after)) = (before, self.forgotten_working_copies(m)) else {
            return;
        };
        let rebased = after.iter().any(|(name, (commit, change, visible))| {
            !visible
                && before
                    .get(name)
                    .is_some_and(|(old, old_change, was_visible)| {
                        !was_visible && old != commit && old_change == change
                    })
        });
        if rebased {
            fired("forgotten:working_copy_rebased");
        }
    }

    /// The `merge_key` of machine `m`'s newest operation.
    fn newest_key(&self, m: usize) -> String {
        let args = [
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n",
            "1",
        ];
        let args: Vec<&str> = args.into_iter().chain(["-T", MERGE_KEY_TEMPLATE]).collect();
        self.raw_jj(m, &args)
    }

    /// Drops from `forgot` each copy the hub's head shows again although its history has the
    /// forget: the copy worked since.
    fn note_shown_again(&mut self) {
        if self.forgot.is_empty() {
            return;
        }
        let shown = self.fx.shown_machines();
        if !self.forgot.keys().any(|key| shown.contains(key)) {
            return;
        }
        let history = self.hub_merge_keys();
        self.forgot
            .retain(|key, forget| !(shown.contains(key) && history.contains(forget)));
    }

    /// Recovers from a sync of node `m` that failed, as a user would from what it says: from
    /// a stop behind records the hub pruned, by making a new copy (`stopped_behind_prune`);
    /// by integrating the history named by an ambiguous-abandon hint; or from a known jj
    /// limitation (docs/internals/races.md), where jj can't merge this machine's operations
    /// with the hive's, so musubi pauses, by reverting the operation the
    /// error names, or where it names none, as a user given its list would: the newest, other
    /// than the recovery's own. Fails the case on any other error, or if the operation to
    /// revert is one already reverted, or a revert the recovery made: reverting it would put
    /// back what it reverted.
    fn recover(&mut self, m: usize, what: &str, err: &anyhow::Error) {
        if self.stopped_behind_prune(m, what, err) {
            return;
        }
        if let Some(target) = err
            .chain()
            .find_map(|e| match e.downcast_ref::<NodeError>() {
                Some(NodeError::AmbiguousAbandon(target)) => Some(target.clone()),
                _ => None,
            })
        {
            if self.recovery_actions >= MAX_RECOVERIES
                || !self
                    .integrated_history
                    .insert((self.fx.machine_key(m), target.clone()))
            {
                self.fail(&format!(
                    "{what} keeps asking to restore the same history: {err:#}"
                ));
            }
            self.recovery_actions += 1;
            self.jj(m, &["op", "integrate", &target]);
            return;
        }
        let found = err
            .chain()
            .find_map(|e| match e.downcast_ref::<NodeError>() {
                Some(NodeError::Unmergeable { ours, culprit, .. }) => {
                    Some((ours.clone(), culprit.clone()))
                }
                _ => None,
            });
        let Some((ours, culprit)) = found else {
            // Several errors share a message: name which.
            let which = err
                .chain()
                .find_map(|e| e.downcast_ref::<NodeError>())
                .map(|e| format!(" ({e:?})"))
                .unwrap_or_default();
            self.fail(&format!(
                "{what} of {} failed: {err:#}{which}",
                self.machine(m)
            ));
        };
        let ops = self.op_summaries(m);
        let op = match culprit {
            Some(op) => Some(op.0.hex()).filter(|op| !self.recovery_ops.contains(op)),
            // As `can_undo` does, skip merges, which jj refuses to revert, and workspace
            // operations, which rewrite no commits, so they can't be what jj fails to
            // merge, and which strand a working copy when reverted.
            None => ours.iter().map(|op| op.0.hex()).find(|op| {
                !self.recovery_ops.contains(op)
                    && ops.get(op).is_some_and(|(parents, description)| {
                        *parents == 1 && !description.to_lowercase().contains("workspace")
                    })
            }),
        };
        let Some(op) = op.filter(|_| self.recovery_actions < MAX_RECOVERIES) else {
            self.fail(&format!(
                "{what} of {} keeps failing: {err:#}",
                self.machine(m)
            ));
        };
        self.recovery_actions += 1;
        self.jj(m, &["op", "revert", &op]);
        let written: Vec<String> = self
            .op_summaries(m)
            .into_keys()
            .filter(|id| !ops.contains_key(id))
            .collect();
        self.recovery_ops.insert(op);
        self.recovery_ops.extend(written);
    }

    /// Every operation in machine `m`'s operation log, by hex id, with its number of parents
    /// and the first line of its description.
    fn op_summaries(&self, m: usize) -> BTreeMap<String, (usize, String)> {
        self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-T",
                r#"id ++ "\t" ++ parents.len() ++ "\t" ++ description.first_line() ++ "\n""#,
            ],
        )
        .lines()
        .filter_map(|line| {
            let mut fields = line.splitn(3, '\t');
            let id = fields.next()?;
            let parents = fields.next()?.parse().ok()?;
            Some((id.to_owned(), (parents, fields.next()?.to_owned())))
        })
        .collect()
    }

    fn root_record_input(&self, m: usize) -> Option<RootRecordInput> {
        if m >= self.imports.preserved_heads.len() {
            return None;
        }
        let node = self.fx.hive.members[m].adapter.repo();
        let hub = self.fx.hive.hub.store();
        let count = usize::try_from(node.record_state().0).ok()?;
        if count < hub.pruned() {
            return None;
        }
        let same_prefix = node.record_prefix().count == hub.pruned() as u64
            && Some(&node.record_prefix().digest) == hub.digest(hub.pruned());
        if same_prefix && node.applied_records() == hub.records() && !node.has_record_custody() {
            return None;
        }
        let common = if same_prefix {
            node.applied_records()
                .iter()
                .zip(hub.records())
                .take_while(|(old, new)| old == new)
                .count()
        } else {
            0
        };
        // Losing an opaque prefix alone does not reset the accepted base. An actual
        // applied suffix must be lost, or the exact saved base must be entirely dropped.
        let lost = common < node.applied_records().len();
        if !lost {
            let base = fs::read_to_string(node.repo_path().join("musubi/accepted_base")).ok()?;
            let base = CanonicalOp(OpId::try_from_hex(base.trim())?);
            let dropped: BTreeSet<_> = hub.records()[common..]
                .iter()
                .flat_map(|record| record.ops())
                .map(|op| hub.canonical().original_id(&op.0))
                .collect::<Result<_, _>>()
                .ok()?;
            let store = node.canonical_store();
            let mut todo = vec![base];
            let mut visited = BTreeSet::new();
            while let Some(op) = todo.pop() {
                if op == *store.root_operation_id() || !visited.insert(op.clone()) {
                    continue;
                }
                if !dropped.contains(&store.original_id(&op).ok()?) {
                    return None;
                }
                todo.extend(CanonicalOp::parents_of(&store.read_operation(&op).ok()?));
            }
        }
        let heads: Vec<_> = self
            .op_heads(m)
            .iter()
            .map(|s| OpId::try_from_hex(s).unwrap())
            .collect();
        let mut before = BTreeSet::new();
        let mut todo = heads.clone();
        while let Some(id) = todo.pop() {
            if before.insert(id.clone()) {
                let op = futures::executor::block_on(node.loader().op_store().read_operation(&id))
                    .ok()?;
                todo.extend(op.parents);
            }
        }
        Some(RootRecordInput {
            copy: self.fx.machine_key(m),
            target: hub.head().1.clone(),
            heads,
            before,
        })
    }

    fn finish_root_record_input(&mut self, m: usize, input: Option<RootRecordInput>) {
        let Some(input) = input.filter(|input| input.copy == self.fx.machine_key(m)) else {
            return;
        };
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let mut todo: Vec<_> = self
            .op_heads(m)
            .iter()
            .map(|s| OpId::try_from_hex(s).unwrap())
            .collect();
        let mut seen = input.before;
        while let Some(id) = todo.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            let Ok(op) = futures::executor::block_on(store.read_operation(&id)) else {
                continue;
            };
            todo.extend(op.parents);
            if op
                .metadata
                .attributes
                .get(musubi_jj::node::CANONICAL_ATTRIBUTE)
                .is_some_and(|target| *target == input.target.hex())
            {
                self.imports.preserved_heads[m]
                    .entry(id)
                    .or_insert_with(|| input.heads.clone());
            }
        }
    }

    /// Observe operations before and after receipt too. A publisher cannot observe an
    /// offline copy's old operation, but a received trim keeps its view while reparenting it.
    fn observe_operation_sources(&mut self, m: usize) {
        self.observe_workspace_fixups(m);
        self.operation_seen.resize_with(self.nodes(), BTreeSet::new);
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let mut pending = self.op_heads(m);
        let mut found = BTreeMap::<String, Vec<jj_lib::op_store::Operation>>::new();
        while let Some(hex) = pending.pop() {
            let id = jj_lib::op_store::OperationId::try_from_hex(&hex).unwrap();
            if !self.operation_seen[m].insert(id.clone()) {
                continue;
            }
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            pending.extend(op.parents.iter().map(jj_lib::object_id::ObjectId::hex));
            let key = merge_key(&op);
            found.entry(key).or_default().push(op);
        }
        for (key, versions) in found {
            let [op] = versions.as_slice() else {
                self.operation_sources.insert((m, key), None);
                continue;
            };
            let source_key = (m, key.clone());
            match self.operation_sources.get(&source_key) {
                Some(Some(source)) if source.operation.parents != op.parents => {
                    if same_source_body(&source.operation, op) {
                        let retained = source.retained.clone();
                        self.remember_retained(key, retained);
                    } else {
                        // Equal time/description alone does not identify an original.
                        self.operation_sources.insert(source_key, None);
                    }
                }
                Some(_) => {}
                None => {
                    let retained = self.retained_source(m, op);
                    self.operation_sources.insert(
                        source_key,
                        Some(OperationSource {
                            operation: op.clone(),
                            retained,
                        }),
                    );
                }
            }
        }
    }

    /// Unambiguous native bodies observed before rewriting, excluding marked renderings.
    pub fn captured_record_sources(
        &self,
        m: usize,
    ) -> BTreeMap<String, jj_lib::op_store::Operation> {
        self.operation_sources
            .iter()
            .filter_map(|((machine, key), source)| {
                let source = source.as_ref()?;
                (*machine == m
                    && !source
                        .operation
                        .metadata
                        .attributes
                        .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE))
                .then(|| (key.clone(), source.operation.clone()))
            })
            .collect()
    }

    /// Canonicalization may replace a native fix-up at the heads with a marked version.
    /// Read its immutable original too, but only files created during this local trim.
    fn observe_workspace_fixups(&mut self, m: usize) {
        let copy = self.fx.machine_key(m);
        let Some(trim) = self.workspace_trim_inputs.get_mut(&m) else {
            return;
        };
        assert_eq!(trim.copy, copy, "trim evidence outlived its copy");
        let node = self.fx.hive.members[m].adapter.repo();
        let store = node.loader().op_store();
        let files = fs::read_dir(node.repo_path().join("op_store/operations")).unwrap();
        for file in files {
            let file = file.unwrap();
            let Some(id) = file.file_name().to_str().and_then(OpId::try_from_hex) else {
                continue;
            };
            if !trim.seen.insert(id.clone()) {
                continue;
            }
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            if !op.metadata.attributes.contains_key("musubi.fixup")
                || op
                    .metadata
                    .attributes
                    .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
                || trim.before.contains(&merge_key(&op))
            {
                continue;
            }
            trim.wrote_fixup = true;
            self.workspace_fixup_inputs
                .entry(merge_key(&op))
                .or_insert_with(|| (trim.copy.clone(), trim.input.clone()));
        }
    }

    fn remember_retained(&mut self, key: String, source: RetainedOperation) {
        // A later trim must not replace the original input with an already-reparented one.
        // An own operation knows that input; a received realization has a different parent.
        self.kept_operations
            .entry(key)
            .and_modify(|before| {
                if source.native && !before.native || before.realized && !source.realized {
                    *before = source.clone();
                }
            })
            .or_insert(source);
    }

    fn retained_source(&self, m: usize, op: &jj_lib::op_store::Operation) -> RetainedOperation {
        let repo = self.fx.hive.members[m].adapter.repo();
        let store = repo.loader().op_store();
        let parent = if let [id] = op.parents.as_slice() {
            let parent = futures::executor::block_on(store.read_operation(id)).unwrap();
            Some(futures::executor::block_on(store.read_view(&parent.view_id)).unwrap())
        } else {
            None
        };
        RetainedOperation {
            copy: self.fx.machine_key(m),
            native: !op
                .metadata
                .attributes
                .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE),
            view: futures::executor::block_on(store.read_view(&op.view_id)).unwrap(),
            realized: realized(op, repo),
            parent,
        }
    }

    /// Records the commits node `m`'s merges made, after a sync.
    pub fn record_merges(&mut self, m: usize) {
        self.observe_operation_sources(m);
        self.finish_workspace_trim(m);
        let after = self.seen(m);
        let what = format!("{}: merge by its node", self.machine(m));
        self.ledger.record_sync(m, &what, &after);
    }

    fn finish_workspace_trim(&mut self, m: usize) {
        if self
            .workspace_trim_inputs
            .get(&m)
            .is_some_and(|trim| trim.wrote_fixup)
            && self.fx.hive.members[m]
                .adapter
                .repo()
                .pending_drops()
                .is_empty()
        {
            self.workspace_trim_inputs.remove(&m);
        }
    }

    /// Lets node `m` poll the hub and take at most `steps` policy steps, delivering every
    /// request but losing the reply to request number `lose`: progress that stops partway,
    /// possibly after an upload but before the push.
    pub fn sync_partial(&mut self, m: usize, steps: usize, lose: Option<usize>) {
        self.observe_operation_sources(m);
        self.touched.insert(m);
        self.record(format!(
            "{}: sync {steps} step(s){}",
            self.machine(m),
            lose.map(|d| format!(", losing reply {d}"))
                .unwrap_or_default()
        ));
        self.merge_local_heads(m);
        let pruned = self.fx.hive.hub.store().pruned();
        // Progress stops here either way: a partial sync that pauses has nothing to retry.
        if let Err(err) = self.try_sync_partial(m, steps, lose, None) {
            self.recover(m, "partial sync", &err);
        }
        self.note_pruning(pruned);
        self.record_merges(m);
    }

    /// Whether node `m` has yet to realize the hub's head.
    pub fn behind_hub(&self, m: usize) -> bool {
        let head = CanonicalOp(self.fx.hive.hub.store().head().1.clone());
        self.fx.hive.members[m]
            .adapter
            .repo()
            .local_of(&head)
            .is_none()
    }

    /// Lets node `m` sync until it has realized `count` operations, or has nothing more to
    /// realize, and stops there, with what it realized perhaps still being written.
    pub fn sync_realizing(&mut self, m: usize, count: usize) {
        self.observe_operation_sources(m);
        self.touched.insert(m);
        self.record(format!(
            "{}: sync until {count} operation(s) realized",
            self.machine(m)
        ));
        self.merge_local_heads(m);
        let pruned = self.fx.hive.hub.store().pruned();
        if let Err(err) = self.try_sync_partial(m, usize::MAX, None, Some(count)) {
            self.recover(m, "partial sync", &err);
        }
        self.note_pruning(pruned);
        self.record_merges(m);
    }

    /// Lets node `m` sync until it has taken the hub's records and realized its head, and
    /// stops there, before advancing to it.
    pub fn sync_taking(&mut self, m: usize) {
        self.observe_operation_sources(m);
        self.touched.insert(m);
        self.record(format!(
            "{}: sync until the hub's records are taken and its head realized",
            self.machine(m)
        ));
        self.merge_local_heads(m);
        let record_input = self.root_record_input(m);
        let result = (|| -> anyhow::Result<()> {
            let poll = {
                let member = &mut self.fx.hive.members[m];
                member.adapter.poll(&member.core)?
            };
            self.deliver(m, poll, false)?;
            self.fx.hive.members[m].adapter.before_sync()?;
            self.observe_workspace_fixups(m);
            if self.fx.hive.members[m]
                .adapter
                .repo()
                .pending_drops()
                .is_empty()
            {
                self.workspace_trim_inputs.remove(&m);
            }
            let mut adopted = false;
            for _ in 0..64 {
                if adopted && !self.behind_hub(m) {
                    return Ok(());
                }
                let member = &mut self.fx.hive.members[m];
                match member.core.step(&mut member.adapter)? {
                    Step::Adopted => adopted = true,
                    Step::Send(requests) => {
                        for request in requests {
                            self.deliver(m, request, false)?;
                        }
                    }
                    Step::Realized(_) | Step::Merged => {}
                    step => anyhow::bail!("{step:?} before taking the records"),
                }
            }
            anyhow::bail!("never took the records and realized the hub's head")
        })();
        self.finish_root_record_input(m, record_input);
        if let Err(err) = result {
            self.fail(&format!("{} taking records: {err:#}", self.machine(m)));
        }
        self.record_merges(m);
    }

    /// From a hive of four, a merge the hub accepted that one machine drops, another keeps,
    /// and a third took the drop of without advancing, before the hub went back and the
    /// keeper published it again: what survives of it is two operations, neither below the
    /// other (`races::history`, `Survivors::Apart`). Alpha commits work and delta takes it;
    /// the hub goes back, and gamma commits separate work; delta merges without publishing, and
    /// alpha's merge of them, which gamma keeps, is accepted. Alpha abandons its merge alone,
    /// and publishes that; beta, with `work` of its own (files it commits), takes the record
    /// and realizes the hub's head, then restarts. The hub goes back to gamma's work, losing the
    /// record, and gamma publishes the merge again. An hour passes after each time the hub goes
    /// back, so that it prunes as soon as every machine has taken its records. Returns it.
    pub fn hold_dropped_merge(&mut self, work: &[usize]) -> OpId {
        assert_eq!(self.nodes(), 4);
        let base = self.hub_seq();
        for &file in work {
            self.commit(1, 0, file);
        }
        self.commit(0, 0, 0);
        self.sync(0);
        self.sync(3);
        self.hub_goes_back(usize::try_from(self.hub_seq() - base).unwrap());
        self.an_hour_passes();
        self.commit(2, 0, 1);
        self.sync(2);
        let q = self.hub_seq();
        self.sync_realizing(3, usize::MAX);
        self.sync(0);
        let ours = self.fx.hive.hub_head();
        self.sync(2);
        self.sync(3);
        let both = self.fx.hive.hub_head();
        self.sync(0);
        self.jj(0, &["describe", "-m", "after survivor merge"]);
        self.sync(0);
        let (theirs, kept) = {
            let node = self.fx.node(0);
            let parents = node
                .canonical_store()
                .parents(&CanonicalOp(both.clone()))
                .unwrap();
            if parents.len() != 2 || !parents.contains(&CanonicalOp(ours.clone())) {
                self.fail(&format!("the merge of both isn't on alpha's: {parents:?}"));
            }
            let node = self.fx.node(0);
            let theirs = parents.into_iter().find(|op| op.0 != ours).unwrap();
            let local = |op: &CanonicalOp| node.local_of(op).unwrap().0.hex();
            (local(&theirs), local(&CanonicalOp(ours.clone())))
        };
        // Only alpha's merge: delta's has both its parents.
        self.abandon_ops(0, &format!("{theirs}..{kept}"), std::slice::from_ref(&kept));
        self.sync(0);
        if self.fx.hive.hub.store().record_count() != 1 {
            self.fail("alpha's abandon was not published");
        }
        self.sync_taking(1);
        self.restart(1);
        self.hub_goes_back(usize::try_from(self.hub_seq() - q).unwrap());
        self.an_hour_passes();
        self.sync(2);
        if self.fx.hive.hub_head() != ours {
            self.fail("gamma did not publish the dropped merge again");
        }
        ours
    }

    /// Machine `m` alone published the drop of `kept`: the hub dropped it, and `m` merged
    /// what survives of it with its own work, three operations, in one operation.
    pub fn check_dropped_by(&mut self, m: usize, kept: &OpId) {
        if !self.fx.hive.hub.is_dropped(kept, &[]).unwrap() {
            self.fail(&format!(
                "{} did not publish the drop of the merge",
                self.machine(m)
            ));
        }
        let merges = self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-T",
                r#"if(parents.len() == 3, description.first_line() ++ "\n")"#,
            ],
        );
        if !merges
            .lines()
            .any(|d| d == "reconcile divergent operations")
        {
            self.fail(&format!(
                "{} did not merge what survives with its work at once",
                self.machine(m)
            ));
        }
    }

    fn try_sync_partial(
        &mut self,
        m: usize,
        steps: usize,
        lose: Option<usize>,
        realizing: Option<usize>,
    ) -> anyhow::Result<()> {
        let input = self.root_record_input(m);
        let result = self.try_sync_partial_inner(m, steps, lose, realizing);
        self.finish_root_record_input(m, input);
        result
    }

    fn try_sync_partial_inner(
        &mut self,
        m: usize,
        steps: usize,
        lose: Option<usize>,
        realizing: Option<usize>,
    ) -> anyhow::Result<()> {
        let mut sent = 0;
        let mut deliver = |world: &mut Self, request| {
            let lost = lose == Some(sent);
            sent += 1;
            world.deliver(m, request, lost)
        };
        // Polled first, as the daemon does (`Driver::sync`).
        let poll = {
            let member = &mut self.fx.hive.members[m];
            member.adapter.poll(&member.core)?
        };
        deliver(self, poll)?;
        self.fx.hive.members[m].adapter.before_sync()?;
        self.observe_workspace_fixups(m);
        if self.fx.hive.members[m]
            .adapter
            .repo()
            .pending_drops()
            .is_empty()
        {
            self.workspace_trim_inputs.remove(&m);
        }
        let mut realized = 0;
        for _ in 0..steps {
            let member = &mut self.fx.hive.members[m];
            match member.core.step(&mut member.adapter)? {
                Step::Idle => break,
                Step::Send(requests) => {
                    for request in requests {
                        deliver(self, request)?;
                    }
                }
                Step::Realized(_) => {
                    realized += 1;
                    if realizing == Some(realized) {
                        break;
                    }
                }
                // Advancing finishes writing what was realized.
                Step::Advanced(_) if realizing.is_some() => break,
                Step::Superseded { push, .. } => deliver(self, push)?,
                Step::Merged | Step::Advanced(_) | Step::Adopted => {}
            }
        }
        Ok(())
    }

    /// Delivers a request to the hub, which then prunes if it can, and its reply back (unless
    /// lost), then any new head to every node, as `Hive` does.
    fn deliver(
        &mut self,
        m: usize,
        request: Request<OpId, Attachment>,
        lost: bool,
    ) -> anyhow::Result<()> {
        let hive = &mut self.fx.hive;
        let handled = hive.handle(request)?;
        if !lost {
            let member = &mut hive.members[m];
            member
                .core
                .handle_reply(&mut member.adapter, handled.reply)?;
        }
        if let Some((seq, head, records)) = handled.publish {
            for member in &mut hive.members {
                let notify = Reply::Head {
                    kind: HeadKind::Notify,
                    seq,
                    head: head.clone(),
                    records: records.clone(),
                };
                member.core.handle(&mut member.adapter, notify)?;
            }
        }
        Ok(())
    }

    /// Forgets node `m`'s volatile protocol state.
    pub fn restart(&mut self, m: usize) {
        self.record(format!("{}: restart", self.machine(m)));
        self.fx.hive.restart(m);
    }

    /// Crashes the hub, which reopens its store.
    pub fn restart_hub(&mut self) {
        if self.fx.hive.hub.store().pruned() > 0 {
            fired("restart_hub:after_prune");
        }
        self.record("hub: restart".to_owned());
        self.restarted_since_prune = true;
        if let Err(err) = self.fx.hive.restart_hub() {
            self.fail(&format!("restarting the hub: {err:#}"));
        }
    }

    /// Whether a power cut can send the hub back: it accepted a head since the one it wrote
    /// its log whole at.
    pub fn hub_can_go_back(&self) -> bool {
        self.hub_seq() > self.fx.hive.oldest_head()
    }

    pub fn hub_seq(&self) -> u64 {
        self.fx.hive.hub.store().head().0
    }

    /// Has the hub lose its last `lost` heads, but not its root, as a power cut can make
    /// it, and restarts it.
    pub fn hub_goes_back(&mut self, lost: usize) {
        if self.fx.hive.hub.store().pruned() > 0 {
            fired("hub_goes_back:after_prune");
        }
        self.record(format!("hub: goes back {lost}"));
        self.restarted_since_prune = true;
        let seq = self
            .hub_seq()
            .saturating_sub(lost as u64)
            .max(self.fx.hive.oldest_head());
        if let Err(err) = self.fx.hive.hub_goes_back(seq) {
            self.fail(&format!("restarting the hub: {err:#}"));
        }
    }

    /// Whether the hub has pruned its records since it last restarted.
    pub fn hub_pruned_since_restart(&self) -> bool {
        self.fx.hive.pruned_since_restart()
    }

    /// Has the hub lose the `heads` log its latest prune wrote, and everything after it, as a
    /// power cut just after the prune can make it, and restarts it: it names the records it
    /// pruned again.
    pub fn hub_loses_prune(&mut self) {
        self.record("hub: loses its prune".to_owned());
        self.restarted_since_prune = true;
        match self.fx.hive.hub_loses_prune() {
            Ok(true) => {}
            Ok(false) => self.fail("the hub had no prune to lose"),
            Err(err) => self.fail(&format!("restarting the hub: {err:#}")),
        }
    }

    /// Moves the hub's clock on an hour ([`WAIT_AFTER_OPENING`]).
    pub fn an_hour_passes(&mut self) {
        self.record("hub: an hour passes".to_owned());
        self.fx.hive.hub.age(WAIT_AFTER_OPENING);
    }

    /// Makes the hive again, empty, as a hub does whose store is corrupt.
    pub fn remake_hub(&mut self) {
        if self.fx.hive.hub.store().pruned() > 0 {
            fired("remake_hub:after_prune");
        }
        if self
            .fx
            .hive
            .members
            .iter()
            .any(|member| member.adapter.repo().record_prefix().count > 0)
        {
            fired("remake_hub:joiner_with_prefix");
        }
        self.record("hub: made again".to_owned());
        if let Err(err) = self.fx.hive.remake_hub() {
            self.fail(&format!("making the hive again: {err:#}"));
        }
    }

    /// Notes, for coverage, what the hub did about pruning during a sync that started with
    /// `before` of its records pruned: whether it pruned, and did so for the first time since it
    /// restarted, which it does only once an hour has passed; and whether a copy the hive forgot
    /// had taken what it pruned; or, if not, whether a copy the hive shows that hasn't said it
    /// took the hub's records held it back, where another had.
    fn note_pruning(&mut self, before: usize) {
        let hub = &self.fx.hive.hub;
        let pruned = hub.store().pruned();
        let shown = self.fx.shown_machines();
        let keys: Vec<String> = (0..self.nodes()).map(|m| self.fx.machine_key(m)).collect();
        if pruned > before {
            fired("prune");
            if std::mem::take(&mut self.restarted_since_prune) {
                fired("prune:after_restart");
            }
            self.trace
                .push(format!("hub: pruned the first {pruned} records"));
            for (m, key) in keys.iter().enumerate() {
                if shown.contains(key) {
                    continue;
                }
                let (taken, _) = self.fx.hive.members[m].adapter.repo().record_state();
                fired(if taken < pruned as u64 {
                    "prune:forgotten_behind"
                } else {
                    "prune:forgotten_took"
                });
            }
        } else if !hub.store().records().is_empty() {
            let records = hub.records();
            let reported = |key: &String| hub.reported(key).as_ref() == Some(&records);
            if keys.iter().any(reported)
                && keys.iter().any(|key| shown.contains(key) && !reported(key))
            {
                fired("prune:held_back");
            }
        }
    }

    /// If `err`, from node `m`'s `what`, is its stop behind records the hub pruned, checks
    /// that it is expected, and recovers from it as a user would, and returns true. It is
    /// expected only of a copy the hub did not wait for at the actual prune and which lacks
    /// that exact count and digest. A later indirect push can make that copy present again.
    /// The user makes a new copy with `musubi clone`,
    /// and runs `musubi leave --force` in this one, which tells the hive nothing and keeps all
    /// it has (docs/troubleshooting.md): this one stays on its machine, out of the hive, and
    /// out of the checks. Whatever it did since its last sync never reached the hive, and the
    /// user brings none of it across.
    fn stopped_behind_prune(&mut self, m: usize, what: &str, err: &anyhow::Error) -> bool {
        let stopped = err.chain().any(|e| {
            matches!(
                e.downcast_ref::<NodeError>(),
                Some(NodeError::PrunedRecords)
            )
        });
        if !stopped {
            return false;
        }
        let pruned = self.fx.hive.hub.pruned();
        let key = self.fx.machine_key(m);
        let observation = self
            .fx
            .hive
            .prunes
            .iter()
            .rev()
            .find(|prune| prune.records == pruned);
        let excluded = observation.is_some_and(|prune| {
            !prune.present.contains(&key)
                && (prune.known.contains(&key) || !prune.reported.contains_key(&key))
        });
        let prefix = musubi_jj::records::RecordPrefix {
            count: pruned.count,
            digest: musubi_jj::records::RecordDigest::from_bytes(&pruned.digest),
        };
        let repo = self.fx.hive.members[m].adapter.repo();
        let missing = repo.held_records(&prefix).is_none();
        if !excluded || !missing {
            self.fail(&format!(
                "{what} of {} refused pruned records {pruned:?}: excluded at prune={excluded}, lacks exact chain={missing}: {err:#}",
                self.machine(m),
            ));
        }
        fired("prune:stopped");
        self.record(format!(
            "{}: {what} stopped behind records the hub pruned; musubi leave --force",
            self.machine(m)
        ));
        self.clone_copy(m);
        true
    }

    /// The `merge_key` of every operation of the hub's history.
    fn hub_merge_keys(&self) -> BTreeSet<String> {
        let store = self.fx.hive.hub.store();
        let canonical = store.canonical();
        let head = CanonicalOp(store.head().1.clone());
        canonical
            .ancestors_until(&[head], |_| false)
            .unwrap()
            .iter()
            .map(|op| merge_key(&canonical.read_operation(op).unwrap()))
            .collect()
    }

    /// A new copy of the hive on machine `m`, as `musubi clone` makes: an empty colocated
    /// repository at a path of its own, with the machine's jj config, joined to the hive on
    /// the root and synced, then on its local `trunk()`. A new machine's, if `m` is `nodes()`, or
    /// else in place of machine `m`'s copy, which has left the hive.
    pub fn clone_copy(&mut self, m: usize) {
        let n = self.next();
        let repo = if m == self.nodes() {
            let machine = MACHINES[m];
            let hostname = match self.naming {
                Naming::SharedHostname => "mac",
                Naming::Own | Naming::Default => machine,
            };
            self.fx.env.init_repo_with_hostname(machine, hostname)
        } else {
            let path = self
                .fx
                .env
                .root()
                .join(format!("{}-copy{n}", self.machine(m)));
            let repo = self.fx.repo(m).another_copy(&path);
            fs::create_dir_all(&path).unwrap();
            repo.jj(&["git", "init", "--colocate"]);
            repo
        };
        // Remotes stay local. Model the user configuring this new copy for Git access,
        // so fetch/push rules continue to cover newly joined and replacement copies.
        repo.jj(&[
            "git",
            "remote",
            "add",
            "origin",
            self.origin.bare.to_str().unwrap(),
        ]);
        if self.fx.hive.hub.store().pruned() > 0 {
            fired("join:after_prune");
        }
        self.record(format!(
            "{}: musubi clone into {}",
            self.machine(m),
            repo.path().display()
        ));
        let own: BTreeSet<String> = repo
            .jj(&["op", "log", "--no-graph", "-T", OP_KEY_TEMPLATE])
            .lines()
            .map(without_op_ids)
            .collect();
        let join_point = native_head(&repo);
        self.fx.add(repo);
        let node = self.fx.hive.members.last().unwrap().adapter.repo();
        let joined = node.canonical_of(&LocalOp(join_point.clone())).unwrap();
        let join_key = merge_key(&node.canonical_store().read_operation(&joined).unwrap());
        let store = node.loader().op_store();
        let joined_from = futures::executor::block_on(store.read_operation(&join_point)).unwrap();
        let join_bindings = futures::executor::block_on(store.read_view(&joined_from.view_id))
            .unwrap()
            .wc_commit_ids
            .into_iter()
            .map(|(name, target)| {
                (
                    format!("{}/{}", node.machine().key(), name.as_str()),
                    target,
                )
            })
            .collect();
        let join_point = join_fingerprint(&joined_from);
        let primary = vec![Workspace {
            name: "default".to_owned(),
            path: None,
        }];
        if m < self.dirty.len() {
            self.fx.repos.swap_remove(m);
            self.fx.hive.members.swap_remove(m);
            self.dirty[m] = false;
            self.workspaces[m] = primary;
            self.seen[m] = None;
            // Its abandons that never reached the hive, whose operations the hub or another
            // machine still has, are gone with it; the rest stay checked.
            let mut others: Vec<BTreeSet<String>> = (0..self.nodes())
                .filter(|&o| o != m)
                .map(|o| self.merge_keys(o))
                .collect();
            others.push(self.hub_merge_keys());
            self.abandoned.retain(|(by, _, merge)| {
                *by != m || !others.iter().any(|keys| keys.contains(merge))
            });
        } else {
            self.dirty.push(false);
            self.workspaces.push(primary);
            self.seen.push(None);
            self.baseline_ids.push(BTreeSet::new());
            self.baseline_keys.push(BTreeSet::new());
            self.join_points.push(join_point.clone());
        }
        self.join_points[m] = join_point;
        self.logical_extras.resize_with(self.nodes(), BTreeSet::new);
        self.logical_extras[m].clear();
        for ws in &self.workspaces[m] {
            let key = format!("{}/{}", self.fx.machine_key(m), ws.name);
            self.workspace_births.insert(key.clone());
            self.initial_workspace_keys.insert(key);
        }
        self.workspace_joins.insert(join_key, join_bindings);
        self.baseline_merge_keys.extend(self.merge_keys(m));
        self.operation_sources.retain(|(copy, _), _| *copy != m);
        self.workspace_trim_inputs.remove(&m);
        self.operation_seen.resize_with(self.nodes(), BTreeSet::new);
        self.operation_seen[m].clear();
        self.sync_counted(m);
        // The hive's history from before it was set up, and its own from before it joined,
        // are its baseline, as each machine's are. It may have only some of the hive's yet,
        // as from a hive made again, which the machines that have it fill again later.
        let keys: BTreeSet<String> = own.union(&self.hive_baseline).cloned().collect();
        self.baseline_ids[m] = self
            .op_ids_and_keys(m, None)
            .into_iter()
            .filter(|(_, key)| keys.contains(key))
            .map(|(id, _)| id)
            .collect();
        self.baseline_keys[m] = keys;
        self.restart_imports(m);
        // As `musubi clone` checks out the destination's local `trunk()`.
        let trunk = self.raw_jj(
            m,
            &[
                "log",
                "--ignore-working-copy",
                "--no-graph",
                "-n1",
                "-r",
                "trunk() ~ root()",
                "-T",
                "commit_id",
            ],
        );
        if !trunk.is_empty() {
            self.jj(m, &["new", &trunk]);
        }
    }

    /// Whether machine `m`'s git has the `origin` remote: configured explicitly for each machine,
    /// including a new copy before it joins.
    pub fn has_origin(&self, m: usize) -> bool {
        self.fx
            .repo(m)
            .git(&["remote"])
            .lines()
            .any(|r| r == "origin")
    }

    /// Takes an operation machine `m` abandoned that a `jj` command there brought back into its
    /// history, absent before it, for jj's doing, not musubi's, which runs no command: with
    /// auto-update-stale, a command in a workspace whose working copy recorded an operation
    /// `jj op abandon` rewrote brings back what it abandoned, as on one machine
    /// (docs/internals/races.md, "Known jj limitations"). jj leaves a working copy so where
    /// the abandon ran in another workspace, or where an operation came after its last
    /// command, as musubi's do. `before` is `abandoned_present` from before the command.
    fn forgive_jj_returns(&mut self, m: usize, before: Option<BTreeSet<String>>) {
        let Some(before) = before else {
            return;
        };
        let keys: BTreeSet<_> = self.replicated_history(m).into_values().collect();
        let count = self.abandoned.len();
        self.abandoned
            .retain(|(by, _, merge)| *by != m || before.contains(merge) || !keys.contains(merge));
        if self.abandoned.len() < count {
            self.record("  (jj brought back an operation it abandoned)".to_owned());
        }
    }

    /// What `forgive_jj_returns` needs before a `jj` command on machine `m`: if `m` abandoned
    /// anything, the keys of what is in its history now.
    fn abandoned_present(&self, m: usize) -> Option<BTreeSet<String>> {
        self.abandoned
            .iter()
            .any(|(by, ..)| *by == m)
            .then(|| self.replicated_history(m).into_values().collect())
    }

    /// The `merge_key` of every operation in machine `m`'s history, read in process: a `jj`
    /// command could merge op heads.
    fn merge_keys(&self, m: usize) -> BTreeSet<String> {
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let root = store.root_operation_id().clone();
        let mut keys = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut stack: Vec<jj_lib::op_store::OperationId> = self
            .op_heads(m)
            .iter()
            .map(|hex| jj_lib::op_store::OperationId::try_from_hex(hex).unwrap())
            .collect();
        while let Some(id) = stack.pop() {
            if id == root || !seen.insert(id.clone()) {
                continue;
            }
            let Ok(op) = futures::executor::block_on(store.read_operation(&id)) else {
                continue;
            };
            keys.insert(merge_key(&op));
            stack.extend(op.parents.iter().cloned());
        }
        keys
    }

    /// Machine `m` runs `jj op abandon` of its native operation `op`.
    pub fn op_abandon(&mut self, m: usize, op: &str) {
        self.abandon_ops(m, op, &[op.to_owned()]);
    }

    /// Publishes new work, pauses before advancing the base to that push, then trims all
    /// history below it. Unlike single-operation abandonment, this can drop the old base
    /// and every join while keeping an accepted operation outside the base's ancestry.
    pub fn trim_below_accepted_push(&mut self, m: usize) {
        self.sync(m);
        let (base, dropped) = self.trim_range(m);
        let description = self.message(m);
        // A fresh child works even when a cloned workspace is at an immutable commit.
        self.jj(m, &["new", "-m", &description]);
        self.sync_partial(m, 1, None);
        self.abandon_ops(m, &format!("..{base}"), &dropped);
        self.sync(m);
    }

    /// Accept a forget, keep the old saved base, then trim both beneath unpublished work.
    /// If the other copy is already forgotten, this also reaches a newer saved base with
    /// an older accepted own push, without manufacturing adapter state.
    pub fn trim_below_accepted_forget(&mut self, m: usize, other: usize) {
        self.sync(m);
        self.forget_copy(m, other);
        self.sync_partial(m, 1, None);
        let (base, dropped) = self.trim_range(m);
        let description = self.message(m);
        self.jj(m, &["new", "-m", &description]);
        self.abandon_ops(m, &format!("..{base}"), &dropped);
        self.sync(m);
    }

    fn trim_range(&self, m: usize) -> (String, Vec<String>) {
        let history = self.op_ids_and_keys(m, None);
        let base = history[0].0.clone();
        let root = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .root_operation_id()
            .hex();
        let dropped = history
            .into_iter()
            .map(|(id, _)| id)
            .filter(|id| *id != root)
            .collect();
        (base, dropped)
    }

    /// `jj op abandon` of `spec` on machine `m`: one operation, or a range `x..y`, which drops
    /// the native operations `dropped`. An operation with another reachable local version
    /// has not been removed from the replicated history.
    pub fn abandon_ops(&mut self, m: usize, spec: &str, dropped: &[String]) {
        self.begin_workspace_trim(m);
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let dropped: Vec<(String, String)> = dropped
            .iter()
            .map(|op| {
                let at = jj_lib::op_store::OperationId::try_from_hex(op).unwrap();
                let op_store = futures::executor::block_on(store.read_operation(&at)).unwrap();
                (self.op_key(m, op), merge_key(&op_store))
            })
            .collect();
        // Every survivor keeps its view when jj changes its parents, including commands
        // and internal fix-ups with one parent. Pin that independent source for the reference.
        let before = self.ops_by_key(m);
        self.jj(m, &["op", "abandon", spec]);
        let after = self.ops_by_key(m);
        for (key, old) in &before {
            // Only a key one operation had before, and has after: operations sharing a key,
            // as two merges a node makes at one tick of its clock can, can't be told apart,
            // and stay jj's merges of their parents.
            let (Some(old), Some(new)) = (single(Some(old)), single(after.get(key))) else {
                continue;
            };
            if old == new {
                continue;
            }
            let id = jj_lib::op_store::OperationId::try_from_hex(old).unwrap();
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            let replaced = self.retained_source(m, &op);
            self.remember_retained(key.clone(), replaced);
        }
        let retained: BTreeSet<_> = self.replicated_history(m).into_values().collect();
        for (key, merge) in dropped {
            // Native abandonment of one physical alias can leave another reachable.
            // The logical operation remains part of the history in that case.
            if !retained.contains(&merge) {
                self.abandoned.push((m, key, merge));
            }
        }
    }

    fn begin_workspace_trim(&mut self, m: usize) {
        self.observe_operation_sources(m);
        self.finish_workspace_trim(m);
        if !self.workspace_trim_inputs.contains_key(&m) {
            let node = self.fx.hive.members[m].adapter.repo();
            let seen: BTreeSet<_> = fs::read_dir(node.repo_path().join("op_store/operations"))
                .unwrap()
                .map(|file| file.unwrap())
                .filter_map(|file| file.file_name().to_str().and_then(OpId::try_from_hex))
                .collect();
            let store = node.loader().op_store();
            let before = seen
                .iter()
                .map(|id| futures::executor::block_on(store.read_operation(id)).unwrap())
                .filter(|op| op.metadata.attributes.contains_key("musubi.fixup"))
                .map(|op| merge_key(&op))
                .collect();
            self.workspace_trim_inputs.insert(
                m,
                WorkspaceTrim {
                    copy: self.fx.machine_key(m),
                    input: CanonicalOp(self.fx.hive.members[m].core.known().1.clone()),
                    wrote_fixup: false,
                    seen,
                    before,
                },
            );
        }
    }

    /// Machine `m`'s operations by `merge_key`, with their ids: more than one where
    /// operations share a key, as two merges a node makes at one tick of its clock can.
    fn ops_by_key(&self, m: usize) -> BTreeMap<String, BTreeSet<String>> {
        let template = format!(r#"{MERGE_KEY_TEMPLATE} ++ "\t" ++ id ++ "\n""#);
        self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-T",
                &template,
            ],
        )
        .lines()
        .filter_map(|line| line.rsplit_once('\t'))
        .fold(BTreeMap::new(), |mut merges, (key, id)| {
            merges
                .entry(key.to_owned())
                .or_insert_with(BTreeSet::new)
                .insert(id.to_owned());
            merges
        })
    }

    /// The key of machine `m`'s operation `op`, as `op_keys` has it.
    pub fn op_key(&self, m: usize, op: &str) -> String {
        let key = self.raw_jj(
            m,
            &[
                "--at-op",
                op,
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                OP_KEY_TEMPLATE,
            ],
        );
        without_op_ids(key.trim_end_matches('\n'))
    }

    /// Crashes node `m`'s daemon: it reopens the repository, losing every in-memory cache,
    /// and with `lose_cache` also the on-disk translation cache. The realizations it was
    /// still writing stay unrecorded, and those `stopped` picks, by bit, lose their operation
    /// files, as if it crashed between a view and its operation. Returns how many it was
    /// writing.
    pub fn crash(&mut self, m: usize, lose_cache: bool, stopped: u64) -> usize {
        let in_flight = self.fx.hive.members[m]
            .adapter
            .repo_mut()
            .crash_before_settling();
        let stopped: Vec<_> = in_flight
            .iter()
            .enumerate()
            .filter(|(i, _)| (stopped >> (i % 64)) & 1 == 1)
            .map(|(_, local)| local)
            .collect();
        self.record(format!(
            "{}: crash{}{}",
            self.machine(m),
            if in_flight.is_empty() {
                String::new()
            } else {
                format!(
                    ", writing {} operations, {} stopped before their files",
                    in_flight.len(),
                    stopped.len()
                )
            },
            if lose_cache {
                ", losing the translation cache"
            } else {
                ""
            }
        ));
        let repo = self.fx.repo(m);
        for local in stopped {
            let path = repo
                .repo_path()
                .join("op_store/operations")
                .join(local.0.hex());
            if path.exists() {
                fs::remove_file(path).unwrap();
            }
        }
        if lose_cache {
            let path = repo.repo_path().join("musubi/translation");
            if path.exists() {
                fs::remove_file(path).unwrap();
            }
        }
        self.fx.reopen(m);
        self.touched.insert(m);
        in_flight.len()
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

    /// The replicated portion of the native history, stopping at this copy's join point.
    /// A native abandon can reparent a join point above shared history; its parents are
    /// still private, even if some of those operations once belonged to the hive.
    pub fn op_keys(&self, m: usize) -> BTreeSet<String> {
        let history = self.replicated_history(m);
        self.op_ids_and_keys(m, None)
            .into_iter()
            .filter(|(id, _)| history.contains_key(&OpId::try_from_hex(id).unwrap()))
            .map(|(_, key)| key)
            .collect()
    }

    /// Native ids and merge keys above the independently observed join boundary.
    fn replicated_history(&self, m: usize) -> BTreeMap<OpId, String> {
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let mut pending = self.fx.hive.members[m]
            .adapter
            .repo()
            .local_heads()
            .unwrap();
        let mut history = BTreeMap::new();
        while let Some(local) = pending.pop() {
            if history.contains_key(&local.0) {
                continue;
            }
            let op = futures::executor::block_on(store.read_operation(&local.0)).unwrap();
            history.insert(local.0, merge_key(&op));
            if join_fingerprint(&op) != self.join_points[m] {
                pending.extend(op.parents.into_iter().map(LocalOp));
            }
        }
        history
    }

    // Workspaces.

    /// Each workspace's working-copy commit on machine `m`, by name.
    pub fn working_copies(&self, m: usize) -> BTreeMap<String, String> {
        self.workspaces[m]
            .iter()
            .map(|ws| ws.name.clone())
            .chain(self.logical_extras[m].iter().cloned())
            .map(|name| {
                let id = self.raw_jj(
                    m,
                    &[
                        "log",
                        "--ignore-working-copy",
                        "--no-graph",
                        "-r",
                        &format!("{name}@"),
                        "-T",
                        "commit_id",
                    ],
                );
                (name, id)
            })
            .collect()
    }

    /// Workspace names from the pool that machine `m` does not use.
    pub fn free_workspace_names(&self, m: usize) -> Vec<String> {
        let mut pool: Vec<String> = WORKSPACES.iter().map(|w| (*w).to_owned()).collect();
        pool.push(self.machine(m).to_owned());
        // Operation preconditions use jj's actual occupied names. Certification of those
        // names remains a separate invariant, so this never authorizes a spurious name.
        let occupied = self.raw_jj(
            m,
            &[
                "workspace",
                "list",
                "--ignore-working-copy",
                "-T",
                "name ++ \"\\n\"",
            ],
        );
        pool.into_iter()
            .filter(|name| !occupied.lines().any(|used| used == name))
            .collect()
    }

    /// Other machines' workspaces as machine `m` shows them, `machine/workspace`.
    pub fn foreign_workspace_names(&self, m: usize) -> Vec<String> {
        self.raw_jj(
            m,
            &[
                "workspace",
                "list",
                "--ignore-working-copy",
                "-T",
                "name ++ \"\\n\"",
            ],
        )
        .lines()
        .filter(|name| name.contains('/'))
        .map(str::to_owned)
        .collect()
    }

    pub fn add_workspace(&mut self, m: usize, name: &str) {
        self.workspace_births
            .insert(format!("{}/{name}", self.fx.machine_key(m)));
        let n = self.next();
        let path = self
            .fx
            .env
            .root()
            .join(format!("{}-ws{n}", self.machine(m)));
        self.jj(
            m,
            &["workspace", "add", "--name", name, path.to_str().unwrap()],
        );
        self.workspaces[m].push(Workspace {
            name: name.to_owned(),
            path: Some(path),
        });
    }

    pub fn rename_workspace(&mut self, m: usize, ws: usize, name: &str) {
        self.workspace_births
            .insert(format!("{}/{name}", self.fx.machine_key(m)));
        self.logical_extras[m].remove(&self.workspaces[m][ws].name);
        self.jj_in(m, ws, &["workspace", "rename", name]);
        self.workspaces[m][ws].name = name.to_owned();
    }

    pub fn forget_workspace(&mut self, m: usize, ws: usize) {
        let name = self.workspaces[m][ws].name.clone();
        self.jj(m, &["workspace", "forget", &name]);
        self.logical_extras[m].remove(&name);
        self.workspaces[m].remove(ws);
    }
}

/// An operation's key without the operation ids its description names, as in "undo:
/// restore to operation <id>": musubi translates those to each machine's own ids.
fn without_op_ids(key: &str) -> String {
    for marker in ["restore to operation ", "revert operation "] {
        if let Some(at) = key.find(marker) {
            let start = at + marker.len();
            let end = key[start..]
                .find(|c: char| !c.is_ascii_hexdigit())
                .map_or(key.len(), |len| start + len);
            return format!("{}<op>{}", &key[..start], &key[end..]);
        }
    }
    key.to_owned()
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
    let native: BTreeSet<_> = world.workspace_fixup_inputs.keys().cloned().collect();
    assert!(!native.is_empty(), "the trim must create native fix-ups");
    assert!(!world.workspace_trim_inputs.contains_key(&0));
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
    world.workspace_fixup_inputs.clear();
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
    assert!(!world.workspace_fixup_inputs.contains_key(&old_key));

    // Lose the sender's witness, then give the receiver an older accepted baseline.
    // Receiving a marked realization must not turn that baseline into source evidence.
    world.workspace_fixup_inputs.clear();
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
    assert!(world.workspace_fixup_inputs.is_empty());
    assert!(!world.workspace_trim_inputs.contains_key(&1));
    world.begin_workspace_trim(1);
    world.clone_copy(1);
    assert!(!world.workspace_trim_inputs.contains_key(&1));
}

#[test]
fn root_record_inputs_distinguish_lost_work_from_an_opaque_prefix() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: true,
        secondary: false,
    });
    assert!(world.root_record_input(0).is_none());
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
    let input = world.root_record_input(0).unwrap();
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
        world.root_record_input(m).is_none(),
        "an opaque prefix is no lost applied suffix"
    );
}

#[test]
fn retained_sources_do_not_infer_native_ownership_from_a_shared_hostname() {
    let world = World::new(Setup {
        nodes: 2,
        naming: Naming::SharedHostname,
        prejoin: false,
        secondary: false,
    });
    let mut checked = false;
    for m in 0..world.nodes() {
        let node = world.fx.hive.members[m].adapter.repo();
        let mut todo: Vec<_> = world
            .op_heads(m)
            .iter()
            .map(|s| OpId::try_from_hex(s).unwrap())
            .collect();
        let mut seen = BTreeSet::new();
        while let Some(id) = todo.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            let op =
                futures::executor::block_on(node.loader().op_store().read_operation(&id)).unwrap();
            todo.extend(op.parents.iter().cloned());
            if op.metadata.workspace_name.is_none()
                && op.metadata.hostname == "mac"
                && op
                    .metadata
                    .attributes
                    .get(musubi_jj::node::CANONICAL_ATTRIBUTE)
                    .and_then(OpId::try_from_hex)
                    .and_then(|id| node.canonical_store().read_operation(&CanonicalOp(id)).ok())
                    .is_some_and(|canonical| {
                        musubi_jj::presence::Kind::of(&canonical.metadata)
                            .work
                            .is_none()
                    })
            {
                let source = world.retained_source(m, &op);
                assert!(
                    !source.realized,
                    "the shared hostname cannot identify its maker"
                );
                assert!(
                    !source.native,
                    "a received marker supplies no native ownership"
                );
                assert_eq!(source.copy, world.fx.machine_key(m));
                checked = true;
            }
        }
    }
    assert!(
        checked,
        "the fixture must contain a marked merge on the other copy"
    );
}
