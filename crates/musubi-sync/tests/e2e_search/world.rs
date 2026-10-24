//! The world a generated sequence acts on: a hive of real colocated repositories sharing a
//! bare `origin`, plus what the test remembers about them, and every action a rule can
//! take. Every action is something a user, git, a remote, or the musubi daemon can do.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use jj_lib::object_id::ObjectId as _;
use musubi_core::hub;
use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::LocalRepo as _;
use musubi_core::node::Step;
use musubi_jj::node::NodeError;
use musubi_jj::node::NodeRepo;
use musubi_sync::Attachment;
use musubi_sync::OpId;
use musubi_sync::node::NodeAdapter;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

use crate::fixture::Fixture;
use crate::ledger::Ledger;
use crate::ledger::Seen;
use crate::origin::Origin;
use crate::view::TEMPLATE;
use crate::view::View;

/// Machine directories. Their hostnames are the same, unless the setup shares one.
pub const MACHINES: [&str; 3] = ["alpha", "beta", "gamma"];
/// Small pools, so that machines collide on names.
pub const BOOKMARKS: [&str; 3] = ["main", "feature", "topic"];
pub const TAGS: [&str; 2] = ["v1", "v2"];
pub const WORKSPACES: [&str; 4] = ["default", "work", "second", "third"];
/// Shared files, so that rebases and merges produce content conflicts.
pub const FILES: [&str; 3] = ["a.txt", "b.txt", "dir/c.txt"];

/// Operation metadata, which a realization shares with the operation it realizes, so it
/// identifies an operation across machines even though local ids differ.
const OP_KEY_TEMPLATE: &str = r#"time.start().format("%Y-%m-%dT%H:%M:%S%.f") ++ " " ++ time.end().format("%Y-%m-%dT%H:%M:%S%.f") ++ " " ++ user ++ " " ++ description.first_line() ++ "\n""#;

/// jj 0.46 cannot merge concurrent operations when one abandons (or moves away) a child of
/// the root that the other made a parent of a merge commit: the rebased merge would have
/// the root as a parent, which the git backend refuses, and every later command fails with
/// "Failed to load the repo" until the operations are dealt with by hand. That is jj's
/// behavior with or without musubi (`--at-op` on one machine reproduces it), so the search
/// stays clear of it:
///
/// - commits directly on the root are immutable, so every machine's work starts above its
///   initial working-copy commit;
/// - importing git refs does not abandon commits that became unreachable, which would
///   abandon root children (origin's first commit, pre-join work) regardless.
const JJ_CONFIG: &str = "
git.abandon-unreachable-commits = false
[revset-aliases]
\"immutable_heads()\" = \"builtin_immutable_heads() | root()+\"
";

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

/// How many operations a sequence may revert to get past jj failing to merge operations.
const MAX_UNMERGEABLE_REVERTS: usize = 10;

pub struct World {
    pub fx: Fixture,
    pub origin: Origin,
    /// Machines with file edits that no `jj` command has snapshotted yet.
    dirty: Vec<bool>,
    /// Each machine's workspaces; the first is the primary.
    pub workspaces: Vec<Vec<Workspace>>,
    /// Each machine's operation ids and keys once the hive was set up.
    baseline_ids: Vec<BTreeSet<String>>,
    pub baseline_keys: Vec<BTreeSet<String>>,
    /// What each machine saw at its op heads, when it last looked.
    seen: Vec<Option<(Vec<String>, Seen)>>,
    pub ledger: Ledger,
    /// Machines whose repository changed in ways no recorded command has loaded since.
    pub touched: BTreeSet<usize>,
    /// Operations reverted so far to get past jj's failure to merge operations.
    unmergeable_reverts: usize,
    /// Those operations, and the ones reverting them wrote, which reverting again would
    /// only undo the recovery: hex ids.
    recovery_ops: BTreeSet<String>,
    /// The change of every commit seen so far, for `fingerprint`.
    change_of: BTreeMap<String, String>,
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
                let config = env.root().join(format!("config-{machine}.toml"));
                let mut text = fs::read_to_string(&config).unwrap();
                text.push_str(JJ_CONFIG);
                fs::write(&config, text).unwrap();
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
        let workspaces = machines
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
        let fx = Fixture::join(env, repos);
        let mut world = Self {
            fx,
            origin,
            dirty: vec![false; setup.nodes],
            workspaces,
            baseline_ids: vec![],
            baseline_keys: vec![],
            seen: vec![None; setup.nodes],
            ledger: Ledger::default(),
            touched: BTreeSet::new(),
            unmergeable_reverts: 0,
            recovery_ops: BTreeSet::new(),
            change_of: BTreeMap::new(),
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
        let view = world.view_at_head(0);
        world.ledger.reset(&view);
        world
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
    /// commit ids, which depend on when jj made the commits, become change ids; operation
    /// ids are masked, and so is the test's directory.
    pub fn fingerprint(&self) -> String {
        let root = self.fx.env.root().to_string_lossy().into_owned();
        let mut out = String::new();
        for line in &self.trace {
            let line = line.replace(&root, "<root>");
            let words: Vec<String> = line
                .split(' ')
                .map(|word| match self.change_of.get(word) {
                    Some(change) => change.clone(),
                    None if word.len() >= 12 && word.chars().all(|c| c.is_ascii_hexdigit()) => {
                        "<id>".to_owned()
                    }
                    None => word.to_owned(),
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

    /// The view at machine `m`'s first op head, without perturbing anything.
    pub fn view_at_head(&self, m: usize) -> View {
        let head = self.op_heads(m).remove(0);
        self.view_at(m, &head)
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
        let before = self.seen(m);
        self.dirty[m] = false;
        let view =
            View::parse(&self.raw_jj(m, &["log", "--no-graph", "-r", "all()", "-T", TEMPLATE]));
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
        if let Err(err) = self.fx.node(m).forget_copy(&key, name) {
            self.fail(&format!(
                "musubi forget {name} failed on {}: {err}",
                self.machine(m)
            ));
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

    /// Machine `m`'s daemon, two hours on by its clock, forgets every other copy that has
    /// gone unused for longer than its `musubi.forget-after`. Records what changed.
    pub fn expire_idle(&mut self, m: usize) {
        let before = self.seen(m);
        self.record(format!(
            "{}: forget the copies unused two hours on",
            self.machine(m)
        ));
        let later = std::time::SystemTime::now() + std::time::Duration::from_secs(2 * 3600);
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
        let before = self.seen(m);
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
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        if !output.status.success() {
            if refusals.iter().any(|r| stderr.contains(r)) {
                let first = stderr.lines().next().unwrap_or("").to_owned();
                self.record(format!("  (refused: {first})"));
                return Err(stderr);
            }
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
        let heads_before = self.op_heads(m);
        let mut full = vec!["--at-op", op];
        full.extend_from_slice(args);
        self.record(format!(
            "{}: jj --at-op {} {}",
            self.machine(m),
            &op[..12],
            args.join(" ")
        ));
        let output = self.fx.repo(m).jj_output(&full);
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
    }

    /// Operations made since setup that machine `m` can run a command at, other than its
    /// current head. (`jj op log` merges concurrent operations first, like any command.)
    pub fn older_ops(&mut self, m: usize) -> Vec<String> {
        let out = self.jj(
            m,
            &["op", "log", "--no-graph", "-n", "8", "-T", "id ++ \"\\n\""],
        );
        out.lines()
            .skip(1)
            .filter(|id| !self.baseline_ids[m].contains(*id))
            .map(str::to_owned)
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
        let heads = self.op_heads(m);
        let template = "workspace_name";
        self.raw_jj(
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
        if let Err(err) = self.fx.hive.members[m].adapter.repo().merge_heads() {
            self.fail(&format!(
                "merging {}'s op heads failed: {err}",
                self.machine(m)
            ));
        }
        let after = self.seen(m);
        let what = format!("{}: merge own op heads before sync", self.machine(m));
        self.ledger.record(m, &what, &before, &after, false);
    }

    /// Lets node `m` poll the hub and run its policy until idle.
    pub fn sync(&mut self, m: usize) {
        self.record(format!("{}: sync", self.machine(m)));
        self.sync_counted(m);
    }

    /// Syncs node `m` until idle and returns how many steps it took.
    pub fn sync_counted(&mut self, m: usize) -> usize {
        self.touched.insert(m);
        self.merge_local_heads(m);
        let steps = loop {
            match self.fx.hive.sync(m) {
                Ok(steps) => break steps,
                Err(err) => self.recover_unmergeable(m, "sync", &err),
            }
        };
        self.record_merges(m);
        steps
    }

    /// Recovers from a sync of node `m` that failed because of a known jj limitation
    /// (docs/internals/races.md): jj can't merge this machine's operations with the hive's, so
    /// musubi pauses. Recovers as the error says, by reverting the newest of this machine's
    /// operations the hive doesn't have, other than the recovery's own: reverting a revert would
    /// put back what it reverted. Fails the case on any other error.
    fn recover_unmergeable(&mut self, m: usize, what: &str, err: &anyhow::Error) {
        let ours = err
            .chain()
            .find_map(|e| match e.downcast_ref::<NodeError>() {
                Some(NodeError::Unmergeable { ours, .. }) => Some(ours.clone()),
                _ => None,
            });
        let Some(ours) = ours else {
            self.fail(&format!("{what} of {} failed: {err:#}", self.machine(m)));
        };
        // As `can_undo` does, skip merges, which jj refuses to revert, and workspace
        // operations, which rewrite no commits, so they can't be what jj fails to merge, and
        // which strand a working copy when reverted.
        let ops = self.op_summaries(m);
        let op = ours.iter().map(|op| op.hex()).find(|op| {
            !self.recovery_ops.contains(op)
                && ops.get(op).is_some_and(|(parents, description)| {
                    *parents == 1 && !description.to_lowercase().contains("workspace")
                })
        });
        let Some(op) = op.filter(|_| self.unmergeable_reverts < MAX_UNMERGEABLE_REVERTS) else {
            self.fail(&format!(
                "{what} of {} keeps failing: {err:#}",
                self.machine(m)
            ));
        };
        self.unmergeable_reverts += 1;
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

    /// Records the commits node `m`'s merges made, after a sync.
    pub fn record_merges(&mut self, m: usize) {
        let after = self.seen(m);
        let what = format!("{}: merge by its node", self.machine(m));
        self.ledger.record_sync(m, &what, &after);
    }

    /// Lets node `m` poll the hub and take at most `steps` policy steps, delivering every
    /// request but losing the reply to request number `lose`: progress that stops partway,
    /// possibly after an upload but before the push.
    pub fn sync_partial(&mut self, m: usize, steps: usize, lose: Option<usize>) {
        self.touched.insert(m);
        self.record(format!(
            "{}: sync {steps} step(s){}",
            self.machine(m),
            lose.map(|d| format!(", losing reply {d}"))
                .unwrap_or_default()
        ));
        self.merge_local_heads(m);
        // Progress stops here either way: a partial sync that pauses has nothing to retry.
        if let Err(err) = self.try_sync_partial(m, steps, lose, None) {
            self.recover_unmergeable(m, "partial sync", &err);
        }
        self.record_merges(m);
    }

    /// Whether node `m` has yet to realize the hub's head.
    pub fn behind_hub(&self, m: usize) -> bool {
        let head = self.fx.hive.hub.store().head().1;
        self.fx.hive.members[m]
            .adapter
            .repo()
            .local_of(head)
            .is_none()
    }

    /// Lets node `m` sync until it has realized `count` operations, or has nothing more to
    /// realize, and stops there, with what it realized perhaps still being written.
    pub fn sync_realizing(&mut self, m: usize, count: usize) {
        self.touched.insert(m);
        self.record(format!(
            "{}: sync until {count} operation(s) realized",
            self.machine(m)
        ));
        self.merge_local_heads(m);
        if let Err(err) = self.try_sync_partial(m, usize::MAX, None, Some(count)) {
            self.recover_unmergeable(m, "partial sync", &err);
        }
        self.record_merges(m);
    }

    fn try_sync_partial(
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
        let poll = {
            let member = &mut self.fx.hive.members[m];
            member.adapter.heads()?;
            member.core.poll(&member.adapter)?
        };
        deliver(self, poll)?;
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
                Step::Merged | Step::Advanced(_) => {}
            }
        }
        Ok(())
    }

    /// Delivers a request to the hub and its reply back (unless lost), then any new head to
    /// every node, as `Hive` does.
    fn deliver(
        &mut self,
        m: usize,
        request: Request<OpId, Attachment>,
        lost: bool,
    ) -> anyhow::Result<()> {
        let hive = &mut self.fx.hive;
        let handled = hub::handle(&mut hive.hub, request)?;
        if !lost {
            let member = &mut hive.members[m];
            member
                .core
                .handle_reply(&mut member.adapter, handled.reply)?;
        }
        if let Some((seq, head)) = handled.publish {
            for member in &mut hive.members {
                let notify = Reply::Head {
                    kind: HeadKind::Notify,
                    seq,
                    head: head.clone(),
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
        self.record("hub: restart".to_owned());
        if let Err(err) = self.fx.hive.restart_hub() {
            self.fail(&format!("restarting the hub: {err:#}"));
        }
    }

    pub fn hub_seq(&self) -> u64 {
        self.fx.hive.hub.store().head().0
    }

    /// Has the hub lose its last `lost` heads, but not its root, as a power cut can make
    /// it, and restarts it.
    pub fn hub_goes_back(&mut self, lost: usize) {
        self.record(format!("hub: goes back {lost}"));
        let heads = self.fx.env.root().join("hub/heads");
        let text = fs::read_to_string(&heads).unwrap();
        let lines: Vec<&str> = text.lines().collect();
        let kept = lines.len().saturating_sub(lost).max(1);
        fs::write(&heads, lines[..kept].join("\n") + "\n").unwrap();
        if let Err(err) = self.fx.hive.restart_hub() {
            self.fail(&format!("restarting the hub: {err:#}"));
        }
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
                .join(local.hex());
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
        let node = match NodeRepo::open(&repo.repo_path(), &repo.settings()) {
            Ok(node) => node.with_repo_config(Some(repo.repo_config_path())),
            Err(err) => self.fail(&format!("reopening {}: {err}", self.machine(m))),
        };
        let adapter = NodeAdapter::new(node).unwrap();
        self.fx.hive.members[m].adapter = adapter;
        self.fx.hive.restart(m);
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

    pub fn op_keys(&self, m: usize) -> BTreeSet<String> {
        self.raw_jj(m, &["op", "log", "--no-graph", "-T", OP_KEY_TEMPLATE])
            .lines()
            .map(without_op_ids)
            .collect()
    }

    // Workspaces.

    /// Each workspace's working-copy commit on machine `m`, by name.
    pub fn working_copies(&self, m: usize) -> BTreeMap<String, String> {
        self.workspaces[m]
            .iter()
            .map(|ws| {
                let id = self.raw_jj(
                    m,
                    &[
                        "log",
                        "--ignore-working-copy",
                        "--no-graph",
                        "-r",
                        &format!("{}@", ws.name),
                        "-T",
                        "commit_id",
                    ],
                );
                (ws.name.clone(), id)
            })
            .collect()
    }

    /// Workspace names from the pool that machine `m` does not use.
    pub fn free_workspace_names(&self, m: usize) -> Vec<String> {
        let mut pool: Vec<String> = WORKSPACES.iter().map(|w| (*w).to_owned()).collect();
        pool.push(self.machine(m).to_owned());
        pool.into_iter()
            .filter(|name| !self.workspaces[m].iter().any(|ws| ws.name == *name))
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
        self.jj_in(m, ws, &["workspace", "rename", name]);
        self.workspaces[m][ws].name = name.to_owned();
    }

    pub fn forget_workspace(&mut self, m: usize, ws: usize) {
        let name = self.workspaces[m][ws].name.clone();
        self.jj(m, &["workspace", "forget", &name]);
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
