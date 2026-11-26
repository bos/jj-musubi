//! The state machine: what the user does on each machine, and what it must see.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::OnceLock;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::Instant;

use antithesis_sdk::assert_always;
use antithesis_sdk::assert_reachable;
use antithesis_sdk::assert_sometimes;
use hegel::TestCase;
use hegel::generators as gs;
use serde_json::json;

use crate::REPO;
use crate::remote;
use crate::remote::Outcome;

/// How long one jj command may take before the driver gives up on it.
const COMMAND: Duration = Duration::from_secs(30);
/// How many recent changes rules pick their targets from.
const POOL: usize = 48;
/// Bookmarks the user moves.
const BOOKMARKS: [&str; 4] = ["main", "b1", "b2", "b3"];
/// Files the user edits.
const FILES: usize = 6;
/// The secondary workspace each machine may have.
const WORKSPACE: &str = "/root/ws1";

/// A commit a command made, which every machine must come to have.
struct Created {
    commit: String,
    machine: usize,
    by: &'static str,
    /// When the command that made it was sent.
    issued: Instant,
}

pub struct Workload {
    pub hub: String,
    pub machines: Vec<String>,
    /// Held while a command runs on a machine: the user types one at a time there.
    busy: Vec<Mutex<()>>,
    next: AtomicU64,
    created: Mutex<Vec<Created>>,
    /// Recent change ids, newest last.
    changes: Mutex<VecDeque<String>>,
    /// Held by the eventually, so that only one runs.
    ending: Mutex<()>,
    /// Held to read by `edit_files`, to write by the eventually, which so waits for edits in
    /// flight and stops new ones: no file changes while it checks that syncing changes none.
    editing: std::sync::RwLock<()>,
    /// When the latest `jj op abandon` that may have taken effect finished. Commits from
    /// commands sent before then may have been in what it abandoned, and so may never leave
    /// their machine: only later ones must reach every machine.
    abandoned_until: Mutex<Option<Instant>>,
    /// Per machine, whether an abandon there was lost: it may still be running, and has
    /// finished once the next exclusive command there gets the machine's lock.
    abandon_pending: Mutex<Vec<bool>>,
    /// Operations reverted for a sync that listed them, so that none is tried twice.
    reverted: Mutex<BTreeSet<String>>,
    /// Whether the rare draw may start an eventually.
    eventually_drawn: bool,
    /// Start an eventually this long after the workload starts, whatever the draws say.
    eventually_after: Option<Duration>,
    started: OnceLock<Instant>,
}

/// What `musubi status` says about a copy.
#[derive(Debug, Clone, PartialEq)]
pub struct Status {
    pub head: String,
    pub sent: bool,
    pub running: bool,
    pub serving: bool,
    pub problem: String,
}

const STATUS_TEMPLATE: &str = r#"'"head=" ++ if(head, head, "none") ++ "\nsent=" ++ sent ++ "\nrunning=" ++ daemon_running ++ "\nserving=" ++ serving ++ "\nproblem=" ++ problem ++ "\n"'"#;

/// The status of the copy on `host`, if it answers.
pub fn status(host: &str) -> Option<Status> {
    let out = remote::run(
        host,
        &format!("cd {REPO} && musubi status -T {STATUS_TEMPLATE}"),
        Duration::from_secs(20),
    );
    let Outcome::Ok { stdout, .. } = out else {
        return None;
    };
    parse_status(&stdout)
}

fn parse_status(text: &str) -> Option<Status> {
    let mut fields = BTreeMap::new();
    let mut problem = String::new();
    let mut in_problem = false;
    for line in text.lines() {
        if in_problem {
            problem.push('\n');
            problem.push_str(line);
        } else if let Some(rest) = line.strip_prefix("problem=") {
            problem.push_str(rest);
            in_problem = true;
        } else if let Some((key, value)) = line.split_once('=') {
            fields.insert(key.to_owned(), value.to_owned());
        }
    }
    Some(Status {
        head: fields.get("head")?.clone(),
        sent: fields.get("sent")? == "true",
        running: fields.get("running")? == "true",
        serving: fields.get("serving")? == "true",
        problem: problem.trim().to_owned(),
    })
}

/// Whether what a command said shows that jj or musubi crashed, rather than refused.
fn crashed(outcome: &Outcome, abandon_seen: bool) -> bool {
    let (code, said) = match outcome {
        Outcome::Ok { .. } => (0, outcome.said()),
        Outcome::Failed { code, .. } => (*code, outcome.said()),
        Outcome::Lost { .. } => return false,
    };
    let crash = code == 101 || said.contains("panicked at") || said.contains("Internal error");
    // jj's duplicate-commit bug (docs/internals/races.md, "Known jj limitations"): a user
    // runs the command again.
    let known = said.contains("Newly-created commit") && said.contains("already exists")
        // jj refusing a workspace recorded at an operation `jj op abandon` rewrote, until the
        // user runs the `jj op integrate` it suggests (races.md, "Known jj limitations").
        || said.contains("seems to be a sibling of the working copy's operation")
        // jj's undo, after `jj op abandon`, restoring a view whose commits its index lacks
        // (antithesis/FINDINGS.md): a bug in jj, not musubi, and only after an abandon.
        || abandon_seen && said.contains("Undid operation") && said.contains("not found in index");
    crash && !known
}

/// The `commit_id change_id` lines a command printed.
fn commits_in(stdout: &str) -> Vec<(String, String)> {
    stdout
        .lines()
        .filter_map(|line| {
            let (commit, change) = line.trim().split_once(' ')?;
            (commit.len() == 40 && commit.bytes().all(|b| b.is_ascii_hexdigit()))
                .then(|| (commit.to_owned(), change.to_owned()))
        })
        .collect()
}

/// A jj command that prints the commit and change ids of `revset`, without snapshotting.
fn print_commits(revset: &str) -> String {
    format!(
        "jj log --ignore-working-copy --no-graph -r '{revset}' \
         -T 'commit_id ++ \" \" ++ change_id ++ \"\\n\"'"
    )
}

impl Workload {
    pub fn from_env() -> Self {
        let machines: Vec<String> = std::env::var("MACHINES")
            .unwrap_or_else(|_| "m1,m2,m3".to_owned())
            .split(',')
            .map(str::to_owned)
            .collect();
        let count = machines.len();
        let eventually_after = std::env::var("DRIVER_EVENTUALLY_AFTER")
            .ok()
            .and_then(|secs| secs.parse().ok())
            .map(Duration::from_secs);
        Workload {
            hub: std::env::var("HUB").unwrap_or_else(|_| "hub".to_owned()),
            busy: (0..count).map(|_| Mutex::new(())).collect(),
            machines,
            next: AtomicU64::new(0),
            created: Mutex::new(Vec::new()),
            changes: Mutex::new(VecDeque::new()),
            ending: Mutex::new(()),
            editing: std::sync::RwLock::new(()),
            abandoned_until: Mutex::new(None),
            abandon_pending: Mutex::new(vec![false; count]),
            reverted: Mutex::new(BTreeSet::new()),
            eventually_drawn: std::env::var("DRIVER_EVENTUALLY").as_deref() != Ok("off"),
            eventually_after,
            started: OnceLock::new(),
        }
    }

    pub fn start(&self) {
        let _ = self.started.set(Instant::now());
    }

    fn id(&self) -> u64 {
        self.next.fetch_add(1, Ordering::Relaxed)
    }

    fn machine(&self, tc: &TestCase) -> usize {
        tc.draw(
            gs::integers::<usize>()
                .min_value(0)
                .max_value(self.machines.len() - 1),
        )
    }

    fn lock(&self, m: usize) -> MutexGuard<'_, ()> {
        self.busy[m].lock().unwrap_or_else(|e| e.into_inner())
    }

    /// A revision for a command to act on: a recent change, another machine's working copy,
    /// a bookmark, or `@`.
    fn revision(&self, tc: &TestCase, m: usize) -> String {
        match tc.draw(gs::integers::<u8>().min_value(0).max_value(9)) {
            0..=4 => {
                let changes = self.changes.lock().unwrap_or_else(|e| e.into_inner());
                if changes.is_empty() {
                    return "@".to_owned();
                }
                let i = tc.draw(
                    gs::integers::<usize>()
                        .min_value(0)
                        .max_value(changes.len() - 1),
                );
                changes[i].clone()
            }
            5 | 6 => {
                let other = self.machine(tc);
                if other == m {
                    "@-".to_owned()
                } else {
                    format!("{}/default@", self.machines[other])
                }
            }
            7 => BOOKMARKS[tc.draw(gs::integers::<usize>().min_value(0).max_value(3))].to_owned(),
            _ => "@".to_owned(),
        }
    }

    fn record(&self, m: usize, by: &'static str, issued: Instant, stdout: &str) {
        let commits = commits_in(stdout);
        let mut created = self.created.lock().unwrap_or_else(|e| e.into_inner());
        let mut changes = self.changes.lock().unwrap_or_else(|e| e.into_inner());
        for (commit, change) in commits {
            created.push(Created {
                commit,
                machine: m,
                by,
                issued,
            });
            if !changes.contains(&change) {
                changes.push_back(change);
                if changes.len() > POOL {
                    changes.pop_front();
                }
            }
        }
    }

    /// Runs `script` in `dir` on machine `m`, holding the machine, checks that nothing
    /// crashed, and updates a stale working copy, as the user would on being told.
    fn command(&self, m: usize, dir: &str, script: &str) -> Outcome {
        let _busy = self.lock(m);
        self.command_held(m, dir, script)
    }

    fn command_held(&self, m: usize, dir: &str, script: &str) -> Outcome {
        let host = &self.machines[m];
        let outcome = remote::run_exclusive(host, &format!("cd {dir} && {script}"), COMMAND);
        if !matches!(outcome, Outcome::Lost { .. }) {
            // It got the machine's lock, so any abandon lost before it has finished.
            let mut pending = self
                .abandon_pending
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            if std::mem::take(&mut pending[m]) {
                self.abandoned_now();
            }
        }
        self.judge(m, script, &outcome);
        if let Outcome::Failed { .. } = &outcome
            && outcome.said().contains("working copy is stale")
        {
            assert_reachable!("a machine's working copy is stale after another machine's work");
            let update = "jj workspace update-stale";
            let updated = remote::run_exclusive(host, &format!("cd {dir} && {update}"), COMMAND);
            self.judge(m, update, &updated);
        } else if let Outcome::Failed { .. } = &outcome
            && outcome
                .said()
                .contains("seems to be a sibling of the working copy's operation")
            && let Some(op) = op_to(&outcome.said(), "jj op integrate ")
        {
            assert_reachable!("a workspace is recorded at an operation an abandon rewrote");
            let integrate = format!("jj op integrate {op}");
            let integrated =
                remote::run_exclusive(host, &format!("cd {dir} && {integrate}"), COMMAND);
            self.judge(m, &integrate, &integrated);
        }
        outcome
    }

    fn abandoned_now(&self) {
        *self
            .abandoned_until
            .lock()
            .unwrap_or_else(|e| e.into_inner()) = Some(Instant::now());
    }

    fn judge(&self, m: usize, script: &str, outcome: &Outcome) {
        let abandon_seen = self
            .abandoned_until
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .is_some()
            || self
                .abandon_pending
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .iter()
                .any(|&pending| pending);
        let crash = crashed(outcome, abandon_seen);
        assert_always!(
            !crash,
            "jj and musubi commands never crash",
            &json!({
                "machine": self.machines[m],
                "command": script,
                "outcome": format!("{outcome:?}"),
            })
        );
        if crash {
            eprintln!(
                "{}: `{script}` crashed: {}",
                self.machines[m],
                outcome.describe()
            );
        }
    }

    /// The directory a jj command runs in: the main workspace, or sometimes the secondary.
    fn dir(&self, tc: &TestCase) -> String {
        if tc.draw(gs::weighted_booleans(0.15)) {
            format!("$( [ -d {WORKSPACE}/.jj ] && echo {WORKSPACE} || echo {REPO} )")
        } else {
            REPO.to_owned()
        }
    }

    fn eventually_due(&self) -> bool {
        match (self.eventually_after, self.started.get()) {
            (Some(after), Some(started)) => started.elapsed() >= after,
            _ => false,
        }
    }
}

#[hegel::concurrent_state_machine]
impl Workload {
    /// Edits files without telling jj, which a later command, or the daemon's background
    /// snapshot, records.
    #[rule(weight = 5)]
    fn edit_files(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let file = tc.draw(gs::integers::<usize>().min_value(0).max_value(FILES - 1));
        let id = self.id();
        let dir = self.dir(&tc);
        let script = match tc.draw(gs::integers::<u8>().min_value(0).max_value(5)) {
            0 => format!("cd {dir} && rm -f f{file}"),
            1 => format!("cd {dir} && mkdir -p d && echo {id} > d/f{file}"),
            _ => format!("cd {dir} && echo {id} >> f{file}"),
        };
        // Not the driver's lock on the machine, which a user typing one command at a time
        // holds, but the machine's own, which every exclusive command takes there: the daemon's
        // background snapshots race the edit, and an edit delivered late, after a later
        // command, doesn't run (remote.rs).
        let _editing = self.editing.read().unwrap_or_else(|e| e.into_inner());
        let _ = remote::run_exclusive(&self.machines[m], &script, COMMAND);
    }

    #[rule(weight = 6)]
    fn new_change(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let mut parents = vec![self.revision(&tc, m)];
        if tc.draw(gs::weighted_booleans(0.2)) {
            parents.push(self.revision(&tc, m));
        }
        let id = self.id();
        let dir = self.dir(&tc);
        let parents: Vec<String> = parents.iter().map(|p| format!("'{p}'")).collect();
        let script = format!(
            "jj new -m w{id} {} && {}",
            parents.join(" "),
            print_commits("@")
        );
        let issued = Instant::now();
        if let Outcome::Ok { stdout, .. } = self.command(m, &dir, &script) {
            if parents.iter().any(|p| p.contains("/default@")) {
                assert_reachable!("a machine builds on another machine's working copy");
            }
            self.record(m, "new", issued, &stdout);
        }
    }

    #[rule(weight = 3)]
    fn commit(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let id = self.id();
        let dir = self.dir(&tc);
        let script = format!("jj commit -m w{id} && {}", print_commits("@- | @"));
        let issued = Instant::now();
        if let Outcome::Ok { stdout, .. } = self.command(m, &dir, &script) {
            self.record(m, "commit", issued, &stdout);
        }
    }

    #[rule(weight = 2)]
    fn describe(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let rev = self.revision(&tc, m);
        let id = self.id();
        let script = format!("jj describe -m w{id} '{rev}' && {}", print_commits(&rev));
        let issued = Instant::now();
        if let Outcome::Ok { stdout, .. } = self.command(m, REPO, &script) {
            self.record(m, "describe", issued, &stdout);
        }
    }

    #[rule(weight = 2)]
    fn rebase(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let what = ["-r", "-s", "-b"][tc.draw(gs::integers::<usize>().min_value(0).max_value(2))];
        let source = self.revision(&tc, m);
        let dest = self.revision(&tc, m);
        let script = format!("jj rebase {what} '{source}' -o '{dest}'");
        if self.command(m, REPO, &script).ok() {
            assert_reachable!("a rebase succeeds");
        }
    }

    #[rule]
    fn squash(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let id = self.id();
        let script = format!("jj squash -m w{id} && {}", print_commits("@-"));
        let issued = Instant::now();
        if let Outcome::Ok { stdout, .. } = self.command(m, REPO, &script) {
            self.record(m, "squash", issued, &stdout);
        }
    }

    #[rule]
    fn abandon(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let rev = self.revision(&tc, m);
        self.command(m, REPO, &format!("jj abandon '{rev}'"));
    }

    #[rule]
    fn edit(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let rev = self.revision(&tc, m);
        self.command(m, REPO, &format!("jj edit '{rev}'"));
    }

    #[rule(weight = 3)]
    fn bookmark(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = BOOKMARKS[tc.draw(gs::integers::<usize>().min_value(0).max_value(3))];
        let script = if tc.draw(gs::weighted_booleans(0.15)) {
            format!("jj bookmark delete {name}")
        } else {
            let rev = self.revision(&tc, m);
            format!("jj bookmark set {name} -r '{rev}' --allow-backwards")
        };
        self.command(m, REPO, &script);
    }

    /// Moves a branch with git, behind jj's back: the next jj command imports it.
    #[rule]
    fn git_branch(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let name = BOOKMARKS[tc.draw(gs::integers::<usize>().min_value(0).max_value(3))];
        let commit = {
            let created = self.created.lock().unwrap_or_else(|e| e.into_inner());
            if created.is_empty() {
                return;
            }
            let i = tc.draw(
                gs::integers::<usize>()
                    .min_value(0)
                    .max_value(created.len() - 1),
            );
            created[i].commit.clone()
        };
        self.command(
            m,
            REPO,
            &format!("git update-ref refs/heads/{name} {commit}"),
        );
    }

    #[rule]
    fn undo(&self, tc: TestCase) {
        let m = self.machine(&tc);
        self.command(m, REPO, "jj undo");
    }

    /// A command at an older operation, concurrent with the head: jj merges the two.
    #[rule]
    fn at_older_op(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let id = self.id();
        let back = tc.draw(gs::integers::<usize>().min_value(1).max_value(4));
        let at = format!("@{}", "-".repeat(back));
        self.command(m, REPO, &format!("jj --at-op {at} new -m w{id}"));
    }

    /// Looks at the repository, as `jj log` does, which also snapshots.
    #[rule(weight = 2)]
    fn look(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let dir = self.dir(&tc);
        let script = "jj log --no-graph -r 'visible_heads() | bookmarks()' \
             -T 'separate(\" \", if(divergent, \"(divergent)\"), bookmarks, working_copies) ++ \"\\n\"'";
        if let Outcome::Ok { stdout, .. } = self.command(m, &dir, script) {
            let other = format!("{}/", self.machines[(m + 1) % self.machines.len()]);
            assert_sometimes!(
                stdout.contains(&other),
                "a machine shows another machine's working copy"
            );
            assert_sometimes!(stdout.contains("(divergent)"), "a change is divergent");
            assert_sometimes!(stdout.contains("??"), "a bookmark is conflicted");
        }
    }

    #[rule]
    fn update_stale(&self, tc: TestCase) {
        let m = self.machine(&tc);
        self.command(m, REPO, "jj workspace update-stale");
    }

    /// Adds or forgets the secondary workspace, whose working copy the other machines show
    /// as `m1/ws1@`.
    #[rule]
    fn workspace(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let script = format!(
            "if [ -d {WORKSPACE}/.jj ]; then jj workspace forget ws1 2>/dev/null; rm -rf {WORKSPACE}; \
             else rm -rf {WORKSPACE} && jj workspace add --name ws1 {WORKSPACE}; fi"
        );
        self.command(m, REPO, &script);
    }

    /// Syncs now, and makes the repair a failed sync asks for, as the user would.
    #[rule]
    fn sync(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let _busy = self.lock(m);
        let synced = self.command_held(m, REPO, "musubi sync 2>&1");
        self.repair(m, &synced.said());
    }

    /// Trims the history below a recent operation, which every copy then drops too.
    #[rule]
    fn op_abandon(&self, tc: TestCase) {
        if !tc.draw(gs::weighted_booleans(0.3)) {
            return;
        }
        let m = self.machine(&tc);
        let back = tc.draw(gs::integers::<usize>().min_value(1).max_value(30));
        let script = format!("jj op abandon ..@{}", "-".repeat(back));
        let outcome = self.command(m, REPO, &script);
        match outcome {
            Outcome::Ok { .. } => self.abandoned_now(),
            Outcome::Lost { .. } => {
                self.abandon_pending
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())[m] = true;
            }
            Outcome::Failed { .. } => {}
        }
        if outcome.ok() {
            assert_reachable!("an operation abandon trims a machine's history");
        }
    }

    /// Turns the daemon's background snapshots on or off.
    #[rule]
    fn auto_snapshot(&self, tc: TestCase) {
        let m = self.machine(&tc);
        let on = tc.draw(gs::booleans());
        self.command(
            m,
            REPO,
            &format!("jj config set --repo musubi.auto-snapshot {on}"),
        );
    }

    #[rule]
    fn status(&self, tc: TestCase) {
        let m = self.machine(&tc);
        if let Some(status) = status(&self.machines[m]) {
            assert_sometimes!(
                !status.problem.is_empty(),
                "musubi status reports a problem"
            );
        }
    }

    /// Stops faults, waits for the machines to converge, checks them, and ends the
    /// timeline.
    #[rule]
    fn eventually(&self, tc: TestCase) {
        let drawn = self.eventually_drawn && tc.draw(gs::weighted_booleans(0.003));
        if drawn || self.eventually_due() {
            self.converge_and_check();
        }
    }
}

/// What every machine must agree on once they have converged.
#[derive(Debug)]
struct View {
    status: Status,
    heads: BTreeSet<String>,
    bookmarks: String,
    /// Every machine's workspaces and their working-copy commits, each named as the other
    /// machines name it: `m1/default`, whichever machine lists it.
    workspaces: BTreeSet<String>,
}

impl Workload {
    fn converge_and_check(&self) {
        let Ok(_ending) = self.ending.try_lock() else {
            return;
        };
        eprintln!("eventually: stopping faults");
        if let Ok(stop) = std::env::var("ANTITHESIS_STOP_FAULTS") {
            let _ = std::process::Command::new(stop).arg("3600").status();
        }
        // No other command or edit runs from now on.
        let _busy: Vec<_> = (0..self.machines.len()).map(|m| self.lock(m)).collect();
        let _no_edits = self.editing.write().unwrap_or_else(|e| e.into_inner());

        // Every machine serves its copy again.
        let deadline = Instant::now() + Duration::from_secs(300);
        let mut statuses;
        loop {
            statuses = self.machines.iter().map(|h| status(h)).collect::<Vec<_>>();
            let up = statuses
                .iter()
                .all(|s| s.as_ref().is_some_and(|s| s.running && s.serving));
            if up || Instant::now() > deadline {
                eprintln!("eventually: assertions start");
                assert_always!(
                    up,
                    "every machine serves its copy again once faults stop",
                    &json!({ "statuses": format!("{statuses:?}") })
                );
                break;
            }
            std::thread::sleep(Duration::from_secs(1));
        }

        // Record what's in each working copy, as a user's next command would.
        for m in 0..self.machines.len() {
            self.command_held(m, REPO, "jj workspace update-stale; jj status >/dev/null");
            self.command_held(
                m,
                REPO,
                &format!(
                    "if [ -d {WORKSPACE}/.jj ]; then cd {WORKSPACE} && \
                     jj workspace update-stale; jj status >/dev/null; fi"
                ),
            );
        }

        let files_before: Vec<_> = (0..self.machines.len()).map(|m| self.files(m)).collect();

        // Sync until the machines agree, repairing what a sync asks the user to repair.
        let deadline = Instant::now() + Duration::from_secs(600);
        let mut views;
        let mut repaired = BTreeMap::new();
        loop {
            for m in 0..self.machines.len() {
                let synced = self.command_held(m, REPO, "musubi sync 2>&1");
                if let Some(repair) = self.repair(m, &synced.said()) {
                    *repaired
                        .entry(format!("{}: {repair}", self.machines[m]))
                        .or_insert(0) += 1;
                }
            }
            views = (0..self.machines.len())
                .map(|m| self.view(m))
                .collect::<Vec<_>>();
            let agreed = views.iter().all(|v| match (v, &views[0]) {
                (Some(v), Some(first)) => {
                    v.status.sent
                        && v.status.problem.is_empty()
                        && v.status.head == first.status.head
                        && v.heads == first.heads
                        && v.bookmarks == first.bookmarks
                        && v.workspaces == first.workspaces
                }
                _ => false,
            });
            if agreed || Instant::now() > deadline {
                assert_always!(
                    agreed,
                    "the machines converge on one history once faults stop",
                    &json!({
                        "views": format!("{views:#?}"),
                        "repaired": repaired,
                    })
                );
                break;
            }
            std::thread::sleep(Duration::from_secs(2));
        }

        // Syncing left every working copy's files as they were, where no repair the user ran
        // could have changed them.
        for (m, before) in files_before.iter().enumerate() {
            let host = &self.machines[m];
            if repaired.keys().any(|r| r.starts_with(&format!("{host}: "))) {
                continue;
            }
            let after = self.files(m);
            if let (Some(before), Some(after)) = (before, &after) {
                assert_always!(
                    before == after,
                    "syncing leaves the files in working copies as they were",
                    &json!({ "machine": host, "before": before, "after": after })
                );
            }
        }

        // Every commit a command made reached every machine. An abandon that was lost and
        // never confirmed finished may still have dropped anything before now.
        if self
            .abandon_pending
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .iter()
            .any(|&pending| pending)
        {
            self.abandoned_now();
        }
        let created = self.created.lock().unwrap_or_else(|e| e.into_inner());
        let abandoned_until = *self
            .abandoned_until
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let checked: Vec<&Created> = created
            .iter()
            .filter(|c| abandoned_until.is_none_or(|until| c.issued > until))
            .collect();
        let input: String = checked.iter().map(|c| format!("{}\n", c.commit)).collect();
        for (m, host) in self.machines.iter().enumerate() {
            let out = remote::run_with_input(
                host,
                &format!("git -C {REPO} cat-file --batch-check"),
                Some(input.as_bytes()),
                Duration::from_secs(120),
                remote::Exclusive::No,
            );
            let Outcome::Ok { stdout, .. } = &out else {
                assert_always!(
                    false,
                    "every commit a command made reaches every machine",
                    &json!({ "machine": host, "outcome": format!("{out:?}") })
                );
                continue;
            };
            let missing: Vec<_> = stdout
                .lines()
                .filter(|line| line.ends_with(" missing"))
                .map(|line| {
                    let commit = line.trim_end_matches(" missing");
                    let made = created.iter().find(|c| c.commit == commit);
                    json!({
                        "commit": commit,
                        "made_on": made.map(|c| self.machines[c.machine].clone()),
                        "by": made.map(|c| c.by),
                    })
                })
                .collect();
            assert_always!(
                missing.is_empty(),
                "every commit a command made reaches every machine",
                &json!({
                    "machine": self.machines[m],
                    "missing": missing,
                    "recorded": created.len(),
                    "checked": checked.len(),
                })
            );
        }
        eprintln!(
            "eventually: done, {} of {} commits checked; ending the timeline",
            checked.len(),
            created.len()
        );
        std::process::exit(0);
    }

    /// Runs the command a failed sync's error names to go on, if it names one, with the
    /// machine held, and returns it.
    fn repair(&self, m: usize, said: &str) -> Option<String> {
        // Without a single culprit, the error lists this machine's operations, newest first,
        // and says musubi names the next once one is reverted: revert the newest that isn't a
        // merge, which `jj op revert` refuses, nor a revert, nor one already tried.
        let revert = op_to(said, "jj op revert ").or_else(|| {
            if !said.contains("jj op revert <id>") {
                return None;
            }
            let mut tried = self.reverted.lock().unwrap_or_else(|e| e.into_inner());
            let op = listed_ops(said).into_iter().find(|(id, description)| {
                !description.starts_with("revert operation")
                    && !description.starts_with("reconcile divergent operations")
                    && !tried.contains(id)
            })?;
            tried.insert(op.0.clone());
            Some(op.0)
        });
        let repair = if let Some(op) = revert {
            assert_reachable!(
                "a sync stops at work jj can't merge, and names an operation to revert"
            );
            format!("jj op revert {op}")
        } else {
            let op = op_to(said, "jj op integrate ")?;
            assert_reachable!(
                "a sync stops at an ambiguous abandon, and names an operation to integrate"
            );
            format!("jj op integrate {op}")
        };
        self.command_held(m, REPO, &repair);
        Some(repair)
    }

    /// A digest of every file in machine `m`'s workspaces, other than jj's and git's own.
    fn files(&self, m: usize) -> Option<String> {
        let script = format!(
            "for dir in {REPO} {WORKSPACE}; do [ -d $dir/.jj ] || continue; cd $dir; \
             echo $dir; find . -path ./.jj -prune -o -path ./.git -prune -o -type f -print \
             | LC_ALL=C sort | xargs -r sha256sum; done | sha256sum"
        );
        match remote::run_exclusive(&self.machines[m], &script, COMMAND) {
            Outcome::Ok { stdout, .. } => Some(stdout.trim().to_owned()),
            _ => None,
        }
    }

    /// What machine `m` shows, read without snapshotting.
    fn view(&self, m: usize) -> Option<View> {
        let host = &self.machines[m];
        let status = status(host)?;
        let heads = remote::run(
            host,
            &format!("cd {REPO} && {}", print_commits("visible_heads()")),
            COMMAND,
        );
        let Outcome::Ok { stdout, .. } = heads else {
            return None;
        };
        let heads = commits_in(&stdout).into_iter().map(|(c, _)| c).collect();
        let bookmarks = remote::run(
            host,
            &format!(
                "cd {REPO} && jj bookmark list --ignore-working-copy --all-remotes \
                 -T 'name ++ if(remote, \"@\" ++ remote) ++ \" \" ++ if(normal_target, normal_target.commit_id(), \"conflict\") ++ \"\\n\"'"
            ),
            COMMAND,
        );
        let Outcome::Ok { stdout, .. } = bookmarks else {
            return None;
        };
        // A machine's own git refs are its own: only jj's view replicates.
        let mut lines: Vec<&str> = stdout.lines().filter(|l| !l.contains("@git ")).collect();
        lines.sort_unstable();
        let workspaces = remote::run(
            host,
            &format!(
                "cd {REPO} && jj workspace list --ignore-working-copy \
                 -T 'name ++ \" \" ++ target.commit_id() ++ \"\\n\"'"
            ),
            COMMAND,
        );
        let Outcome::Ok { stdout, .. } = workspaces else {
            return None;
        };
        let workspaces = stdout
            .lines()
            .map(|line| {
                if line
                    .split(' ')
                    .next()
                    .is_some_and(|name| name.contains('/'))
                {
                    line.to_owned()
                } else {
                    format!("{host}/{line}")
                }
            })
            .collect();
        Some(View {
            status,
            heads,
            bookmarks: lines.join("\n"),
            workspaces,
        })
    }
}

/// The operations a sync error lists, newest first, as "newest first: 1a2b3c4d5e6f
/// (describe commit …), 7a8b9c0d1e2f (snapshot working copy), and 3 older", with their
/// descriptions.
fn listed_ops(said: &str) -> Vec<(String, String)> {
    let Some(at) = said.find("newest first: ") else {
        return Vec::new();
    };
    let mut rest = &said[at + "newest first: ".len()..];
    let mut ops = Vec::new();
    loop {
        let id: String = rest.chars().take_while(|c| c.is_ascii_hexdigit()).collect();
        if id.is_empty() {
            break;
        }
        rest = &rest[id.len()..];
        let Some(after) = rest.strip_prefix(" (") else {
            break;
        };
        // The description runs to the parenthesis that closes it.
        let mut depth = 1;
        let Some(end) = after.char_indices().find_map(|(i, c)| {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            (depth == 0).then_some(i)
        }) else {
            break;
        };
        ops.push((id, after[..end].to_owned()));
        rest = &after[end + 1..];
        let Some(next) = rest.strip_prefix(", ") else {
            break;
        };
        rest = next;
    }
    ops
}

/// The operation id after `prefix` in what a command said, as in "`jj op revert 1a2b3c`".
fn op_to(said: &str, prefix: &str) -> Option<String> {
    let at = said.find(prefix)? + prefix.len();
    let id: String = said[at..]
        .chars()
        .take_while(|c| c.is_ascii_hexdigit())
        .collect();
    (!id.is_empty()).then_some(id)
}

#[cfg(test)]
mod tests {
    #[test]
    fn listed_ops_reads_the_unmergeable_error() {
        let said = "To go on, revert this machine's operation that conflicts with them, one of \
                    those the hive doesn't have yet (newest first: 1a2b3c4d5e6f (revert \
                    operation x (y)), 7a8b9c0d1e2f (snapshot working copy), and 3 older), with \
                    `jj op revert <id>`; musubi then catches up";
        assert_eq!(
            super::listed_ops(said),
            vec![
                (
                    "1a2b3c4d5e6f".to_owned(),
                    "revert operation x (y)".to_owned()
                ),
                (
                    "7a8b9c0d1e2f".to_owned(),
                    "snapshot working copy".to_owned()
                ),
            ]
        );
    }
}
