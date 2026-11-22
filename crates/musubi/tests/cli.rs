//! The `musubi` binary end to end: a hub process, machines joining and matching hives,
//! cloning, listing, and each machine's daemon, started by joining, picking up repositories
//! and other machines' work by itself.

#![allow(clippy::unwrap_used)]

use std::fmt::Write as _;
use std::fs;
use std::io::BufRead as _;
use std::io::BufReader;
use std::path::Path;
use std::path::PathBuf;
use std::process::Child;
use std::process::Command;
use std::process::Stdio;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::mpsc;
use std::time::Duration;
use std::time::Instant;

use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

/// How long one command may take. A command that hangs usually means a hub or daemon that
/// stopped answering, so failing here, with their logs, says more than nextest's timeout.
const DEADLINE: Duration = Duration::from_secs(45);

/// A `jj workspace list` template giving only each working copy's name, one to a line: jj's
/// default format differs between releases.
const NAMES: &str = "name ++ \"\\n\"";

fn musubi() -> &'static Path {
    Path::new(env!("CARGO_BIN_EXE_musubi"))
}

/// Takes out of the snapshots of the rest of the test what differs from run to run: the test's
/// directory, this computer's name, process ids, and how long ago something happened.
#[must_use]
fn snapshot_filters(env: &TestEnv) -> impl Sized {
    let mut settings = insta::Settings::clone_current();
    // The canonical form first: on macOS it holds the other, under /private.
    for root in [env.root().canonicalize().unwrap(), env.root().to_owned()] {
        // `$$` is a `$` in a replacement.
        settings.add_filter(&regex_escape(root.to_str().unwrap()), "$$ROOT");
    }
    if cfg!(windows) {
        settings.add_filter(r"\\", "/");
        settings.add_filter(r"(?m)^Usage: musubi\.exe ", "Usage: musubi ");
    }
    // This computer's name only where musubi prints a hub's: anywhere else, a computer named
    // `alpha`, say, would hide what it stood for.
    let host = regex_escape(&whoami::hostname().unwrap());
    for (pattern, replacement) in [
        ("--hub {host}\\b", "--hub $$HOST"),
        ("Hub {host}:", "Hub $$HOST:"),
        ("on {host},", "on $$HOST,"),
        ("isn't {host}\\.", "isn't $$HOST."),
    ] {
        settings.add_filter(&pattern.replace("{host}", &host), replacement);
    }
    // The daemon's socket is a file beside its state on Unix, a named pipe on Windows.
    settings.add_filter(
        r"\$ROOT/home/musubi-[^/\s]+/daemon\.sock|//\./pipe/musubi-[0-9a-f]+",
        "[daemon socket]",
    );
    settings.add_filter(r"\b\d+[smhd] ago\b", "N ago");
    settings.add_filter(r"#\d+", "#N");
    settings.add_filter(r"\(pid \d+\)", "(pid N)");
    // SMF starts services at boot where launchd and systemd start them at login, and the
    // snapshots say "at login" for both. Only after "starts" or "runs", so that help text naming
    // both ("at login (at boot on illumos)") keeps its own words.
    if SMF {
        settings.add_filter(r"\b(starts?|runs?) at boot\b", "$1 at login");
    }
    settings.bind_to_scope()
}

/// `text`, matching only itself in a regular expression.
fn regex_escape(text: &str) -> String {
    let mut escaped = String::new();
    for c in text.chars() {
        if "\\.+*?()|[]{}^$".contains(c) {
            escaped.push('\\');
        }
        escaped.push(c);
    }
    escaped
}

/// The logs of the background processes, and the repositories whose operation logs go with
/// them, for failure messages.
#[derive(Default)]
struct Logs {
    files: Vec<PathBuf>,
    repos: Vec<TestRepo>,
}

impl Logs {
    /// A log file for a background process: its stderr, at debug level for musubi.
    fn attach(&mut self, env: &TestEnv, name: &str, command: &mut Command) {
        let path = env.root().join(format!("{name}.log"));
        command
            .env("RUST_LOG", "info,musubi=debug,musubi_sync=debug")
            .stderr(fs::File::create(&path).unwrap());
        self.files.push(path);
    }

    /// Includes the daemon log of `repo`'s machine, and `repo`'s operation log, in failure
    /// messages.
    fn daemon_of(&mut self, env: &TestEnv, repo: &TestRepo) {
        self.files.push(state_dir(env, repo).join("daemon.log"));
        self.op_log_of(repo);
    }

    /// Includes `repo`'s operation log in failure messages: which machine's work, or which
    /// musubi command, wrote each operation.
    fn op_log_of(&mut self, repo: &TestRepo) {
        self.repos.push(repo.another_copy(repo.path()));
    }

    fn dump(&self) -> String {
        let mut dump = String::new();
        for path in &self.files {
            let log = fs::read_to_string(path).unwrap_or_default();
            writeln!(dump, "--- {}:\n{log}", path.display()).unwrap();
        }
        // Newest first, each with the workspace it was made in and musubi's attributes, such
        // as `musubi.work`, which say whose work it is. From each op head in turn, and without
        // snapshotting: either could write an operation of its own, a merge of divergent heads
        // or a snapshot, which would count as the machine's work.
        let template = r#"id.short() ++ " " ++ time.end().format("%H:%M:%S%.3f") ++ " "
            ++ user ++ " " ++ workspace_name ++ " " ++ description.first_line()
            ++ if(attributes, " {" ++ attributes.lines().join("; ") ++ "}") ++ "\n""#;
        for repo in &self.repos {
            // A repository a failed clone never made has none.
            let heads = fs::read_dir(repo.repo_path().join("op_heads/heads"))
                .map(|dir| {
                    dir.filter_map(|entry| entry.ok()?.file_name().into_string().ok())
                        .filter(|name| name.bytes().all(|b| b.is_ascii_hexdigit()))
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            for head in heads {
                let output = repo.jj_output(&[
                    "op",
                    "log",
                    "--no-graph",
                    "--ignore-working-copy",
                    "--at-op",
                    &head,
                    "-n",
                    "40",
                    "-T",
                    template,
                ]);
                writeln!(
                    dump,
                    "--- operations of {} from {}:\n{}{}",
                    repo.machine(),
                    head.get(..12).unwrap_or(&head),
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr),
                )
                .unwrap();
            }
        }
        dump
    }
}

/// Failure diagnostics find moved repositories and read each operation head without writing
/// a snapshot or merging concurrent operations into the history being diagnosed.
#[test]
fn failure_logs_read_operation_heads_without_changing_them() {
    let env = TestEnv::new();
    let repo = env.init_repo_with_hostname("alpha", "laptop");
    let path = env.root().join("moved");
    fs::rename(repo.path(), &path).unwrap();
    let repo = repo.another_copy(&path);
    repo.jj(&["new", "-m", "first head"]);
    repo.jj(&["--at-op", "@-", "new", "-m", "second head"]);
    let heads = || {
        let mut heads: Vec<_> = fs::read_dir(repo.repo_path().join("op_heads/heads"))
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect();
        heads.sort();
        heads
    };
    let before = heads();
    assert_eq!(before.len(), 2);
    let mut logs = Logs::default();
    logs.op_log_of(&repo);
    let dump = logs.dump();
    assert_eq!(
        dump.matches("--- operations of alpha from ").count(),
        2,
        "{dump}"
    );
    assert!(dump.contains("first head"), "{dump}");
    assert!(dump.contains("second head"), "{dump}");
    assert!(!dump.contains("Error:"), "{dump}");
    assert_eq!(heads(), before);
}

/// Where `TestRepo::program` points musubi's state for the repository's machine.
fn state_dir(env: &TestEnv, repo: &TestRepo) -> PathBuf {
    env.root().join(format!("home/musubi-{}", repo.machine()))
}

/// Runs `command` to completion within the deadline, returning whether it succeeded, its
/// stdout, and its stderr.
fn try_run(logs: &Logs, env: &TestEnv, mut command: Command) -> (bool, String, String) {
    static RUNS: AtomicUsize = AtomicUsize::new(0);
    let n = RUNS.fetch_add(1, Ordering::Relaxed);
    let out = env.root().join(format!("run-{n}.out"));
    let err = env.root().join(format!("run-{n}.err"));
    command
        .stdout(fs::File::create(&out).unwrap())
        .stderr(fs::File::create(&err).unwrap());
    let mut child = command.spawn().unwrap();
    let deadline = Instant::now() + DEADLINE;
    // Most commands finish in milliseconds: look again soon, then less often.
    let mut pause = Duration::from_millis(1);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() > deadline {
            child.kill().ok();
            child.wait().ok();
            panic!("{command:?} did not finish in time:\n{}", logs.dump());
        }
        std::thread::sleep(pause);
        pause = (pause * 2).min(Duration::from_millis(50));
    };
    (
        status.success(),
        fs::read_to_string(&out).unwrap(),
        fs::read_to_string(&err).unwrap(),
    )
}

/// Runs `command`, which must succeed, returning its stdout.
fn run(env: &TestEnv, logs: &Logs, command: Command) -> String {
    let description = format!("{command:?}");
    let (ok, stdout, stderr) = try_run(logs, env, command);
    assert!(
        ok,
        "{description} failed:\n{stdout}{stderr}\n{}",
        logs.dump()
    );
    stdout
}

fn musubi_in(env: &TestEnv, logs: &Logs, repo: &TestRepo, args: &[&str]) -> String {
    let mut command = repo.program(musubi());
    command.args(args);
    run(env, logs, command)
}

/// `musubi status` in `repo`, which must succeed: its stdout, and its warnings and hints.
fn status_in(env: &TestEnv, logs: &Logs, repo: &TestRepo) -> (String, String) {
    let mut command = repo.program(musubi());
    command.arg("status");
    let (ok, stdout, stderr) = try_run(logs, env, command);
    assert!(
        ok,
        "musubi status failed:\n{stdout}{stderr}\n{}",
        logs.dump()
    );
    (stdout, stderr)
}

/// Runs musubi in `repo`, which must fail, returning its stderr.
fn musubi_fails(env: &TestEnv, logs: &Logs, repo: &TestRepo, args: &[&str]) -> String {
    let mut command = repo.program(musubi());
    command.args(args);
    let (ok, stdout, stderr) = try_run(logs, env, command);
    assert!(!ok, "musubi {args:?} succeeded:\n{stdout}");
    stderr
}

/// What the shell gets on completing the last of `words` as you type, as fish asks musubi
/// for it: a candidate a line, with its help after a tab.
fn completions(env: &TestEnv, logs: &Logs, repo: &TestRepo, words: &[&str]) -> String {
    let mut command = repo.program(musubi());
    command.env("COMPLETE", "fish").arg("--").args(words);
    run(env, logs, command)
}

/// A `musubi hub` process serving `<root>/hub`.
struct Hub {
    child: Child,
    dir: PathBuf,
    /// Its directory, which machines here join with.
    url: String,
    /// The first line it printed; `the_quick_start_works_as_written` pins the rest.
    greeting: String,
    /// What it printed on starting, through its last line of instructions.
    printed: Vec<String>,
}

impl Hub {
    fn start(env: &TestEnv, logs: &mut Logs) -> Self {
        Self::start_in(env, logs, "hub")
    }

    /// A hub serving the directory `name`, as another machine's might.
    fn start_in(env: &TestEnv, logs: &mut Logs, name: &str) -> Self {
        let dir = env.root().join(name);
        let mut command = Command::new(musubi());
        command
            .args([
                "hub",
                "-d",
                dir.to_str().unwrap(),
                "--advertise",
                "127.0.0.1",
            ])
            .env("MUSUBI_STATE_DIR", env.root().join(format!("{name}-state")))
            .env(
                "JJ_CONFIG",
                env.root().join(format!("{name}-state/absent.toml")),
            );
        Self::spawn(env, logs, name, command, dir)
    }

    /// The hub `musubi hub` serves by default on `repo`'s machine, `musubi/hub` in the data
    /// directory, run in the repository, as a user might run it anywhere.
    #[cfg(unix)]
    fn start_on(env: &TestEnv, logs: &mut Logs, repo: &TestRepo) -> Self {
        let command = default_hub_command(env, repo);
        let dir = env.root().join("data/musubi/hub");
        Self::spawn(env, logs, "hub", command, dir)
    }

    /// Runs `command`, a hub serving `dir`, and waits until it is serving.
    fn spawn(
        env: &TestEnv,
        logs: &mut Logs,
        name: &str,
        mut command: Command,
        dir: PathBuf,
    ) -> Self {
        command.stdout(Stdio::piped());
        logs.attach(env, name, &mut command);
        let mut child = command.spawn().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (tx, rx) = mpsc::channel();
        // Reads to the end even once nobody listens: closing the pipe early would break the
        // hub's later writes.
        std::thread::spawn(move || {
            let mut stdout = BufReader::new(stdout);
            loop {
                let mut line = String::new();
                if stdout.read_line(&mut line).unwrap_or(0) == 0 {
                    break;
                }
                tx.send(line).ok();
            }
        });
        let mut hub = Self {
            child,
            dir,
            url: String::new(),
            greeting: String::new(),
            printed: vec![],
        };
        let deadline = Instant::now() + DEADLINE;
        // Its instructions end with what to pass on this machine.
        while !hub
            .printed
            .last()
            .is_some_and(|line| line.starts_with("On this machine"))
        {
            let left = deadline.saturating_duration_since(Instant::now());
            let line = rx
                .recv_timeout(left)
                .unwrap_or_else(|_| panic!("the hub did not start serving:\n{}", logs.dump()));
            if line.starts_with("To share a repository:") {
                hub.url = hub.dir.display().to_string();
            }
            hub.printed.push(line.trim_end().to_owned());
        }
        hub.greeting.clone_from(&hub.printed[0]);
        hub
    }

    /// Kills the hub the hard way.
    fn kill(&mut self) {
        self.child.kill().ok();
        self.child.wait().ok();
    }
}

impl Drop for Hub {
    fn drop(&mut self) {
        self.kill();
    }
}

/// Removes `dir`, retrying for a while: on Windows a process just killed, or one it
/// started, can hold files in it open a little longer, which Windows refuses to remove as
/// a sharing violation (error 32). Any other error fails at once.
fn remove_dir_when_free(dir: &Path) {
    const ERROR_SHARING_VIOLATION: i32 = 32;
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        match fs::remove_dir_all(dir) {
            Ok(()) => return,
            Err(e)
                if cfg!(windows)
                    && e.raw_os_error() == Some(ERROR_SHARING_VIOLATION)
                    && Instant::now() < deadline =>
            {
                eprintln!("retrying removing {}: {e}", dir.display());
                std::thread::sleep(Duration::from_millis(200));
            }
            Err(e) => panic!("removing {}: {e}", dir.display()),
        }
    }
}

/// Stops the daemons of the machines it was given when dropped.
#[derive(Default)]
struct Daemons(Vec<Command>);

impl Daemons {
    fn of(&mut self, repo: &TestRepo) {
        let mut stop = repo.program(musubi());
        // Not in the repository, which a test may move or delete.
        stop.args(["daemon", "stop"])
            .current_dir(repo.path().parent().unwrap())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        self.0.push(stop);
    }
}

impl Drop for Daemons {
    fn drop(&mut self) {
        for stop in &mut self.0 {
            stop.status().ok();
        }
    }
}

fn log(repo: &TestRepo) -> String {
    repo.jj(&[
        "log",
        "--no-graph",
        "-r",
        "all()",
        "-T",
        "commit_id ++ \" \" ++ description.first_line() ++ \"\\n\"",
    ])
}

/// The repository's log, or `None` if `jj` failed. On Windows, a `jj` command can fail
/// with "Access is denied" while a daemon writes the same repository: jj renames index
/// files into place, and Windows won't rename over a file another process has open.
fn try_log(repo: &TestRepo) -> Option<String> {
    let template = "commit_id ++ \" \" ++ description.first_line() ++ \"\\n\"";
    let output = repo.jj_output(&["log", "--no-graph", "-r", "all()", "-T", template]);
    output
        .status
        .success()
        .then(|| String::from_utf8(output.stdout).unwrap())
}

fn wait_for(logs: &Logs, what: &str, done: impl FnMut() -> bool) {
    wait_within(logs, what, DEADLINE, done);
}

/// As [`wait_for`], for at most `within`: for what the daemon must do before its poll would.
fn wait_within(logs: &Logs, what: &str, within: Duration, mut done: impl FnMut() -> bool) {
    let deadline = Instant::now() + within;
    while !done() {
        assert!(
            Instant::now() < deadline,
            "timed out waiting for {what}:\n{}",
            logs.dump()
        );
        std::thread::sleep(Duration::from_millis(100));
    }
}

/// Gives `to` the history of `from`, as a clone would, without leaving a remote behind.
fn fetch_history(from: &TestRepo, to: &TestRepo) {
    to.jj(&[
        "git",
        "remote",
        "add",
        "seed",
        from.path().to_str().unwrap(),
    ]);
    to.jj(&["git", "fetch", "--remote", "seed"]);
    to.jj(&["git", "remote", "remove", "seed"]);
}

/// A received hive operation need not have a local counterpart until it is realized.
#[test]
fn debug_identifies_an_operation_received_but_not_realized() {
    use jj_lib::object_id::ObjectId as _;
    use musubi_jj::node::NodeRepo;
    use musubi_jj::op_id::LocalOp;

    let env = TestEnv::new();
    let source = env.init_repo("source");
    let target = env.init_repo("target");
    let mut node = NodeRepo::open(&source.repo_path(), &source.settings()).unwrap();
    let head = source.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let head = LocalOp(jj_lib::op_store::OperationId::try_from_hex(&head).unwrap());
    let canonical = node.canonicalize(&head).unwrap();
    let target_node = NodeRepo::open(&target.repo_path(), &target.settings()).unwrap();
    // Transfer what a peer sends, without realizing any of its operations locally.
    for id in node.canonical_store().operation_ids().unwrap() {
        let op = node.canonical_store().read_operation(&id).unwrap();
        if !target_node.canonical_store().has_view(&op.view_id) {
            target_node
                .canonical_store()
                .import_view(
                    &op.view_id,
                    &node.canonical_store().view_bytes(&op.view_id).unwrap(),
                )
                .unwrap();
        }
        target_node
            .canonical_store()
            .import_operation(&id, &node.canonical_store().operation_bytes(&id).unwrap())
            .unwrap();
    }
    assert!(target_node.local_of(&canonical).is_none());
    drop(target_node);
    let id = canonical.0.hex();
    let logs = Logs::default();
    let out = musubi_in(&env, &logs, &target, &["debug", "op-id", &id[..15]]);
    assert_eq!(
        out,
        format!("hive {id} is not realized on this machine yet\n")
    );
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(&id, "$$HIVE");
    settings.bind(|| {
        insta::assert_snapshot!(out, @"hive $HIVE is not realized on this machine yet");
    });
}

/// A clean stop removes the socket and releases both locks; restarting in the hub directory
/// remembers its advertised name, without a new --dir or --advertise.
#[cfg(unix)]
#[test]
fn a_hub_restarts_in_its_directory_and_keeps_its_advertised_name() {
    let env = TestEnv::new();
    let machine = env.init_repo("hub-machine");
    let mut logs = Logs::default();
    let _filters = snapshot_filters(&env);
    let dir = env.root().join("my-hub");
    machine.jj(&["config", "set", "--user", "musubi.hub-dir", "~/other-hub"]);
    fs::create_dir(&dir).unwrap();
    let alias = env.root().join("hub-link");
    std::os::unix::fs::symlink(&dir, &alias).unwrap();
    let mut command = machine.program(musubi());
    command.args([
        "hub",
        "--dir",
        alias.to_str().unwrap(),
        "--advertise",
        "hub.example",
    ]);
    let mut hub = Hub::spawn(&env, &mut logs, "first", command, dir.clone());
    let err = musubi_fails(
        &env,
        &logs,
        &machine,
        &["hub", "--dir", dir.to_str().unwrap()],
    );
    insta::assert_snapshot!(err, @"Error: a hub is already serving $ROOT/my-hub");
    let terminate = |hub: &mut Hub, logs: &Logs| {
        assert!(dir.join("run/hub.sock").exists());
        let pid = rustix::process::Pid::from_raw(i32::try_from(hub.child.id()).unwrap()).unwrap();
        rustix::process::kill_process(pid, rustix::process::Signal::TERM).unwrap();
        wait_for(logs, "the hub to stop cleanly", || {
            hub.child.try_wait().unwrap().is_some_and(|status| {
                assert!(status.success(), "{status}");
                true
            })
        });
        assert!(!dir.join("run/hub.sock").exists());
    };
    terminate(&mut hub, &logs);
    let mut command = machine.program(musubi());
    command.arg("hub").current_dir(&dir);
    let mut restarted = Hub::spawn(&env, &mut logs, "restarted", command, dir.clone());
    insta::assert_snapshot!(restarted.printed.join("\n"), @"
    Serving 0 hives from $ROOT/my-hub
    To share a repository:               musubi create --hub hub.example
    To add another machine's copy of it: musubi join --hub hub.example
    To make a new copy of a hive:        musubi clone <name> [<dir>] --hub hub.example
    Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't hub.example.
    On this machine, leave out --hub.
    ");
    let err = musubi_fails(&env, &logs, &machine, &["hub"]);
    insta::assert_snapshot!(err, @"Error: a hub is already running, serving $ROOT/my-hub; use --dir to run another");
    terminate(&mut restarted, &logs);

    // The default can name this directory but still be too long for a Unix socket.
    // In that case the explicit short path in the instructions must remain usable.
    let long_parent = env.root().join("long".repeat(40));
    fs::create_dir(&long_parent).unwrap();
    let long_alias = long_parent.join("hub-link");
    std::os::unix::fs::symlink(&dir, &long_alias).unwrap();
    machine.jj(&[
        "config",
        "set",
        "--user",
        "musubi.hub",
        long_alias.to_str().unwrap(),
    ]);
    machine.jj(&[
        "config",
        "set",
        "--user",
        "musubi.hub-dir",
        dir.to_str().unwrap(),
    ]);
    let mut command = machine.program(musubi());
    command.arg("hub");
    let mut short = Hub::spawn(&env, &mut logs, "short", command, dir.clone());
    insta::assert_snapshot!(short.printed.last().unwrap(), @"On this machine, use --hub $ROOT/my-hub.");
    let err = musubi_fails(
        &env,
        &logs,
        &machine,
        &[
            "hub",
            "rename",
            "absent",
            "renamed",
            "--hub",
            dir.to_str().unwrap(),
        ],
    );
    insta::assert_snapshot!(err, @"Error: this hub has no hive named absent");
    terminate(&mut short, &logs);
}

/// `musubi hub` run with nothing naming its directory, on `repo`'s machine. Its data
/// directory is `$ROOT/data`, not `~/.local/share`: under macOS's long temporary directory,
/// the hub's socket there would be too long a path.
#[cfg(unix)]
fn default_hub_command(env: &TestEnv, repo: &TestRepo) -> Command {
    let mut command = repo.program(musubi());
    command
        .arg("hub")
        .env("XDG_DATA_HOME", env.root().join("data"));
    command
}

/// A hub an earlier release made in `~/musubi-hub` stays there, saying how to keep it there
/// for good; with `musubi.hub-dir` naming it, nothing needs saying. A directory there with
/// no hub in it is no hub's.
#[cfg(unix)]
#[test]
fn a_hub_made_in_the_old_default_directory_stays_there() {
    let env = TestEnv::new();
    let machine = env.init_repo("hub-machine");
    let mut logs = Logs::default();
    let _filters = snapshot_filters(&env);
    let old = env.root().join("home/musubi-hub");
    fs::create_dir_all(&old).unwrap();
    let new = env.root().join("data/musubi/hub");
    let command = default_hub_command(&env, &machine);
    let hub = Hub::spawn(&env, &mut logs, "new", command, new.clone());
    insta::assert_snapshot!(hub.greeting, @"Created a new hub in $ROOT/data/musubi/hub");
    drop(hub);
    fs::remove_dir_all(&new).unwrap();

    fs::write(old.join("hub.toml"), "").unwrap();
    let command = default_hub_command(&env, &machine);
    let hub = Hub::spawn(&env, &mut logs, "old", command, old.clone());
    insta::assert_snapshot!(hub.greeting, @"Serving 0 hives from $ROOT/home/musubi-hub");
    drop(hub);
    let log = fs::read_to_string(env.root().join("old.log")).unwrap();
    let hint = log.lines().find(|line| line.starts_with("Hint: ")).unwrap();
    insta::assert_snapshot!(hint, @"Hint: Earlier releases made hubs in ~/musubi-hub, and a later release will stop looking there. To keep serving this hub, run `jj config set --user musubi.hub-dir '~/musubi-hub'`. Don't move it: this machine's repositories name it by its path.");
    assert!(!new.exists());

    machine.jj(&["config", "set", "--user", "musubi.hub-dir", "~/musubi-hub"]);
    let command = default_hub_command(&env, &machine);
    let hub = Hub::spawn(&env, &mut logs, "configured", command, old);
    insta::assert_snapshot!(hub.greeting, @"Serving 0 hives from $ROOT/home/musubi-hub");
    drop(hub);
    let log = fs::read_to_string(env.root().join("configured.log")).unwrap();
    assert!(!log.contains("Hint: "), "{log}");
}

/// A stale clone and a hive have independently observed rewritten upstream history. An
/// unavailable origin leaves an actionable warning; rejoining with access fetches a fresh
/// value, even one neither copy knew, and preserves local work and unsnapshotted files.
#[test]
fn joining_fetches_ambiguous_remote_bookmarks() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let _filters = snapshot_filters(&env);
    let hub = Hub::start(&env, &mut logs);
    let mut daemons = Daemons::default();
    let source = env.init_repo("source");
    let origin = env.root().join("origin.git");
    source.git(&["init", "--quiet", "--bare", origin.to_str().unwrap()]);
    source.jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
    source.write_file("base", "shared history");
    source.jj(&["commit", "-m", "base"]);
    source.jj(&["bookmark", "create", "base", "-r", "@-"]);
    source.write_file("upstream", "first");
    source.jj(&["commit", "-m", "first"]);
    source.jj(&["bookmark", "create", "main", "-r", "@-"]);
    source.jj(&["git", "push", "--bookmark", "main"]);
    let alpha = env.init_repo("alpha");
    let beta = env.init_non_colocated_repo("beta");
    for repo in [&alpha, &beta] {
        repo.jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
        repo.jj(&["git", "fetch"]);
        repo.jj(&["bookmark", "track", "main", "--remote", "origin"]);
        logs.daemon_of(&env, repo);
        daemons.of(repo);
    }
    musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
    let old = beta.jj(&["log", "--no-graph", "-r", "main", "-T", "commit_id"]);
    let change = beta.jj(&["log", "--no-graph", "-r", "main", "-T", "change_id"]);
    // The incident's exact distinction: rebasing the parent changes main's commit id,
    // while preserving both its change id and its tree. Beta keeps the obsolete version.
    alpha.jj(&[
        "--ignore-immutable",
        "describe",
        "-r",
        "main-",
        "-m",
        "rewritten base",
    ]);
    let rewritten = alpha.jj(&["log", "--no-graph", "-r", "main", "-T", "commit_id"]);
    assert_ne!(old, rewritten);
    assert_eq!(
        alpha.jj(&["log", "--no-graph", "-r", "main", "-T", "change_id"]),
        change
    );
    assert_eq!(
        alpha.jj(&["diff", "--from", &old, "--to", &rewritten, "--stat"]),
        "0 files changed, 0 insertions(+), 0 deletions(-)\n"
    );
    alpha.jj(&["new", "main"]);
    alpha.write_file("later", "later work");
    alpha.jj(&["commit", "-m", "later work"]);
    alpha.jj(&["bookmark", "set", "main", "-r", "@-"]);
    alpha.jj(&["git", "push", "--bookmark", "main"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    beta.jj(&["new", "main"]);
    beta.write_file("local", "local work");
    beta.jj(&["describe", "-m", "local work"]);
    beta.jj(&["bookmark", "create", "work"]);
    let work = beta.jj(&["log", "--no-graph", "-r", "work", "-T", "change_id"]);
    let side = env.root().join("beta-side");
    beta.jj(&[
        "workspace",
        "add",
        "--colocate",
        "--name",
        "side",
        "-r",
        "work",
        side.to_str().unwrap(),
    ]);
    beta.write_file("unsnapshotted", "still here");
    // A fresh observation must also handle upstream advancing beyond either snapshot.
    source.jj(&["git", "fetch"]);
    source.jj(&["new", "main"]);
    source.write_file("fresh", "fresh upstream work");
    source.jj(&["commit", "-m", "fresh upstream work"]);
    source.jj(&["bookmark", "set", "main", "-r", "@-"]);
    source.jj(&["git", "push", "--bookmark", "main"]);
    let expected = source.jj(&["log", "--no-graph", "-r", "main", "-T", "commit_id"]);
    // The configured URL stays unchanged, so admission succeeds while the fetch cannot.
    let offline = env.root().join("offline.git");
    fs::rename(&origin, &offline).unwrap();
    let mut join = beta.program(musubi());
    join.args(["join", "--hub", &hub.url]);
    let (ok, stdout, stderr) = try_run(&logs, &env, join);
    assert!(ok, "{stdout}{stderr}\n{}", logs.dump());
    insta::assert_snapshot!(stdout, @"Joined hive origin (matched remote origin), 2 machines");
    insta::assert_snapshot!(stderr, @"
    Warning: Remote bookmarks for origin remain conflicted after joining.
    Hint: Run `musubi join` again on a machine with access to that remote.
    ");
    let remote = |name: &str| {
        let template = format!(
            "if(remote == {name:?}, if(conflict, \"conflict\", normal_target.commit_id()))"
        );
        beta.jj(&[
            "--ignore-working-copy",
            "bookmark",
            "list",
            "--all-remotes",
            "main",
            "-T",
            &template,
        ])
    };
    assert_eq!(remote("origin"), "conflict");
    fs::rename(&offline, &origin).unwrap();
    // The ampersand is legal in a Windows filename but needs quoting in jj patterns.
    // Configured filters must not omit the bookmark being repaired. Only the secondary
    // workspace is colocated here.
    beta.jj(&[
        "--ignore-working-copy",
        "git",
        "remote",
        "rename",
        "origin",
        "foo&bar",
    ]);
    beta.jj(&[
        "--ignore-working-copy",
        "config",
        "set",
        "--repo",
        r#"remotes."foo&bar".fetch-bookmarks"#,
        "topic-*",
    ]);
    let mut retry = beta.program(musubi());
    retry.arg("join").current_dir(&side);
    let (ok, stdout, stderr) = try_run(&logs, &env, retry);
    assert!(ok, "{stdout}{stderr}\n{}", logs.dump());
    assert!(stderr.is_empty(), "{stderr}");
    assert_eq!(remote("foo&bar"), expected);
    assert_eq!(
        beta.jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            "main",
            "-T",
            "commit_id"
        ]),
        expected
    );
    assert_eq!(
        beta.jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            "work",
            "-T",
            "change_id"
        ]),
        work
    );
    assert_eq!(
        fs::read_to_string(beta.path().join("local")).unwrap(),
        "local work"
    );
    assert_eq!(
        fs::read_to_string(beta.path().join("unsnapshotted")).unwrap(),
        "still here"
    );
    musubi_in(&env, &logs, &alpha, &["sync"]);
    assert_eq!(
        alpha.jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            r#"main@"foo&bar""#,
            "-T",
            "commit_id"
        ]),
        expected
    );
}

#[test]
#[cfg_attr(
    windows,
    ignore = "on Windows, the forgotten copy sometimes comes back (bos/jj-musubi#67)"
)]
fn hub_join_sync_clone_and_list() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let _filters = snapshot_filters(&env);
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    insta::assert_snapshot!(hub.greeting, @"Created a new hub in $ROOT/hub");
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    logs.daemon_of(&env, &alpha);
    logs.daemon_of(&env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);

    // The creator can opt another portable setting into the one-time clone defaults.
    let creator_config = env.root().join("config-alpha.toml");
    let mut config = fs::read_to_string(&creator_config).unwrap();
    config.push_str(
        "\nmusubi.clone-config = ['user.name', 'user.email', 'aliases.pickup']\n\
         aliases.pickup = ['log', '--no-graph']\n",
    );
    // Alpha's machine goes by another name than its host's.
    let hostname = "operation.hostname = \"alpha\"";
    assert!(config.contains(hostname), "{config}");
    let config = config.replace(hostname, "operation.hostname = \"laptop\"");
    fs::write(&creator_config, config).unwrap();

    let key = alpha.repo_path().join("musubi/machine");

    // Nothing to share yet.
    let err = musubi_fails(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
    insta::assert_snapshot!(err, @"Error: this repository has no commits to share yet; commit something first");
    // Nor is there anything to look up in a repository in no hive, which makes no key.
    let err = musubi_fails(&env, &logs, &alpha, &["debug", "op-id", "00"]);
    insta::assert_snapshot!(err, @"Error: this repository is not part of a hive");

    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "from alpha"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "ssh://git@[2001:db8::1]:22/team/project.git",
    ]);
    // Joining never starts a hive; creating does.
    let err = musubi_fails(&env, &logs, &alpha, &["join", "--hub", &hub.url]);
    insta::assert_snapshot!(err, @"Error: no hive on this hub shares history with this repository; `musubi create` starts one");
    // A refused join leaves the machine unnamed, for the next to name.
    assert!(!key.exists());
    // An agent setting up a persistent copy gets the same default as a person.
    let mut create = alpha.program(musubi());
    create.args(["create", "--hub", &hub.url, "--machine", "alpha"]);
    for variable in [
        "CODEX_THREAD_ID",
        "CODEX_SESSION_ID",
        "CLAUDE_CODE_SESSION_ID",
    ] {
        create.env(variable, "a session");
    }
    let out = run(&env, &logs, create);
    insta::assert_snapshot!(out, @"Created hive project");
    assert_eq!(
        alpha.jj(&["config", "get", "musubi.forget-after"]).trim(),
        "never"
    );

    // A copy of the same repository, with its remote spelled another way, joins it, and
    // the daemon its join started brings it alpha's work.
    fetch_history(&alpha, &beta);
    // Git accepts bracketed IPv6 in scp-style URLs; jj's remote command doesn't yet.
    beta.git(&["remote", "add", "origin", "git@[2001:db8::1]:team/project"]);
    // A matching second remote must not hide a conflicting name, even with --hive.
    beta.git(&[
        "remote",
        "set-url",
        "origin",
        "https://example.org/other.git",
    ]);
    beta.git(&[
        "remote",
        "add",
        "mirror",
        "ssh://git@[2001:db8::1]/team/project",
    ]);
    let before = beta.jj(&["op", "log", "--limit", "1", "--no-graph", "-T", "id"]);
    let remotes_before = beta.jj(&["git", "remote", "list"]);
    for extra in [None, Some("project")] {
        let mut args = vec!["join", "--hub", hub.url.as_str()];
        if let Some(name) = extra {
            args.extend(["--hive", name]);
        }
        let err = musubi_fails(&env, &logs, &beta, &args);
        insta::allow_duplicates! {
        insta::assert_snapshot!(err, @"Error: remote names origin have different fetch or push destinations than hive project recorded; give different destinations different remote names before joining");
        }
        assert_eq!(
            beta.jj(&["op", "log", "--limit", "1", "--no-graph", "-T", "id"]),
            before
        );
        assert_eq!(beta.jj(&["git", "remote", "list"]), remotes_before);
        assert!(!beta.repo_path().join("musubi/hive.toml").exists());
    }
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(list.contains("1 machine: alpha"), "{list}");
    beta.git(&["remote", "remove", "mirror"]);
    beta.git(&[
        "remote",
        "set-url",
        "origin",
        "git@[2001:db8::1]:team/project",
    ]);
    // The hub's directory given another way is the same hub, as the list and status below
    // spell it.
    let out = musubi_in(&env, &logs, &beta, &["join", "--hub", "../hub/"]);
    insta::assert_snapshot!(out, @"Joined hive project (matched remote origin), 2 machines");
    assert!(log(&beta).contains("from alpha"));
    // Without an explicit lease, the hive keeps it however long it goes unused.
    assert_eq!(
        beta.jj(&["config", "get", "musubi.forget-after"]).trim(),
        "never"
    );

    // A local rejoin checks the history too, so losing hub state cannot bypass the name.
    beta.git(&[
        "remote",
        "set-url",
        "origin",
        "https://example.org/other.git",
    ]);
    let err = musubi_fails(&env, &logs, &beta, &["join"]);
    insta::assert_snapshot!(err, @"Error: remote destinations disagree with this hive's recorded names: origin; use distinct remote names for different destinations");
    beta.git(&[
        "remote",
        "set-url",
        "origin",
        "git@[2001:db8::1]:team/project",
    ]);

    // The first join saved the hub: from now on no command needs --hub.
    let list = musubi_in(&env, &logs, &beta, &[]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      project  2 machines: alpha, beta
        here: $ROOT/beta  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    // `musubi status` shows the repository's part in the hive: every machine's working
    // copies, as jj names them here, this machine's first, and each copy.
    let (status, warnings) = status_in(&env, &logs, &beta);
    insta::assert_snapshot!(status, @"
    Hive: project on $ROOT/hub
    This machine: beta, synced N ago; the hub has all its work
    Working copies:
    beta@: kkmpptxz aa1f41eb (no description set)
    alpha/alpha@: yostqsxw b737eb34 (no description set)
    Copies:
    beta (this machine): used N ago, never forgotten
    alpha: used N ago, never forgotten
    Daemon: running (pid N), serving this repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-beta/daemon.log
    ");
    // A sync failing meanwhile, which a retry fixes, would be no fault of status's.
    assert!(!warnings.contains("Warning: The daemon"), "{warnings}");
    // Through a template -T gives, and as JSON, for a script or an agent.
    let line = musubi_in(
        &env,
        &logs,
        &beta,
        &[
            "status",
            "-T",
            "hive ++ \" \" ++ machine ++ \" \" ++ serving",
        ],
    );
    // Exactly, as a script reads it: a snapshot would ignore a trailing newline.
    assert_eq!(line, "project beta true");
    let json = musubi_in(&env, &logs, &beta, &["status", "-T", "json(self)"]);
    let json: serde_json::Value = serde_json::from_str(&json).expect(&json);
    assert_eq!(json["hive"]["name"], "project", "{json}");
    assert_eq!(json["hive"]["machine"], "beta", "{json}");
    assert_eq!(json["hive"]["copies"][0]["this"], true, "{json}");
    assert_eq!(json["daemon"]["serving"], true, "{json}");
    // Each line through a template -T gives: here the hive of each copy, then each line as
    // JSON, for a script.
    let hives = musubi_in(
        &env,
        &logs,
        &beta,
        &["list", "-T", "if(path, hive ++ \"\\n\")"],
    );
    assert_eq!(hives, "project\n");
    let json = musubi_in(&env, &logs, &beta, &["list", "-T", "json(self) ++ \"\\n\""]);
    assert!(
        json.lines().all(|line| line.starts_with("{\"hub\":"))
            && json.contains("\"hive\":\"project\",\"id\":"),
        "{json}"
    );
    // It prints through jj's formatting, labelled; the daemon's log has no colour codes.
    let labelled = musubi_in(&env, &logs, &beta, &["--color=debug"]);
    insta::assert_snapshot!(labelled, @"
    [1m<<heading::Hub >><<heading hub::$ROOT/hub>><<heading:::>>[0m
      [1m<<hive hive::project>>[0m  <<machines len::2>> machines: [38;5;2m<<machines map join machine::alpha>>[39m<<machines map join::, >>[38;5;2m<<machines map join machine::beta>>[39m
        here: <<path::$ROOT/beta>>  <<status::synced N ago>>
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    let daemon_log = fs::read_to_string(state_dir(&env, &beta).join("daemon.log")).unwrap();
    assert!(
        !daemon_log.is_empty() && !daemon_log.contains('\x1b'),
        "{daemon_log}"
    );

    // Completing as you type, the shell gets the hub's hives, and the hubs this machine knows.
    let hives = completions(&env, &logs, &beta, &["musubi", "clone", "pr"]);
    insta::assert_snapshot!(hives, @"project	2 machines: alpha, beta");
    let hubs = completions(&env, &logs, &beta, &["musubi", "join", "--hub", ""]);
    insta::assert_snapshot!(hubs, @"$ROOT/hub	the default hub");
    // `musubi.hub` in jj's config takes the place of the hub the first join saved.
    beta.jj(&["config", "set", "--user", "musubi.hub", "elsewhere"]);
    let hubs = completions(&env, &logs, &beta, &["musubi", "join", "--hub", ""]);
    insta::assert_snapshot!(hubs, @"
    elsewhere	the default hub
    $ROOT/hub
    ");
    beta.jj(&["config", "unset", "--user", "musubi.hub"]);

    // Daemons keep the machines in sync on their own.
    alpha.write_file("b", "more");
    alpha.jj(&["commit", "-m", "picked up by the daemon"]);
    wait_for(&logs, "beta's daemon to fetch alpha's commit", || {
        try_log(&beta).is_some_and(|log| log.contains("picked up by the daemon"))
    });
    // `musubi sync` goes through the daemon.
    let out = musubi_in(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(out, @"");

    // Without a terminal, `musubi top` prints once what the hub has seen: the heads that
    // came in, and each machine up to date once its daemon has reported the latest.
    let mut top = String::new();
    wait_for(&logs, "both machines to report the hive's head", || {
        top = musubi_in(&env, &logs, &beta, &["top"]);
        top.contains("2/2")
    });
    // Its counts and sizes, and so its columns' widths, depend on how the daemons' syncs fell,
    // as do the heads that came in, listed last.
    let (top, _heads) = top.split_once("\n\n  AGO").expect(&top);
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(r"up \d+[smhd](?:\d+[smhd])?,", "up <uptime>,");
    settings.add_filter(r"\d+(\.\d+)?", "N");
    // Whichever, one or more.
    settings.add_filter(r"N operation\b", "N operations");
    settings.add_filter(r"N commit\b", "N commits");
    settings.add_filter(r"N push\b", "N pushes");
    settings.add_filter(r" {2,}", "  ");
    settings.bind(|| {
        insta::assert_snapshot!(top, @"
    musubi top: N hub
    This machine's daemon is running, serving N repository.
    Hub $ROOT/hub: up <uptime>, musubi N.N, N hive.
    No issues.

    HIVE  HEAD  IN/s  OUT/s  OPS  COMMITS  MACHINES  ISSUES
    project  #N  —  —  N  N  N/N

    project since the hub started:
      received N KiB and sent N KiB
      N operations came in, with N commits, and N went out
      N pushes moved the head, and N found it moved already

      MACHINE  HEARD  AT  MUSUBI  STATE
      alpha  N ago  #N  N.N  up to date
      beta  N ago  #N  N.N  up to date
    ");
    });

    // The same hub and daemon also serve the real interactive path through a PTY.
    top_in_a_terminal(&beta);

    // Operation ids translate between this machine's and the hive's.
    let local = beta.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let translated = musubi_in(&env, &logs, &beta, &["debug", "op-id", &local]);
    assert!(
        translated.starts_with(&format!("local {local}")),
        "{translated}"
    );
    let canonical = translated
        .strip_prefix(&format!("local {local} = hive "))
        .unwrap()
        .trim();
    // An odd-length prefix exercises jj's nibble prefix resolution in both stores.
    assert_eq!(
        musubi_in(&env, &logs, &beta, &["debug", "op-id", &local[..15]]),
        translated
    );
    let reverse = musubi_in(&env, &logs, &beta, &["debug", "op-id", &canonical[..15]]);
    assert_eq!(reverse, format!("hive {canonical} = local {local}\n"));
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(&local, "$$LOCAL");
    settings.add_filter(canonical, "$$HIVE");
    settings.bind(|| {
        insta::assert_snapshot!(format!("{translated}{reverse}"), @"
        local $LOCAL = hive $HIVE
        hive $HIVE = local $LOCAL
        ");
    });
    let err = musubi_fails(&env, &logs, &beta, &["debug", "op-id", "not-hex"]);
    insta::assert_snapshot!(err, @"Error: not a hex operation id");
    // No 128-digit operation id in the fixture is all f's.
    let missing = "f".repeat(128);
    let err = musubi_fails(&env, &logs, &beta, &["debug", "op-id", &missing]);
    settings.add_filter(&missing, "$$MISSING");
    settings.bind(|| {
        insta::assert_snapshot!(err, @"Error: no operation $MISSING here or in the hive");
    });

    // A `musubi.forget-after` that isn't one fails a clone before it makes anything.
    beta.jj(&["config", "set", "--user", "musubi.forget-after", "soon"]);
    let delta = env.root().join("delta");
    let err = musubi_fails(
        &env,
        &logs,
        &beta,
        &["clone", "proj", delta.to_str().unwrap()],
    );
    insta::assert_snapshot!(err, @"Error: musubi.forget-after in your user config is neither `never` nor a duration such as `6h`; fix it and run this again");
    assert!(!delta.exists());
    // Nor does one too short.
    beta.jj(&["config", "set", "--user", "musubi.forget-after", "500ms"]);
    let err = musubi_fails(
        &env,
        &logs,
        &beta,
        &["clone", "proj", delta.to_str().unwrap()],
    );
    insta::assert_snapshot!(err, @"Error: musubi.forget-after in your user config is shorter than a second, the least it can be; fix it and run this again");
    assert!(!delta.exists());
    beta.jj(&["config", "unset", "--user", "musubi.forget-after"]);

    // A clone inherits global Git configuration too. Refuse a conflicting destination
    // before creating either the clone directory or its missing parent.
    alpha.git(&[
        "config",
        "--global",
        "remote.origin.url",
        "https://example.org/other.git",
    ]);
    let conflicting_clone = env.root().join("conflicting-parent/clone");
    let err = musubi_fails(
        &env,
        &logs,
        &alpha,
        &["clone", "project", conflicting_clone.to_str().unwrap()],
    );
    insta::assert_snapshot!(err, @"Error: remote names origin have different fetch or push destinations than hive project recorded; give different destinations different remote names before joining");
    assert!(!conflicting_clone.parent().unwrap().exists());
    alpha.git(&["config", "--global", "--unset-all", "remote.origin.url"]);

    let included = env.root().join("inherited-remote.gitconfig");
    fs::write(
        &included,
        "[remote \"origin\"]\n url = https://example.org/other.git\n",
    )
    .unwrap();
    let include = format!(
        "includeIf.gitdir:{}.path",
        env.root()
            .canonicalize()
            .unwrap()
            .join("conflicting-parent/clone/.git")
            .display()
    );
    alpha.git(&["config", "--global", &include, included.to_str().unwrap()]);
    let err = musubi_fails(
        &env,
        &logs,
        &alpha,
        &["clone", "project", "../conflicting-parent/clone"],
    );
    insta::assert_snapshot!(err, @"Error: remote names origin have different fetch or push destinations than hive project recorded; give different destinations different remote names before joining");
    assert!(!conflicting_clone.parent().unwrap().exists());
    alpha.git(&["config", "--global", "--unset-all", &include]);

    // A clone uses its own user's trunk alias, not the source repository's override.
    alpha.jj(&[
        "config",
        "set",
        "--repo",
        r#"revset-aliases."trunk()""#,
        "root()",
    ]);
    alpha.jj(&[
        "config",
        "set",
        "--user",
        r#"revset-aliases."trunk()""#,
        "main",
    ]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    // No local identity or alias is configured on this machine when clone runs.
    for key in ["user.name", "user.email", "aliases.pickup"] {
        alpha.jj(&["config", "unset", "--user", key]);
    }
    // A new machine clones the hive by a prefix of its name.
    let gamma = env.repo_handle_at("gamma", &env.root().join("src/gamma"));
    logs.op_log_of(&gamma);
    let mut clone = alpha.program(musubi());
    // A relative destination, through a parent, lands where it says, in a directory it
    // makes.
    clone.args([
        "clone",
        "proj",
        "../src/gamma",
        "--machine",
        "gamma",
        "--lease",
        "6h",
    ]);
    clone.current_dir(env.root().join("home"));
    // This temporary copy explicitly leases six hours, even with a user default of never.
    alpha.jj(&["config", "set", "--user", "musubi.forget-after", "never"]);
    clone.env("CLAUDE_CODE_SESSION_ID", "a session");
    // Per-command overrides from a caller's Git hook must not become inherited remotes.
    clone
        .env("GIT_CONFIG_COUNT", "1")
        .env("GIT_CONFIG_KEY_0", "remote.origin.url")
        .env("GIT_CONFIG_VALUE_0", "https://example.org/other.git");
    // jj colouring what musubi reads of it doesn't keep the trunk from being checked out.
    alpha.jj(&["config", "set", "--user", "ui.color", "always"]);
    clone.arg("--color=never");
    let out = run(&env, &logs, clone);
    alpha.jj(&["config", "set", "--user", "ui.color", "never"]);
    let clone_jj = |args: &[&str]| {
        let mut command = alpha.program(Path::new("jj"));
        command.current_dir(gamma.path()).args(args);
        run(&env, &logs, command)
    };
    assert_eq!(
        clone_jj(&["config", "get", "user.name"]).trim(),
        "Test User"
    );
    assert_eq!(
        clone_jj(&["config", "get", "user.email"]).trim(),
        "test@example.com"
    );
    let alias: toml::Table = toml::from_str(&format!(
        "value = {}",
        clone_jj(&["config", "get", "aliases.pickup"])
    ))
    .unwrap();
    assert_eq!(
        alias["value"].as_array().unwrap(),
        &["log", "--no-graph"].map(|s| toml::Value::String(s.to_owned()))
    );
    alpha.jj(&["config", "set", "--user", "user.name", "Changed User"]);
    alpha.jj(&[
        "config",
        "set",
        "--user",
        "user.email",
        "changed@example.com",
    ]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    assert_eq!(
        clone_jj(&["config", "get", "user.name"]).trim(),
        "Test User"
    );
    // As `jj git clone` checks out the remote's default branch.
    let parent = [
        "log",
        "--ignore-working-copy",
        "--no-graph",
        "-r",
        "@-",
        "-T",
        "bookmarks",
    ];
    assert_eq!(gamma.jj(&parent), "main");
    assert_eq!(gamma.jj(&["git", "remote", "list"]), "");
    assert_eq!(
        clone_jj(&["config", "get", "musubi.forget-after"]).trim(),
        "6h"
    );
    assert_eq!(
        fs::read_to_string(gamma.path().join("a")).unwrap(),
        "from alpha"
    );
    assert!(log(&gamma).contains("picked up by the daemon"));
    insta::assert_snapshot!(out, @"Cloned hive project into ../src/gamma");
    wait_for(&logs, "beta to hear gamma's musubi.forget-after", || {
        status_in(&env, &logs, &beta)
            .0
            .contains("forgotten once unused for 6h, in 5h")
    });

    // A machine forgotten elsewhere drops out of the hive, though its daemon still syncs,
    // until it's next used. Its `jj` commands above are work, and imported git's refs as
    // they started: one that reached the hub after the forget, or that alpha hadn't taken
    // when it forgot gamma, would bring gamma back, rightly, so let gamma's daemon send them
    // first, and alpha take them.
    // Gamma is a copy on alpha's machine, which cloned it.
    let mut sync = alpha.program(musubi());
    sync.arg("sync").current_dir(gamma.path());
    let out = run(&env, &logs, sync);
    insta::assert_snapshot!(out, @"");
    musubi_in(&env, &logs, &alpha, &["sync"]);
    let out = musubi_in(&env, &logs, &alpha, &["forget", "gamma"]);
    insta::assert_snapshot!(out, @"Forgot gamma");
    // The hub counts gamma out once it has the forget, which `musubi forget`'s sync sends.
    wait_for(&logs, "the hub to count gamma out", || {
        musubi_in(&env, &logs, &alpha, &["list"]).contains("project  2 machines: alpha, beta")
    });
    // Gamma is a copy on alpha's machine, which cloned it.
    wait_for(&logs, "gamma's daemon to hear it was forgotten", || {
        let mut status = alpha.program(musubi());
        status.arg("status").current_dir(gamma.path());
        run(&env, &logs, status).contains("Forgotten by the hive")
    });

    // A renamed hive goes by its new name on every machine, once its daemon next syncs. A
    // prefix names it, but no name at all names none.
    let out = musubi_in(&env, &logs, &alpha, &["hub", "rename", "proj", "renamed"]);
    insta::assert_snapshot!(out, @"Renamed hive project to renamed");
    let out = musubi_in(&env, &logs, &alpha, &["hub", "rename", "ren", "renamed"]);
    insta::assert_snapshot!(out, @"Hive renamed already has that name");
    let err = musubi_fails(&env, &logs, &alpha, &["hub", "rename", "", "other"]);
    insta::assert_snapshot!(err, @"Error: a hive name can't be empty");
    musubi_in(&env, &logs, &beta, &["sync"]);
    wait_for(&logs, "beta's daemon to hear the hive's new name", || {
        status_in(&env, &logs, &beta)
            .0
            .contains("Hive: renamed on ")
    });

    // A workspace override must not silently shadow a requested repo lease, including
    // when rejoining from a different workspace than the daemon serves.
    let side_path = env.root().join("beta-side");
    beta.jj(&[
        "workspace",
        "add",
        "--name",
        "side",
        side_path.to_str().unwrap(),
    ]);
    let side = env.repo_handle_at("beta", &side_path);
    beta.jj(&[
        "config",
        "set",
        "--workspace",
        "musubi.forget-after",
        "never",
    ]);
    let before = beta.jj(&["op", "log", "--limit", "1", "--no-graph", "-T", "id"]);
    for workspace in [&beta, &side] {
        let err = musubi_fails(&env, &logs, workspace, &["join", "--lease", "6h"]);
        insta::allow_duplicates! {
            insta::assert_snapshot!(err, @"Error: musubi.forget-after in workspace config for $ROOT/beta overrides --lease; unset it and run this again");
        }
        assert_eq!(
            beta.jj(&["op", "log", "--limit", "1", "--no-graph", "-T", "id"]),
            before
        );
    }
    beta.jj(&["config", "unset", "--workspace", "musubi.forget-after"]);

    // An explicit lease replaces this copy's existing never policy. A later ordinary
    // rejoin keeps the lease, and the running daemon publishes it without a restart.
    let out = musubi_in(&env, &logs, &beta, &["join", "--lease", "2h"]);
    insta::assert_snapshot!(out, @"Hive renamed is on the hub, and this repository is part of it");
    musubi_in(&env, &logs, &beta, &["join"]);
    assert_eq!(
        beta.jj(&["config", "get", "musubi.forget-after"]).trim(),
        "2h"
    );
    wait_for(&logs, "alpha to hear beta's explicit lease", || {
        status_in(&env, &logs, &alpha)
            .0
            .contains("forgotten once unused for 2h")
    });

    // Leaving takes the copy out of the hive, and stops the syncing.
    let out = musubi_in(&env, &logs, &beta, &["leave"]);
    insta::assert_snapshot!(out, @"This repository has left hive renamed.");
    wait_for(&logs, "alpha's daemon to drop beta's working copy", || {
        !alpha.jj(&["workspace", "list"]).contains("beta/")
    });
    // It keeps its working copy.
    let workspaces = beta.jj(&["workspace", "list", "-T", NAMES]);
    assert!(
        workspaces.lines().any(|line| line == "beta"),
        "{workspaces}"
    );
    let list = musubi_in(&env, &logs, &beta, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      renamed  1 machine: alpha
    Daemon: running, serving 0 repositories; doesn't start at login; `musubi daemon install` makes it
    ");

    insta::assert_snapshot!(musubi_in(&env, &logs, &alpha, &["join", "--help"]), @"
    Make the repository in the current directory part of the hive on the hub it shares history and a
    remote with.

    The hub chooses the hive that has some of the repository's history and one of its remotes' URLs. It
    refuses a repository that matches no hive or several, and a fork, which shares history but not a
    remote: choose a hive yourself with `--hive`, or start a new one with `musubi create`. It starts the
    daemon if it isn't running, and returns once the repository has synced. Git remotes and jj config
    stay local. A newer descendant of `main` can come from either copy. If remote bookmarks remain
    conflicted, it tries fetching their remotes once and syncs the result. An unavailable remote leaves
    a warning; local bookmark differences still merge as jj merges them. Automatic fetches select only
    conflicted bookmarks, with a 30-second limit per remote.

    Remote URLs recorded by explicit joins help match later copies; run `musubi join` again after
    changing them to register equivalent URLs. A name is bound to its fetch and push destinations for
    the hive's lifetime. Different destinations need distinct names; a mismatch refuses the join, even
    with `--hive`. Missing remotes are allowed.

    A bracketed IPv6 host matches in scp-style and ssh:// remote URLs alike.

    Copies are never forgotten by default, including when an agent joins them. Use `--lease 6h` for a
    temporary copy, forgotten after six hours without a local operation. An existing
    `musubi.forget-after` is kept unless `--lease` sets another duration. `musubi create` and `musubi
    clone` do the same.

    Usage: musubi join [OPTIONS]

    Options:
          --hive <HIVE>
              Choose this hive (a name, a prefix of one, or an id). Remote destination checks still
              apply

          --original
              Sync this repository as the copy it was made from, which must be gone: for a copy moved by
              copying it and deleting the original, or restored onto a new machine. musubi otherwise
              takes it for a duplicate, and syncs nothing

          --machine <MACHINE>
              This machine's name in the hive, which other machines show its workspaces under, as in
              `laptop/default`. Defaults to jj's `operation.hostname`

          --full-history
              Replicate the whole operation history, not just the current state

          --lease <DURATION>
              Forget this copy after this long without a local operation, such as `6h`. Sets
              `musubi.forget-after` in repo config, overriding its existing value

          --hub <HUB>
              The hub, as `musubi hub` prints it: the name this machine ssh-es to the hub's machine by,
              or on that machine, the hub's directory, or the machine's name or `localhost`, for the hub
              `musubi hub` serves there without `--dir`, reached without ssh [default: this machine's
              default hub]

      -h, --help
              Print help (see a summary with '-h')

    Global options:
          --socket <SOCKET>
              The daemon's control socket, in place of the usual one

          --log <FILTER>
              What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`. It
              applies to this command, not to a daemon it starts, which uses `musubi.daemon.log` in jj's
              config

          --color <WHEN>
              When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color` says]
              
              [possible values: always, never, debug, auto]
    ");
    insta::assert_snapshot!(musubi_in(&env, &logs, &alpha, &["clone", "--help"]), @"
    Create a new colocated repository from a hive.

    It makes the repository, joins it to the hive, and returns once it has synced, with the daemon
    keeping it in sync from then on. It checks out `trunk()` using this machine's jj config. It fills
    missing settings once from the defaults recorded when the hive was created: `user.name` and
    `user.email`, unless `musubi.clone-config` chose other keys there. Existing destination settings
    take precedence; sync never copies config.

    Before creating the destination, it checks inherited Git remotes and the hive's recorded names for
    conflicting destinations. It adds no Git remotes; configure one here when you want to fetch or push
    upstream.

    Usage: musubi clone [OPTIONS] <HIVE> [DESTINATION]

    Arguments:
      <HIVE>
              The hive: a name, a prefix of one, or an id, resolved once before setup

      [DESTINATION]
              A new or empty directory for the repository [default: one in the current directory named
              after the hive, as `dotfiles` for `bos/dotfiles`]. Missing parent directories are made

    Options:
          --hub <HUB>
              The hub, as `musubi hub` prints it [default: this machine's default hub]

          --machine <MACHINE>
              This machine's name in the hive. Defaults to jj's `operation.hostname`

          --lease <DURATION>
              Forget this copy after this long without a local operation, such as `6h`. Sets
              `musubi.forget-after` in repo config, overriding its existing value

      -h, --help
              Print help (see a summary with '-h')

    Global options:
          --socket <SOCKET>
              The daemon's control socket, in place of the usual one

          --log <FILTER>
              What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`. It
              applies to this command, not to a daemon it starts, which uses `musubi.daemon.log` in jj's
              config

          --color <WHEN>
              When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color` says]
              
              [possible values: always, never, debug, auto]
    ");
}

/// Screen predicates synchronize with the real process; no test waits for a refresh timer.
/// Refresh scheduling itself is tested under paused Tokio time in `top::tests`.
fn top_in_a_terminal(repo: &TestRepo) {
    use termlens::Key;
    use termlens::Terminal;

    for quit in [Key::Char('q'), Key::Ctrl('c')] {
        let command = repo.program(musubi());
        let mut terminal = Terminal::builder()
            .size(80, 24)
            .timeout(DEADLINE)
            .env_clear()
            .envs(
                command
                    .get_envs()
                    .filter_map(|(key, value)| value.map(|value| (key, value))),
            )
            .current_dir(command.get_current_dir().unwrap())
            .args(["top", "--interval", "60"])
            .spawn(musubi())
            .unwrap();
        terminal
            .wait_until(|screen| {
                screen.contains("project since the hub started:")
                    && screen.alternate_screen()
                    && !screen.cursor_visible()
            })
            .unwrap();
        terminal.send(Key::Char('-')).unwrap();
        terminal
            .wait_until(|screen| screen.contains("every 59s"))
            .unwrap();
        terminal.send(Key::Char('+')).unwrap();
        terminal
            .wait_until(|screen| screen.contains("every 1m"))
            .unwrap();
        terminal.send(Key::Char('d')).unwrap();
        terminal
            .wait_until(|screen| screen.contains("Refresh every how many seconds"))
            .unwrap();
        for key in [Key::Char('3'), Key::Char('0'), Key::Enter] {
            terminal.send(key).unwrap();
        }
        terminal
            .wait_until(|screen| screen.contains("every 30s"))
            .unwrap();
        terminal.resize(100, 30).unwrap();
        terminal
            .wait_until(|screen| screen.row_text(29).contains("q quit"))
            .unwrap();
        terminal.send(quit).unwrap();
        assert!(terminal.wait_exit().unwrap().success());
        let screen = terminal.screen();
        assert!(!screen.alternate_screen(), "{screen}");
        assert!(screen.cursor_visible(), "{screen}");
    }
}

/// `musubi completion` prints a script for each shell it names.
#[test]
fn completion_scripts_complete_the_commands() {
    for shell in ["bash", "elvish", "fish", "nushell", "powershell", "zsh"] {
        let mut command = Command::new(musubi());
        command.args(["completion", shell]).env_clear();
        if let Some(path) = std::env::var_os("LLVM_PROFILE_FILE") {
            command.env("LLVM_PROFILE_FILE", path);
        }
        let out = command.output().unwrap();
        let script = String::from_utf8(out.stdout).unwrap();
        assert!(
            out.status.success(),
            "{shell}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(script.contains("clone"), "{shell}: {script}");
    }
}

/// A command whose output stops being read, as `head` stops it in `musubi list | head`,
/// still does all it would, printing nothing more there, and exits with jj's status for
/// that.
#[test]
fn commands_carry_on_once_their_output_goes_unread() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let repo = env.init_repo("alpha");
    // Nothing reads what it prints, from the start.
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    let mut command = repo.program(musubi());
    command.arg("list").stdout(writer).stderr(Stdio::piped());
    let out = command.spawn().unwrap().wait_with_output().unwrap();
    let err = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(3), "{err}");
    // Past the line it couldn't print, to the hint after it.
    insta::assert_snapshot!(err, @"Hint: Run `musubi hub` on one machine, then the join command it prints.");
}

/// The daemon starts where the umask lets the group write what musubi makes, as musubi
/// makes its state directory, which holds the socket here, private; a `musubi daemon install`
/// the service manager refuses leaves the daemon running, and nothing installed for
/// uninstalling to remove; and uninstalling a daemon that wasn't set to start at login says
/// whether it stopped one.
#[test]
fn daemon_install_and_uninstall_leave_the_daemon_as_they_say() {
    let env = TestEnv::new();
    let logs = Logs::default();
    let repo = env.init_repo("alpha");
    let mut daemons = Daemons::default();
    daemons.of(&repo);
    // Never the real service manager, even should a regression leave the daemon installed.
    #[cfg(unix)]
    let path = with_service_manager(&env);
    let musubi_here = |args: &[&str]| {
        let mut command = repo.program(musubi());
        command.args(args);
        #[cfg(unix)]
        command.env("PATH", &path);
        command
    };
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        let mut start = repo.program(Path::new("sh"));
        start.env("PATH", &path).args([
            "-c",
            r#"umask 002 && exec "$0" daemon start"#,
            musubi().to_str().unwrap(),
        ]);
        run(&env, &logs, start);
        let mode = fs::metadata(state_dir(&env, &repo))
            .unwrap()
            .permissions()
            .mode();
        assert_eq!(mode & 0o777, 0o700);

        fs::write(env.root().join("home/fail-install"), "").unwrap();
        let (ok, out, err) = try_run(&logs, &env, musubi_here(&["daemon", "install"]));
        assert!(!ok, "{out}");
        if cfg!(target_os = "linux") {
            insta::assert_snapshot!(err, @"Error: `systemctl --user enable --now musubi.service` failed: installation refused");
        }
        assert!(err.contains("installation refused"), "{err}");
        // Without the rights SMF wants, the hint says which profile.
        if SMF {
            let deny = env.root().join("home/deny");
            fs::write(&deny, "").unwrap();
            let (ok, out, err) = try_run(&logs, &env, musubi_here(&["daemon", "install"]));
            assert!(!ok, "{out}");
            assert!(
                err.contains("Hint: If `profiles` doesn't list Service Management"),
                "{err}"
            );
            // Refused at the import, nothing is left installed, and the daemon this stopped
            // starts again as before.
            assert!(!err.contains("removes what's left"), "{err}");
            assert!(!err.contains("Couldn't start the daemon again"), "{err}");
            fs::remove_file(&deny).unwrap();
        }
    }
    #[cfg(not(unix))]
    run(&env, &logs, musubi_here(&["daemon", "start"]));
    let out = run(&env, &logs, musubi_here(&["daemon", "uninstall"]));
    assert_eq!(
        out,
        format!("Stopped the daemon. It wasn't set to start {STARTS}.\n")
    );
    let out = run(&env, &logs, musubi_here(&["daemon", "uninstall"]));
    assert_eq!(out, format!("The daemon wasn't set to start {STARTS}.\n"));
}

/// A stand-in for systemctl and launchctl, in `<root>/service-manager`, which notes each call
/// in `~/service-calls`, refuses to install the daemon while `~/fail-install` exists, and runs
/// the hub that an installed unit or agent names as the service manager would, with the
/// musubi in `MUSUBI_EXE`: a `PATH` that finds it first. It never reaches the real one. On
/// illumos, musubi_testutil's pfexec and svcs stand-ins do the same for SMF, and pfexec also
/// refuses every command while `~/deny` exists.
#[cfg(unix)]
fn with_service_manager(env: &TestEnv) -> std::ffi::OsString {
    use std::os::unix::fs::PermissionsExt as _;
    let bin = env.root().join("service-manager");
    fs::create_dir_all(&bin).unwrap();
    let script = r#"#!/bin/sh
printf '%s\n' "$*" >> "$HOME/service-calls"
pid="$HOME/hub-service.pid"
case "$*" in
    'print system/'*) test -f "$HOME/system/${2##*/}.plist"; exit $? ;;
    'show --property=LoadState --value '*)
        if test -f "$HOME/system/$4"; then echo loaded; else echo not-found; fi
        exit 0 ;;
    '--user enable --now musubi.service'|'bootstrap '*'/io.github.bos.musubi.plist')
        if test -f "$HOME/fail-install"; then
            echo 'installation refused' >&2
            exit 1
        fi ;;
    '--user enable --now musubi-hub.service')
        dir=$(sed -n 's/^WorkingDirectory=//p' \
            "$XDG_CONFIG_HOME/systemd/user/musubi-hub.service") ;;
    'enable --now musubi-hub-'*)
        dir=$(sed -n 's/^WorkingDirectory=//p' "$HOME"/system/musubi-hub-*.service) ;;
    'bootstrap '*'/io.github.bos.musubi.hub'*'.plist')
        dir=$(sed -n '/<key>WorkingDirectory<\/key>/{n;s/.*<string>\(.*\)<\/string>.*/\1/p;}' "$3") ;;
    '--user disable --now musubi-hub.service'|'disable --now musubi-hub-'*|'bootout '*'/io.github.bos.musubi.hub'*)
        if test -f "$pid"; then
            kill "$(cat "$pid")"
            rm "$pid"
        fi ;;
    'print '*) exit 1 ;;
esac
if test -n "${dir:-}"; then
    (cd "$dir" && exec "$MUSUBI_EXE" hub) </dev/null >>"$HOME/hub-service.log" 2>&1 &
    echo $! > "$pid"
fi
"#;
    for (name, text) in [
        ("systemctl", script),
        ("launchctl", script),
        ("pfexec", musubi_testutil::PFEXEC_STAND_IN),
        ("svcs", musubi_testutil::SVCS_STAND_IN),
    ] {
        let path = bin.join(name);
        fs::write(&path, text).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    }
    let sudo = bin.join("sudo");
    fs::write(
        &sudo,
        r#"#!/bin/sh
if test "$*" = '-- /usr/bin/true'; then exit 0; fi
program=$2
shift 2
case "$program" in
    /usr/bin/install)
        mkdir -p "$HOME/system"
        while test "$#" -gt 2; do shift; done
        cp "$1" "$HOME/system/${2##*/}" ;;
    /bin/rm) rm -f "$HOME/system/${2##*/}" ;;
    /bin/test) test -e "$HOME/system/${2##*/}" ;;
    /bin/launchctl)
        if test "$1" = bootstrap; then
            exec launchctl "$1" "$2" "$HOME/system/${3##*/}"
        fi
        exec launchctl "$@" ;;
    /usr/bin/systemctl) exec systemctl "$@" ;;
    *) exit 1 ;;
esac
"#,
    )
    .unwrap();
    fs::set_permissions(sudo, fs::Permissions::from_mode(0o755)).unwrap();
    let path = std::env::var_os("PATH").unwrap_or_default();
    std::env::join_paths(std::iter::once(bin).chain(std::env::split_paths(&path))).unwrap()
}

/// `musubi hub install` for a directory another hub serves refuses before it stops the hub
/// installed already, which goes on serving.
#[cfg(unix)]
#[test]
fn a_refused_hub_install_leaves_the_installed_hub_running() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let repo = env.init_repo("alpha");
    let home = env.root().join("home");
    logs.files.push(home.join("hub-service.log"));
    let path = with_service_manager(&env);
    let hub = |args: &[&str]| {
        let mut command = repo.program(musubi());
        command
            .arg("hub")
            .args(args)
            .env("PATH", &path)
            .env("MUSUBI_EXE", musubi());
        command
    };
    // Stops the installed hub, however the test ends.
    let mut uninstall = hub(&["uninstall"]);
    uninstall.stdout(Stdio::null()).stderr(Stdio::null());
    let _uninstall = Daemons(vec![uninstall]);
    // Leave room for the socket path under macOS's long temporary directory.
    repo.jj(&["config", "set", "--user", "musubi.hub-dir", "~/hub"]);
    let installed = home.join("hub");
    let installed = installed.to_str().unwrap();
    let (ok, out, hint) = try_run(&logs, &env, hub(&["install"]));
    assert!(ok, "{hint}");
    assert!(Path::new(installed).join("hub.toml").is_file());
    let first = out.lines().next().unwrap_or_default();
    assert!(
        first.starts_with("The hub serves /")
            && first.contains(&format!(", and runs {STARTS} from now on, through ")),
        "{out}"
    );
    if cfg!(target_os = "linux") {
        insta::assert_snapshot!(hint, @"Hint: To start it at boot and keep it running after logout: `musubi hub install --at-boot --dir $ROOT/home/hub`");
    }
    let pid = fs::read_to_string(home.join("hub-service.pid")).unwrap();
    let calls = fs::read_to_string(home.join("service-calls")).unwrap();

    let other = Hub::start(&env, &mut logs);
    let (ok, _, err) = try_run(
        &logs,
        &env,
        hub(&["install", "--dir", other.dir.to_str().unwrap()]),
    );
    assert!(!ok);
    insta::assert_snapshot!(err, @"Error: a hub is already serving $ROOT/hub; stop it, then run this again");
    assert_eq!(
        fs::read_to_string(home.join("service-calls")).unwrap(),
        calls
    );
    assert!(
        Command::new("kill")
            .args(["-0", pid.trim()])
            .status()
            .unwrap()
            .success()
    );
    // Switching to boot startup replaces the login service, then switching back removes
    // the system service. The daemon's separate login service is never touched. SMF starts
    // the hub at boot either way, so there is no system service to switch to.
    if !SMF && !rustix::process::getuid().is_root() {
        let out = run(
            &env,
            &logs,
            hub(&["install", "--at-boot", "--dir", installed]),
        );
        let first = out.lines().next().unwrap();
        let uid = rustix::process::getuid().as_raw();
        let suffix = if cfg!(target_os = "macos") {
            format!(".{uid}.plist.")
        } else {
            format!("-{uid}.service.")
        };
        let (prefix, suffix) = (
            first.strip_suffix(&suffix).unwrap(),
            if cfg!(target_os = "macos") {
                ".[uid].plist."
            } else {
                "-[uid].service."
            },
        );
        let first = format!("{prefix}{suffix}");
        if cfg!(target_os = "macos") {
            insta::assert_snapshot!(first, @"The hub serves $ROOT/home/hub, and runs at boot from now on, through a launchd daemon, /Library/LaunchDaemons/io.github.bos.musubi.hub.[uid].plist.");
        } else {
            insta::assert_snapshot!(first, @"The hub serves $ROOT/home/hub, and runs at boot from now on, through a systemd system unit, /etc/systemd/system/musubi-hub-[uid].service.");
        }
        let calls = fs::read_to_string(home.join("service-calls")).unwrap();
        assert!(!calls.contains("enable-linger"), "{calls}");
        let pid = fs::read_to_string(home.join("hub-service.pid")).unwrap();
        let mut other_state = hub(&["install", "--at-boot", "--dir", installed]);
        other_state.env("MUSUBI_STATE_DIR", env.root().join("other-state"));
        let (ok, _, err) = try_run(&logs, &env, other_state);
        assert!(!ok);
        insta::assert_snapshot!(err, @"Error: a boot hub service is already installed for this user; uninstall it with its original state directory first");
        assert_eq!(
            fs::read_to_string(home.join("hub-service.pid")).unwrap(),
            pid
        );
        run(&env, &logs, hub(&["install", "--dir", installed]));
    }
    let out = run(&env, &logs, hub(&["uninstall"]));
    insta::assert_snapshot!(out, @"The hub's service is removed, and the hub is stopped.");
    let out = run(&env, &logs, hub(&["uninstall"]));
    insta::assert_snapshot!(out, @"The hub had no installed service.");
}

/// One daemon serves a machine, whatever socket each command would use, and however it
/// loses its own: a socket chosen with a setting is the same from every directory; commands
/// that choose none find the daemon where it listens; a daemon can't start on another socket,
/// and says where the one running listens; and when a temp cleaner deletes the socket, the
/// list says so, the daemon listens there again, and it can be stopped meanwhile.
#[cfg(unix)]
#[test]
fn one_daemon_serves_a_machine_wherever_it_listens() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let repo = env.init_repo("alpha");
    logs.daemon_of(&env, &repo);
    let mut daemons = Daemons::default();
    daemons.of(&repo);
    let musubi_on = |socket: Option<&str>, args: &[&str]| {
        let mut command = repo.program(musubi());
        command.args(args);
        if let Some(socket) = socket {
            command.env("MUSUBI_SOCKET", socket);
        }
        command
    };
    let daemon_line = |socket: Option<&str>| {
        let out = run(&env, &logs, musubi_on(socket, &["list"]));
        out.lines()
            .find(|line| line.starts_with("Daemon:"))
            .unwrap()
            .to_owned()
    };

    let (ok, _, err) = try_run(&logs, &env, musubi_on(Some("d.sock"), &["daemon", "start"]));
    assert!(!ok);
    insta::assert_snapshot!(err, @"Error: the daemon's socket d.sock is a relative path; give an absolute one, or one starting with ~/");
    run(
        &env,
        &logs,
        musubi_on(Some("~/.musubi/d.sock"), &["daemon", "start"]),
    );
    let chosen = env.root().join("home/.musubi/d.sock");
    assert!(chosen.exists());
    assert!(!repo.path().join("~").exists());

    // No other daemon starts on the usual socket.
    run(&env, &logs, musubi_on(None, &["daemon", "start"]));
    assert!(!state_dir(&env, &repo).join("daemon.sock").exists());
    insta::assert_snapshot!(daemon_line(None), @"Daemon: running, serving 0 repositories; doesn't start at login; `musubi daemon install` makes it");
    let other = env.root().join("other.sock");
    let other = other.to_str().unwrap();
    let (ok, _, err) = try_run(&logs, &env, musubi_on(Some(other), &["daemon", "start"]));
    assert!(!ok);
    insta::assert_snapshot!(err, @"Error: this machine's daemon already runs, listening on $ROOT/home/.musubi/d.sock, not $ROOT/other.sock");
    let (ok, _, err) = try_run(&logs, &env, musubi_on(Some(other), &["daemon"]));
    assert!(!ok);
    insta::assert_snapshot!(err, @"Error: this machine's daemon already runs, listening on $ROOT/home/.musubi/d.sock, not $ROOT/other.sock");
    insta::assert_snapshot!(daemon_line(Some(other)), @"Daemon: this machine's daemon already runs, listening on $ROOT/home/.musubi/d.sock, not $ROOT/other.sock");

    // A daemon whose pid file names another build of the release is refused, whatever it says
    // when asked, with the way out, and restarting it asks it to stop, as the daemon of any
    // build is asked.
    let info = state_dir(&env, &repo).join("daemon.pid");
    let written = fs::read_to_string(&info).unwrap();
    let (kept, version) = written.trim_end().rsplit_once('\n').unwrap();
    let (release, _) = version.split_once('/').unwrap();
    // One from before pid files named builds can't be restarted, and is ended by hand.
    fs::write(&info, format!("{kept}\n")).unwrap();
    let (ok, _, err) = try_run(&logs, &env, musubi_on(None, &["daemon", "start"]));
    assert!(!ok);
    insta::assert_snapshot!(err, @"
    Error: the running daemon is from an earlier build of musubi
    Hint: End it by hand (pid N), then run `musubi daemon start`.
    ");
    fs::write(&info, format!("{kept}\n{release}/control-0\n")).unwrap();
    let (ok, _, err) = try_run(&logs, &env, musubi_on(None, &["daemon", "start"]));
    assert!(!ok);
    insta::assert_snapshot!(err, @"
    Error: the running daemon is from another build of musubi
    Hint: `musubi daemon restart` restarts it.
    ");
    let out = run(
        &env,
        &logs,
        musubi_on(Some("~/.musubi/d.sock"), &["daemon", "restart"]),
    );
    assert_eq!(out, "Started the daemon.\n");
    assert!(chosen.exists());

    // As a temp cleaner would, while the daemon is held still, so that it can't listen again
    // before the commands below look.
    let pid = daemon_pid(&state_dir(&env, &repo)).unwrap();
    let signal = |signal: &str| {
        let sent = Command::new("kill").args([signal, &pid]).status().unwrap();
        assert!(sent.success());
    };
    /// Lets the daemon go on, however the test ends, before it is stopped.
    struct Continue<'a>(&'a str);
    impl Drop for Continue<'_> {
        fn drop(&mut self) {
            Command::new("kill").args(["-CONT", self.0]).status().ok();
        }
    }
    let _continue = Continue(&pid);
    signal("-STOP");
    fs::remove_file(&chosen).unwrap();
    insta::assert_snapshot!(daemon_line(None), @"Daemon: running (pid N), but not listening on $ROOT/home/.musubi/d.sock; restart it with `musubi daemon restart`");
    let status = run(&env, &logs, musubi_on(None, &["status"]));
    let status = status.lines().find(|line| line.starts_with("Daemon:"));
    insta::assert_snapshot!(status.unwrap(), @"Daemon: running (pid N), but not listening on $ROOT/home/.musubi/d.sock; restart it with `musubi daemon restart`; doesn't start at login");
    signal("-CONT");
    // Once it notices, within seconds.
    run(&env, &logs, musubi_on(None, &["daemon", "start"]));
    assert!(chosen.exists());
    fs::remove_file(&chosen).unwrap();
    let out = run(&env, &logs, musubi_on(None, &["daemon", "stop"]));
    assert_eq!(out, "Stopped the daemon.\n");
    let out = run(&env, &logs, musubi_on(None, &["daemon", "stop"]));
    assert_eq!(out, "No daemon is running.\n");
}

/// A log file never has colour, even where `--color` asks for it.
#[test]
fn logs_have_no_colour() {
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let repo = env.init_repo("alpha");
    let mut daemons = Daemons::default();
    daemons.of(&repo);
    let log = env.root().join("foreground-daemon.log");
    logs.files.push(log.clone());
    let mut daemon = repo.program(musubi());
    daemon
        .args(["--color=always", "daemon"])
        .stdout(Stdio::null())
        .stderr(fs::File::create(&log).unwrap());
    let mut child = daemon.spawn().unwrap();
    wait_for(&logs, "the daemon to listen", || {
        fs::read_to_string(&log).is_ok_and(|text| text.contains("listening on"))
    });
    musubi_in(&env, &logs, &repo, &["daemon", "stop"]);
    child.wait().unwrap();
    let text = fs::read_to_string(&log).unwrap();
    assert!(!text.contains('\x1b'), "{text}");
    // Nor what the daemon says there itself, as when it can't start.
    let failed = env.root().join("failed-daemon.log");
    let mut daemon = repo.program(musubi());
    daemon
        .args(["--color=always", "--log=musubi=bogus", "daemon"])
        .stdout(Stdio::null())
        .stderr(fs::File::create(&failed).unwrap());
    assert!(!daemon.status().unwrap().success());
    let text = fs::read_to_string(&failed).unwrap();
    assert!(text.contains("Error: ") && !text.contains('\x1b'), "{text}");
}

/// A machine's daemon serves a repository joined after it started, without a restart, and
/// a restarted hub serves its hives again, to the daemons connected before as well.
#[test]
fn the_daemon_picks_up_new_repositories() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let help = musubi_in(&env, &logs, &alpha, &["daemon", "--help"]);
    let introduction = help.split("\nUsage:").next().unwrap();
    insta::assert_snapshot!(introduction, @"
    Run the daemon that keeps this machine's repositories in sync, or control it.

    Without a subcommand, it runs the daemon in the foreground, logging to standard error. Other
    commands start it in the background when they need it, logging to `daemon.log` in musubi's state
    directory, under systemd to the journal, or under SMF to its log in /var/svc/log.

    After detecting that the machine has woken, it ends old ssh connections and clears the delay from
    failed ssh attempts.

    On Unix, a daemon started by a command uses the latest responsive SSH agent supplied by a musubi
    command for signing and proxy hops. Commands inheriting that agent keep using it.

    It reloads changed jj settings for a repository before its next sync. Changes made during a sync
    apply to the following one; `musubi sync` waits for one with the new settings. Its own
    `musubi.daemon.*` settings need `musubi daemon restart`.

    Set `musubi.auto-snapshot = true` in jj's config to record saved edits in the background.

    When a hub runs a newer release of musubi, the daemon runs the command named by
    `musubi.upgrade-command`, if set, with `MUSUBI_UPGRADE_TO` set to that release. Once the command
    installs that release at the daemon's executable path, the daemon restarts from it. Keep the
    installer in the foreground and preserve its standard input, which on Unix holds the upgrade lock
    across daemon restarts. While the daemon that launched it runs, the command may run for up to an
    hour; a timeout stops its process group on Unix, or the command process on Windows. A command
    surviving its daemon has no timeout monitor.
    ");
    logs.daemon_of(&env, &alpha);
    logs.daemon_of(&env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "first project"]);
    musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);

    // A second repository on alpha: another hive, named after its directory, served by
    // the daemon the first join started. Its git names objects with SHA-256, which the
    // hive, the hub's store and a clone of it follow.
    let second = env.root().join("second");
    let mut init = alpha.program(Path::new("jj"));
    init.args([
        "git",
        "init",
        "--colocate",
        "--object-hash=sha256",
        second.to_str().unwrap(),
    ]);
    run(&env, &logs, init);
    let jj_in_second = |args: &[&str]| {
        let mut command = alpha.program(Path::new("jj"));
        command.args(args).current_dir(&second);
        run(&env, &logs, command)
    };
    fs::write(second.join("s"), "s").unwrap();
    jj_in_second(&["commit", "-m", "second project"]);
    let mut join = alpha.program(musubi());
    join.arg("create").current_dir(&second);
    let out = run(&env, &logs, join);
    insta::assert_snapshot!(out, @"Created hive second");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  1 machine: alpha
        here: $ROOT/alpha  synced N ago
      second  1 machine: alpha
        here: $ROOT/second  synced N ago
    Daemon: running, serving 2 repositories; doesn't start at login; `musubi daemon install` makes it
    ");

    // Cloning must not adopt another directory's files or Git history into this hive, nor
    // another repository already named as the hive is.
    let err = musubi_fails_at(&env, &logs, &alpha, env.root(), &["clone", "alpha"]);
    insta::assert_snapshot!(err, @"
    Error: destination alpha is not empty; choose a new or empty directory
    Hint: `musubi clone alpha <dir>` clones into a directory you name
    ");
    let occupied = env.root().join("occupied");
    fs::create_dir(&occupied).unwrap();
    fs::write(occupied.join("private.txt"), "not for this hive").unwrap();
    for with_git in [false, true] {
        if with_git {
            musubi_testutil::copy_tree(&alpha.path().join(".git"), &occupied.join(".git"));
        }
        let err = musubi_fails(
            &env,
            &logs,
            &alpha,
            &["clone", "alpha", occupied.to_str().unwrap()],
        );
        insta::allow_duplicates! {
            insta::assert_snapshot!(err, @"Error: destination $ROOT/occupied is not empty; choose a new or empty directory");
        }
        assert!(!occupied.join(".jj").exists());
        assert_eq!(
            fs::read_to_string(occupied.join("private.txt")).unwrap(),
            "not for this hive"
        );
    }

    // Existing user settings win, with no repository identity overrides left behind.
    beta.jj(&["config", "set", "--user", "user.name", "Existing Beta"]);
    beta.jj(&["config", "set", "--user", "user.email", "beta@example.com"]);
    // An existing empty destination is safe to use too.
    fs::create_dir(env.root().join("beta-second")).unwrap();
    let mut clone = beta.program(musubi());
    clone.args([
        "clone",
        "second",
        env.root().join("beta-second").to_str().unwrap(),
        "--hub",
        &hub.url,
    ]);
    run(&env, &logs, clone);
    let mut config_path = beta.program(Path::new("jj"));
    config_path
        .current_dir(env.root().join("beta-second"))
        .args(["config", "path", "--repo"]);
    let config = fs::read_to_string(run(&env, &logs, config_path).trim()).unwrap();
    assert!(
        !config.contains("user"),
        "clone should use beta's existing identity: {config}"
    );
    let mut name = beta.program(Path::new("jj"));
    name.current_dir(env.root().join("beta-second"))
        .args(["config", "get", "user.name"]);
    assert_eq!(run(&env, &logs, name).trim(), "Existing Beta");
    let beta_second = env.repo_handle("beta-second");
    assert!(log(&beta_second).contains("second project"));
    // As the hive's, though beta's jj would make SHA-1.
    let mut format = beta.program(Path::new("git"));
    format
        .current_dir(env.root().join("beta-second"))
        .args(["rev-parse", "--show-object-format"]);
    assert_eq!(run(&env, &logs, format).trim(), "sha256");
    // A copy of beta's own, made with SHA-1, can't join it, and is told why.
    let sha1 = env.root().join("beta-sha1");
    let jj_in_sha1 = |args: &[&str]| {
        let mut command = beta.program(Path::new("jj"));
        command.args(args).current_dir(&sha1);
        run(&env, &logs, command)
    };
    fs::create_dir(&sha1).unwrap();
    jj_in_sha1(&["git", "init", "--colocate"]);
    fs::write(sha1.join("s"), "s").unwrap();
    jj_in_sha1(&["commit", "-m", "second project"]);
    let mut join = beta.program(musubi());
    join.args(["join", "--hive", "second", "--hub", &hub.url])
        .current_dir(&sha1);
    let (ok, _, err) = try_run(&logs, &env, join);
    assert!(!ok);
    insta::assert_snapshot!(err, @"Error: this repository's git names objects with SHA-1, but hive second's with SHA-256, so it can't join it; `musubi clone second <dir>` makes a copy that can");

    // Work in the second repository reaches beta with no command run: alpha's daemon
    // serves it.
    jj_in_second(&["describe", "@-", "-m", "second project, reworded"]);
    wait_for(&logs, "the second repository's work to reach beta", || {
        try_log(&beta_second).is_some_and(|log| log.contains("second project, reworded"))
    });

    // A restarted hub serves the same hives, and the daemons connect to it again.
    hub.kill();
    // Completing a hive's name falls back on this machine's copies when the hub is out of
    // reach. An empty word completes the flags too.
    let hives = completions(&env, &logs, &alpha, &["musubi", "clone", ""]);
    insta::assert_snapshot!(hives, @"
    alpha
    second
    --hub	The hub, as `musubi hub` prints it [default: this machine's default hub]
    --machine	This machine's name in the hive. Defaults to jj's `operation.hostname`
    --lease	Forget this copy after this long without a local operation, such as `6h`. Sets `musubi.forget-after` in repo config, overriding its existing value
    --help	Print help (see more with '--help')
    --socket	The daemon's control socket, in place of the usual one
    --log	What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`. It applies to this command, not to a daemon it starts, which uses `musubi.daemon.log` in jj's config
    --color	When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color` says]
    ");
    let restarted = Hub::start(&env, &mut logs);
    insta::assert_snapshot!(restarted.greeting, @"Serving 2 hives from $ROOT/hub");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  1 machine: alpha
        here: $ROOT/alpha  synced N ago
      second  2 machines: alpha, beta
        here: $ROOT/second  synced N ago
    Daemon: running, serving 2 repositories; doesn't start at login; `musubi daemon install` makes it
    ");
    let mut describe = alpha.program(Path::new("jj"));
    describe
        .args(["describe", "@-", "-m", "second project, after the restart"])
        .current_dir(&second);
    run(&env, &logs, describe);
    wait_for(&logs, "work after the hub's restart to reach beta", || {
        try_log(&beta_second).is_some_and(|log| log.contains("after the restart"))
    });
    // A different hive's name must not shadow the id returned for the requested hive.
    let record: toml::Table =
        toml::from_str(&fs::read_to_string(alpha.repo_path().join("musubi/hive.toml")).unwrap())
            .unwrap();
    let alpha_id = record["hive"].as_str().unwrap();
    musubi_in(&env, &logs, &alpha, &["hub", "rename", "second", alpha_id]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    beta.jj(&[
        "config",
        "set",
        "--user",
        r#"revset-aliases."trunk()""#,
        "main",
    ]);
    let destination = env.root().join("beta-alpha");
    let out = musubi_in(
        &env,
        &logs,
        &beta,
        &["clone", "alpha", destination.to_str().unwrap()],
    );
    insta::assert_snapshot!(out, @"Cloned hive alpha into $ROOT/beta-alpha");
    assert_eq!(fs::read_to_string(destination.join("a")).unwrap(), "a");
    assert!(!destination.join("s").exists());
}

#[test]
fn machines_whose_workspaces_are_all_default_can_join() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "default");
    daemons.of(&alpha);
    daemons.of(&beta);
    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "from alpha"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
    // Without remotes, a repository joins the one hive it shares history with.
    fetch_history(&alpha, &beta);
    let out = musubi_in(&env, &logs, &beta, &["join", "--hub", &hub.url]);
    insta::assert_snapshot!(out, @"Joined hive alpha (matched commits), 2 machines");
    assert!(log(&beta).contains("from alpha"));
    // A copy with no workspace is still present, and can still be forgotten by name.
    beta.jj(&["workspace", "forget", "default"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    let err = musubi_fails(&env, &logs, &alpha, &["forget", "absent"]);
    insta::assert_snapshot!(err, @"Error: no machine absent shows here in hive alpha; `musubi status` names those that do");
    let out = musubi_in(&env, &logs, &alpha, &["forget", "beta"]);
    insta::assert_snapshot!(out, @"Forgot beta");
    insta::assert_snapshot!(musubi_in(&env, &logs, &alpha, &["forget", "--help"]), @"
    Forget another machine's copy of this repository: the other machines stop showing its working
    copies, and the hub stops counting it.
    
    For a machine that went away without `musubi leave`, as a short-lived machine can, or an earlier
    copy on this machine, deleted without it. Its working-copy commit is abandoned if it's empty, and
    otherwise stays as an ordinary commit. The copy keeps its remaining local workspaces. If it is still
    there, the hive shows it again as soon as it's used. A copy with no workspaces can still be
    forgotten, by its name in `musubi status`.
    
    Usage: musubi forget [OPTIONS] <MACHINE>
    
    Arguments:
      <MACHINE>
              The machine, as its working copies are named here: `laptop` for `laptop/default@`,
              `laptop-1a2b` for `laptop-1a2b/default@`, or, where even the start of its id is another
              machine's, its whole id, as in `laptop-1a2b3c4d/default@`. The name `musubi list` gives it
              will do too, if no other machine could have that name
    
    Options:
      -h, --help
              Print help (see a summary with '-h')
    
    Global options:
          --socket <SOCKET>
              The daemon's control socket, in place of the usual one
    
          --log <FILTER>
              What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`. It
              applies to this command, not to a daemon it starts, which uses `musubi.daemon.log` in jj's
              config
    
          --color <WHEN>
              When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color` says]
              
              [possible values: always, never, debug, auto]
    ");
}

/// Two machines in one hive, with their daemons running.
fn two_machines(
    env: &TestEnv,
    logs: &mut Logs,
    daemons: &mut Daemons,
    hub: &Hub,
) -> (TestRepo, TestRepo) {
    two_machines_with(env, logs, daemons, hub, |_| {})
}

/// [`two_machines`], with `configure` run in each repository before anything else.
fn two_machines_with(
    env: &TestEnv,
    logs: &mut Logs,
    daemons: &mut Daemons,
    hub: &Hub,
    configure: impl Fn(&TestRepo),
) -> (TestRepo, TestRepo) {
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    configure(&alpha);
    configure(&beta);
    logs.daemon_of(env, &alpha);
    logs.daemon_of(env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    musubi_in(env, logs, &alpha, &["create", "--hub", &hub.url]);
    fetch_history(&alpha, &beta);
    musubi_in(env, logs, &beta, &["join", "--hub", &hub.url]);
    (alpha, beta)
}

/// Background snapshots record unprompted edits in every local workspace even while the hub
/// is down. A later sync publishes those operations without any snapshotting jj command.
#[test]
fn background_snapshots_from_secondary_workspaces_reach_other_copies() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    musubi_in(&env, &logs, &alpha, &["daemon", "stop"]);
    let secondary_path = env.root().join("secondary");
    alpha.jj(&[
        "workspace",
        "add",
        "--colocate",
        secondary_path.to_str().unwrap(),
    ]);
    let moved_path = env.root().join("moved-secondary");
    // Git knows where the worktree moved. jj still has its original path.
    alpha.git(&[
        "worktree",
        "move",
        secondary_path.to_str().unwrap(),
        moved_path.to_str().unwrap(),
    ]);
    let secondary = alpha.another_copy(&moved_path);
    alpha.jj(&["config", "set", "--repo", "musubi.auto-snapshot", "true"]);
    hub.kill();

    alpha.write_file("primary.txt", "primary edit\n");
    secondary.write_file("secondary.txt", "secondary edit\n");
    musubi_in(&env, &logs, &alpha, &["daemon", "start"]);

    let has_file = |repo: &TestRepo, workspace: &str, file: &str, content: &str| {
        let output = repo.jj_output(&[
            "--ignore-working-copy",
            "file",
            "show",
            "-r",
            workspace,
            file,
        ]);
        output.status.success() && output.stdout == content.as_bytes()
    };
    wait_for(
        &logs,
        "both local workspaces to snapshot while offline",
        || {
            has_file(&alpha, "alpha@", "primary.txt", "primary edit\n")
                && has_file(&alpha, "secondary@", "secondary.txt", "secondary edit\n")
        },
    );

    let _hub = Hub::start(&env, &mut logs);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    assert!(
        has_file(&beta, "alpha/alpha@", "primary.txt", "primary edit\n"),
        "{}",
        logs.dump()
    );
    assert!(
        has_file(
            &beta,
            "alpha/secondary@",
            "secondary.txt",
            "secondary edit\n"
        ),
        "{}",
        logs.dump()
    );
}

/// The daemon knows a repository by the workspace it was made in, but commands run in any
/// other workspace of it act on the same repository: a create there names the hive after the
/// repository, a join in each doesn't have the daemon serve it twice, `musubi status` there
/// finds it served, a leave there stops the serving, and once that workspace is forgotten and
/// deleted, the repository syncs on.
#[test]
fn commands_in_another_workspace_act_on_the_repository() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    logs.daemon_of(&env, &alpha);
    daemons.of(&alpha);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    let second = env.root().join("alpha-second");
    alpha.jj(&["workspace", "add", second.to_str().unwrap()]);
    let secondary = alpha.another_copy(&second);
    for (key, value) in [
        ("musubi.auto-snapshot", "true"),
        ("fsmonitor.watchman.register-snapshot-trigger", "true"),
        ("fsmonitor.backend", "watchman"),
    ] {
        secondary.jj(&[
            "--ignore-working-copy",
            "config",
            "set",
            "--workspace",
            key,
            value,
        ]);
    }
    let in_second = |args: &[&str]| {
        let mut command = alpha.program(musubi());
        command.args(args).current_dir(&second);
        command
    };
    let out = run(&env, &logs, in_second(&["create", "--hub", &hub.url]));
    insta::assert_snapshot!(out, @"Created hive alpha");

    // Joining again from the other workspace, as to make a lost hive again.
    musubi_in(&env, &logs, &alpha, &["join"]);
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  1 machine: alpha
        here: $ROOT/alpha  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    // Listed once, by the workspace it was made in, so a daemon starting serves it once.
    let state_path = state_dir(&env, &alpha).join("state.toml");
    let state = fs::read_to_string(&state_path).unwrap();
    assert!(!state.contains("alpha-second"), "{state}");
    let (mut status, mut warnings) = (String::new(), String::new());
    wait_for(&logs, "the secondary workspace's Watchman warning", || {
        (status, warnings) = status_in(&env, &logs, &secondary);
        warnings.contains("Background snapshot skipped for alpha-second@")
    });
    insta::assert_snapshot!(status, @"
    Hive: alpha on $ROOT/hub
    This machine: alpha, synced N ago; the hub has all its work
    Working copies:
    alpha@: zsuskuln 95c553be (no description set)
    alpha-second@: zxsnswpr 0b2c4657 (no description set)
    Copies:
    alpha (this machine): used N ago, never forgotten
    Daemon: running (pid N), serving this repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");
    insta::assert_snapshot!(warnings, @"Warning: Background snapshot skipped for alpha-second@ (jj's Watchman snapshot trigger is enabled).");

    let out = run(&env, &logs, in_second(&["leave"]));
    insta::assert_snapshot!(out, @"This repository has left hive alpha.");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  no machines yet
    Daemon: running, serving 0 repositories; doesn't start at login; `musubi daemon install` makes it
    ");
    let state = fs::read_to_string(&state_path).unwrap();
    assert!(!state.contains("alpha"), "{state}");

    // With the main workspace moved away, the other can't reach the repository, and says so:
    // on Unix, whose error the snapshots show.
    #[cfg(unix)]
    {
        let moved = env.root().join("alpha-moved");
        fs::rename(alpha.path(), &moved).unwrap();
        let status = run(&env, &logs, in_second(&["status"]));
        insta::assert_snapshot!(status, @"
    Can't reach this workspace's repository, $ROOT/alpha/.jj/repo: No such file or directory (os error 2).
    Default hub: $ROOT/hub
    Daemon: running (pid N), serving 0 repositories; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");
        let (ok, _, err) = try_run(&logs, &env, in_second(&["sync"]));
        assert!(!ok);
        insta::assert_snapshot!(err, @"Error: can't reach this workspace's repository, $ROOT/alpha/.jj/repo: No such file or directory (os error 2)");
        fs::rename(&moved, alpha.path()).unwrap();
    }

    // Joined from the other workspace, which then goes, it syncs on.
    run(&env, &logs, in_second(&["join"]));
    let state = fs::read_to_string(&state_path).unwrap();
    assert!(!state.contains("alpha-second"), "{state}");
    alpha.jj(&["workspace", "forget", "alpha-second"]);
    fs::remove_dir_all(&second).unwrap();
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  1 machine: alpha
        here: $ROOT/alpha  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
}

/// A copy that left its hive can join it again, even after jj has run in it since, and
/// whether it first joined with its whole operation history or not: it carries on from the
/// history it shared, which the hive has.
#[test]
fn a_copy_can_join_again_after_leaving() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    let gamma = env.init_repo("gamma");
    logs.daemon_of(&env, &gamma);
    daemons.of(&gamma);
    fetch_history(&alpha, &gamma);
    musubi_in(
        &env,
        &logs,
        &gamma,
        &["join", "--full-history", "--hub", &hub.url],
    );
    for (repo, name) in [(&beta, "beta"), (&gamma, "gamma")] {
        musubi_in(&env, &logs, repo, &["leave"]);
        let message = format!("made in {name} while out of the hive");
        repo.write_file(name, name);
        repo.jj(&["commit", "-m", &message]);
        let out = musubi_in(&env, &logs, repo, &["join"]);
        // Each says the same.
        insta::allow_duplicates! {
            insta::assert_snapshot!(out, @"Joined hive alpha (matched commits), 3 machines");
        }
        wait_for(
            &logs,
            &format!("alpha's daemon to fetch {name}'s commit"),
            || try_log(&alpha).is_some_and(|log| log.contains(&message)),
        );
    }
    // Every machine's working copy keeps its own name.
    let list = alpha.jj(&["workspace", "list", "-T", NAMES]);
    let listed: Vec<&str> = list.lines().collect();
    assert_eq!(listed, ["alpha", "beta/beta", "gamma/gamma"], "{list}");
}

/// A hub that lost its directory knows none of its hives; one `musubi join`, in one copy,
/// makes a hive again under its id, and the other copies, their work since included, fill
/// it as they sync, with every machine's working copy under its own name. Moving to another
/// hub is `musubi join --hub` in each copy: the first makes the hive again there, under its
/// id, and the rest join it, carrying on as before.
#[test]
fn copies_make_a_lost_hive_again_on_its_hub_or_another() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    let new = Hub::start_in(&env, &mut logs, "newhub");
    // Stopped before the hubs.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    hub.kill();
    remove_dir_when_free(&hub.dir);
    hub = Hub::start(&env, &mut logs);
    insta::assert_snapshot!(hub.greeting, @"Created a new hub in $ROOT/hub");
    for (repo, file) in [(&alpha, "from alpha"), (&beta, "from beta")] {
        repo.write_file(file, file);
        repo.jj(&["commit", "-m", file]);
    }
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    insta::assert_snapshot!(err, @"Error: the hub has no record of this repository's hive; if it's the right hub, `musubi join` in this repository makes the hive again");
    let out = musubi_in(&env, &logs, &alpha, &["join"]);
    insta::assert_snapshot!(out, @"Made hive alpha again from this repository");
    let out = musubi_in(&env, &logs, &beta, &["sync"]);
    insta::assert_snapshot!(out, @"");
    wait_for(&logs, "the machines to share their work", || {
        try_log(&alpha).is_some_and(|log| log.contains("from beta"))
            && try_log(&beta).is_some_and(|log| log.contains("from alpha"))
    });
    for (repo, names) in [
        (&alpha, ["alpha", "beta/beta"]),
        (&beta, ["alpha/alpha", "beta"]),
    ] {
        let list = repo.jj(&["workspace", "list", "-T", NAMES]);
        let listed: Vec<&str> = list.lines().collect();
        assert_eq!(listed, names, "{list}");
    }

    hub.kill();
    let out = musubi_in(&env, &logs, &alpha, &["join", "--hub", &new.url]);
    insta::assert_snapshot!(out, @"Made hive alpha again from this repository");
    let out = musubi_in(&env, &logs, &beta, &["join", "--hub", &new.url]);
    insta::assert_snapshot!(out, @"Hive alpha is on the hub, and this repository is part of it");
    alpha.write_file("moved", "moved");
    alpha.jj(&["commit", "-m", "after the move"]);
    wait_for(
        &logs,
        "beta's daemon to fetch alpha's commit from the new hub",
        || try_log(&beta).is_some_and(|log| log.contains("after the move")),
    );
}

/// A hive removed from the hub is over: each copy leaves it as it hears, keeping everything
/// it has, whether its daemon hears or `musubi sync` does.
#[test]
fn copies_leave_a_removed_hive() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    // Without its daemon, which would otherwise sync at any moment and hear first, beta
    // hears through `musubi sync`.
    musubi_in(&env, &logs, &beta, &["daemon", "stop"]);
    let out = musubi_in(&env, &logs, &alpha, &["hub", "rm", "alpha"]);
    insta::assert_snapshot!(out, @"Removed hive alpha");
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    insta::assert_snapshot!(err, @"Error: this repository's hive was removed from the hub, so this repository no longer syncs with it; everything it has stays");
    assert_eq!(membership(&beta), "removed");
    let list = musubi_in(&env, &logs, &beta, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
    Daemon: not running (doesn't start at login; `musubi daemon install` makes it); `musubi daemon start` starts it
    ");
    assert!(log(&beta).contains("start"));
    // It remembers its hive was removed, rather than joining another its history matches.
    let err = musubi_fails(&env, &logs, &beta, &["join", "--hub", &hub.url]);
    insta::assert_snapshot!(err, @"Error: this repository's hive, alpha, was removed from its hub; `musubi join --hive <name>` joins another, and `musubi create` starts a new one");
    // Leaving it records that it left, as any copy that left, with nothing to tell the hive.
    let out = musubi_in(&env, &logs, &beta, &["leave"]);
    insta::assert_snapshot!(out, @"This repository has left hive alpha.");
    assert_eq!(membership(&beta), "left");
    let (status, _) = status_in(&env, &logs, &beta);
    insta::assert_snapshot!(status, @"
    This repository is not part of a hive: $ROOT/beta
    Default hub: $ROOT/hub
    Daemon: not running; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-beta/daemon.log
    ");
    // Alpha's daemon hears when it next syncs, as after an operation here.
    alpha.write_file("after", "after");
    alpha.jj(&["status"]);
    // Membership is saved before the daemon finishes leaving. Wait for its thread too,
    // since `musubi list` counts it until it exits.
    wait_for(
        &logs,
        "alpha's daemon to stop serving the removed hive",
        || {
            if membership(&alpha) != "removed" {
                return false;
            }
            let status = musubi_in(&env, &logs, &alpha, &["status", "-T", "json(self)"]);
            let status: serde_json::Value = serde_json::from_str(&status).expect(&status);
            status["daemon"]["running"] == true && status["daemon"]["served"] == 0
        },
    );
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
    Daemon: running, serving 0 repositories; doesn't start at login; `musubi daemon install` makes it
    ");
    assert!(log(&alpha).contains("start"));
}

/// `musubi pause` in one copy stops every machine syncing the hive, one whose daemon was
/// stopped at the time included, once it comes back, and `musubi status` and `musubi sync` say
/// so everywhere; jj works meanwhile, and nothing can join. `musubi pause --cancel`, from any
/// copy, lets the work done meanwhile sync. Breaking the hub's check, or the daemon's hold,
/// fails the snapshots of what `musubi sync` and `musubi status` print.
#[test]
fn a_paused_hive_holds_every_machine_until_cancelled() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    insta::assert_snapshot!(musubi_in(&env, &logs, &alpha, &["pause", "--help"]), @"
    Stop every machine syncing the hive of the repository in the current directory, until `musubi
    resume` or `musubi pause --cancel`.

    The hub refuses the hive's syncs as soon as it's paused. Each machine's daemon finds out at its next
    attempt to sync, within half a minute, or once the machine is back online, and waits; from then on,
    `musubi status` there says who paused the hive and when, as `musubi sync` does. jj works as usual
    meanwhile, and work done on a machine stays on it: it syncs once `musubi pause --cancel` lifts the
    pause, and after `musubi resume` it stays there, to bring across to a new copy. `musubi join` and
    `musubi clone` refuse a paused hive.

    It doesn't sync first, so it works in a copy whose syncing fails. Pausing a hive that is paused
    already says who paused it, and when.

    Usage: musubi pause [OPTIONS]

    Options:
          --cancel
              Lift the pause instead, from any copy: every machine syncs again, as before

      -h, --help
              Print help (see a summary with '-h')

    Global options:
          --socket <SOCKET>
              The daemon's control socket, in place of the usual one

          --log <FILTER>
              What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`. It
              applies to this command, not to a daemon it starts, which uses `musubi.daemon.log` in jj's
              config

          --color <WHEN>
              When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color` says]
              
              [possible values: always, never, debug, auto]
    ");
    // Beta is offline as the hive pauses.
    musubi_in(&env, &logs, &beta, &["daemon", "stop"]);
    let out = musubi_in(&env, &logs, &alpha, &["pause"]);
    insta::assert_snapshot!(out, @"Paused hive alpha: nothing syncs with it until `musubi resume` or `musubi pause --cancel`.");
    let out = musubi_in(&env, &logs, &alpha, &["pause"]);
    insta::assert_snapshot!(out, @"Hive alpha was paused already (by alpha, N ago).");
    let (_, hints) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(hints, @"
    Warning: Hive alpha is paused (by alpha, N ago), so nothing syncs.
    Hint: `musubi resume` in a copy you've cleaned up resets the hive from it; `musubi pause --cancel` in any copy lets it sync again unchanged.
    ");

    // jj works on both machines meanwhile, and nothing syncs.
    alpha.write_file("from-alpha", "alpha");
    alpha.jj(&["commit", "-m", "alpha while paused"]);
    beta.write_file("from-beta", "beta");
    beta.jj(&["commit", "-m", "beta while paused"]);
    let err = musubi_fails(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(err, @"
    Error: hive alpha is paused (by alpha, N ago)
    Hint: `musubi resume` in a copy you've cleaned up resets the hive from it; `musubi pause --cancel` in any copy lets it sync again unchanged.
    ");
    // Beta's daemon, back, hears at its first sync, and waits.
    musubi_in(&env, &logs, &beta, &["daemon", "start"]);
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    insta::assert_snapshot!(err, @"
    Error: hive alpha is paused (by alpha, N ago)
    Hint: `musubi resume` in a copy you've cleaned up resets the hive from it; `musubi pause --cancel` in any copy lets it sync again unchanged.
    ");
    let (_, hints) = status_in(&env, &logs, &beta);
    insta::assert_snapshot!(hints, @"
    Warning: Hive alpha is paused (by alpha, N ago), so nothing syncs.
    Hint: `musubi resume` in a copy you've cleaned up resets the hive from it; `musubi pause --cancel` in any copy lets it sync again unchanged.
    ");
    let clone = env.root().join("clone");
    let err = musubi_fails(
        &env,
        &logs,
        &alpha,
        &["clone", "alpha", clone.to_str().unwrap(), "--hub", &hub.url],
    );
    insta::assert_snapshot!(err, @"Error: hive alpha is paused (by alpha); it can be joined once `musubi pause --cancel` or `musubi resume` is run in one of its copies");
    assert!(!log(&alpha).contains("beta while paused"));
    assert!(!log(&beta).contains("alpha while paused"));

    // Beta's daemon waited rather than retrying, which logs each failure as a warning.
    let daemon_log = fs::read_to_string(state_dir(&env, &beta).join("daemon.log")).unwrap();
    let paused: Vec<&str> = daemon_log
        .lines()
        .filter(|line| line.contains("the hive is paused"))
        .collect();
    assert!(
        !paused.is_empty()
            && paused
                .iter()
                .all(|line| line.contains("waiting for the pause")),
        "{daemon_log}"
    );

    // Lifted from another copy, everything syncs, with nothing lost: beta sends its work as
    // the pause lifts, and the daemons, told of each other's, send and fetch the rest.
    let out = musubi_in(&env, &logs, &beta, &["pause", "--cancel"]);
    insta::assert_snapshot!(out, @"Hive alpha syncs again.");
    let out = musubi_in(&env, &logs, &beta, &["pause", "--cancel"]);
    insta::assert_snapshot!(out, @"Hive alpha isn't paused.");
    for repo in [&alpha, &beta] {
        wait_for(&logs, "both machines' work everywhere", || {
            let log = log(repo);
            log.contains("alpha while paused") && log.contains("beta while paused")
        });
        let (_, hints) = status_in(&env, &logs, repo);
        assert_eq!(hints, "");
    }
}

/// `musubi resume`, in a copy cleaned up with jj while its hive is paused, `jj op abandon`
/// included, makes the hive again from that copy alone: a secret it no longer shows is in none
/// of the new hive's objects, though the old hive had it, and the copy goes on syncing, a jj
/// command at an operation from before a reset included. The guide's way of removing the old
/// history from that copy's disk works. Every other copy, one online and one offline
/// throughout, hears at its next contact, stops syncing for good with its unsent work kept,
/// never joins a hive again, even after leaving without hearing of the reset, and gets its work
/// across to a new copy, which syncs. Resume refuses a hive that isn't paused, or whose head is
/// past what the copy has, unless forced. Taking out the hub's check of the head fails the
/// snapshot of the refusal; carrying the old history into the new hive fails the search of its
/// objects; a daemon that didn't stop on the reset fails the snapshots of beta's `musubi sync`
/// and status; reading a pre-reset realization's dangling attribute as the hive's fails alpha's
/// sync after the late command; taking out the hub's refusal of a join that carries a reset
/// hive's history lets gamma join. It can't reach a crash partway through a reset, which
/// `a_reset_hive_starts_again_under_a_new_id` covers on the hub.
#[test]
fn a_resumed_hive_leaves_its_old_history_behind() {
    const SECRET: &str = "hunter2-correct-horse-battery";
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    let gamma = env.init_repo("gamma");
    logs.daemon_of(&env, &gamma);
    daemons.of(&gamma);
    fetch_history(&alpha, &gamma);
    musubi_in(&env, &logs, &gamma, &["join", "--hub", &hub.url]);
    let hive_id = |repo: &TestRepo| musubi_in(&env, &logs, repo, &["status", "-T", "id"]);
    let old = hive_id(&alpha);
    // Everything a hive's store holds, as git has it: every object, packed or loose.
    let hub_dir = hub.dir.clone();
    let objects = |id: &str| {
        let mut git = Command::new("git");
        git.args(["cat-file", "--batch-all-objects", "--batch"])
            .current_dir(hub_dir.join(id).join("git"));
        String::from_utf8_lossy(&git.output().unwrap().stdout).into_owned()
    };

    // A secret, committed and synced everywhere.
    alpha.write_file("secret.txt", SECRET);
    alpha.jj(&["commit", "-m", "add the secret"]);
    let secret = alpha.jj(&[
        "log",
        "--no-graph",
        "-r",
        "description(substring:\"add the secret\")",
        "-T",
        "commit_id",
    ]);
    for repo in [&beta, &gamma] {
        wait_for(&logs, "the secret on every machine", || {
            log(repo).contains("add the secret")
        });
    }
    assert!(objects(&old).contains(SECRET));
    // Gamma goes offline for good, with work it never sends.
    musubi_in(&env, &logs, &gamma, &["daemon", "stop"]);
    gamma.write_file("from-gamma", "gamma");
    gamma.jj(&["commit", "-m", "gamma offline"]);

    insta::assert_snapshot!(musubi_in(&env, &logs, &alpha, &["resume", "--help"]), @r#"
    Make the paused hive of the repository in the current directory again from this copy's current state
    alone, deleting its old history from the hub.

    For removing something from every machine, such as a secret committed by mistake: pause the hive
    with `musubi pause`, remove it from this copy with jj (`jj abandon`, say), then run this. The hive
    starts again as this copy's current state, with none of its operation history, so only the commits
    this copy shows go to the hub. This copy goes on syncing, and keeps its own operation history.

    Every other copy stops syncing for good once it hears, and keeps everything it has: replace it with
    `musubi clone`, bringing across any work the new copy lacks. "Clean up history on every machine" in
    the user guide says how.

    It refuses if the hive has work this copy hasn't received, unless `--force`.

    Usage: musubi resume [OPTIONS]

    Options:
      -y, --yes
              Reset the hive without asking first

          --force
              Reset it though it has work, from other machines, that this copy hasn't received, which
              then reaches the new hive only if they bring it across

      -h, --help
              Print help (see a summary with '-h')

    Global options:
          --socket <SOCKET>
              The daemon's control socket, in place of the usual one

          --log <FILTER>
              What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`. It
              applies to this command, not to a daemon it starts, which uses `musubi.daemon.log` in jj's
              config

          --color <WHEN>
              When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color` says]
              
              [possible values: always, never, debug, auto]
    "#);
    let err = musubi_fails(&env, &logs, &alpha, &["resume", "--yes"]);
    insta::assert_snapshot!(err, @"
    Error: hive alpha isn't paused
    Hint: Run `musubi pause`, clean up this copy with jj, then run `musubi resume` again.
    ");
    // Alpha misses beta's latest work, which reaches the hub before the pause.
    musubi_in(&env, &logs, &alpha, &["daemon", "stop"]);
    beta.write_file("from-beta", "beta");
    beta.jj(&["commit", "-m", "beta sent"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    musubi_in(&env, &logs, &alpha, &["pause"]);
    let err = musubi_fails(&env, &logs, &alpha, &["resume", "--yes"]);
    insta::assert_snapshot!(err, @"
    Error: hive alpha has work from beta that this copy hasn't received
    Hint: Run `musubi pause --cancel` and `musubi sync` here, then `musubi pause` and clean up again; or run `musubi resume --force` to leave that work out.
    ");
    // Lifting the pause brings it, and alpha pauses again.
    musubi_in(&env, &logs, &alpha, &["pause", "--cancel"]);
    assert!(log(&alpha).contains("beta sent"));
    musubi_in(&env, &logs, &alpha, &["pause"]);
    beta.write_file("beta-paused", "beta");
    beta.jj(&["commit", "-m", "beta while paused"]);
    // Alpha cleans up, abandoning the operations too, which would stop it syncing, and resets
    // the hive from what it has now.
    alpha.jj(&["abandon", "-r", secret.trim()]);
    alpha.jj(&["op", "abandon", "..@-"]);
    assert!(!alpha.path().join("secret.txt").exists());
    let err = musubi_fails(&env, &logs, &alpha, &["resume"]);
    insta::assert_snapshot!(err, @"
    Error: `musubi resume` asks before it resets the hive
    Hint: Run it in a terminal, or with `--yes` to reset it without asking.
    ");
    let mut resume = alpha.program(musubi());
    resume.args(["resume", "--yes"]);
    let (ok, out, err) = try_run(&logs, &env, resume);
    assert!(ok, "{out}{err}\n{}", logs.dump());
    insta::assert_snapshot!(format!("{out}{err}"), @r#"
    Reset hive alpha from this copy; the hub has none of its old history.
    Hint: This machine still has the old history; "Remove data from a machine's disk" in the user guide says how to remove it.
    "#);
    let new = hive_id(&alpha);
    assert_ne!(new, old);
    let stored = objects(&new);
    assert!(!stored.contains(SECRET) && !stored.contains("add the secret"));
    assert!(stored.contains("beta sent"), "{stored}");
    let removed = hub_dir.join("removed");
    wait_for(&logs, "the old store deleted", || {
        let tombstone = fs::read_dir(&removed)
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        fs::read_dir(tombstone).unwrap().count() == 2
    });

    // Alpha removes the old history from its own disk, as the guide says, and syncs on.
    let reset_op = alpha.jj(&[
        "op",
        "log",
        "--no-graph",
        "-T",
        "if(description.starts_with(\"musubi: reset the hive\"), id)",
    ]);
    alpha.jj(&["op", "abandon", &format!("..{}-", reset_op.trim())]);
    let mut git = Command::new("git");
    git.args(["reflog", "expire", "--expire=now", "--all"])
        .current_dir(alpha.path());
    assert!(git.status().unwrap().success());
    alpha.jj(&["util", "gc", "--expire=now"]);
    let mut git = Command::new("git");
    git.args(["cat-file", "--batch-all-objects", "--batch"])
        .current_dir(alpha.path());
    assert!(!String::from_utf8_lossy(&git.output().unwrap().stdout).contains(SECRET));
    alpha.write_file("after", "after");
    alpha.jj(&["commit", "-m", "alpha after the reset"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    let (_, hints) = status_in(&env, &logs, &alpha);
    assert_eq!(hints, "");

    // Beta hears at its next sync, and keeps what it did meanwhile.
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    insta::assert_snapshot!(err, @r#"
    Error: hive alpha was reset (by alpha, N ago) to remove history this copy still has, so it no longer syncs
    Hint: Make a new copy with `musubi clone alpha <dir>`, bring across any work it lacks, then delete this copy; "Clean up history on every machine" in the user guide says how.
    "#);
    assert_eq!(membership(&beta), "reset");
    let (status, hints) = status_in(&env, &logs, &beta);
    insta::assert_snapshot!(format!("{status}{hints}"), @r#"
    Hive alpha was reset (by alpha, N ago) to remove history this copy still has, so it no longer syncs.
    Default hub: $ROOT/hub
    Daemon: running (pid N), serving 0 repositories; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-beta/daemon.log
    Hint: Make a new copy with `musubi clone alpha <dir>`, bring across any work it lacks, then delete this copy; "Clean up history on every machine" in the user guide says how.
    "#);
    assert!(log(&beta).contains("beta while paused"));
    let err = musubi_fails(&env, &logs, &beta, &["join"]);
    insta::assert_snapshot!(err, @"
    Error: this copy has history hive alpha was reset to remove, so it can't join a hive again
    Hint: Make a new copy with `musubi clone alpha <dir>` instead.
    ");
    insta::assert_snapshot!(musubi_in(&env, &logs, &beta, &["leave"]), @"This repository has left hive alpha.");
    let err = musubi_fails(&env, &logs, &beta, &["join", "--hub", &hub.url]);
    insta::assert_snapshot!(err, @"
    Error: this copy has history hive alpha was reset to remove, so it can't join a hive again
    Hint: Make a new copy with `musubi clone alpha <dir>` instead.
    ");
    // Its work goes to a new copy as files.
    let rescued = env.root().join("beta-new");
    musubi_in(
        &env,
        &logs,
        &beta,
        &["clone", "alpha", rescued.to_str().unwrap()],
    );
    fs::copy(beta.path().join("beta-paused"), rescued.join("beta-paused")).unwrap();
    jj_at(
        &env,
        &logs,
        &beta,
        &rescued,
        &["commit", "-m", "beta rescued"],
    );
    musubi_at(&env, &logs, &beta, &rescued, &["sync"]);

    // Gamma, offline throughout, leaves while the hub is out of reach, without hearing of the
    // reset. Joining once the hub is back would bring the old history into the new hive.
    hub.kill();
    musubi_in(&env, &logs, &gamma, &["leave", "--force"]);
    assert_eq!(membership(&gamma), "left");
    hub = Hub::start(&env, &mut logs);
    let err = musubi_fails(&env, &logs, &gamma, &["join", "--hub", &hub.url]);
    insta::assert_snapshot!(err, @r#"
    Error: hive alpha was reset (by alpha, N ago) to remove history this copy still has, so it no longer syncs
    Hint: Make a new copy with `musubi clone alpha <dir>`, bring across any work it lacks, then delete this copy; "Clean up history on every machine" in the user guide says how.
    "#);
    assert_eq!(membership(&gamma), "reset");
    let err = musubi_fails(&env, &logs, &gamma, &["resume", "--yes"]);
    assert!(err.contains("was reset"), "{err}");
    assert!(log(&gamma).contains("gamma offline"));
    // Its work goes to a new copy through a bookmark.
    gamma.jj(&["bookmark", "create", "rescue-1", "-r", "@-"]);
    let rescued = env.root().join("gamma-new");
    musubi_in(
        &env,
        &logs,
        &gamma,
        &["clone", "alpha", rescued.to_str().unwrap()],
    );
    let root = gamma.jj(&["git", "root"]);
    for args in [
        &["git", "remote", "add", "rescue", root.trim()][..],
        &["git", "fetch", "--remote", "rescue", "-b", "rescue-*"],
        &["bookmark", "track", "rescue-*", "--remote", "rescue"],
        &["git", "remote", "remove", "rescue"],
    ] {
        jj_at(&env, &logs, &gamma, &rescued, args);
    }
    musubi_at(&env, &logs, &gamma, &rescued, &["sync"]);
    wait_for(&logs, "the rescued work on alpha", || {
        let log = log(&alpha);
        log.contains("beta rescued") && log.contains("gamma offline")
    });
    assert!(!log(&alpha).contains("add the secret"));
    assert!(!objects(&new).contains(SECRET));

    // Reset again, forced, a jj command at an operation from before it, which has the new
    // copies' work, carries on from it.
    musubi_in(&env, &logs, &alpha, &["pause"]);
    let before = alpha.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    musubi_in(&env, &logs, &alpha, &["resume", "--yes", "--force"]);
    alpha.jj(&[
        "--ignore-working-copy",
        "--at-op",
        before.trim(),
        "bookmark",
        "create",
        "late",
        "-r",
        "main",
    ]);
    alpha.write_file("later", "later");
    alpha.jj(&["commit", "-m", "alpha after the second reset"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    let (_, hints) = status_in(&env, &logs, &alpha);
    assert_eq!(hints, "");
}

/// Whether the repository is part of the hive its record names: `joined`, `left`, `removed`
/// or `reset`.
fn membership(repo: &TestRepo) -> String {
    let record = fs::read_to_string(repo.repo_path().join("musubi/hive.toml")).unwrap();
    let line = record
        .lines()
        .find_map(|line| line.strip_prefix("state = "))
        .unwrap_or_else(|| panic!("no state in {record}"));
    line.trim_matches('"').to_owned()
}

/// With its hub gone, `musubi sync` through the daemon says why at once, as it does without
/// a daemon, rather than once the sync's requests time out, and `musubi list` says it too.
/// `musubi leave` fails, leaving the repository part of its hive, served and with its working
/// copy; `--force` leaves without telling the hive.
#[test]
fn a_copy_whose_hub_is_gone_says_so_at_once_and_leaves_only_if_forced() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    logs.daemon_of(&env, &alpha);
    daemons.of(&alpha);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
    hub.kill();
    let started = Instant::now();
    let err = musubi_fails(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(err, @"Error: no hub is serving $ROOT/hub");
    assert!(started.elapsed() < Duration::from_secs(10), "{err}");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub: no hub is serving $ROOT/hub. This machine's copies:
      alpha
        here: $ROOT/alpha  sync failing: no hub is serving $ROOT/hub
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    let err = musubi_fails(&env, &logs, &alpha, &["leave"]);
    insta::assert_snapshot!(err, @"
    Error: couldn't tell hive alpha that this repository leaves: no hub is serving $ROOT/hub
    Hint: `musubi leave --force` leaves without telling the hive
    ");
    assert_eq!(membership(&alpha), "joined");
    // It keeps its working copy, though on the empty commit its forget abandoned.
    let workspaces = alpha.jj(&["workspace", "list", "--ignore-working-copy", "-T", NAMES]);
    assert!(
        workspaces.lines().any(|line| line == "alpha"),
        "{workspaces}"
    );
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub: no hub is serving $ROOT/hub. This machine's copies:
      alpha
        here: $ROOT/alpha  sync failing: no hub is serving $ROOT/hub
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    assert!(log(&alpha).contains("start"));
    // As soon as the hub is back, a sync goes through: what the daemon knew is not stale.
    hub = Hub::start(&env, &mut logs);
    insta::assert_snapshot!(hub.greeting, @"Serving 1 hive from $ROOT/hub");
    let out = musubi_in(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(out, @"");
    hub.kill();
    let out = musubi_in(&env, &logs, &alpha, &["leave", "--force"]);
    insta::assert_snapshot!(out, @"This repository has left hive alpha.");
    assert_eq!(membership(&alpha), "left");
    // With a new commit to work on, which no next work of its in the hive will make now.
    let at = alpha.jj(&[
        "log",
        "--ignore-working-copy",
        "-r",
        "@",
        "--no-graph",
        "-T",
        "if(hidden, \"hidden\", \"visible\")",
    ]);
    assert_eq!(at.trim(), "visible");
}

/// A daemon whose hub runs a newer release runs `musubi.upgrade-command`, telling it the
/// release, and once its binary is that release, starts again from it, in place. Here the hub
/// runs a build deployed from source, whose release says when it was deployed and its commit,
/// and the command first installs a stand-in that says it is that build, and runs the real
/// binary; the daemon run from that runs the command again, which installs nothing this time,
/// so the daemon carries on as it is, and `musubi status` says why.
#[cfg(unix)]
#[test]
fn the_daemon_upgrades_towards_a_newer_hub() {
    let env = TestEnv::with_real_op_times();
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(&regex_escape(musubi().to_str().unwrap()), "[musubi]");
    settings.add_filter(
        &regex_escape(&format!("musubi {}", musubi_sync::wire::RELEASE)),
        "musubi [this release]",
    );
    settings.add_filter(
        &regex_escape(&format!("jj-lib {}", musubi_sync::wire::JJ_LIB_VERSION)),
        "jj-lib [this jj version]",
    );
    settings.add_filter(r"protocol \d+", "protocol N");
    let _release = settings.bind_to_scope();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    logs.daemon_of(&env, &alpha);
    daemons.of(&alpha);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    // The daemon runs from a copy of musubi, which the command can replace.
    let bin = env.root().join("bin");
    fs::create_dir(&bin).unwrap();
    let exe = bin.join("musubi");
    fs::copy(musubi(), &exe).unwrap();
    let (ran, installed) = (env.root().join("ran"), env.root().join("installed"));
    let script = env.root().join("upgrade.sh");
    fs::write(
        &script,
        format!(
            r#"echo "$MUSUBI_UPGRADE_TO" >>"{ran}"
[ -e "{installed}" ] && exit 0
: >"{installed}"
printf '#!/bin/sh\n[ "$1" = --version ] && exec echo musubi 99.0.0+20991231235959.ffffffffffff\nexec "%s" "$@"\n' \
  "{real}" >"{exe}.new"
chmod +x "{exe}.new" && mv "{exe}.new" "{exe}"
"#,
            ran = ran.display(),
            installed = installed.display(),
            real = musubi().display(),
            exe = exe.display(),
        ),
    )
    .unwrap();
    // As a TOML string, since `jj config set` reads TOML.
    let command = format!("'sh \"{}\"'", script.display());
    alpha.jj(&[
        "config",
        "set",
        "--user",
        "musubi.upgrade-command",
        &command,
    ]);
    let mut create = alpha.program(&exe);
    create.args(["create", "--hub", &hub.url]);
    run(&env, &logs, create);
    let state = state_dir(&env, &alpha);
    let pid = daemon_pid(&state).unwrap();
    let help = musubi_in(&env, &logs, &alpha, &["daemon", "--help"]);
    insta::assert_snapshot!(help, @"
    Run the daemon that keeps this machine's repositories in sync, or control it.

    Without a subcommand, it runs the daemon in the foreground, logging to standard error. Other
    commands start it in the background when they need it, logging to `daemon.log` in musubi's state
    directory, under systemd to the journal, or under SMF to its log in /var/svc/log.

    After detecting that the machine has woken, it ends old ssh connections and clears the delay from
    failed ssh attempts.

    On Unix, a daemon started by a command uses the latest responsive SSH agent supplied by a musubi
    command for signing and proxy hops. Commands inheriting that agent keep using it.

    It reloads changed jj settings for a repository before its next sync. Changes made during a sync
    apply to the following one; `musubi sync` waits for one with the new settings. Its own
    `musubi.daemon.*` settings need `musubi daemon restart`.

    Set `musubi.auto-snapshot = true` in jj's config to record saved edits in the background.

    When a hub runs a newer release of musubi, the daemon runs the command named by
    `musubi.upgrade-command`, if set, with `MUSUBI_UPGRADE_TO` set to that release. Once the command
    installs that release at the daemon's executable path, the daemon restarts from it. Keep the
    installer in the foreground and preserve its standard input, which on Unix holds the upgrade lock
    across daemon restarts. While the daemon that launched it runs, the command may run for up to an
    hour; a timeout stops its process group on Unix, or the command process on Windows. A command
    surviving its daemon has no timeout monitor.

    Usage: musubi daemon [OPTIONS] [COMMAND]

    Commands:
      start      Start the daemon in the background, unless it is running
      stop       Stop the running daemon
      restart    Stop the running daemon, if any, and start a new one in the background
      install    Start the daemon at login (at boot on illumos) from now on, and now: through a launchd
                 agent on macOS, a systemd user unit on Linux, an SMF service on illumos, or a Run
                 registry entry on Windows
      uninstall  Stop starting the daemon at login (at boot on illumos), and stop it
      help       Print this message or the help of the given subcommand(s)

    Options:
      -h, --help
              Print help (see a summary with '-h')

    Global options:
          --socket <SOCKET>
              The daemon's control socket, in place of the usual one

          --log <FILTER>
              What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`. It
              applies to this command, not to a daemon it starts, which uses `musubi.daemon.log` in jj's
              config

          --color <WHEN>
              When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color` says]
              
              [possible values: always, never, debug, auto]
    ");
    hub.kill();
    let _newer = serve_newer_hub(&hub.dir);
    musubi_fails(&env, &logs, &alpha, &["sync"]);
    let failed = state.join("upgrade-failed");
    wait_for(&logs, "the upgrade to fail", || failed.exists());
    assert_eq!(
        fs::read_to_string(&ran).unwrap(),
        "99.0.0+20991231235959.ffffffffffff\n99.0.0+20991231235959.ffffffffffff\n"
    );
    assert_eq!(
        daemon_pid(&state).unwrap(),
        pid,
        "the daemon is another process"
    );
    assert!(daemon_logged(
        &env,
        &alpha,
        "upgraded to musubi 99.0.0+20991231235959.ffffffffffff; starting again"
    ));
    let (stdout, stderr) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(stdout, @"
    Hive: alpha on $ROOT/hub
    This machine: alpha, synced N ago; the hub lacks its latest work
    Working copies:
    alpha@: zsuskuln 95c553be (no description set)
    Copies:
    alpha (this machine): used N ago, never forgotten
    Daemon: running (pid N), serving this repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    Upgrade: upgrading to musubi 99.0.0+20991231235959.ffffffffffff failed: musubi.upgrade-command succeeded, but [musubi] is musubi [this release], not musubi 99.0.0+20991231235959.ffffffffffff
    ");
    insta::assert_snapshot!(stderr, @"
    Hint: Once that's fixed, `musubi daemon restart` tries again.
    Warning: Syncing fails: incompatible peer: protocol N with jj-lib [this jj version] (musubi 99.0.0+20991231235959.ffffffffffff), but this is protocol N with jj-lib [this jj version] (musubi [this release]); run the same release of musubi on the hub and every machine
    Hint: The daemon keeps trying. Its log: $ROOT/home/musubi-alpha/daemon.log
    ");
}

/// The example `musubi.upgrade-command`, `contrib/upgrade-from-source`, run from another
/// directory as the daemon runs it, installs the release it is told from that release's tag in
/// a jj repository of musubi's source, and a build deployed from source from that build's
/// commit, rather than from `main`, which has moved on. With `--deploy`, it installs `main` as a
/// build named for the time, in UTC, and its commit. It builds neither the edit in progress in
/// the repository's working copy nor snapshots it, and refuses, installing nothing, no release,
/// a release with `--deploy`, what names neither a release nor a build, and a release or build
/// the repository lacks. Once the repository has a remote, it refuses to deploy what the remote
/// lacks, which no machine could fetch. The source is a stand-in whose `musubi` says only the
/// release musubi's own build script names, which builds in a second. Fetching a commit or tag
/// from a remote isn't tried.
#[cfg(unix)]
#[test]
fn the_example_upgrade_command_installs_from_source() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let source = env.init_repo("source");
    let manifest = |release: &str| {
        format!(
            "[workspace]\nmembers = [\"crates/musubi\"]\nresolver = \"3\"\n\n\
             [workspace.package]\nversion = \"{release}\"\nedition = \"2024\"\n"
        )
    };
    let lock = |release: &str| {
        format!("version = 4\n\n[[package]]\nname = \"jj-musubi\"\nversion = \"{release}\"\n")
    };
    source.write_file("Cargo.toml", &manifest("0.2.0"));
    source.write_file("Cargo.lock", &lock("0.2.0"));
    source.write_file(
        "crates/musubi/Cargo.toml",
        "[package]\nname = \"jj-musubi\"\nversion.workspace = true\n\
         edition.workspace = true\n\n[[bin]]\nname = \"musubi\"\npath = \"main.rs\"\n",
    );
    source.write_file(
        "crates/musubi/build.rs",
        include_str!("../../musubi-sync/build.rs"),
    );
    source.write_file(
        "crates/musubi/main.rs",
        "fn main() {\n    println!(\"musubi {}\", env!(\"MUSUBI_RELEASE\"));\n}\n",
    );
    source.jj(&["commit", "-m", "musubi 0.2.0"]);
    source.jj(&["tag", "set", "v0.2.0", "-r", "@-"]);
    source.write_file("Cargo.toml", &manifest("0.2.1"));
    source.write_file("Cargo.lock", &lock("0.2.1"));
    source.jj(&["commit", "-m", "musubi 0.2.1"]);
    source.jj(&["bookmark", "create", "main", "-r", "@-"]);
    let short_id = |revision: &str| {
        let log = [
            "log",
            "--ignore-working-copy",
            "--no-graph",
            "-r",
            revision,
            "-T",
            "commit_id.short()",
        ];
        source.jj(&log)
    };
    let (tagged, main) = (short_id("@--"), short_id("@-"));
    let op_log = [
        "op",
        "log",
        "--ignore-working-copy",
        "--no-graph",
        "-T",
        "id",
    ];
    let op = source.jj(&op_log);
    source.write_file("Cargo.toml", &manifest("0.3.0"));
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../contrib/upgrade-from-source");
    let installed = env.root().join("installed");
    // The cargo building this test, ahead of any rustup proxy, which would look for its
    // toolchains in the test's home.
    let cargo = Path::new(env!("CARGO"));
    let path = std::env::join_paths(
        std::iter::once(cargo.parent().unwrap().to_owned())
            .chain(std::env::split_paths(&std::env::var_os("PATH").unwrap())),
    )
    .unwrap();
    // In a time zone far from UTC, so that a build named for the local time would show.
    let upgrade = |deploy: bool, release: Option<&str>| {
        let mut command = source.program(&script);
        if deploy {
            command.arg("--deploy");
        }
        command
            .arg(source.path())
            .current_dir(env.root())
            .env_remove("MUSUBI_UPGRADE_TO")
            .env("TZ", "Pacific/Kiritimati")
            .env("PATH", &path)
            .env("CARGO_INSTALL_ROOT", &installed);
        if let Some(release) = release {
            command.env("MUSUBI_UPGRADE_TO", release);
        }
        command.output().unwrap()
    };
    let refusals: String = [
        (false, None),
        (true, Some("0.2.0")),
        (false, Some("0.2.0+custom")),
        (false, Some("0.3.0")),
        (false, Some("0.2.0+20261102153012.ffffffffffff")),
    ]
    .into_iter()
    .map(|(deploy, release)| {
        let output = upgrade(deploy, release);
        assert!(!output.status.success());
        String::from_utf8_lossy(&output.stderr).into_owned()
    })
    .collect();
    insta::assert_snapshot!(refusals, @"
    upgrade-from-source: MUSUBI_UPGRADE_TO must name the release to install
    upgrade-from-source: --deploy takes no MUSUBI_UPGRADE_TO
    upgrade-from-source: 0.2.0+custom isn't a release or a build deployed from source
    upgrade-from-source: no tag v0.3.0 in $ROOT/source
    upgrade-from-source: no commit ffffffffffff in $ROOT/source
    ");
    assert!(!installed.exists());
    let installs = |deploy: bool, release: Option<&str>| {
        let output = upgrade(deploy, release);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let version = Command::new(installed.join("bin/musubi"))
            .arg("--version")
            .output()
            .unwrap();
        String::from_utf8_lossy(&version.stdout).into_owned()
    };
    assert_eq!(installs(false, Some("0.2.0")), "musubi 0.2.0\n");
    let utc_now = || {
        let date = Command::new("date")
            .args(["-u", "+%Y%m%d%H%M%S"])
            .output()
            .unwrap();
        String::from_utf8_lossy(&date.stdout).trim().to_owned()
    };
    let before = utc_now();
    let deployed = installs(true, None);
    let after = utc_now();
    let (at, commit) = deployed
        .strip_prefix("musubi 0.2.1+")
        .and_then(|build| build.trim_end().split_once('.'))
        .unwrap_or_else(|| panic!("deployed {deployed:?}"));
    assert!(
        before.as_str() <= at && at <= after.as_str(),
        "deployed at {at}, between {before} and {after}"
    );
    assert_eq!(commit, main);
    let build = format!("0.2.0+20261102153012.{tagged}");
    assert_eq!(installs(false, Some(&build)), format!("musubi {build}\n"));
    assert_eq!(source.jj(&op_log), op, "the command changed the source");
    assert_eq!(
        fs::read_to_string(source.path().join("Cargo.toml")).unwrap(),
        manifest("0.3.0")
    );
    // A remote that has none of the source's commits.
    let remote = env.root().join("remote.git");
    source.git(&["init", "--bare", "--quiet", remote.to_str().unwrap()]);
    source.jj(&["git", "remote", "add", "origin", remote.to_str().unwrap()]);
    let output = upgrade(true, None);
    assert!(!output.status.success());
    insta::assert_snapshot!(String::from_utf8_lossy(&output.stderr), @"upgrade-from-source: main in $ROOT/source is on no remote; push it first");
}

/// Serves the hub's socket in `dir` as a hub of a build deployed from source of musubi 99.0.0,
/// on another protocol, would: answering every request with a message this release refuses.
/// Serves until the runtime it returns is dropped.
#[cfg(unix)]
fn serve_newer_hub(dir: &Path) -> tokio::runtime::Runtime {
    use std::sync::Arc;

    use musubi_sync::wire::Envelope;
    use musubi_sync::wire::HubWideReply;
    use musubi_sync::wire::JJ_LIB_VERSION;
    use musubi_sync::wire::PROTOCOL_VERSION;
    use musubi_transport::Transport;

    let runtime = tokio::runtime::Runtime::new().unwrap();
    let transport: Arc<dyn Transport> =
        Arc::new(musubi_transport::MemoryNetwork::new(1, 1 << 20).connect());
    let refusal = bytes::Bytes::from(
        postcard::to_stdvec(&Envelope {
            protocol: PROTOCOL_VERSION + 1,
            jj_lib: JJ_LIB_VERSION.to_owned(),
            release: "99.0.0+20991231235959.ffffffffffff".to_owned(),
            body: HubWideReply::Error("from the future".to_owned()),
        })
        .unwrap(),
    );
    let socket = dir.join("run/hub.sock");
    fs::remove_file(&socket).ok();
    let (listener, mut requests) = runtime.block_on(async {
        (
            tokio::net::UnixListener::bind(&socket).unwrap(),
            transport.subscribe("musubi.*.rpc").await.unwrap(),
        )
    });
    let replies = transport.clone();
    runtime.spawn(async move {
        while let Some(request) = requests.next().await {
            if let Some(reply) = request.reply {
                replies.publish(&reply, refusal.clone()).await.ok();
            }
        }
    });
    runtime.spawn(async move {
        while let Ok((stream, _)) = listener.accept().await {
            let transport = transport.clone();
            tokio::spawn(async move {
                let (reader, writer) = tokio::io::split(stream);
                musubi_transport::stream::serve(transport, reader, writer)
                    .await
                    .ok();
            });
        }
    });
    runtime
}

/// The daemon reopens the repository after a failed sync, so it carries on after changes
/// an open repository can't follow, such as turning colocation off.
#[test]
fn daemon_carries_on_after_colocation_changes() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    // On Windows, moving `.git` fails while the daemon has a file in it open (to read the
    // remotes, say), and jj then leaves it where it was: try again.
    wait_for(&logs, "jj to stop colocating beta", || {
        beta.jj_output(&["git", "colocation", "disable"])
            .status
            .success()
    });
    alpha.write_file("b", "from alpha");
    alpha.jj(&["commit", "-m", "after beta stopped colocating"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    wait_for(&logs, "beta's daemon to fetch alpha's commit", || {
        try_log(&beta).is_some_and(|log| log.contains("after beta stopped colocating"))
    });
}

/// A daemon started where git's repository variables are set, as in a git hook, ignores
/// them: they name some other repository, and the daemon serves every repository on the
/// machine for as long as it runs.
#[test]
fn the_daemon_ignores_the_git_repository_it_was_started_in() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    logs.daemon_of(&env, &alpha);
    logs.daemon_of(&env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    let elsewhere = env.root().join("elsewhere.git");
    alpha.git(&["init", "--quiet", "--bare", elsewhere.to_str().unwrap()]);
    let mut create = alpha.program(musubi());
    create
        .args(["create", "--hub", &hub.url])
        .env("GIT_DIR", &elsewhere)
        .env("GIT_OBJECT_DIRECTORY", elsewhere.join("objects"))
        .env("GIT_INDEX_FILE", elsewhere.join("index"))
        .env("GIT_WORK_TREE", env.root());
    run(&env, &logs, create);
    fetch_history(&alpha, &beta);
    musubi_in(&env, &logs, &beta, &["join", "--hub", &hub.url]);
    alpha.write_file("b", "b");
    alpha.jj(&["commit", "-m", "later from alpha"]);
    wait_for(&logs, "alpha's daemon to sync alpha's later commit", || {
        try_log(&beta).is_some_and(|log| log.contains("later from alpha"))
    });
}

/// A daemon doesn't stay in the directory of the command that started it, often a repository
/// it serves: gix needs the current directory to open any repository, so once that one was
/// deleted, no repository on the machine could sync.
// Moving and deleting a repository whose files the daemon has open is for Unix only
// (docs/internals/copies.md, "Out of scope").
#[cfg(unix)]
#[test]
fn the_daemon_outlives_the_directory_it_was_started_in() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    logs.daemon_of(&env, &alpha);
    daemons.of(&alpha);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "first project"]);
    // Started from alpha's directory.
    musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
    musubi_in(&env, &logs, &alpha, &["leave"]);
    fs::remove_dir_all(alpha.path()).unwrap();

    // Run from a directory deleted meanwhile, commands that need none work, `musubi status`
    // says what's wrong, and commands that act on the repository there say why they can't.
    let (ok, script, err) = musubi_in_deleted_dir(&env, &logs, &alpha, &["completion", "bash"]);
    assert!(ok && script.contains("musubi"), "{err}");
    let (ok, list, err) = musubi_in_deleted_dir(&env, &logs, &alpha, &["list"]);
    assert!(ok && list.starts_with("Hub "), "{list}{err}");
    let (ok, status, err) = musubi_in_deleted_dir(&env, &logs, &alpha, &["status"]);
    assert!(ok, "{err}");
    insta::assert_snapshot!(status, @"
    The current directory no longer exists.
    Default hub: $ROOT/hub
    Daemon: running (pid N), serving 0 repositories; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");
    let (ok, _, err) = musubi_in_deleted_dir(&env, &logs, &alpha, &["sync"]);
    assert!(!ok);
    insta::assert_snapshot!(err, @"Error: the current directory no longer exists");

    let second = env.root().join("second");
    let mut init = alpha.program(Path::new("jj"));
    init.args(["git", "init", "--colocate", second.to_str().unwrap()])
        .current_dir(env.root());
    run(&env, &logs, init);
    fs::write(second.join("s"), "s").unwrap();
    let mut commit = alpha.program(Path::new("jj"));
    commit
        .args(["commit", "-m", "second project"])
        .current_dir(&second);
    run(&env, &logs, commit);
    let mut create = alpha.program(musubi());
    create
        .args(["create", "--hub", &hub.url])
        .current_dir(&second);
    let out = run(&env, &logs, create);
    insta::assert_snapshot!(out, @"Created hive second");
}

/// Runs musubi as `machine` runs it, in a directory deleted once it's there, returning
/// whether it succeeded, its stdout, and its stderr.
#[cfg(unix)]
fn musubi_in_deleted_dir(
    env: &TestEnv,
    logs: &Logs,
    machine: &TestRepo,
    args: &[&str],
) -> (bool, String, String) {
    let gone = env.root().join("gone");
    fs::create_dir(&gone).unwrap();
    let mut command = machine.program(Path::new("sh"));
    command
        .current_dir(env.root())
        // A subshell removes the directory, since illumos refuses to remove a process's own
        // current directory.
        .args([
            "-c",
            r#"cd "$1" && (cd / && rmdir "$1") && shift && exec "$@""#,
            "sh",
        ])
        .arg(&gone)
        .arg(musubi())
        .args(args);
    try_run(logs, env, command)
}

/// Runs musubi in `dir` as `machine` runs it, which must succeed, returning its stdout.
fn musubi_at(env: &TestEnv, logs: &Logs, machine: &TestRepo, dir: &Path, args: &[&str]) -> String {
    let mut command = machine.program(musubi());
    command.args(args).current_dir(dir);
    run(env, logs, command)
}

/// Runs musubi in `dir` as `machine` runs it, which must fail, returning its stderr.
fn musubi_fails_at(
    env: &TestEnv,
    logs: &Logs,
    machine: &TestRepo,
    dir: &Path,
    args: &[&str],
) -> String {
    let mut command = machine.program(musubi());
    command.args(args).current_dir(dir);
    let (ok, stdout, stderr) = try_run(logs, env, command);
    assert!(!ok, "musubi {args:?} succeeded:\n{stdout}");
    stderr
}

/// Whether the daemon of `repo`'s machine has logged `text`: what it did, rather than what a
/// command finds looking at the files.
fn daemon_logged(env: &TestEnv, repo: &TestRepo, text: &str) -> bool {
    fs::read_to_string(state_dir(env, repo).join("daemon.log")).is_ok_and(|log| log.contains(text))
}

/// Waits for `dir`'s daemon to be idle, having synced beta's join, as after [`two_machines`],
/// so that a test moving, deleting or copying the repository there doesn't do it during a
/// sync, which docs/internals/copies.md leaves out: a `musubi sync` through the daemon
/// returns only once a whole sync is done, and nothing else wakes it until beta does more.
fn settled(env: &TestEnv, logs: &Logs, alpha: &TestRepo, dir: &Path) {
    wait_for(logs, "alpha to sync beta's join", || {
        jj_at(env, logs, alpha, dir, &["workspace", "list"]).contains("beta/")
    });
    musubi_at(env, logs, alpha, dir, &["sync"]);
}

/// Runs jj in `dir` as `machine` runs it.
fn jj_at(env: &TestEnv, logs: &Logs, machine: &TestRepo, dir: &Path, args: &[&str]) -> String {
    let mut command = machine.program(Path::new("jj"));
    command.args(args).current_dir(dir);
    run(env, logs, command)
}

/// A duplicate of a copy, made with `cp -a` (docs/internals/copies.md), carries its key and
/// record, but musubi never syncs it: it says so, refuses to join or leave in it, and the
/// original goes on syncing.
#[test]
fn duplicates_are_never_synced() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    settled(&env, &logs, &alpha, alpha.path());
    let duplicate = env.root().join("duplicate");
    musubi_testutil::copy_tree(alpha.path(), &duplicate);
    let status = musubi_at(&env, &logs, &alpha, &duplicate, &["status"]);
    insta::assert_snapshot!(status, @"
    This repository duplicates a copy in hive alpha, which is at $ROOT/alpha, so musubi doesn't sync it.
    Default hub: $ROOT/hub
    Daemon: running (pid N), serving 1 repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");
    let mut errors = String::new();
    for args in [
        &["join"][..],
        &["leave"],
        &["sync"],
        &["join", "--original"],
    ] {
        let err = musubi_fails_at(&env, &logs, &alpha, &duplicate, args);
        writeln!(errors, "$ musubi {}\n{err}", args.join(" ")).unwrap();
    }
    insta::assert_snapshot!(errors, @"
    $ musubi join
    Error: this repository duplicates a copy in hive alpha, which is at $ROOT/alpha, so musubi doesn't sync it; `musubi clone` makes another copy

    $ musubi leave
    Error: this repository duplicates a copy in hive alpha, which is at $ROOT/alpha, so musubi doesn't sync it; `musubi clone` makes another copy

    $ musubi sync
    Error: this repository duplicates a copy in hive alpha, which is at $ROOT/alpha, so musubi doesn't sync it; `musubi clone` makes another copy

    $ musubi join --original
    Error: the copy of this repository's key is at $ROOT/alpha, so this repository isn't it; `musubi clone` makes another copy
    ");
    jj_at(
        &env,
        &logs,
        &alpha,
        &duplicate,
        &["commit", "-m", "in the duplicate"],
    );
    alpha.write_file("b", "b");
    alpha.jj(&["commit", "-m", "in the original"]);
    wait_for(&logs, "the original's work to reach beta", || {
        try_log(&beta).is_some_and(|log| log.contains("in the original"))
    });
    assert!(!log(&beta).contains("in the duplicate"));
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  2 machines: alpha, beta
        here: $ROOT/alpha  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
}

/// A copy restored onto another machine, from a backup, say, is taken for a duplicate until
/// `musubi join --original` says it is the copy, whose original is gone; then it syncs as
/// that copy.
// Moving and deleting a repository whose files the daemon has open is for Unix only
// (docs/internals/copies.md, "Out of scope").
#[cfg(unix)]
#[test]
fn a_copy_restored_elsewhere_syncs_as_the_original() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    let gamma = env.init_repo("gamma");
    logs.daemon_of(&env, &gamma);
    daemons.of(&gamma);
    settled(&env, &logs, &alpha, alpha.path());
    let restored = env.root().join("restored");
    musubi_testutil::copy_tree(alpha.path(), &restored);
    musubi_in(&env, &logs, &alpha, &["daemon", "stop"]);
    fs::remove_dir_all(alpha.path()).unwrap();
    let err = musubi_fails_at(&env, &logs, &gamma, &restored, &["join"]);
    insta::assert_snapshot!(err, @"Error: this repository duplicates a copy in hive alpha, so musubi doesn't sync it; `musubi clone` makes another copy; if this is that copy, moved here, and the original is gone, `musubi join --original` syncs it");
    let out = musubi_at(&env, &logs, &gamma, &restored, &["join", "--original"]);
    insta::assert_snapshot!(out, @"Hive alpha is on the hub, and this repository is part of it");
    jj_at(
        &env,
        &logs,
        &gamma,
        &restored,
        &["commit", "-m", "after the restore"],
    );
    wait_for(&logs, "the restored copy's work to reach beta", || {
        try_log(&beta).is_some_and(|log| log.contains("after the restore"))
    });
}

/// A copy moved with `mv` syncs again once jj has run in it, which records where it went:
/// at once, not at the daemon's next poll, half a minute away. Only on macOS does that take
/// watching jj's record: inotify follows the moved directory, so the op heads watch sees the
/// new operation.
// Moving and deleting a repository whose files the daemon has open is for Unix only
// (docs/internals/copies.md, "Out of scope").
#[cfg(unix)]
#[test]
fn moved_copies_sync_again() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    settled(&env, &logs, &alpha, alpha.path());
    let moved = env.root().join("moved");
    fs::rename(alpha.path(), &moved).unwrap();
    jj_at(
        &env,
        &logs,
        &alpha,
        &moved,
        &["commit", "-m", "after the move"],
    );
    wait_within(
        &logs,
        "the moved copy's work to reach beta",
        Duration::from_secs(15),
        || try_log(&beta).is_some_and(|log| log.contains("after the move")),
    );
    let list = musubi_at(&env, &logs, &alpha, &moved, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  2 machines: alpha, beta
        here: $ROOT/moved  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    // Away for a while, as on a disk unmounted, it syncs again when it's back.
    settled(&env, &logs, &alpha, &moved);
    let missing = format!("{} is missing", moved.canonicalize().unwrap().display());
    let away = env.root().join("away");
    fs::rename(&moved, &away).unwrap();
    beta.write_file("b", "b");
    beta.jj(&["commit", "-m", "while alpha is away"]);
    wait_for(&logs, "alpha's daemon to miss it", || {
        daemon_logged(&env, &alpha, &missing)
    });
    fs::rename(&away, &moved).unwrap();
    wait_for(&logs, "the copy to sync again once it's back", || {
        jj_at(
            &env,
            &logs,
            &alpha,
            &moved,
            &["log", "--ignore-working-copy", "-r", "all()"],
        )
        .contains("while alpha is away")
    });
    // Moved again, with no daemon to follow it, it is where jj last saw it, not missing, and
    // `musubi leave` with its old path doesn't stop syncing it.
    musubi_at(&env, &logs, &alpha, &moved, &["daemon", "stop"]);
    let again = env.root().join("again");
    fs::rename(&moved, &again).unwrap();
    jj_at(&env, &logs, &alpha, &again, &["status"]);
    let root = env.root();
    let list = musubi_at(&env, &logs, &alpha, root, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  2 machines: alpha, beta
        here: $ROOT/again  synced N ago
    Daemon: not running (doesn't start at login; `musubi daemon install` makes it); `musubi daemon start` starts it
    ");
    let moved = moved.to_str().unwrap();
    let err = musubi_fails_at(&env, &logs, &alpha, root, &["leave", moved]);
    insta::assert_snapshot!(err, @"Error: the copy is at $ROOT/again; `musubi leave` there takes it out of its hive");
}

/// A copy deleted while its daemon runs can be deleted: the daemon writes nothing there,
/// and stops syncing it until it comes back. `musubi list` says so, and a clone made in its
/// place, or `musubi leave` with its path, puts an end to it. The hive shows the clone
/// beside the deleted copy, both of this machine's name, until that is forgotten: told apart
/// by part of their keys, which `musubi status` and `musubi forget` in the clone take too.
// Moving and deleting a repository whose files the daemon has open is for Unix only
// (docs/internals/copies.md, "Out of scope").
#[cfg(unix)]
#[test]
fn deleted_copies_stop_syncing() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    settled(&env, &logs, &alpha, alpha.path());
    // The start of each copy's key shows in the hive's names for it, where both are alpha.
    let short_key = |repo: &TestRepo| {
        let key = fs::read_to_string(repo.repo_path().join("musubi/machine")).unwrap();
        musubi_jj::workspaces::qualified_name(key.trim())
    };
    let deleted = short_key(&alpha);
    let root = env.root();
    let path = alpha.path().to_str().unwrap();
    let missing = format!(
        "{} is missing",
        alpha.path().canonicalize().unwrap().display()
    );
    fs::remove_dir_all(alpha.path()).unwrap();
    // Work announced while it's gone wakes the daemon, which writes nothing.
    beta.write_file("b", "b");
    beta.jj(&["commit", "-m", "while alpha is gone"]);
    wait_for(&logs, "alpha's daemon to stop syncing it", || {
        daemon_logged(&env, &alpha, &missing)
    });
    assert!(!alpha.path().exists());
    let list = musubi_at(&env, &logs, &alpha, root, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  2 machines: alpha, beta
        here: $ROOT/alpha  not syncing: it's missing
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    // A clone in its place takes over its entry. Given no directory, it makes one named after
    // the hive, not after the prefix that chose it.
    let out = musubi_at(&env, &logs, &alpha, root, &["clone", "alp"]);
    insta::assert_snapshot!(out, @"Cloned hive alpha into alpha");
    let clone = short_key(&alpha);
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(&regex_escape(&deleted), "alpha-DELETED");
    settings.add_filter(&regex_escape(&clone), "alpha-CLONE");
    // Working copies' ids: the clone's commit has the time `musubi clone` made it, and the
    // change ids depend on how many commands the waits above ran.
    settings.add_filter(r"(?m)^(\S+@): [k-z]{8} [0-9a-f]{8} ", "$1: [ids] ");
    let _keys = settings.bind_to_scope();
    // The hive's machines are listed in the order of their keys, which differs from run to
    // run.
    let either = |list: String| {
        list.lines()
            .map(|line| {
                if line.contains("machines:") {
                    line.replace(&deleted, "alpha-XXXX")
                        .replace(&clone, "alpha-XXXX")
                } else {
                    line.to_owned()
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    let list = either(musubi_at(&env, &logs, &alpha, root, &["list"]));
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  3 machines: alpha-XXXX, alpha-XXXX, beta
        here: $ROOT/alpha as alpha-CLONE  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    // The clone is named as the hive names it, here as elsewhere.
    let (status, _) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(status, @"
    Hive: alpha on $ROOT/hub
    This machine: alpha-CLONE, synced N ago; the hub has all its work
    Working copies:
    default@: [ids] (no description set)
    alpha-DELETED/alpha@: [ids] (no description set)
    beta/beta@: [ids] (no description set)
    Copies:
    alpha-CLONE (this machine): used N ago, never forgotten
    alpha-DELETED: used N ago, never forgotten
    beta: used N ago, never forgotten
    Daemon: running (pid N), serving this repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");
    let err = musubi_fails(&env, &logs, &alpha, &["forget", &clone]);
    insta::assert_snapshot!(err, @"Error: alpha-CLONE is this machine; `musubi leave` takes this repository out of hive alpha");
    // The plain name is the other copy's, the only one it can mean, and the hive then names
    // the clone plainly, as `musubi status` does.
    let out = musubi_in(&env, &logs, &alpha, &["forget", "alpha"]);
    insta::assert_snapshot!(out, @"Forgot alpha-DELETED");
    let list = musubi_at(&env, &logs, &alpha, root, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  2 machines: alpha, beta
        here: $ROOT/alpha  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    let machine = musubi_in(&env, &logs, &alpha, &["status", "-T", r#"machine ++ "\n""#]);
    insta::assert_snapshot!(machine, @"alpha");
    musubi_at(&env, &logs, &alpha, alpha.path(), &["daemon", "stop"]);
    fs::remove_dir_all(alpha.path()).unwrap();
    let out = musubi_at(&env, &logs, &alpha, root, &["leave", path]);
    insta::assert_snapshot!(out, @"This machine no longer syncs the copy at $ROOT/alpha.");
    let list = musubi_at(&env, &logs, &alpha, root, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  2 machines: alpha, beta
    Daemon: not running (doesn't start at login; `musubi daemon install` makes it); `musubi daemon start` starts it
    ");
}

/// A directory the daemon syncs that comes to hold another repository is never synced into
/// the first one's hive, nor written to: not a repository in no hive, nor a copy of another
/// hive, which is synced into its own.
// Moving and deleting a repository whose files the daemon has open is for Unix only
// (docs/internals/copies.md, "Out of scope").
#[cfg(unix)]
#[test]
fn a_replaced_copy_is_never_synced_into_its_hive() {
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    settled(&env, &logs, &alpha, alpha.path());
    let root = env.root();
    let path = alpha.path().to_str().unwrap();
    // A second hive on alpha's machine.
    let other = root.join("other");
    jj_at(
        &env,
        &logs,
        &alpha,
        root,
        &["git", "init", "--colocate", "other"],
    );
    fs::write(other.join("o"), "o").unwrap();
    jj_at(
        &env,
        &logs,
        &alpha,
        &other,
        &["commit", "-m", "other's work"],
    );
    musubi_at(&env, &logs, &alpha, &other, &["create", "other"]);

    // A repository in no hive.
    fs::rename(alpha.path(), root.join("away")).unwrap();
    jj_at(
        &env,
        &logs,
        &alpha,
        root,
        &["git", "init", "--colocate", path],
    );
    alpha.write_file("s", "s");
    alpha.jj(&["commit", "-m", "a stranger's work"]);
    // Work announced wakes alpha's daemon, whose watcher went with the directory moved away.
    beta.write_file("b", "b");
    beta.jj(&["commit", "-m", "beta's work"]);
    wait_for(&logs, "alpha's daemon to stop syncing its path", || {
        daemon_logged(&env, &alpha, "isn't the copy: it is not part of a hive")
    });
    assert!(!alpha.repo_path().join("musubi").exists());

    // A copy of the other hive, which syncs with that hive from its new place.
    fs::remove_dir_all(alpha.path()).unwrap();
    fs::rename(&other, alpha.path()).unwrap();
    alpha.write_file("p", "p");
    alpha.jj(&["commit", "-m", "other's work, moved"]);
    let here = format!("here: {}", alpha.path().canonicalize().unwrap().display());
    wait_for(
        &logs,
        "alpha's daemon to sync the other hive from there",
        || {
            let list = musubi_at(&env, &logs, &alpha, root, &["list"]);
            list.contains(&here) && list.contains("other  1 machine")
        },
    );
    let mut sync = alpha.program(musubi());
    sync.arg("sync").current_dir(alpha.path());
    run(&env, &logs, sync);
    let beta_log = log(&beta);
    assert!(!beta_log.contains("stranger"), "{beta_log}");
    assert!(!beta_log.contains("other's work"), "{beta_log}");
}

/// A backup restored in place over a copy is the copy, as jj sees it: the daemon opens it
/// afresh, and watches it, so its work syncs at once.
// Moving and deleting a repository whose files the daemon has open is for Unix only
// (docs/internals/copies.md, "Out of scope").
#[cfg(unix)]
#[test]
fn a_copy_restored_in_place_syncs_as_before() {
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    settled(&env, &logs, &alpha, alpha.path());
    let backup = env.root().join("backup");
    musubi_testutil::copy_tree(alpha.path(), &backup);
    alpha.write_file("b", "b");
    alpha.jj(&["commit", "-m", "after the backup"]);
    wait_for(&logs, "alpha's work to reach beta", || {
        try_log(&beta).is_some_and(|log| log.contains("after the backup"))
    });
    settled(&env, &logs, &alpha, alpha.path());
    fs::remove_dir_all(alpha.path()).unwrap();
    fs::rename(&backup, alpha.path()).unwrap();
    // The first sync finds the directory replaced; the watcher is the new directory's after.
    musubi_in(&env, &logs, &alpha, &["sync"]);
    assert!(log(&alpha).contains("after the backup"));
    alpha.write_file("r", "r");
    alpha.jj(&["commit", "-m", "after the restore"]);
    wait_for(&logs, "the restored copy's work to reach beta", || {
        try_log(&beta).is_some_and(|log| log.contains("after the restore"))
    });
}

/// A copy whose machine key is missing isn't given a new one by anything but a join, which
/// would show it on every other machine as a second copy: it isn't synced, and says why.
#[test]
fn a_copy_without_its_key_is_not_synced() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, _beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    let machine = alpha.repo_path().join("musubi/machine");
    fs::remove_file(&machine).unwrap();
    let (status, _) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(status, @"
    This repository's record says it is part of hive alpha, but its machine key or jj config id is missing.
    Default hub: $ROOT/hub
    Daemon: running (pid N), serving 1 repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");
    let err = musubi_fails(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(err, @"Error: this repository's record says it is part of hive alpha, but its machine key or jj config id is missing; `musubi clone` makes a new copy");
    alpha.write_file("b", "b");
    alpha.jj(&["commit", "-m", "without a key"]);
    wait_for(&logs, "alpha's daemon to stop syncing it", || {
        daemon_logged(&env, &alpha, "isn't the copy: it has no machine key")
    });
    assert!(!machine.exists());
}

/// A copy that leaves one hive and starts another doesn't bring the first one's copies
/// into it as members.
#[test]
fn a_new_hive_doesnt_inherit_members() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (_alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    musubi_in(&env, &logs, &beta, &["leave"]);
    // Two at once, as from two terminals: one makes its hive, and the other finds the
    // repository part of it, rather than making a hive no copy is part of.
    let create = |name: &str| {
        let mut command = beta.program(musubi());
        command.args(["create", name]);
        command
    };
    let (first, second) = std::thread::scope(|scope| {
        let first = scope.spawn(|| try_run(&logs, &env, create("other")));
        let second = try_run(&logs, &env, create("other2"));
        (first.join().unwrap(), second)
    });
    let (made, refused) = match (first, second) {
        ((true, out, _), (false, _, err)) | ((false, _, err), (true, out, _)) => (out, err),
        both => panic!("not one of them refused: {both:?}"),
    };
    // Whichever made its hive goes by `other` here.
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(r"\bother2\b", "other");
    let _other = settings.bind_to_scope();
    insta::assert_snapshot!(made, @"Created hive other");
    insta::assert_snapshot!(refused, @"Error: this repository is already part of hive other; `musubi leave` first to join another");
    let list = musubi_in(&env, &logs, &beta, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  1 machine: alpha
      other  1 machine: beta
        here: $ROOT/beta  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    let workspaces = beta.jj(&["workspace", "list"]);
    assert!(!workspaces.contains("alpha/"), "{workspaces}");
}

/// Copies that left a hive can start another together, each keeping its work, a linked
/// workspace's included. What the first copy to leave still shows of the old hive, another
/// machine's working copy, doesn't become its own in the new hive.
#[test]
fn recreating_hives_keeps_work_without_inheriting_remote_workspaces() {
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    let linked = env.root().join("alpha-linked");
    alpha.jj(&[
        "workspace",
        "add",
        "--name",
        "local/linked",
        linked.to_str().unwrap(),
    ]);
    fs::write(linked.join("linked-work"), "saved work").unwrap();
    let mut describe = alpha.program(Path::new("jj"));
    describe
        .args(["describe", "-m", "linked work"])
        .current_dir(&linked);
    run(&env, &logs, describe);
    for repo in [&alpha, &beta] {
        repo.write_file("saved-work", repo.machine());
        repo.jj(&["describe", "-m", "saved local work"]);
    }
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    let head = [
        "--ignore-working-copy",
        "log",
        "-r",
        "@",
        "--no-graph",
        "-T",
        "commit_id",
    ];
    let mut linked_head = alpha.program(Path::new("jj"));
    linked_head.args(head).current_dir(&linked);
    let mut commits = vec![run(&env, &logs, linked_head)];
    musubi_in(&env, &logs, &alpha, &["leave"]);
    musubi_in(&env, &logs, &beta, &["leave"]);
    for repo in [&alpha, &beta] {
        commits.push(repo.jj(&head));
    }
    // Having left first, alpha didn't hear beta leave.
    let names = alpha.jj(&["workspace", "list", "-T", NAMES]);
    assert!(names.lines().any(|name| name == "beta/beta"), "{names}");
    musubi_in(&env, &logs, &alpha, &["create", "again"]);
    musubi_in(&env, &logs, &beta, &["join", "--hive", "again"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    for (repo, expected) in [
        (&alpha, vec!["alpha", "local/linked", "beta/beta"]),
        (&beta, vec!["beta", "alpha/alpha"]),
    ] {
        let names = repo.jj(&["workspace", "list", "-T", NAMES]);
        let actual: std::collections::BTreeSet<_> = names.lines().collect();
        assert_eq!(actual, expected.into_iter().collect());
        for commit in &commits {
            let revset = format!("all() & {}", commit.trim());
            let found = repo.jj(&[
                "--ignore-working-copy",
                "log",
                "-r",
                &revset,
                "--no-graph",
                "-T",
                "commit_id",
            ]);
            assert_eq!(found, *commit);
        }
    }
    // alpha keeps its own `local/linked`, which no other machine shows, and says why.
    let (_, warnings) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(warnings, @r#"
    Warning: Other machines don't show workspace local/linked@, because its name has a "/".
    Hint: Run `jj workspace rename <new name>`, with no "/", in local/linked's directory (`jj workspace root --name local/linked`).
    "#);
    // jj displays Windows paths without the verbatim prefix canonicalize adds.
    let displayed = alpha.jj(&["workspace", "root", "--name", "local/linked"]);
    assert_eq!(
        Path::new(displayed.trim()).canonicalize().unwrap(),
        linked.canonicalize().unwrap()
    );
}

/// A `file://` URL for `path`, which git, unlike for a plain path, fetches from as from any
/// other remote: shallowly, if asked.
fn file_url(path: &Path) -> String {
    let path = path.to_string_lossy().replace('\\', "/");
    format!(
        "file://{}{path}",
        if path.starts_with('/') { "" } else { "/" }
    )
}

/// A shallow clone can't send the history below its shallow commits, which the hub needs
/// with everything else an operation requires, so musubi refuses one at once, saying what
/// to do instead: to start a hive, to join one, and to sync a repository that has become
/// shallow since it joined.
#[test]
fn shallow_clones_are_refused() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    alpha.write_file("b", "b");
    alpha.jj(&["commit", "-m", "second"]);
    alpha.jj(&["bookmark", "move", "main", "--to", "@-"]);
    let url = file_url(alpha.path());
    let gamma = env.init_repo("gamma");
    daemons.of(&gamma);
    gamma.git(&["fetch", "--quiet", "--depth=1", &url, "main:alpha"]);
    let create = musubi_fails(&env, &logs, &gamma, &["create", "--hub", &hub.url]);
    insta::assert_snapshot!(create, @"Error: musubi needs all of a repository's history, and this one is a shallow clone. `musubi clone <hive> <dir>` makes a full copy of a hive from its hub, and `jj git clone`, without `--depth`, a full clone of a remote");
    let join = musubi_fails(&env, &logs, &gamma, &["join", "--hub", &hub.url]);
    insta::assert_snapshot!(join, @"Error: musubi needs all of a repository's history, and this one is a shallow clone. `musubi clone <hive> <dir>` makes a full copy of a hive from its hub, and `jj git clone`, without `--depth`, a full clone of a remote");
    beta.git(&["fetch", "--quiet", "--depth=1", &url, "main"]);
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    insta::assert_snapshot!(err, @"Error: musubi needs all of a repository's history, and this one is a shallow clone. `musubi clone <hive> <dir>` makes a full copy of a hive from its hub, and `jj git clone`, without `--depth`, a full clone of a remote");
}

/// Without a daemon, `musubi sync` syncs in its own process, and records how it went for
/// `musubi list` and `musubi status`, as the daemon would. Until then, `musubi status` says
/// the hub lacks this machine's work, and what to do.
#[test]
fn syncing_without_the_daemon_shows_in_the_list() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, _beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    // So that alpha has beta's join, which its status shows, before its daemon stops.
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &alpha, &["daemon", "stop"]);
    // As the daemon left it when its last sync failed, after it had synced.
    let path = alpha.repo_path().join("musubi/status.json");
    let synced = fs::read_to_string(&path).unwrap();
    let failed = synced.replace("\"error\": null", "\"error\": \"the hub was out of reach\"");
    assert_ne!(failed, synced);
    fs::write(&path, failed).unwrap();
    // Work no daemon sends.
    alpha.write_file("unsent", "unsent");
    alpha.jj(&["commit", "-m", "unsent"]);
    let (status, warnings) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(status, @"
    Hive: alpha on $ROOT/hub
    This machine: alpha, synced N ago; the hub lacks its latest work
    Working copies:
    alpha@: nkmrtpmo e3da2e74 (no description set)
    beta/beta@: kkmpptxz aa1f41eb (no description set)
    Copies:
    alpha (this machine): used N ago, never forgotten
    beta: used N ago, never forgotten
    Daemon: not running; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");
    insta::assert_snapshot!(warnings, @"
    Warning: Syncing fails: the hub was out of reach
    Hint: `musubi sync` tries again.
    Warning: The daemon isn't running, so this repository syncs only when you run `musubi sync`.
    Hint: `musubi daemon start` starts it.
    ");
    let mut sync = alpha.program(musubi());
    sync.arg("sync");
    let (ok, out, err) = try_run(&logs, &env, sync);
    assert!(ok, "{out}{err}");
    insta::assert_snapshot!(out, @"");
    insta::assert_snapshot!(err, @"
    Warning: The daemon isn't running, so this synced in its own process, and nothing keeps this repository in sync.
    Hint: `musubi daemon start` starts it.
    ");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  2 machines: alpha, beta
        here: $ROOT/alpha  synced N ago
    Daemon: not running (doesn't start at login; `musubi daemon install` makes it); `musubi daemon start` starts it
    ");
    let (status, warnings) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(status, @"
    Hive: alpha on $ROOT/hub
    This machine: alpha, synced N ago; the hub has all its work
    Working copies:
    alpha@: nkmrtpmo e3da2e74 (no description set)
    beta/beta@: kkmpptxz aa1f41eb (no description set)
    Copies:
    alpha (this machine): used N ago, never forgotten
    beta: used N ago, never forgotten
    Daemon: not running; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");
    insta::assert_snapshot!(warnings, @"
    Warning: The daemon isn't running, so this repository syncs only when you run `musubi sync`.
    Hint: `musubi daemon start` starts it.
    ");
}

/// The running daemon reloads local settings without copying remotes or repo config.
#[test]
fn settings_stay_local_and_the_daemon_reloads_them() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines_with(&env, &mut logs, &mut daemons, &hub, |repo| {
        repo.jj(&["config", "set", "--user", "musubi.forget-after", "never"]);
    });
    // The running daemon must reload user config too, without requiring a restart.
    alpha.jj(&["config", "set", "--user", "musubi.forget-after", "2h"]);
    let out = musubi_in(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(out, @"");
    musubi_in(&env, &logs, &beta, &["sync"]);
    let status = status_in(&env, &logs, &beta).0;
    assert!(status.contains("forgotten once unused for 2h"), "{status}");
    let key = r#"revset-aliases."trunk()""#;
    let beta_trunk = beta.jj(&["config", "get", key]);
    alpha.jj(&["config", "set", "--repo", key, "main@upstream"]);
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "upstream",
        "https://private-token@example.com/up.git",
    ]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    assert_eq!(beta.jj(&["config", "get", key]), beta_trunk);
    assert_eq!(beta.jj(&["git", "remote", "list"]), "");
    let operations = beta.jj(&["op", "log", "--no-graph", "-T", "attributes"]);
    assert!(!operations.contains("private-token"), "{operations}");
    musubi_in(&env, &logs, &alpha, &["join"]);
    let record: toml::Value =
        toml::from_str(&fs::read_to_string(alpha.repo_path().join("musubi/hive.toml")).unwrap())
            .unwrap();
    let hive_id = record["hive"].as_str().unwrap();
    // A peer can publish conflicting metadata. Clone must refuse it before creating even
    // the missing parent directory; no configuration from the peer is applied here.
    alpha.jj(&[
        "git",
        "remote",
        "set-url",
        "upstream",
        "https://example.org/other.git",
    ]);
    let mut node = musubi_jj::node::NodeRepo::open(&alpha.repo_path(), &alpha.settings()).unwrap();
    let remotes = node.join_summary().unwrap().remote_snapshot();
    node.mark_joined_with_remotes("peer join with conflicting remotes", hive_id, &remotes)
        .unwrap();
    drop(node);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    let destination = env.root().join("missing-parent/clone");
    let err = musubi_fails(
        &env,
        &logs,
        &alpha,
        &["clone", hive_id, destination.to_str().unwrap()],
    );
    insta::assert_snapshot!(err, @"Error: hive alpha has inconsistent recorded remotes: upstream; make a new hive from a consistently configured copy");
    assert!(!destination.parent().unwrap().exists());
}

/// `jj op abandon` of history the hive has stops that copy syncing, where jj can tell what it
/// abandoned: the error says how to carry on, `musubi status`, reading what the daemon
/// recorded, says that retrying won't help, and joining again doesn't either. The other
/// machine keeps the abandoned operations, and syncs on.
#[test]
fn status_says_when_retrying_cannot_help() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    insta::assert_snapshot!(musubi_in(&env, &logs, &alpha, &["sync", "--help"]), @"
    Sync the repository in the current directory now.

    The daemon syncs by itself whenever the repository or its hive changes, so this is rarely needed,
    except to see at once how a sync goes. It asks the daemon to sync, if the daemon serves the
    repository, and otherwise syncs in this process, saying if that's because the daemon isn't running.

    In a colocated repository, sync exports resolved bookmarks moved by a merge to Git.

    If a hub reply leaves needed data missing, the sync fails. If the daemon serves this copy, it
    retries from the hub's current state. Run `musubi sync` again to retry at once.

    Automatic snapshots may retain files you subsequently removed. Sending pauses if that content
    exceeds 1,000 paths or 64 MiB beyond explicit change history and shared content; receiving
    continues. Inspect with --outgoing, approve exactly what it shows with --approve TOKEN, or discard
    selected unpublished operations with --prune OPERATION... . Add --dry-run to preview without
    changing history; current work and explicit change versions are retained, but earlier uncommitted
    versions may become unrecoverable. jj config keys musubi.publication.max-files and
    musubi.publication.max-bytes set the limits; 0 disables the corresponding limit.

    `jj op abandon` of operations the hive already has stops this copy syncing for good, since other
    machines keep them. To discard operations not yet sent, use --prune.

    Usage: musubi sync [OPTIONS]

    Options:
          --outgoing
              Inspect the snapshot content waiting to be sent, without sending or snapshotting

          --approve <TOKEN>
              Send the exact publication inspected with --outgoing, despite its snapshot budget

          --prune <OPERATION>...
              Snapshot current edits, then discard selected unpublished operations

          --dry-run
              Preview recorded history without discarding operations or snapshotting current files

      -h, --help
              Print help (see a summary with '-h')

    Global options:
          --socket <SOCKET>
              The daemon's control socket, in place of the usual one

          --log <FILTER>
              What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`. It
              applies to this command, not to a daemon it starts, which uses `musubi.daemon.log` in jj's
              config

          --color <WHEN>
              When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color` says]
              
              [possible values: always, never, debug, auto]
    ");
    // jj can coalesce a surviving restore into an earlier restore's exact id. Stop the
    // daemons while making that history so that no intervening realization distinguishes it.
    for repo in [&alpha, &beta] {
        musubi_in(&env, &logs, repo, &["daemon", "stop"]);
    }
    let head = || {
        alpha.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n1",
            "-T",
            "id",
        ])
    };
    let target = head();
    let restore = || {
        let mut command = alpha.program(Path::new("jj"));
        command
            .args(["--ignore-working-copy", "op", "restore", target.trim()])
            .env("JJ_OP_TIMESTAMP", "2001-02-03T04:05:06Z");
        run(&env, &logs, command);
        head()
    };
    alpha.jj(&["describe", "-m", "before the restore"]);
    let first = restore();
    alpha.jj(&["describe", "-m", "between the restores"]);
    let last = restore();
    musubi_in(&env, &logs, &alpha, &["sync"]);
    alpha.jj(&[
        "--ignore-working-copy",
        "op",
        "abandon",
        &format!("{}-..{}-", first.trim(), last.trim()),
    ]);
    insta::assert_snapshot!(musubi_fails(&env, &logs, &alpha, &["sync"]), @r#"
    Error: this repository lost history the hive has (was `jj op abandon` run?)
    Hint: Make a new copy with `musubi clone`, bring this one's work across, then run `musubi leave --force` here; "Rescue work in a new copy" in the troubleshooting guide says how.
    "#);
    // Restoring what was abandoned, before anything else changes, puts the copy back.
    alpha.jj(&["--ignore-working-copy", "op", "integrate", last.trim()]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    for repo in [&alpha, &beta] {
        musubi_in(&env, &logs, repo, &["daemon", "start"]);
    }

    alpha.write_file("b", "b");
    alpha.jj(&["commit", "-m", "second"]);
    let accepted = alpha.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    // The operation that made the commit, which only it describes so.
    let abandoned = alpha
        .jj(&["op", "log", "--no-graph", "-T", "description ++ \"\\n\""])
        .lines()
        .find(|line| line.starts_with("commit "))
        .expect("an operation that made a commit")
        .to_owned();
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    let ops =
        |repo: &TestRepo| repo.jj(&["op", "log", "--no-graph", "-T", "description ++ \"\\n\""]);
    let has = |repo: &TestRepo| ops(repo).lines().any(|line| line == abandoned);
    assert!(has(&beta), "{}", ops(&beta));
    alpha.jj(&["describe", "-m", "third"]);
    alpha.jj(&["op", "abandon", &format!("..{accepted}")]);
    // Whether the daemon's sync meets the abandon first, or this one, depends on timing.
    let mut settings = insta::Settings::clone_current();
    settings.add_filter("the first sync failed: ", "");
    let checks = settings.bind_to_scope();
    let err = musubi_fails(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(err, @r#"
    Error: this repository lost history the hive has (was `jj op abandon` run?)
    Hint: Make a new copy with `musubi clone`, bring this one's work across, then run `musubi leave --force` here; "Rescue work in a new copy" in the troubleshooting guide says how.
    "#);
    let (_, hints) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(hints, @r#"
    Warning: Syncing fails: this repository lost history the hive has (was `jj op abandon` run?)
    Hint: Make a new copy with `musubi clone`, bring this one's work across, then run `musubi leave --force` here; "Rescue work in a new copy" in the troubleshooting guide says how.
    "#);
    // It can still pause the hive, since pausing doesn't sync first, and lifting the pause
    // says again what it lost.
    insta::assert_snapshot!(musubi_in(&env, &logs, &alpha, &["pause"]), @"Paused hive alpha: nothing syncs with it until `musubi resume` or `musubi pause --cancel`.");
    insta::assert_snapshot!(musubi_fails(&env, &logs, &beta, &["sync"]), @"
    Error: hive alpha is paused (by alpha, N ago)
    Hint: `musubi resume` in a copy you've cleaned up resets the hive from it; `musubi pause --cancel` in any copy lets it sync again unchanged.
    ");
    let mut cancel = alpha.program(musubi());
    cancel.args(["pause", "--cancel"]);
    let (ok, out, err) = try_run(&logs, &env, cancel);
    assert!(ok, "{out}{err}");
    insta::assert_snapshot!(format!("{out}{err}"), @r#"
    Hive alpha syncs again.
    Warning: Syncing fails: this repository lost history the hive has (was `jj op abandon` run?)
    Hint: Make a new copy with `musubi clone`, bring this one's work across, then run `musubi leave --force` here; "Rescue work in a new copy" in the troubleshooting guide says how.
    "#);

    // The other machine keeps what was abandoned, and syncs on.
    beta.write_file("d", "d");
    beta.jj(&["commit", "-m", "beta's"]);
    insta::assert_snapshot!(musubi_in(&env, &logs, &beta, &["sync"]), @"");
    assert!(has(&beta), "{}", ops(&beta));
    let (_, hints) = status_in(&env, &logs, &beta);
    insta::assert_snapshot!(hints, @"");

    // Nor does joining again, which says so, though the copy joins.
    musubi_in(&env, &logs, &alpha, &["leave", "--force"]);
    let err = musubi_fails(&env, &logs, &alpha, &["join"]);
    insta::assert_snapshot!(err, @r#"
    Error: this repository lost history the hive has (was `jj op abandon` run?)
    Hint: Make a new copy with `musubi clone`, bring this one's work across, then run `musubi leave --force` here; "Rescue work in a new copy" in the troubleshooting guide says how.
    "#);
    drop(checks);
}

/// With commit signing on, the commits musubi rewrites when it merges another machine's
/// operations are signed, as jj's own rewrites are: musubi loads jj's signing config as jj
/// does. jj signs and verifies with `ssh-keygen` here; Unix only until a Windows runner
/// has shown its OpenSSH does the same.
#[cfg(unix)]
#[test]
fn rewrites_are_signed_as_jj_signs_them() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let key = env.root().join("signing-key");
    let keygen = Command::new("ssh-keygen")
        .args(["-q", "-t", "ed25519", "-N", "", "-C", "", "-f"])
        .arg(&key)
        .output()
        .unwrap();
    assert!(
        keygen.status.success(),
        "{}",
        String::from_utf8_lossy(&keygen.stderr)
    );
    let public = fs::read_to_string(key.with_extension("pub")).unwrap();
    let signers = env.root().join("allowed-signers");
    fs::write(&signers, format!("test@example.com {public}")).unwrap();
    let signing = [
        ("signing.behavior", "own"),
        ("signing.backend", "ssh"),
        ("signing.key", key.to_str().unwrap()),
        (
            "signing.backends.ssh.allowed-signers",
            signers.to_str().unwrap(),
        ),
    ];
    let (alpha, beta) = two_machines_with(&env, &mut logs, &mut daemons, &hub, |repo| {
        for (name, value) in signing {
            repo.jj(&["config", "set", "--user", name, value]);
        }
    });
    // Without the daemons, `musubi sync` syncs directly, and nothing else does, so neither
    // machine sees the other's change before musubi merges them.
    for repo in [&alpha, &beta] {
        musubi_in(&env, &logs, repo, &["daemon", "stop"]);
    }
    alpha.write_file("x", "x");
    alpha.jj(&["commit", "-m", "X"]);
    let x = alpha.jj(&["log", "--no-graph", "-r", "@-", "-T", "commit_id"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &beta, &["sync"]);

    // Alpha rewrites X while beta builds Y on it. Beta syncs second, so its musubi rebases
    // Y onto the rewrite.
    alpha.jj(&["describe", "-r", &x, "-m", "X, rewritten"]);
    beta.jj(&["new", &x]);
    beta.write_file("y", "y");
    beta.jj(&["commit", "-m", "Y"]);
    for repo in [&alpha, &beta, &alpha] {
        musubi_in(&env, &logs, repo, &["sync"]);
    }
    let template = r#"parents.map(|p| p.description().first_line()).join(",") ++ ": " ++ if(signature, signature.status(), "unsigned") ++ "\n""#;
    for repo in [&alpha, &beta] {
        let rebased = repo.jj(&[
            "log",
            "--no-graph",
            "-r",
            r#"description(exact:"Y\n")"#,
            "-T",
            template,
        ]);
        assert_eq!(rebased, "X, rewritten: good\n", "on {}", repo.machine());
    }
}

/// Stands in for ssh to the hub's machine, whatever its name, noting each call's arguments in
/// `ssh-args`: runs what a machine's key may run there, after printing `banner` (in `printf`'s
/// notation), and takes anything else to be adding a key, to `authorized_keys`.
#[cfg(unix)]
fn fake_ssh(env: &TestEnv, hub: &Hub, banner: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt as _;

    let ssh = env.root().join("ssh");
    fs::write(
        &ssh,
        format!(
            "#!/bin/sh\necho \"$*\" >> '{args}'\ncase \"$*\" in\n  *'hub connect')\n    \
             printf '{banner}'\n    exec '{musubi}' hub connect --dir '{dir}' ;;\n  \
             *) cat >> '{authorized}' ;;\nesac\n",
            args = env.root().join("ssh-args").display(),
            musubi = musubi().display(),
            dir = hub.dir.display(),
            authorized = env.root().join("authorized_keys").display(),
        ),
    )
    .unwrap();
    fs::set_permissions(&ssh, fs::Permissions::from_mode(0o755)).unwrap();
    ssh
}

/// Machines reach a hub over ssh: joining creates the machine's key and adds it on the hub's
/// machine, allowed only to run `musubi hub connect`, and the daemon syncs through that,
/// which relays to the hub's socket; and what the shell's startup files there print first,
/// as some do for every shell, is no matter.
#[cfg(unix)]
#[test]
fn machines_reach_the_hub_over_ssh() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    // What the shell's startup files print first, as some do for every shell: a banner and a
    // line with no newline.
    let ssh = fake_ssh(
        &env,
        &hub,
        "  _))\\n > *\\\\  Welcome to hubhost\\n\\033[0mLast login: never",
    );
    let args = env.root().join("ssh-args");
    let authorized = env.root().join("authorized_keys");
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    logs.daemon_of(&env, &alpha);
    logs.daemon_of(&env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    let over_ssh = |repo: &TestRepo, args: &[&str]| {
        let mut command = repo.program(musubi());
        command.args(args).env("MUSUBI_SSH", &ssh);
        run(&env, &logs, command)
    };
    let key = state_dir(&env, &alpha).join("hub_key");
    fs::create_dir_all(key.with_extension("pub")).unwrap();
    let mut blocked = alpha.program(musubi());
    blocked
        .args(["create", "--hub", "hubhost"])
        .env("MUSUBI_SSH", &ssh);
    let (ok, out, err) = try_run(&logs, &env, blocked);
    assert!(!ok && out.is_empty());
    insta::assert_snapshot!(err, @"
    Error: could not save musubi's public SSH key $ROOT/home/musubi-alpha/hub_key.pub: Is a directory (os error 21)
    ");
    assert!(!key.exists(), "failed setup published a private identity");
    fs::remove_dir(key.with_extension("pub")).unwrap();
    let out = over_ssh(&alpha, &["create", "--hub", "hubhost"]);
    insta::assert_snapshot!(out, @"
    Created an ssh key for musubi: $ROOT/home/musubi-alpha/hub_key
    Adding it to ~/.ssh/authorized_keys on hubhost, allowed only to run `musubi hub connect`. ssh may ask for your password.
    Created hive alpha
    ");
    let keys = fs::read_to_string(&authorized).unwrap();
    assert!(
        keys.starts_with("restrict,command=\"musubi hub connect\" ssh-ed25519 "),
        "{keys}"
    );
    // The daemon's ssh never prompts, and doesn't compress what musubi already has.
    let args = fs::read_to_string(&args).unwrap();
    assert!(
        args.contains("BatchMode=yes") && args.contains("Compression=no"),
        "{args}"
    );

    fetch_history(&alpha, &beta);
    let out = over_ssh(&beta, &["join", "--hub", "hubhost"]);
    insta::assert_snapshot!(out, @"
    Created an ssh key for musubi: $ROOT/home/musubi-beta/hub_key
    Adding it to ~/.ssh/authorized_keys on hubhost, allowed only to run `musubi hub connect`. ssh may ask for your password.
    Joined hive alpha (matched commits), 2 machines
    ");
    // Listing reaches the hub over ssh too.
    let list = over_ssh(&beta, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub hubhost:
      alpha  2 machines: alpha, beta
        here: $ROOT/beta  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");

    alpha.write_file("b", "more");
    alpha.jj(&["commit", "-m", "over ssh"]);
    wait_for(
        &logs,
        "beta's daemon to fetch alpha's commit over ssh",
        || try_log(&beta).is_some_and(|log| log.contains("over ssh")),
    );

    // Another process fills a clone destination while the command is contacting the hub.
    // The ssh wrapper makes that ordering deterministic, without a delay or a second hub.
    let raced = env.root().join("raced");
    let racing_ssh = env.root().join("racing-ssh");
    fs::write(
        &racing_ssh,
        format!(
            "#!/bin/sh\nmkdir -p '{dest}'\nprintf private > '{dest}/private.txt'\nexec '{ssh}' \"$@\"\n",
            dest = raced.display(),
            ssh = ssh.display(),
        ),
    )
    .unwrap();
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(&racing_ssh, fs::Permissions::from_mode(0o755)).unwrap();
    }
    let mut clone = alpha.program(musubi());
    clone
        .args([
            "clone",
            "alpha",
            raced.to_str().unwrap(),
            "--hub",
            "hubhost",
        ])
        .env("MUSUBI_SSH", &racing_ssh);
    let (ok, _, err) = try_run(&logs, &env, clone);
    assert!(!ok);
    insta::assert_snapshot!(err, @"Error: destination $ROOT/raced is not empty; choose a new or empty directory");
    assert!(!raced.join(".jj").exists());
    assert_eq!(
        fs::read_to_string(raced.join("private.txt")).unwrap(),
        "private"
    );

    // The daemon shares one connection to a hub, and so one ssh, among every copy it serves
    // there: started again with a second copy on alpha's machine, it connects once.
    let gamma = env.repo_handle("gamma");
    over_ssh(&alpha, &["clone", "alpha", gamma.path().to_str().unwrap()]);
    let key = state_dir(&env, &alpha).join("hub_key");
    let key = key.to_str().unwrap();
    let connects = || {
        let args = fs::read_to_string(env.root().join("ssh-args")).unwrap();
        args.lines()
            .filter(|line| line.contains(key) && line.ends_with("hub connect"))
            .count()
    };
    let before = connects();
    over_ssh(&alpha, &["daemon", "restart"]);
    alpha.write_file("c", "c");
    alpha.jj(&["commit", "-m", "from alpha again"]);
    gamma.write_file("d", "d");
    gamma.jj(&["commit", "-m", "from gamma"]);
    wait_for(&logs, "beta to fetch both copies' commits", || {
        try_log(&beta)
            .is_some_and(|log| log.contains("from alpha again") && log.contains("from gamma"))
    });
    assert_eq!(connects() - before, 1);
}

/// On the hub's machine, `localhost` reaches the hub `musubi hub` serves there by default
/// without ssh, and names the same hub as its directory does, which `musubi hub` saved as
/// the default.
#[cfg(unix)]
#[test]
fn localhost_reaches_the_hub_here_without_ssh() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let alpha = env.init_repo("alpha");
    let _hub = Hub::start_on(&env, &mut logs, &alpha);
    let mut daemons = Daemons::default();
    logs.daemon_of(&env, &alpha);
    daemons.of(&alpha);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    let mut create = alpha.program(musubi());
    create
        .args(["create", "--hub", "localhost"])
        .env("MUSUBI_SSH", "/bin/false");
    let out = run(&env, &logs, create);
    insta::assert_snapshot!(out, @"Created hive alpha");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/data/musubi/hub:
      alpha  1 machine: alpha
        here: $ROOT/alpha  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
}

/// The README's quick start, as a new user follows it: `musubi hub` run wherever they happen
/// to be, then on each machine the command it printed, pasted as printed, then commands with
/// no `--hub`, and the refusals a new user meets on the way. The snapshot is everything they
/// see, so that a review reads it as they would: a change to it is a change to their first
/// experience of musubi.
///
/// alpha is the hub's machine, and beta reaches it through a stand-in for ssh. Starting at login
/// changes the real machine, so this leaves it out.
#[cfg(unix)]
#[test]
fn the_quick_start_works_as_written() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut daemons = Daemons::default();
    for repo in [&alpha, &beta] {
        logs.daemon_of(&env, repo);
        daemons.of(repo);
    }
    // Run in a repository, the hub still lives in the data directory.
    let hub = Hub::start_on(&env, &mut logs, &alpha);
    let mut transcript = format!("$ musubi hub\n{}\n", hub.printed.join("\n"));
    let printed = |what: &str| -> Vec<String> {
        let line = hub.printed.iter().find(|line| line.starts_with(what));
        let line = line.unwrap_or_else(|| panic!("no {what:?} in {:#?}", hub.printed));
        let command = line.split_once(':').unwrap().1;
        command
            .split_whitespace()
            .skip(1)
            .map(str::to_owned)
            .collect()
    };
    let (create, join, clone) = (
        printed("To share a repository"),
        printed("To add another machine's copy"),
        printed("To make a new copy of a hive"),
    );
    // Runs musubi on `repo`'s machine, adding what it printed to the transcript.
    let ssh = fake_ssh(&env, &hub, "");
    let mut musubi_on = |repo: &TestRepo, args: &[&str], succeeds: bool| {
        let mut command = repo.program(musubi());
        command.args(args);
        if repo.machine() != "alpha" {
            command.env("MUSUBI_SSH", &ssh);
        }
        let (ok, stdout, stderr) = try_run(&logs, &env, command);
        writeln!(transcript, "{}$ musubi {}", repo.machine(), args.join(" ")).unwrap();
        transcript.push_str(&stdout);
        transcript.push_str(&stderr);
        assert_eq!(ok, succeeds, "musubi {args:?}:\n{stdout}{stderr}");
    };
    fn strs(args: &[String]) -> Vec<&str> {
        args.iter().map(String::as_str).collect()
    }

    // A machine that has heard of no hub, and a repository with nothing in it, are where a
    // new user starts.
    musubi_on(&beta, &["create"], false);
    musubi_on(&alpha, &strs(&create), false);
    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "from alpha"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    musubi_on(&alpha, &strs(&create), true);
    fetch_history(&alpha, &beta);
    musubi_on(&beta, &strs(&join), true);
    // From now on, no command needs --hub.
    musubi_on(&beta, &["list"], true);
    musubi_on(&alpha, &["sync"], true);
    musubi_on(&beta, &["sync"], true);
    musubi_on(&alpha, &["status"], true);
    musubi_on(&beta, &["status"], true);
    alpha.write_file("b", "later");
    alpha.jj(&["status"]);
    musubi_on(&alpha, &["sync"], true);
    musubi_on(&beta, &["sync"], true);
    assert_eq!(
        beta.jj(&["file", "show", "-r", "alpha/alpha@", "b"]),
        "later"
    );
    let gamma = env.repo_handle("gamma");
    let dir = gamma.path().to_str().unwrap();
    let args: Vec<&str> = strs(&clone)
        .into_iter()
        .map(|arg| match arg {
            "<name>" => "alpha",
            "[<dir>]" => dir,
            arg => arg,
        })
        .collect();
    musubi_on(&beta, &args, true);
    assert_eq!(
        gamma.jj(&["file", "show", "-r", "alpha/alpha@", "b"]),
        "later"
    );

    let _filters = snapshot_filters(&env);
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(r"(?m)^(\S+@): [k-z]{8} [0-9a-f]{8} ", "$1: [ids] ");
    settings.add_filter(
        &format!(
            "Hive: alpha on {}",
            regex_escape(&whoami::hostname().unwrap())
        ),
        "Hive: alpha on $$HOST",
    );
    let _filters = settings.bind_to_scope();
    insta::assert_snapshot!(transcript, @"
    $ musubi hub
    Created a new hub in $ROOT/data/musubi/hub
    To share a repository:               musubi create --hub $HOST
    To add another machine's copy of it: musubi join --hub $HOST
    To make a new copy of a hive:        musubi clone <name> [<dir>] --hub $HOST
    Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't $HOST.
    On this machine, leave out --hub.
    beta$ musubi create
    Error: no hub given; pass --hub <host>, or run `musubi hub` to serve one here
    alpha$ musubi create --hub $HOST
    Error: this repository has no commits to share yet; commit something first
    alpha$ musubi create --hub $HOST
    Created hive alpha
    beta$ musubi join --hub $HOST
    Created an ssh key for musubi: $ROOT/home/musubi-beta/hub_key
    Adding it to ~/.ssh/authorized_keys on $HOST, allowed only to run `musubi hub connect`. ssh may ask for your password.
    Joined hive alpha (matched commits), 2 machines
    beta$ musubi list
    Hub $HOST:
      alpha  2 machines: alpha, beta
        here: $ROOT/beta  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    alpha$ musubi sync
    beta$ musubi sync
    alpha$ musubi status
    Hive: alpha on $ROOT/data/musubi/hub
    This machine: alpha, synced N ago; the hub has all its work
    Working copies:
    alpha@: [ids] (no description set)
    beta/beta@: [ids] (no description set)
    Copies:
    alpha (this machine): used N ago, never forgotten
    beta: used N ago, never forgotten
    Daemon: running (pid N), serving this repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    beta$ musubi status
    Hive: alpha on $HOST
    This machine: beta, synced N ago; the hub has all its work
    Working copies:
    beta@: [ids] (no description set)
    alpha/alpha@: [ids] (no description set)
    Copies:
    beta (this machine): used N ago, never forgotten
    alpha: used N ago, never forgotten
    Daemon: running (pid N), serving this repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-beta/daemon.log
    alpha$ musubi sync
    beta$ musubi sync
    beta$ musubi clone alpha $ROOT/gamma --hub $HOST
    Cloned hive alpha into $ROOT/gamma
    ");
}

/// A `musubi` command with this process's environment, so the real user's service manager
/// (launchd, systemd, the registry), but its own state directory, and no jj user config.
fn musubi_as_user(state: &Path, args: &[&str]) -> Command {
    let mut command = Command::new(musubi());
    command
        .args(args)
        .env("MUSUBI_STATE_DIR", state)
        .env("JJ_CONFIG", state.join("absent.toml"))
        .env_remove("MUSUBI_SOCKET");
    command
}

/// The running daemon's pid, from the first line of the file it writes beside its lock.
fn daemon_pid(state: &Path) -> Option<String> {
    let info = fs::read_to_string(state.join("daemon.pid")).ok()?;
    Some(info.lines().next()?.trim().to_owned())
}

/// `musubi list`, which says whether the daemon runs.
fn daemon_line(env: &TestEnv, logs: &Logs, state: &Path) -> String {
    let out = run(env, logs, musubi_as_user(state, &["list"]));
    out.lines()
        .find(|line| line.starts_with("Daemon:"))
        .unwrap_or_default()
        .to_owned()
}

/// `musubi daemon install` hands the daemon to the platform's service manager, which then
/// starts it, restarts it after a crash but not after `musubi daemon stop`, and starts it
/// for commands that need it. This installs a real login service for the user running the
/// test, so it runs only when `MUSUBI_TEST_LOGIN_SERVICE` is set, as CI does: don't set it
/// where musubi is installed for real.
#[test]
fn the_daemon_starts_through_the_login_service() {
    if std::env::var_os("MUSUBI_TEST_LOGIN_SERVICE").is_none() {
        eprintln!("skipped: set MUSUBI_TEST_LOGIN_SERVICE=1 to install a login service");
        return;
    }
    let env = TestEnv::with_real_op_times();
    let mut files = vec![env.root().join("state/daemon.log")];
    if SMF {
        files.push(smf_log("daemon"));
    }
    let logs = Logs {
        files,
        repos: Vec::new(),
    };
    let state = env.root().join("state");
    // Make sure no list shows a hub it can't reach.
    fs::create_dir_all(&state).unwrap();
    // Uninstalls, and so stops the daemon, whatever happens below.
    let mut uninstall = musubi_as_user(&state, &["daemon", "uninstall"]);
    uninstall.stdout(Stdio::null()).stderr(Stdio::null());
    let _uninstall = Daemons(vec![uninstall]);
    let out = run(&env, &logs, musubi_as_user(&state, &["daemon", "install"]));
    assert!(
        out.contains(&format!("starts {STARTS} from now on")),
        "{out}"
    );
    let line = daemon_line(&env, &logs, &state);
    assert!(
        line.contains("running") && line.contains(&format!("starts {STARTS}")),
        "{line}"
    );
    let first = daemon_pid(&state).unwrap();

    if cfg!(windows) {
        // Windows runs the Run entry's command at login: run it as Windows would. A
        // daemon is already running, so it starts no other.
        let query = Command::new("reg")
            .args([
                "query",
                r"HKCU\Software\Microsoft\Windows\CurrentVersion\Run",
                "/v",
                "musubi",
            ])
            .output()
            .unwrap();
        let entry = String::from_utf8_lossy(&query.stdout).into_owned();
        assert!(entry.contains("daemon start"), "{entry}");
        run(&env, &logs, musubi_as_user(&state, &["daemon", "stop"]));
        run(&env, &logs, musubi_as_user(&state, &["daemon", "start"]));
        let started = daemon_pid(&state).unwrap();
        run(&env, &logs, musubi_as_user(&state, &["daemon", "start"]));
        assert_eq!(daemon_pid(&state).unwrap(), started);
    } else {
        // A crash: the service manager starts it again.
        Command::new("kill").args(["-9", &first]).status().unwrap();
        wait_for(&logs, "the service manager to restart the daemon", || {
            daemon_pid(&state).is_some_and(|pid| pid != first)
                && daemon_line(&env, &logs, &state).contains("running,")
        });
        // A clean stop: it stays stopped.
        let out = run(&env, &logs, musubi_as_user(&state, &["daemon", "stop"]));
        assert_eq!(out, "Stopped the daemon.\n");
        // launchd and systemd decide in their own time whether to start it again. SMF has
        // disabled it by the time `daemon stop` returns, and never starts a disabled instance.
        if SMF {
            let state = Command::new("svcs")
                .args(["-H", "-o", "state", &smf_fmri("daemon")])
                .output()
                .unwrap();
            assert_eq!(String::from_utf8_lossy(&state.stdout).trim(), "disabled");
        } else {
            std::thread::sleep(Duration::from_secs(12));
        }
        let line = daemon_line(&env, &logs, &state);
        assert!(line.contains("not running"), "{line}");
        // Stopping again finds nothing to stop, though the service manager still has the service.
        let out = run(&env, &logs, musubi_as_user(&state, &["daemon", "stop"]));
        assert_eq!(out, "No daemon is running.\n");
        // A command that needs it starts it through the service manager.
        run(&env, &logs, musubi_as_user(&state, &["daemon", "start"]));
        let managed = if cfg!(target_os = "macos") {
            let uid =
                String::from_utf8(Command::new("id").arg("-u").output().unwrap().stdout).unwrap();
            ["gui", "user"].iter().any(|domain| {
                let print = Command::new("launchctl")
                    .args([
                        "print",
                        &format!("{domain}/{}/io.github.bos.musubi", uid.trim()),
                    ])
                    .output()
                    .unwrap();
                String::from_utf8_lossy(&print.stdout).contains("state = running")
            })
        } else if SMF {
            let state = Command::new("svcs")
                .args(["-H", "-o", "state", &smf_fmri("daemon")])
                .output()
                .unwrap();
            String::from_utf8_lossy(&state.stdout).trim() == "online"
        } else {
            Command::new("systemctl")
                .args(["--user", "is-active", "--quiet", "musubi.service"])
                .status()
                .unwrap()
                .success()
        };
        assert!(managed, "the service manager isn't running the daemon");
    }

    let out = run(
        &env,
        &logs,
        musubi_as_user(&state, &["daemon", "uninstall"]),
    );
    assert!(out.contains(&format!("no longer starts {STARTS}")), "{out}");
    let line = daemon_line(&env, &logs, &state);
    assert!(line.contains("not running"), "{line}");
}

/// Whether SMF, which says "at boot" where launchd and systemd say "at login", runs the login
/// services here.
const SMF: bool = cfg!(any(target_os = "illumos", target_os = "solaris"));
const STARTS: &str = if SMF { "at boot" } else { "at login" };

/// The SMF instance musubi installs for `kind` (daemon or hub) for the user running the test,
/// whose name these tests assume is a valid instance name.
fn smf_fmri(kind: &str) -> String {
    format!("svc:/site/musubi/{kind}:{}", whoami::username().unwrap())
}

/// Where svc.startd logs the instance: its FMRI without `svc:/`, with `/` as `-`.
fn smf_log(kind: &str) -> PathBuf {
    let fmri = smf_fmri(kind);
    let name = fmri.trim_start_matches("svc:/").replace('/', "-");
    PathBuf::from(format!("/var/svc/log/{name}.log"))
}

/// The pid the service manager runs the hub as, if it runs it.
fn hub_service_pid(at_boot: bool) -> Option<String> {
    if cfg!(target_os = "macos") {
        let uid = String::from_utf8(Command::new("id").arg("-u").output().unwrap().stdout).unwrap();
        let targets = if at_boot {
            vec![format!("system/io.github.bos.musubi.hub.{}", uid.trim())]
        } else {
            ["gui", "user"]
                .iter()
                .map(|domain| format!("{domain}/{}/io.github.bos.musubi.hub", uid.trim()))
                .collect()
        };
        targets.iter().find_map(|target| {
            let print = Command::new("launchctl")
                .args(["print", target])
                .output()
                .unwrap();
            String::from_utf8_lossy(&print.stdout)
                .lines()
                .find_map(|line| line.trim().strip_prefix("pid = ").map(str::to_owned))
        })
    } else if SMF {
        // `svcs -Hp` prints the instance's line, then one line for each process: its start time,
        // pid and name.
        let processes = Command::new("svcs")
            .args(["-H", "-p", &smf_fmri("hub")])
            .output()
            .unwrap();
        String::from_utf8_lossy(&processes.stdout)
            .lines()
            .nth(1)
            .and_then(|line| line.split_whitespace().nth(1).map(str::to_owned))
    } else {
        let mut command = Command::new("systemctl");
        let unit = if at_boot {
            let uid = Command::new("id").arg("-u").output().unwrap();
            format!(
                "musubi-hub-{}.service",
                String::from_utf8_lossy(&uid.stdout).trim()
            )
        } else {
            command.arg("--user");
            "musubi-hub.service".to_owned()
        };
        let show = command
            .args(["show", "-p", "MainPID", "--value", &unit])
            .output()
            .unwrap();
        let pid = String::from_utf8_lossy(&show.stdout).trim().to_owned();
        (!pid.is_empty() && pid != "0").then_some(pid)
    }
}

/// `musubi hub install` hands the hub to the platform's service manager, which then runs
/// it, serving repositories, and starts it again after a crash; installing again, for
/// another directory, replaces it, and `musubi hub uninstall` stops it. Windows runs no hub at login, and says so. Like
/// `the_daemon_starts_through_the_login_service`, this installs a real login service, and so
/// runs only when `MUSUBI_TEST_LOGIN_SERVICE` is set.
#[test]
fn the_hub_runs_through_the_login_service() {
    hub_runs_through_service(false);
}

/// Opt-in system-service exercise: identity, service-manager acceptance, crash restart,
/// replacement and removal. It doesn't reboot or log out the test machine.
#[test]
fn the_hub_runs_through_the_boot_service() {
    if cfg!(windows) || std::env::var("MUSUBI_TEST_BOOT_SERVICE").as_deref() != Ok("1") {
        eprintln!("skipped: set MUSUBI_TEST_BOOT_SERVICE=1 to install a boot service");
        return;
    }
    // Under SMF, `--at-boot` installs the hub's own service, which
    // `the_hub_runs_through_the_login_service` exercises; running both would have two tests
    // install that one instance at once.
    if SMF {
        eprintln!("skipped: SMF's hub service is the login service test's");
        return;
    }
    hub_runs_through_service(true);
}

fn hub_runs_through_service(at_boot: bool) {
    let env = TestEnv::with_real_op_times();
    let state = env.root().join("hub-state");
    let dir = env.root().join("hub");
    let install = |dir: &Path| {
        let dir = dir.to_str().unwrap();
        let mut command = musubi_as_user(
            &state,
            &["hub", "install", "--dir", dir, "--advertise", "127.0.0.1"],
        );
        if at_boot {
            command.arg("--at-boot");
        }
        command
    };
    if cfg!(windows) {
        let (ok, _, err) = try_run(&Logs::default(), &env, install(&dir));
        assert!(!ok);
        assert_eq!(err, "Error: musubi can't run a hub at login on Windows\n");
        return;
    }
    if !at_boot && std::env::var_os("MUSUBI_TEST_LOGIN_SERVICE").is_none() {
        eprintln!("skipped: set MUSUBI_TEST_LOGIN_SERVICE=1 to install a login service");
        return;
    }
    // Where launchd sends the hub's output; systemd sends it to the journal.
    let mut logs = Logs {
        files: vec![state.join("hub.log")],
        ..Logs::default()
    };
    if SMF {
        logs.files.push(smf_log("hub"));
    }
    fs::create_dir_all(&state).unwrap();
    // Uninstalls, and so stops the hub, whatever happens below, once the daemons stop.
    let mut uninstall = musubi_as_user(&state, &["hub", "uninstall"]);
    uninstall.stdout(Stdio::null()).stderr(Stdio::null());
    let _uninstall = Daemons(vec![uninstall]);
    let out = run(&env, &logs, install(&dir));
    let runs = if at_boot {
        "runs at boot from now on".to_owned()
    } else {
        format!("runs {STARTS} from now on")
    };
    assert!(out.contains(&runs), "{out}");
    assert!(out.contains("musubi create --hub 127.0.0.1"), "{out}");
    let first = hub_service_pid(at_boot).expect("the service manager isn't running the hub");
    #[cfg(unix)]
    if at_boot {
        let owner = Command::new("ps")
            .args(["-o", "uid=", "-p", &first])
            .output()
            .unwrap();
        assert_eq!(
            String::from_utf8_lossy(&owner.stdout).trim(),
            rustix::process::getuid().as_raw().to_string()
        );
    }

    // It serves the directory as it would serve it run by hand: the path it names, symbolic
    // links resolved.
    let hub = fs::canonicalize(&dir).unwrap();
    let hub = hub.to_str().unwrap();
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    // Shares through the hub installed for another directory, below.
    let beta = env.init_repo("beta");
    for repo in [&alpha, &beta] {
        logs.daemon_of(&env, repo);
        daemons.of(repo);
    }
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    musubi_in(&env, &logs, &alpha, &["create", "--hub", hub]);
    let syncs = |repo: &TestRepo| {
        let mut sync = repo.program(musubi());
        sync.arg("sync");
        try_run(&logs, &env, sync).0
    };

    // A crash: the service manager starts it again.
    Command::new("kill").args(["-9", &first]).status().unwrap();
    wait_for(&logs, "the service manager to restart the hub", || {
        hub_service_pid(at_boot).is_some_and(|pid| pid != first) && syncs(&alpha)
    });

    // Installing again, for another directory, replaces the hub it runs: the first is
    // stopped by the time it returns, and the second serves.
    let restarted = hub_service_pid(at_boot).unwrap();
    let other = env.root().join("other-hub");
    let out = run(&env, &logs, install(&other));
    assert!(out.contains(&runs), "{out}");
    let replaced = hub_service_pid(at_boot).expect("the service manager isn't running the hub");
    assert_ne!(replaced, restarted);
    let err = musubi_fails(&env, &logs, &alpha, &["sync"]);
    assert!(err.contains("no hub is serving"), "{err}");
    let other = fs::canonicalize(&other).unwrap();
    beta.write_file("b", "b");
    beta.jj(&["commit", "-m", "start"]);
    musubi_in(
        &env,
        &logs,
        &beta,
        &["create", "--hub", other.to_str().unwrap()],
    );

    let out = run(&env, &logs, musubi_as_user(&state, &["hub", "uninstall"]));
    assert_eq!(
        out,
        "The hub's service is removed, and the hub is stopped.\n"
    );
    // launchd may return while the hub is still on its way out.
    wait_for(&logs, "the hub to stop", || {
        hub_service_pid(at_boot).is_none() && !syncs(&beta)
    });
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    assert!(err.contains("no hub is serving"), "{err}");
    let out = run(&env, &logs, musubi_as_user(&state, &["hub", "uninstall"]));
    assert_eq!(out, "The hub had no installed service.\n");
}

/// A held sender can inspect, discard selected recovery history, or approve exactly one
/// publication. Dry runs leave history alone; cleanup snapshots and preserves current edits.
#[test]
fn publication_budget_inspection_cleanup_and_override() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(r"\b[0-9a-f]{128}\b", "[operation]");
    settings.add_filter(r"\b[0-9a-f]{64}\b", "[token]");
    settings.add_filter(r"\b[0-9a-f]{12}\b", "[operation]");
    settings.add_filter(r"\b[0-9a-f]{40}\b", "[commit]");
    let _filters = settings.bind_to_scope();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines_with(&env, &mut logs, &mut daemons, &hub, |repo| {
        repo.jj(&[
            "config",
            "set",
            "--repo",
            "musubi.publication.max-files",
            "10",
        ]);
        repo.jj(&[
            "config",
            "set",
            "--repo",
            "musubi.publication.max-bytes",
            "32",
        ]);
    });
    // Settle membership and stop background writers so operation rows are reproducible.
    musubi_in(&env, &logs, &alpha, &["daemon", "stop"]);
    musubi_in(&env, &logs, &beta, &["daemon", "stop"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    alpha.write_file("README.txt", "README");
    alpha.write_file("AGENTS.md", "keep");
    alpha.write_file("accident", &"x".repeat(64));
    alpha.jj(&["status"]);
    alpha.jj(&["commit", "README.txt", "-m", "Keep README"]);
    fs::remove_file(alpha.path().join("accident")).unwrap();
    alpha.jj(&["status"]);
    insta::assert_snapshot!(musubi_fails(&env, &logs, &alpha, &["sync"]), @"
    Error: sending held: snapshots retain 2 files (68 bytes), exceeding the publication budget
    Hint: run `musubi sync --outgoing` to inspect or approve them
    ");
    let outgoing = musubi_in(&env, &logs, &alpha, &["sync", "--outgoing"]);
    insta::assert_snapshot!(outgoing, @"
    Sending held: snapshots retain 2 files, 68 bytes beyond intentional history.
    Limits: 10 files, 32 bytes (0 disables a limit).

    Files (versions shared by operations are counted once):
      AGENTS.md  4 bytes, 1 version
      accident  64 bytes, 1 version

    Retaining operations (their byte counts overlap):
      [operation]  2 files, 68 bytes  snapshot working copy
      [operation]  2 files, 68 bytes  commit [commit]
      [operation]  2 files, 68 bytes  snapshot working copy

    Send this work: musubi sync --approve [token]
    Preview cleanup: musubi sync --prune <operation>... --dry-run
    ");
    let selectors = |outgoing: &str| {
        outgoing
            .lines()
            .filter_map(|line| {
                let word = line.strip_prefix("  ")?.split_whitespace().next()?;
                (word.len() >= 12 && word.bytes().all(|c| c.is_ascii_hexdigit()))
                    .then(|| word.to_owned())
            })
            .collect::<Vec<_>>()
    };
    let selected = selectors(&outgoing);
    let mut prune = vec!["sync", "--prune"];
    prune.extend(selected.iter().map(String::as_str));
    alpha.write_file("AGENTS.md", "unsnapshotted at preview");
    let head = || {
        alpha.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n",
            "1",
            "-T",
            "id",
        ])
    };
    let before = head();
    let mut dry_run = prune.clone();
    dry_run.push("--dry-run");
    let preview = musubi_in(&env, &logs, &alpha, &dry_run);
    insta::assert_snapshot!(preview, @"
    Discard 3 unpublished operations.
    Keep all current commits, bookmarks, workspaces and files.
    Earlier versions of uncommitted files may become unrecoverable.
    Snapshot content: 2 files, 68 bytes -> 1 file, 4 bytes.
    ");
    assert_eq!(
        head(),
        before,
        "a dry run must not snapshot edits or prune history"
    );
    assert_eq!(musubi_in(&env, &logs, &alpha, &dry_run), preview);
    alpha.write_file("AGENTS.md", "latest");
    let mut command = alpha.program(musubi());
    command.args(&prune);
    let (ok, stdout, stderr) = try_run(&logs, &env, command);
    assert!(ok, "{stdout}{stderr}\n{}", logs.dump());
    insta::assert_snapshot!(stderr, @"Discarded 3 unpublished operations; current work is unchanged.");
    assert_eq!(
        fs::read_to_string(alpha.path().join("AGENTS.md")).unwrap(),
        "latest"
    );
    // Cleanup records current edits without requiring a separate jj command.
    assert_eq!(
        alpha.jj(&["--ignore-working-copy", "file", "show", "AGENTS.md"]),
        "latest"
    );
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    assert!(
        !beta
            .jj(&[
                "--ignore-working-copy",
                "log",
                "--no-graph",
                "-r",
                "all()",
                "-T",
                "description"
            ])
            .contains("accident")
    );
    // Deleting accidental files and pruning is one command even when jj has not
    // recorded their removal. The cleanup's own snapshot must not retain the accident.
    alpha.write_file("one-command-accident", &"x".repeat(64));
    alpha.jj(&["status"]);
    let outgoing = musubi_in(&env, &logs, &alpha, &["sync", "--outgoing"]);
    let selected = selectors(&outgoing);
    assert!(!selected.is_empty(), "{outgoing}");
    fs::remove_file(alpha.path().join("one-command-accident")).unwrap();
    alpha.write_file("AGENTS.md", "newest");
    let mut prune = vec!["sync", "--prune"];
    prune.extend(selected.iter().map(String::as_str));
    let mut command = alpha.program(musubi());
    command.args(&prune);
    let (ok, stdout, stderr) = try_run(&logs, &env, command);
    assert!(ok, "{stdout}{stderr}\n{}", logs.dump());
    assert_eq!(
        alpha.jj(&["--ignore-working-copy", "file", "show", "AGENTS.md"]),
        "newest"
    );
    assert!(!alpha.path().join("one-command-accident").exists());
    let outgoing = musubi_in(&env, &logs, &alpha, &["sync", "--outgoing"]);
    assert!(!outgoing.contains("one-command-accident"), "{outgoing}");
    musubi_in(&env, &logs, &alpha, &["sync"]);

    // Snapshotting the invoking workspace must not bypass secondary-workspace checks.
    let other_path = env.root().join("other-workspace");
    alpha.jj(&[
        "workspace",
        "add",
        "--name",
        "other",
        other_path.to_str().unwrap(),
    ]);
    let other = alpha.another_copy(&other_path);
    alpha.write_file("stale-probe", &"p".repeat(64));
    alpha.jj(&["status"]);
    fs::remove_file(alpha.path().join("stale-probe")).unwrap();
    alpha.jj(&["status"]);
    alpha.jj(&["restore", "--from", "@", "--into", "other@", "AGENTS.md"]);
    assert!(!other.path().join("AGENTS.md").exists());
    let outgoing = musubi_in(&env, &logs, &alpha, &["sync", "--outgoing"]);
    let selected = selectors(&outgoing);
    assert!(!selected.is_empty(), "{outgoing}");
    let mut prune = vec!["sync", "--prune"];
    prune.extend(selected.iter().map(String::as_str));
    let err = musubi_fails(&env, &logs, &alpha, &prune);
    assert!(
        err.contains("workspace other must be updated before pruning"),
        "{err}"
    );
    assert!(!other.path().join("AGENTS.md").exists());
    other.jj(&["status"]);

    // Even when jj's automatic stale recovery is enabled, pruning must not check out
    // another tree in the invoking workspace. Leave recovery to an explicit jj command.
    other.write_file("stale-source", "from other");
    other.jj(&["commit", "-m", "other work"]);
    other.jj(&[
        "restore",
        "--from",
        "@-",
        "--into",
        "alpha@",
        "stale-source",
    ]);
    alpha.write_file("AGENTS.md", "pending stale edit");
    let before = head();
    alpha.jj(&["config", "set", "--user", "ui.color", "always"]);
    let mut stale_prune = vec!["--color=never"];
    stale_prune.extend(prune.iter().copied());
    let err = musubi_fails(&env, &logs, &alpha, &stale_prune);
    alpha.jj(&["config", "set", "--user", "ui.color", "never"]);
    insta::assert_snapshot!(err, @"
    Error: The working copy is stale (not updated since operation [operation]).
    Hint: Run `jj workspace update-stale` to update it.
    See https://docs.jj-vcs.dev/latest/working-copy/#stale-working-copy for more information.
    ");
    assert_eq!(head(), before);
    assert!(!alpha.path().join("stale-source").exists());
    assert_eq!(
        fs::read_to_string(alpha.path().join("AGENTS.md")).unwrap(),
        "pending stale edit"
    );
    alpha.jj(&["workspace", "update-stale"]);
    let outgoing = musubi_in(&env, &logs, &alpha, &["sync", "--outgoing"]);
    let selected = selectors(&outgoing);
    let mut prune = vec!["sync", "--prune"];
    prune.extend(selected.iter().map(String::as_str));
    musubi_in(&env, &logs, &alpha, &prune);
    musubi_in(&env, &logs, &alpha, &["sync"]);

    for index in 0..51 {
        alpha.write_file(&format!("large-{index:02}"), &"z".repeat(64));
    }
    alpha.jj(&["status"]);
    let outgoing = musubi_in(&env, &logs, &alpha, &["sync", "--outgoing"]);
    {
        let mut settings = insta::Settings::clone_current();
        settings.add_filter(
            r"(?m)(?:^  large-[0-4][0-9]  64 bytes, 1 version\n){50}",
            "  [first 50 paths]\n",
        );
        let _filters = settings.bind_to_scope();
        insta::assert_snapshot!(outgoing, @"
        Sending held: snapshots retain 51 files, 64 bytes beyond intentional history.
        Limits: 10 files, 32 bytes (0 disables a limit).

        Files (versions shared by operations are counted once):
          [first 50 paths]
          large-50  64 bytes, 1 version

        Retaining operations (their byte counts overlap):
          [operation]  51 files, 64 bytes  snapshot working copy

        Send this work: musubi sync --approve [token]
        Preview cleanup: musubi sync --prune <operation>... --dry-run
        ");
    }
    let token = outgoing
        .lines()
        .find_map(|line| line.strip_prefix("Send this work: musubi sync --approve "))
        .unwrap();
    musubi_in(&env, &logs, &alpha, &["sync", "--approve", token]);
    insta::assert_snapshot!(musubi_in(&env, &logs, &alpha, &["sync", "--outgoing"]), @"Within publication budget: snapshots retain 0 files, 0 bytes beyond intentional history.");
    alpha.write_file("pending", &"p".repeat(64));
    alpha.jj(&["status"]);
    alpha.jj(&["bookmark", "create", "unrelated", "-r", "root()"]);
    alpha.jj(&["undo"]);
    let outgoing = musubi_in(&env, &logs, &alpha, &["sync", "--outgoing"]);
    insta::assert_snapshot!(outgoing.lines().last().unwrap(), @"Cleanup unavailable: jj did not record enough information to preserve an earlier command's changes.");
}
