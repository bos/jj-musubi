//! The `musubi` binary end to end: a hub process, nodes joining, syncing, cloning, and a
//! daemon picking up another machine's work by itself, all over a real `nats-server`.

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

use musubi_testutil::NatsServer;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

/// How long one command may take. A command that hangs usually means a hub or daemon that
/// stopped answering, so failing here, with their logs, says more than nextest's timeout.
const DEADLINE: Duration = Duration::from_secs(45);

fn musubi() -> &'static Path {
    Path::new(env!("CARGO_BIN_EXE_musubi"))
}

struct Killed(Child);

impl Drop for Killed {
    fn drop(&mut self) {
        self.0.kill().ok();
        self.0.wait().ok();
    }
}

/// The logs of the background processes, for failure messages.
#[derive(Default)]
struct Logs(Vec<PathBuf>);

impl Logs {
    /// A log file for a background process: its stderr, at debug level for musubi.
    fn attach(&mut self, env: &TestEnv, name: &str, command: &mut Command) {
        let path = env.root().join(format!("{name}.log"));
        command
            .env("RUST_LOG", "info,musubi=debug,musubi_sync=debug")
            .stderr(fs::File::create(&path).unwrap());
        self.0.push(path);
    }

    fn dump(&self) -> String {
        let mut dump = String::new();
        for path in &self.0 {
            let log = fs::read_to_string(path).unwrap_or_default();
            writeln!(dump, "--- {}:\n{log}", path.display()).unwrap();
        }
        dump
    }
}

/// Runs `command` to completion within the deadline, returning its stdout.
fn run(env: &TestEnv, logs: &Logs, mut command: Command) -> String {
    static RUNS: AtomicUsize = AtomicUsize::new(0);
    let n = RUNS.fetch_add(1, Ordering::Relaxed);
    let out = env.root().join(format!("run-{n}.out"));
    let err = env.root().join(format!("run-{n}.err"));
    command
        .stdout(fs::File::create(&out).unwrap())
        .stderr(fs::File::create(&err).unwrap());
    let mut child = command.spawn().unwrap();
    let deadline = Instant::now() + DEADLINE;
    let (status, outcome) = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break (status, "failed");
        }
        if Instant::now() > deadline {
            child.kill().ok();
            break (child.wait().unwrap(), "did not finish in time");
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    let stdout = fs::read_to_string(&out).unwrap();
    assert!(
        status.success(),
        "{command:?} {outcome}:\n{stdout}{}\n{}",
        fs::read_to_string(&err).unwrap(),
        logs.dump()
    );
    stdout
}

fn musubi_in(env: &TestEnv, logs: &Logs, repo: &TestRepo, args: &[&str]) -> String {
    let mut command = repo.program(musubi());
    command.args(args);
    run(env, logs, command)
}

/// Starts `musubi hub` and returns it with the hive id it prints once it is serving.
fn start_hub(env: &TestEnv, logs: &mut Logs, nats: &str) -> (Killed, String) {
    let mut command = Command::new(musubi());
    command
        .args([
            "hub",
            "--dir",
            env.root().join("hub").to_str().unwrap(),
            "--nats",
            nats,
        ])
        .stdout(Stdio::piped());
    logs.attach(env, "hub", &mut command);
    let mut child = command.spawn().unwrap();
    let stdout = child.stdout.take().unwrap();
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut line = String::new();
        let mut stdout = BufReader::new(stdout);
        stdout.read_line(&mut line).ok();
        tx.send(line).ok();
        // Keep reading, so the hub never writes to a closed pipe.
        std::io::copy(&mut stdout, &mut std::io::sink()).ok();
    });
    let hub = Killed(child);
    let line = rx
        .recv_timeout(DEADLINE)
        .unwrap_or_else(|_| panic!("the hub did not start serving:\n{}", logs.dump()));
    assert!(!line.trim().is_empty(), "the hub exited:\n{}", logs.dump());
    (hub, line.trim().to_owned())
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

fn wait_for(logs: &Logs, what: &str, mut done: impl FnMut() -> bool) {
    let deadline = Instant::now() + DEADLINE;
    while !done() {
        assert!(
            Instant::now() < deadline,
            "timed out waiting for {what}:\n{}",
            logs.dump()
        );
        std::thread::sleep(Duration::from_millis(100));
    }
}

#[test]
fn hub_join_sync_clone_and_daemon() {
    let server = NatsServer::start(1024 * 1024);
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let (_hub, hive) = start_hub(&env, &mut logs, &server.url());
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");

    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "from alpha"]);
    musubi_in(
        &env,
        &logs,
        &alpha,
        &["join", &hive, "--nats", &server.url()],
    );
    musubi_in(
        &env,
        &logs,
        &beta,
        &["join", &hive, "--nats", &server.url()],
    );
    assert!(log(&beta).contains("from alpha"));

    let status = musubi_in(&env, &logs, &beta, &["status"]);
    assert!(
        status.contains(&hive) && status.contains("Machine:   beta"),
        "{status}"
    );
    // Every machine's workspaces are listed, by machine.
    assert!(status.contains("alpha@alpha is at"), "{status}");

    // The daemon keeps beta in sync on its own.
    let mut daemon = beta.program(musubi());
    daemon.arg("daemon").stdout(Stdio::null());
    logs.attach(&env, "daemon", &mut daemon);
    let _daemon = Killed(daemon.spawn().unwrap());
    alpha.write_file("b", "more");
    alpha.jj(&["commit", "-m", "picked up by the daemon"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    wait_for(&logs, "beta's daemon to fetch alpha's commit", || {
        try_log(&beta).is_some_and(|log| log.contains("picked up by the daemon"))
    });

    // Operation ids translate between this machine's and the hive's.
    let local = beta.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let translated = musubi_in(&env, &logs, &beta, &["op-id", &local]);
    assert!(
        translated.starts_with(&format!("local {local}")),
        "{translated}"
    );

    // A new machine clones the hive.
    let gamma = env.repo_handle("gamma");
    let mut clone = alpha.program(musubi());
    clone.args([
        "clone",
        &hive,
        env.root().join("gamma").to_str().unwrap(),
        "--nats",
        &server.url(),
    ]);
    clone.current_dir(env.root());
    run(&env, &logs, clone);
    assert!(log(&gamma).contains("picked up by the daemon"));
}

#[test]
fn machines_whose_workspaces_are_all_default_can_join() {
    let server = NatsServer::start(1024 * 1024);
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let (_hub, hive) = start_hub(&env, &mut logs, &server.url());
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "default");
    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "from alpha"]);
    musubi_in(
        &env,
        &logs,
        &alpha,
        &["join", &hive, "--nats", &server.url()],
    );
    musubi_in(
        &env,
        &logs,
        &beta,
        &["join", &hive, "--nats", &server.url()],
    );
    assert!(log(&beta).contains("from alpha"));
}

/// The daemon reopens the repository after a failed sync, so it carries on after changes
/// an open repository can't follow, such as turning colocation off.
#[test]
fn daemon_carries_on_after_colocation_changes() {
    let server = NatsServer::start(1024 * 1024);
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let (_hub, hive) = start_hub(&env, &mut logs, &server.url());
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    musubi_in(
        &env,
        &logs,
        &alpha,
        &["join", &hive, "--nats", &server.url()],
    );
    musubi_in(
        &env,
        &logs,
        &beta,
        &["join", &hive, "--nats", &server.url()],
    );

    let mut daemon = beta.program(musubi());
    daemon.arg("daemon").stdout(Stdio::null());
    logs.attach(&env, "daemon", &mut daemon);
    let _daemon = Killed(daemon.spawn().unwrap());
    beta.jj(&["git", "colocation", "disable"]);
    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "after beta stopped colocating"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    wait_for(&logs, "beta's daemon to fetch alpha's commit", || {
        try_log(&beta).is_some_and(|log| log.contains("after beta stopped colocating"))
    });
}

/// The hive shares remotes and chosen repo config through the binary, which finds jj's
/// repo config where jj keeps it.
#[test]
fn settings_are_shared_through_the_binary() {
    let server = NatsServer::start(1024 * 1024);
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let (_hub, hive) = start_hub(&env, &mut logs, &server.url());
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let join = ["join", &hive, "--nats", &server.url()];
    musubi_in(&env, &logs, &alpha, &join);
    musubi_in(&env, &logs, &beta, &join);
    let key = r#"revset-aliases."trunk()""#;
    alpha.jj(&["config", "set", "--repo", key, "main@upstream"]);
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "upstream",
        "https://example.com/up.git",
    ]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    musubi_in(&env, &logs, &beta, &["sync"]);
    assert_eq!(beta.jj(&["config", "get", key]), "main@upstream\n");
    assert_eq!(
        beta.jj(&["git", "remote", "list"]),
        "upstream https://example.com/up.git\n"
    );
}
