//! The `musubi` binary end to end: a hub process, nodes joining, syncing, cloning, and a
//! daemon picking up another machine's work by itself, all over a real `nats-server`.

#![allow(clippy::unwrap_used)]

use std::io::BufRead as _;
use std::io::BufReader;
use std::path::Path;
use std::process::Child;
use std::process::Command;
use std::process::Output;
use std::process::Stdio;
use std::time::Duration;
use std::time::Instant;

use musubi_testutil::NatsServer;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

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

fn run(mut command: Command) -> String {
    let output: Output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{command:?} failed:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

fn musubi_in(repo: &TestRepo, args: &[&str]) -> String {
    let mut command = repo.program(musubi());
    command.args(args);
    run(command)
}

/// Starts `musubi hub` and returns it with the hive id it prints.
fn start_hub(env: &TestEnv, nats: &str) -> (Killed, String) {
    let mut child = Command::new(musubi())
        .args([
            "hub",
            "--dir",
            env.root().join("hub").to_str().unwrap(),
            "--nats",
            nats,
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut line = String::new();
    BufReader::new(child.stdout.take().unwrap())
        .read_line(&mut line)
        .unwrap();
    (Killed(child), line.trim().to_owned())
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

fn wait_for(what: &str, mut done: impl FnMut() -> bool) {
    let deadline = Instant::now() + Duration::from_secs(20);
    while !done() {
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        std::thread::sleep(Duration::from_millis(100));
    }
}

#[test]
fn hub_join_sync_clone_and_daemon() {
    let server = NatsServer::start(1024 * 1024);
    let env = TestEnv::new();
    let (_hub, hive) = start_hub(&env, &server.url());
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");

    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "from alpha"]);
    musubi_in(&alpha, &["join", &hive, "--nats", &server.url()]);
    musubi_in(&beta, &["join", &hive, "--nats", &server.url()]);
    assert!(log(&beta).contains("from alpha"));

    let status = musubi_in(&beta, &["status"]);
    assert!(
        status.contains(&hive) && status.contains("Machine:   beta"),
        "{status}"
    );
    // Every machine's workspaces are listed, by machine.
    assert!(status.contains("alpha@alpha is at"), "{status}");

    // The daemon keeps beta in sync on its own.
    let mut daemon = beta.program(musubi());
    daemon
        .arg("daemon")
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    let _daemon = Killed(daemon.spawn().unwrap());
    alpha.write_file("b", "more");
    alpha.jj(&["commit", "-m", "picked up by the daemon"]);
    musubi_in(&alpha, &["sync"]);
    wait_for("beta's daemon to fetch alpha's commit", || {
        log(&beta).contains("picked up by the daemon")
    });

    // Operation ids translate between this machine's and the hive's.
    let local = beta.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let translated = musubi_in(&beta, &["op-id", &local]);
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
    run(clone);
    assert!(log(&gamma).contains("picked up by the daemon"));
}

#[test]
fn machines_whose_workspaces_are_all_default_can_join() {
    let server = NatsServer::start(1024 * 1024);
    let env = TestEnv::new();
    let (_hub, hive) = start_hub(&env, &server.url());
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "default");
    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "from alpha"]);
    musubi_in(&alpha, &["join", &hive, "--nats", &server.url()]);
    musubi_in(&beta, &["join", &hive, "--nats", &server.url()]);
    assert!(log(&beta).contains("from alpha"));
}
