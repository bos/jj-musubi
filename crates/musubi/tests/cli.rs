//! The `musubi` binary end to end: a hub process with the NATS server it starts, machines
//! joining and matching hives, cloning, listing, and each machine's daemon, started by
//! joining, picking up repositories and other machines' work by itself.

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

fn musubi() -> &'static Path {
    Path::new(env!("CARGO_BIN_EXE_musubi"))
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

    /// Includes the daemon log of `repo`'s machine in failure messages.
    fn daemon_of(&mut self, env: &TestEnv, repo: &TestRepo) {
        self.0.push(config_dir(env, repo).join("daemon.log"));
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

/// Where `TestRepo::program` points musubi's config for the repository's machine.
fn config_dir(env: &TestEnv, repo: &TestRepo) -> PathBuf {
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
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() > deadline {
            child.kill().ok();
            child.wait().ok();
            panic!("{command:?} did not finish in time:\n{}", logs.dump());
        }
        std::thread::sleep(Duration::from_millis(50));
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

/// Runs musubi in `repo`, which must fail, returning its stderr.
fn musubi_fails(env: &TestEnv, logs: &Logs, repo: &TestRepo, args: &[&str]) -> String {
    let mut command = repo.program(musubi());
    command.args(args);
    let (ok, stdout, stderr) = try_run(logs, env, command);
    assert!(!ok, "musubi {args:?} succeeded:\n{stdout}");
    stderr
}

/// A `musubi hub` process serving `<root>/hub` with a NATS server of its own.
struct Hub {
    child: Child,
    dir: PathBuf,
    /// The URL it says to join with.
    url: String,
    /// The first line it printed.
    greeting: String,
}

impl Hub {
    fn start(env: &TestEnv, logs: &mut Logs) -> Self {
        Self::start_with(env, logs, &[])
    }

    fn start_with(env: &TestEnv, logs: &mut Logs, args: &[&str]) -> Self {
        let dir = env.root().join("hub");
        let mut command = Command::new(musubi());
        command
            .args([
                "hub",
                "-d",
                dir.to_str().unwrap(),
                "--advertise",
                "127.0.0.1",
            ])
            .args(args)
            .env("MUSUBI_CONFIG_DIR", env.root().join("hub-config"))
            .stdout(Stdio::piped());
        logs.attach(env, "hub", &mut command);
        let mut child = command.spawn().unwrap();
        let stdout = child.stdout.take().unwrap();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let mut stdout = BufReader::new(stdout);
            loop {
                let mut line = String::new();
                if stdout.read_line(&mut line).unwrap_or(0) == 0 {
                    break;
                }
                if tx.send(line).is_err() {
                    break;
                }
            }
        });
        let mut hub = Self {
            child,
            dir,
            url: String::new(),
            greeting: String::new(),
        };
        let deadline = Instant::now() + DEADLINE;
        while hub.url.is_empty() {
            let left = deadline.saturating_duration_since(Instant::now());
            let line = rx
                .recv_timeout(left)
                .unwrap_or_else(|_| panic!("the hub did not start serving:\n{}", logs.dump()));
            if hub.greeting.is_empty() {
                hub.greeting = line.trim().to_owned();
            }
            if let Some(url) = line
                .trim()
                .strip_prefix("To add a repository on any machine: musubi join --nats ")
            {
                hub.url = url.to_owned();
            }
        }
        hub
    }

    /// Kills the hub the hard way, leaving its NATS server running.
    fn kill(&mut self) {
        self.child.kill().ok();
        self.child.wait().ok();
    }
}

impl Drop for Hub {
    fn drop(&mut self) {
        self.kill();
        // The NATS server outlives a killed hub.
        if let Ok(pid) = fs::read_to_string(self.dir.join("nats.pid")) {
            let pid = pid.trim();
            if cfg!(windows) {
                Command::new("taskkill")
                    .args(["/F", "/PID", pid])
                    .output()
                    .ok();
            } else {
                Command::new("kill").arg(pid).output().ok();
            }
        }
    }
}

/// Stops the daemons of the machines it was given when dropped.
#[derive(Default)]
struct Daemons(Vec<Command>);

impl Daemons {
    fn of(&mut self, repo: &TestRepo) {
        let mut stop = repo.program(musubi());
        stop.args(["daemon", "stop"])
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

#[test]
fn hub_join_sync_clone_and_list() {
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    assert!(
        hub.greeting.starts_with("Created a new hub in"),
        "{}",
        hub.greeting
    );
    // No token unless asked for.
    assert!(hub.url.starts_with("nats://127.0.0.1:"), "{}", hub.url);
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    logs.daemon_of(&env, &alpha);
    logs.daemon_of(&env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);

    // Nothing to share yet.
    let err = musubi_fails(&env, &logs, &alpha, &["join", "--nats", &hub.url]);
    assert!(err.contains("commit something first"), "{err}");

    alpha.write_file("a", "from alpha");
    alpha.jj(&["commit", "-m", "from alpha"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.com/team/project.git",
    ]);
    let out = musubi_in(&env, &logs, &alpha, &["join", "--nats", &hub.url]);
    assert!(out.contains("Created hive project"), "{out}");
    assert!(out.contains("Synced with the hub"), "{out}");

    // A copy of the same repository, with its remote spelled another way, joins it, and
    // the daemon its join started brings it alpha's work.
    fetch_history(&alpha, &beta);
    beta.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "git@example.com:team/project",
    ]);
    let out = musubi_in(&env, &logs, &beta, &["join", "--nats", &hub.url]);
    assert!(
        out.contains("Joined hive project (matched origin), 2 machines"),
        "{out}"
    );
    assert!(log(&beta).contains("from alpha"));

    // The first join saved the hub: from now on no command needs --nats.
    let list = musubi_in(&env, &logs, &beta, &[]);
    assert!(list.contains("project  2 machines: alpha, beta"), "{list}");
    assert!(
        list.contains(&format!(
            "here: {}",
            beta.path().canonicalize().unwrap().display()
        )),
        "{list}"
    );
    assert!(
        list.contains("Daemon: running, serving 1 repositories;"),
        "{list}"
    );
    // Every machine's workspaces are listed, by machine.
    assert!(list.contains("alpha@alpha is at"), "{list}");
    assert!(list.contains("Machine:   beta"), "{list}");

    // Daemons keep the machines in sync on their own.
    alpha.write_file("b", "more");
    alpha.jj(&["commit", "-m", "picked up by the daemon"]);
    wait_for(&logs, "beta's daemon to fetch alpha's commit", || {
        try_log(&beta).is_some_and(|log| log.contains("picked up by the daemon"))
    });
    // `musubi sync` goes through the daemon.
    let out = musubi_in(&env, &logs, &alpha, &["sync"]);
    assert!(out.contains("Synced (hive at #"), "{out}");

    // Operation ids translate between this machine's and the hive's.
    let local = beta.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let translated = musubi_in(&env, &logs, &beta, &["debug", "op-id", &local]);
    assert!(
        translated.starts_with(&format!("local {local}")),
        "{translated}"
    );

    // A new machine clones the hive by a prefix of its name.
    let gamma = env.repo_handle("gamma");
    let mut clone = alpha.program(musubi());
    // A relative destination, through a parent, lands where it says.
    clone.args(["clone", "proj", "../gamma"]);
    clone.current_dir(env.root().join("home"));
    let out = run(&env, &logs, clone);
    assert!(out.contains("Cloning hive project into"), "{out}");
    assert!(log(&gamma).contains("picked up by the daemon"));

    // Leaving stops the syncing.
    let out = musubi_in(&env, &logs, &beta, &["leave"]);
    assert!(out.contains("no longer syncs with hive project"), "{out}");
    let list = musubi_in(&env, &logs, &beta, &["list"]);
    assert!(!list.contains("here:"), "{list}");
    assert!(
        list.contains("Daemon: running, serving 0 repositories;"),
        "{list}"
    );
}

/// A machine's daemon serves a repository joined after it started, without a restart,
/// and a restarted hub serves its hives again on the same URL, token and all.
#[test]
fn the_daemon_picks_up_new_repositories() {
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let mut hub = Hub::start_with(&env, &mut logs, &["--token"]);
    assert!(hub.url.contains("@127.0.0.1:"), "{}", hub.url);
    // The token is in a config file only its owner can read, not on a command line.
    let token = hub
        .url
        .strip_prefix("nats://")
        .unwrap()
        .split('@')
        .next()
        .unwrap();
    let conf = hub.dir.join("nats.conf");
    assert!(fs::read_to_string(&conf).unwrap().contains(token));
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        let mode = fs::metadata(&conf).unwrap().permissions().mode();
        assert_eq!(mode & 0o777, 0o600);
        let pid = fs::read_to_string(hub.dir.join("nats.pid")).unwrap();
        let ps = Command::new("ps")
            .args(["-o", "args=", "-p", pid.trim()])
            .output()
            .unwrap();
        let args = String::from_utf8_lossy(&ps.stdout);
        assert!(
            args.contains("nats-server") && !args.contains(token),
            "{args}"
        );
    }
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    logs.daemon_of(&env, &alpha);
    logs.daemon_of(&env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "first project"]);
    musubi_in(&env, &logs, &alpha, &["join", "--nats", &hub.url]);

    // A second repository on alpha: another hive, named after its directory, served by
    // the daemon the first join started.
    let second = env.root().join("second");
    let mut init = alpha.program(Path::new("jj"));
    init.args(["git", "init", "--colocate", second.to_str().unwrap()]);
    run(&env, &logs, init);
    let jj_in_second = |args: &[&str]| {
        let mut command = alpha.program(Path::new("jj"));
        command.args(args).current_dir(&second);
        run(&env, &logs, command)
    };
    fs::write(second.join("s"), "s").unwrap();
    jj_in_second(&["commit", "-m", "second project"]);
    let mut join = alpha.program(musubi());
    join.arg("join").current_dir(&second);
    let out = run(&env, &logs, join);
    assert!(out.contains("Created hive second"), "{out}");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(
        list.contains("Daemon: running, serving 2 repositories;"),
        "{list}"
    );

    let mut clone = beta.program(musubi());
    clone.args([
        "clone",
        "second",
        env.root().join("beta-second").to_str().unwrap(),
        "--nats",
        &hub.url,
    ]);
    run(&env, &logs, clone);
    let beta_second = env.repo_handle("beta-second");
    assert!(log(&beta_second).contains("second project"));

    // Work in the second repository reaches beta with no command run: alpha's daemon
    // serves it.
    jj_in_second(&["describe", "@-", "-m", "second project, reworded"]);
    wait_for(&logs, "the second repository's work to reach beta", || {
        try_log(&beta_second).is_some_and(|log| log.contains("second project, reworded"))
    });

    // A restarted hub serves the same hives on the same URL, its NATS server and all.
    hub.kill();
    let restarted = Hub::start(&env, &mut logs);
    assert_eq!(restarted.url, hub.url);
    assert!(
        restarted.greeting.starts_with("Serving 2 hives from"),
        "{}",
        restarted.greeting
    );
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(list.contains("alpha  1 machine: alpha"), "{list}");
    assert!(list.contains("second  2 machines: alpha, beta"), "{list}");
}

#[test]
fn machines_whose_workspaces_are_all_default_can_join() {
    let env = TestEnv::new();
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
    musubi_in(&env, &logs, &alpha, &["join", "--nats", &hub.url]);
    // Without remotes, a repository joins the one hive it shares history with.
    fetch_history(&alpha, &beta);
    let out = musubi_in(&env, &logs, &beta, &["join", "--nats", &hub.url]);
    assert!(out.contains("Joined hive alpha (matched commits)"), "{out}");
    assert!(log(&beta).contains("from alpha"));
}

/// Two machines in one hive, with their daemons running.
fn two_machines(
    env: &TestEnv,
    logs: &mut Logs,
    daemons: &mut Daemons,
    hub: &Hub,
) -> (TestRepo, TestRepo) {
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    logs.daemon_of(env, &alpha);
    logs.daemon_of(env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    musubi_in(env, logs, &alpha, &["join", "--nats", &hub.url]);
    fetch_history(&alpha, &beta);
    musubi_in(env, logs, &beta, &["join", "--nats", &hub.url]);
    (alpha, beta)
}

/// The daemon reopens the repository after a failed sync, so it carries on after changes
/// an open repository can't follow, such as turning colocation off.
#[test]
fn daemon_carries_on_after_colocation_changes() {
    let env = TestEnv::new();
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

/// The hive shares remotes and chosen repo config through the binary, which finds jj's
/// repo config where jj keeps it.
#[test]
fn settings_are_shared_through_the_binary() {
    let env = TestEnv::new();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
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

/// A `musubi` command with this process's environment, so the real user's service manager
/// (launchd, systemd, the registry), but its own config directory.
fn musubi_as_user(config: &Path, args: &[&str]) -> Command {
    let mut command = Command::new(musubi());
    command
        .args(args)
        .env("MUSUBI_CONFIG_DIR", config)
        .env_remove("MUSUBI_SOCKET");
    command
}

/// The running daemon's pid, from the file it writes beside its lock.
fn daemon_pid(config: &Path) -> Option<String> {
    fs::read_dir(config)
        .ok()?
        .flatten()
        .find(|entry| {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            name.starts_with("daemon-") && name.ends_with(".pid")
        })
        .and_then(|entry| fs::read_to_string(entry.path()).ok())
        .map(|pid| pid.trim().to_owned())
}

/// `musubi list`, which says whether the daemon runs.
fn daemon_line(env: &TestEnv, logs: &Logs, config: &Path) -> String {
    let out = run(env, logs, musubi_as_user(config, &["list"]));
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
    let env = TestEnv::new();
    let logs = Logs(vec![env.root().join("config/daemon.log")]);
    let config = env.root().join("config");
    // Make sure no list shows a hub it can't reach.
    fs::create_dir_all(&config).unwrap();
    // Uninstalls, and so stops the daemon, whatever happens below.
    let mut uninstall = musubi_as_user(&config, &["daemon", "uninstall"]);
    uninstall.stdout(Stdio::null()).stderr(Stdio::null());
    let _uninstall = Daemons(vec![uninstall]);
    let out = run(&env, &logs, musubi_as_user(&config, &["daemon", "install"]));
    assert!(out.contains("starts at login from now on"), "{out}");
    let line = daemon_line(&env, &logs, &config);
    assert!(
        line.contains("running") && line.contains("starts at login"),
        "{line}"
    );
    let first = daemon_pid(&config).unwrap();

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
        run(&env, &logs, musubi_as_user(&config, &["daemon", "stop"]));
        run(&env, &logs, musubi_as_user(&config, &["daemon", "start"]));
        let started = daemon_pid(&config).unwrap();
        run(&env, &logs, musubi_as_user(&config, &["daemon", "start"]));
        assert_eq!(daemon_pid(&config).unwrap(), started);
    } else {
        // A crash: the service manager starts it again.
        Command::new("kill").args(["-9", &first]).status().unwrap();
        wait_for(&logs, "the service manager to restart the daemon", || {
            daemon_pid(&config).is_some_and(|pid| pid != first)
                && daemon_line(&env, &logs, &config).contains("running,")
        });
        // A clean stop: it stays stopped.
        run(&env, &logs, musubi_as_user(&config, &["daemon", "stop"]));
        std::thread::sleep(Duration::from_secs(12));
        let line = daemon_line(&env, &logs, &config);
        assert!(line.contains("not running"), "{line}");
        // A command that needs it starts it through the service manager.
        run(&env, &logs, musubi_as_user(&config, &["daemon", "start"]));
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
        musubi_as_user(&config, &["daemon", "uninstall"]),
    );
    assert!(out.contains("no longer starts at login"), "{out}");
    let line = daemon_line(&env, &logs, &config);
    assert!(line.contains("not running"), "{line}");
}
