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
        self.0.push(state_dir(env, repo).join("daemon.log"));
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
    /// The first line it printed.
    greeting: String,
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
            )
            .stdout(Stdio::piped());
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
            if line.starts_with("To share a repository:") {
                hub.url = hub.dir.display().to_string();
            }
        }
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
#[cfg_attr(
    windows,
    ignore = "on Windows, the forgotten copy sometimes comes back (bos/jj-musubi#67)"
)]
fn hub_join_sync_clone_and_list() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    assert!(
        hub.greeting.starts_with("Created a new hub in"),
        "{}",
        hub.greeting
    );
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    logs.daemon_of(&env, &alpha);
    logs.daemon_of(&env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);

    // Nothing to share yet.
    let err = musubi_fails(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
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
    // Joining never starts a hive; creating does.
    let err = musubi_fails(&env, &logs, &alpha, &["join", "--hub", &hub.url]);
    assert!(err.contains("musubi create"), "{err}");
    let out = musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
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
    let out = musubi_in(&env, &logs, &beta, &["join", "--hub", &hub.url]);
    assert!(
        out.contains("Joined hive project (matched remote origin), 2 machines"),
        "{out}"
    );
    assert!(log(&beta).contains("from alpha"));
    // A person joined it, so the hive keeps it however long it goes unused, and says so.
    assert!(
        out.contains("The hive keeps this copy however long it goes unused, since a person"),
        "{out}"
    );
    assert_eq!(
        beta.jj(&["config", "get", "musubi.forget-after"]).trim(),
        "never"
    );

    // The first join saved the hub: from now on no command needs --hub.
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
    // `musubi status` shows the repository's part in the hive: every machine's working
    // copies, as jj names them here, this machine's first, and each copy.
    let (status, warnings) = status_in(&env, &logs, &beta);
    assert!(status.contains("Hive: project on "), "{status}");
    assert!(status.contains("This machine: beta, synced "), "{status}");
    let own = status.find("\nbeta@: ").expect(&status);
    let other = status.find("\nalpha/alpha@: ").expect(&status);
    assert!(own < other, "{status}");
    assert!(
        status.contains("beta (this machine): used ") && status.contains("never forgotten"),
        "{status}"
    );
    assert!(
        status.contains("Daemon: running (pid ") && status.contains("serving this repository"),
        "{status}"
    );
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
    assert!(
        labelled.contains("hive::project>>") && labelled.contains("machine::alpha>>"),
        "{labelled}"
    );
    let daemon_log = fs::read_to_string(state_dir(&env, &beta).join("daemon.log")).unwrap();
    assert!(
        !daemon_log.is_empty() && !daemon_log.contains('\x1b'),
        "{daemon_log}"
    );

    // Completing as you type, the shell gets the hub's hives, and the hubs this machine knows.
    let hives = completions(&env, &logs, &beta, &["musubi", "clone", "pr"]);
    assert_eq!(hives, "project\t2 machines: alpha, beta\n");
    let hubs = completions(&env, &logs, &beta, &["musubi", "join", "--hub", ""]);
    assert_eq!(hubs, format!("{}\tthe default hub\n", hub.url));
    // `musubi.hub` in jj's config takes the place of the hub the first join saved.
    beta.jj(&["config", "set", "--user", "musubi.hub", "elsewhere"]);
    let hubs = completions(&env, &logs, &beta, &["musubi", "join", "--hub", ""]);
    assert_eq!(hubs, format!("elsewhere\tthe default hub\n{}\n", hub.url));
    beta.jj(&["config", "unset", "--user", "musubi.hub"]);

    // Daemons keep the machines in sync on their own.
    alpha.write_file("b", "more");
    alpha.jj(&["commit", "-m", "picked up by the daemon"]);
    wait_for(&logs, "beta's daemon to fetch alpha's commit", || {
        try_log(&beta).is_some_and(|log| log.contains("picked up by the daemon"))
    });
    // `musubi sync` goes through the daemon.
    let out = musubi_in(&env, &logs, &alpha, &["sync"]);
    assert!(out.contains("Synced (hive at #"), "{out}");

    // Without a terminal, `musubi top` prints once what the hub has seen: the heads that
    // came in, and each machine up to date once its daemon has reported the latest.
    let mut top = String::new();
    wait_for(&logs, "both machines to report the hive's head", || {
        top = musubi_in(&env, &logs, &beta, &["top"]);
        top.contains("2/2")
    });
    assert!(top.contains("No issues."), "{top}");
    assert!(top.contains("\nproject since the hub started"), "{top}");
    for machine in ["alpha", "beta"] {
        assert!(top.contains(&format!("  {machine} ")), "{top}");
    }
    assert!(top.contains("up to date"), "{top}");
    assert!(top.contains("AGO"), "{top}");

    // Operation ids translate between this machine's and the hive's.
    let local = beta.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let translated = musubi_in(&env, &logs, &beta, &["debug", "op-id", &local]);
    assert!(
        translated.starts_with(&format!("local {local}")),
        "{translated}"
    );

    // A `musubi.forget-after` that isn't one fails a clone before it makes anything.
    beta.jj(&["config", "set", "--user", "musubi.forget-after", "soon"]);
    let delta = env.root().join("delta");
    let err = musubi_fails(
        &env,
        &logs,
        &beta,
        &["clone", "proj", delta.to_str().unwrap()],
    );
    assert!(err.contains("neither `never` nor a duration"), "{err}");
    assert!(!delta.exists());
    beta.jj(&["config", "unset", "--user", "musubi.forget-after"]);

    // A new machine clones the hive by a prefix of its name.
    let gamma = env.repo_handle("gamma");
    let mut clone = alpha.program(musubi());
    // A relative destination, through a parent, lands where it says.
    clone.args(["clone", "proj", "../gamma", "--machine", "gamma"]);
    clone.current_dir(env.root().join("home"));
    // An agent clones it, so the hive forgets gamma's copy once it goes unused for 6h.
    clone.env("CLAUDE_CODE_SESSION_ID", "a session");
    let out = run(&env, &logs, clone);
    assert!(out.contains("Cloning hive project into"), "{out}");
    assert!(log(&gamma).contains("picked up by the daemon"));
    assert!(
        out.contains("The hive forgets this copy once it goes unused for 6h, since an agent"),
        "{out}"
    );
    wait_for(&logs, "beta to hear gamma's musubi.forget-after", || {
        status_in(&env, &logs, &beta)
            .0
            .contains("forgotten once unused for 6h, in 5h")
    });

    // A machine forgotten elsewhere drops out of the hive, though its daemon still syncs,
    // until it's next used. Its `jj` commands above are work, and imported git's refs as
    // they started: one that reached the hub after the forget would bring gamma back,
    // rightly, so let gamma's daemon send them first.
    let out = musubi_in(&env, &logs, &gamma, &["sync"]);
    assert!(out.contains("Synced (hive at #"), "{out}");
    let out = musubi_in(&env, &logs, &alpha, &["forget", "gamma"]);
    assert!(out.contains("Forgot gamma"), "{out}");
    // The hub counts gamma out once it has the forget, which `musubi forget`'s sync sends.
    wait_for(&logs, "the hub to count gamma out", || {
        musubi_in(&env, &logs, &alpha, &["list"]).contains("project  2 machines: alpha, beta")
    });
    wait_for(&logs, "gamma's daemon to hear it was forgotten", || {
        status_in(&env, &logs, &gamma)
            .0
            .contains("Forgotten by the hive")
    });

    // A renamed hive goes by its new name on every machine, once its daemon next syncs.
    let out = musubi_in(
        &env,
        &logs,
        &alpha,
        &["hub", "rename", "project", "renamed"],
    );
    assert!(out.contains("Renamed hive project to renamed"), "{out}");
    let out = musubi_in(
        &env,
        &logs,
        &alpha,
        &["hub", "rename", "renamed", "renamed"],
    );
    assert!(out.contains("Hive renamed already has that name"), "{out}");
    musubi_in(&env, &logs, &beta, &["sync"]);
    wait_for(&logs, "beta's daemon to hear the hive's new name", || {
        status_in(&env, &logs, &beta)
            .0
            .contains("Hive: renamed on ")
    });

    // Leaving takes the copy out of the hive, and stops the syncing.
    let out = musubi_in(&env, &logs, &beta, &["leave"]);
    assert!(out.contains("has left hive renamed"), "{out}");
    wait_for(&logs, "alpha's daemon to drop beta's working copy", || {
        !alpha.jj(&["workspace", "list"]).contains("beta/")
    });
    // It keeps its working copy.
    let workspaces = beta.jj(&["workspace", "list"]);
    assert!(
        workspaces.lines().any(|line| line.starts_with("beta: ")),
        "{workspaces}"
    );
    let list = musubi_in(&env, &logs, &beta, &["list"]);
    assert!(!list.contains("here:"), "{list}");
    assert!(
        list.contains("Daemon: running, serving 0 repositories;"),
        "{list}"
    );
}

/// `musubi completion` prints a script for each shell it names.
#[test]
fn completion_scripts_complete_the_commands() {
    for shell in ["bash", "elvish", "fish", "nushell", "powershell", "zsh"] {
        let out = Command::new(musubi())
            .args(["completion", shell])
            .env_clear()
            .output()
            .unwrap();
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
    assert!(err.contains("Hint: Run `musubi hub`"), "{err}");
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
    logs.0.push(log.clone());
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
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    logs.daemon_of(&env, &alpha);
    logs.daemon_of(&env, &beta);
    daemons.of(&alpha);
    daemons.of(&beta);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "first project"]);
    musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);

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
    join.arg("create").current_dir(&second);
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
        "--hub",
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

    // A restarted hub serves the same hives, and the daemons connect to it again.
    hub.kill();
    // Completing a hive's name falls back on this machine's copies when the hub is out of
    // reach. An empty word completes the flags too.
    let hives = completions(&env, &logs, &alpha, &["musubi", "clone", ""]);
    let names: Vec<&str> = hives
        .lines()
        .filter(|line| !line.starts_with('-'))
        .collect();
    assert_eq!(names, ["alpha", "second"], "{hives}");
    let restarted = Hub::start(&env, &mut logs);
    assert!(
        restarted.greeting.starts_with("Serving 2 hives from"),
        "{}",
        restarted.greeting
    );
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(list.contains("alpha  1 machine: alpha"), "{list}");
    assert!(list.contains("second  2 machines: alpha, beta"), "{list}");
    let mut describe = alpha.program(Path::new("jj"));
    describe
        .args(["describe", "@-", "-m", "second project, after the restart"])
        .current_dir(&second);
    run(&env, &logs, describe);
    wait_for(&logs, "work after the hub's restart to reach beta", || {
        try_log(&beta_second).is_some_and(|log| log.contains("after the restart"))
    });
}

#[test]
fn machines_whose_workspaces_are_all_default_can_join() {
    let env = TestEnv::with_real_op_times();
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

/// The daemon knows a repository by one of its workspaces, but commands run in any other
/// workspace of it act on the same repository: a join there doesn't have the daemon serve
/// it twice, `musubi status` there finds it served, and a leave there stops the serving.
#[test]
fn commands_in_another_workspace_act_on_the_repository() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let alpha = env.init_repo("alpha");
    logs.daemon_of(&env, &alpha);
    daemons.of(&alpha);
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "start"]);
    musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
    let second = env.root().join("alpha-second");
    alpha.jj(&["workspace", "add", second.to_str().unwrap()]);
    let in_second = |args: &[&str]| {
        let mut command = alpha.program(musubi());
        command.args(args).current_dir(&second);
        command
    };

    // Joining again from the other workspace, as to make a lost hive again.
    run(&env, &logs, in_second(&["join"]));
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(
        list.contains("Daemon: running, serving 1 repositories;"),
        "{list}"
    );
    // Listed once, through the workspace it joined from, so a daemon starting serves it once.
    let state_path = state_dir(&env, &alpha).join("state.toml");
    let state = fs::read_to_string(&state_path).unwrap();
    assert!(!state.contains("alpha-second"), "{state}");
    let status = run(&env, &logs, in_second(&["status"]));
    assert!(status.contains("serving this repository"), "{status}");

    let out = run(&env, &logs, in_second(&["leave"]));
    assert!(out.contains("has left hive"), "{out}");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(
        list.contains("Daemon: running, serving 0 repositories;"),
        "{list}"
    );
    let state = fs::read_to_string(&state_path).unwrap();
    assert!(!state.contains("alpha"), "{state}");
}

/// A copy that left its hive can join it again, even after jj has run in it since, and
/// whether it first joined with its whole operation history or not: it carries on from the
/// history it shared, which the hive has.
#[test]
fn a_copy_can_join_again_after_leaving() {
    let env = TestEnv::with_real_op_times();
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
        assert!(out.contains("Synced with the hub"), "{out}");
        wait_for(
            &logs,
            &format!("alpha's daemon to fetch {name}'s commit"),
            || try_log(&alpha).is_some_and(|log| log.contains(&message)),
        );
    }
    // Every machine's working copy keeps its own name.
    let list = alpha.jj(&["workspace", "list"]);
    let listed: Vec<&str> = list.lines().filter_map(|l| l.split(':').next()).collect();
    assert_eq!(listed, ["alpha", "beta/beta", "gamma/gamma"], "{list}");
}

/// A hub that lost its directory knows none of its hives; one `musubi join`, in one copy,
/// makes a hive again under its id, and the other copies, their work since included, fill
/// it as they sync, with every machine's working copy under its own name.
#[test]
fn copies_make_a_lost_hive_again() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    hub.kill();
    remove_dir_when_free(&hub.dir);
    hub = Hub::start(&env, &mut logs);
    assert!(
        hub.greeting.starts_with("Created a new hub"),
        "{}",
        hub.greeting
    );
    for (repo, file) in [(&alpha, "from alpha"), (&beta, "from beta")] {
        repo.write_file(file, file);
        repo.jj(&["commit", "-m", file]);
    }
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    assert!(
        err.contains("`musubi join` in this repository makes the hive again"),
        "{err}"
    );
    let out = musubi_in(&env, &logs, &alpha, &["join"]);
    assert!(
        out.contains("Made hive alpha again from this repository"),
        "{out}"
    );
    let out = musubi_in(&env, &logs, &beta, &["sync"]);
    assert!(out.contains("Synced (hive at #"), "{out}");
    wait_for(&logs, "the machines to share their work", || {
        try_log(&alpha).is_some_and(|log| log.contains("from beta"))
            && try_log(&beta).is_some_and(|log| log.contains("from alpha"))
    });
    for (repo, names) in [
        (&alpha, ["alpha", "beta/beta"]),
        (&beta, ["alpha/alpha", "beta"]),
    ] {
        let list = repo.jj(&["workspace", "list"]);
        let listed: Vec<&str> = list.lines().filter_map(|l| l.split(':').next()).collect();
        assert_eq!(listed, names, "{list}");
    }
}

/// Moving to another hub is `musubi join --hub` in each copy: the first makes the hive
/// again there, under its id, and the rest join it, carrying on as before.
#[test]
fn copies_move_to_another_hub() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let mut old = Hub::start(&env, &mut logs);
    let new = Hub::start_in(&env, &mut logs, "newhub");
    // Stopped before the hubs.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &old);
    old.kill();
    let out = musubi_in(&env, &logs, &alpha, &["join", "--hub", &new.url]);
    assert!(
        out.contains("Made hive alpha again from this repository"),
        "{out}"
    );
    let out = musubi_in(&env, &logs, &beta, &["join", "--hub", &new.url]);
    assert!(
        out.contains("Hive alpha is on the hub, and this repository is part of it"),
        "{out}"
    );
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
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    // Without its daemon, which would otherwise sync at any moment and hear first, beta
    // hears through `musubi sync`.
    musubi_in(&env, &logs, &beta, &["daemon", "stop"]);
    let out = musubi_in(&env, &logs, &alpha, &["hub", "rm", "alpha"]);
    assert!(out.contains("Removed hive alpha"), "{out}");
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    assert!(err.contains("removed from the hub"), "{err}");
    assert!(!beta.repo_path().join("musubi/hive.toml").exists());
    let list = musubi_in(&env, &logs, &beta, &["list"]);
    assert!(!list.contains("here:"), "{list}");
    assert!(log(&beta).contains("start"));
    // Alpha's daemon hears when it next syncs, as after an operation here.
    alpha.write_file("after", "after");
    alpha.jj(&["status"]);
    wait_for(&logs, "alpha's daemon to leave the hive", || {
        !alpha.repo_path().join("musubi/hive.toml").exists()
    });
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(!list.contains("here:"), "{list}");
    assert!(log(&alpha).contains("start"));
}

/// With its hub gone, `musubi sync` through the daemon says why at once, as it does without
/// a daemon, rather than once the sync's requests time out, and `musubi list` says it too.
#[test]
fn a_sync_says_at_once_that_the_hub_is_gone() {
    let env = TestEnv::with_real_op_times();
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
    assert!(err.contains("no hub is serving"), "{err}");
    assert!(started.elapsed() < Duration::from_secs(10), "{err}");
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(list.contains("sync failing: no hub is serving"), "{list}");
    // As soon as the hub is back, a sync goes through: what the daemon knew is not stale.
    hub = Hub::start(&env, &mut logs);
    assert!(
        hub.greeting.starts_with("Serving 1 hive"),
        "{}",
        hub.greeting
    );
    let out = musubi_in(&env, &logs, &alpha, &["sync"]);
    assert!(out.contains("Synced (hive at #"), "{out}");
}

/// `musubi leave` with its hub gone fails, leaving the repository part of its hive, served
/// and with its working copy; `--force` leaves without telling the hive.
#[test]
fn leaving_needs_the_hub_unless_forced() {
    let env = TestEnv::with_real_op_times();
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
    let err = musubi_fails(&env, &logs, &alpha, &["leave"]);
    assert!(err.contains("still part of hive"), "{err}");
    assert!(alpha.repo_path().join("musubi/hive.toml").exists());
    // It keeps its working copy, though on the empty commit its forget abandoned.
    let workspaces = alpha.jj(&["workspace", "list", "--ignore-working-copy"]);
    assert!(
        workspaces.lines().any(|line| line.starts_with("alpha: ")),
        "{workspaces}"
    );
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(list.contains("here:"), "{list}");
    assert!(log(&alpha).contains("start"));
    let out = musubi_in(&env, &logs, &alpha, &["leave", "--force"]);
    assert!(out.contains("has left hive"), "{out}");
    assert!(!alpha.repo_path().join("musubi/hive.toml").exists());
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
    for command in ["create", "join"] {
        let err = musubi_fails(&env, &logs, &gamma, &[command, "--hub", &hub.url]);
        assert!(err.contains("this one is a shallow clone"), "{err}");
        assert!(err.contains("musubi clone"), "{err}");
    }
    beta.git(&["fetch", "--quiet", "--depth=1", &url, "main"]);
    let err = musubi_fails(&env, &logs, &beta, &["sync"]);
    assert!(err.contains("this one is a shallow clone"), "{err}");
}

/// Without a daemon, `musubi sync` syncs in its own process, and records how it went for
/// `musubi list` and `musubi status`, as the daemon would. Until then, `musubi status` says
/// the hub lacks this machine's work, and what to do.
#[test]
fn syncing_without_the_daemon_shows_in_the_list() {
    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, _beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
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
    assert!(status.contains("the hub lacks its latest work"), "{status}");
    assert!(
        warnings.contains("the hub was out of reach") && warnings.contains("`musubi sync`"),
        "{warnings}"
    );
    assert!(warnings.contains("`musubi daemon start`"), "{warnings}");
    let mut sync = alpha.program(musubi());
    sync.arg("sync");
    let (ok, out, err) = try_run(&logs, &env, sync);
    assert!(ok, "{out}{err}");
    assert!(
        err.contains("daemon isn't running") && err.contains("musubi daemon start"),
        "{err}"
    );
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    assert!(list.contains("Daemon: not running"), "{list}");
    assert!(list.contains("  synced "), "{list}");
    let (status, warnings) = status_in(&env, &logs, &alpha);
    assert!(status.contains("the hub has all its work"), "{status}");
    assert!(!warnings.contains("Syncing fails"), "{warnings}");
}

/// The hive shares remotes and chosen repo config through the binary, which finds jj's
/// repo config where jj keeps it.
#[test]
fn settings_are_shared_through_the_binary() {
    let env = TestEnv::with_real_op_times();
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

/// Machines reach a hub over ssh: joining creates the machine's key and adds it on the hub's
/// machine, allowed only to run `musubi hub connect`, and the daemon syncs through that,
/// which relays to the hub's socket; and what the shell's startup files there print first,
/// as some do for every shell, is no matter.
#[cfg(unix)]
#[test]
fn machines_reach_the_hub_over_ssh() {
    use std::os::unix::fs::PermissionsExt as _;

    let env = TestEnv::with_real_op_times();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    // Stands in for ssh to the hub's machine: runs what the machine's key may run there, after
    // a banner and a line with no newline, and takes anything else to be adding a key.
    let ssh = env.root().join("ssh");
    let args = env.root().join("ssh-args");
    let authorized = env.root().join("authorized_keys");
    fs::write(
        &ssh,
        format!(
            "#!/bin/sh\necho \"$*\" >> '{args}'\ncase \"$*\" in\n  *'hub connect')\n    \
             printf '  _))\\n > *\\\\  Welcome to hubhost\\n\\033[0mLast login: never'\n    \
             exec '{musubi}' hub connect --dir '{dir}' ;;\n  *) cat >> '{authorized}' ;;\nesac\n",
            args = args.display(),
            musubi = musubi().display(),
            dir = hub.dir.display(),
            authorized = authorized.display(),
        ),
    )
    .unwrap();
    fs::set_permissions(&ssh, fs::Permissions::from_mode(0o755)).unwrap();
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
    let out = over_ssh(&alpha, &["create", "--hub", "hubhost"]);
    assert!(out.contains("Created an ssh key for musubi"), "{out}");
    assert!(
        out.contains("Adding it to ~/.ssh/authorized_keys on hubhost"),
        "{out}"
    );
    assert!(
        out.contains("Saved hubhost as this machine's default hub"),
        "{out}"
    );
    assert!(out.contains("Created hive alpha"), "{out}");
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
    assert!(out.contains("Joined hive alpha"), "{out}");
    // Listing reaches the hub over ssh too.
    let list = over_ssh(&beta, &["list"]);
    assert!(list.contains("Hub hubhost:"), "{list}");
    assert!(list.contains("alpha  2 machines: alpha, beta"), "{list}");

    alpha.write_file("b", "more");
    alpha.jj(&["commit", "-m", "over ssh"]);
    wait_for(
        &logs,
        "beta's daemon to fetch alpha's commit over ssh",
        || try_log(&beta).is_some_and(|log| log.contains("over ssh")),
    );
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

/// The running daemon's pid, from the file it writes beside its lock.
fn daemon_pid(state: &Path) -> Option<String> {
    fs::read_dir(state)
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
    let logs = Logs(vec![env.root().join("state/daemon.log")]);
    let state = env.root().join("state");
    // Make sure no list shows a hub it can't reach.
    fs::create_dir_all(&state).unwrap();
    // Uninstalls, and so stops the daemon, whatever happens below.
    let mut uninstall = musubi_as_user(&state, &["daemon", "uninstall"]);
    uninstall.stdout(Stdio::null()).stderr(Stdio::null());
    let _uninstall = Daemons(vec![uninstall]);
    let out = run(&env, &logs, musubi_as_user(&state, &["daemon", "install"]));
    assert!(out.contains("starts at login from now on"), "{out}");
    let line = daemon_line(&env, &logs, &state);
    assert!(
        line.contains("running") && line.contains("starts at login"),
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
        run(&env, &logs, musubi_as_user(&state, &["daemon", "stop"]));
        std::thread::sleep(Duration::from_secs(12));
        let line = daemon_line(&env, &logs, &state);
        assert!(line.contains("not running"), "{line}");
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
    assert!(out.contains("no longer starts at login"), "{out}");
    let line = daemon_line(&env, &logs, &state);
    assert!(line.contains("not running"), "{line}");
}
