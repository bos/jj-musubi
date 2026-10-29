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

    /// The hub `musubi hub` serves by default on `repo`'s machine, `~/musubi-hub`, run in
    /// the repository, as a user might run it anywhere.
    #[cfg(unix)]
    fn start_on(env: &TestEnv, logs: &mut Logs, repo: &TestRepo) -> Self {
        let mut command = repo.program(musubi());
        command.arg("hub");
        let dir = env.root().join("home/musubi-hub");
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

    // Nothing to share yet.
    let err = musubi_fails(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
    insta::assert_snapshot!(err, @"Error: this repository has no commits to share yet; commit something first");

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
    insta::assert_snapshot!(err, @"Error: no hive on this hub shares history with this repository; `musubi create` starts one");
    let out = musubi_in(&env, &logs, &alpha, &["create", "--hub", &hub.url]);
    insta::assert_snapshot!(out, @"Created hive project");

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
    insta::assert_snapshot!(out, @"Joined hive project (matched remote origin), 2 machines");
    assert!(log(&beta).contains("from alpha"));
    // A person joined it, so the hive keeps it however long it goes unused.
    assert_eq!(
        beta.jj(&["config", "get", "musubi.forget-after"]).trim(),
        "never"
    );

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
    alpha/alpha@: vruxwmqv 8a0ddcb6 (no description set)
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
    settings.add_filter(r"\d+(\.\d+)?", "N");
    settings.add_filter(r" {2,}", "  ");
    settings.bind(|| insta::assert_snapshot!(top, @"
    musubi top: N hub
    This machine's daemon is running, serving N repository.
    Hub $ROOT/hub: up Ns, musubi N.N, N hive.
    No issues.

    HIVE  HEAD  IN/s  OUT/s  OPS  COMMITS  MACHINES  ISSUES
    project  #N  —  —  N  N  N/N

    project since the hub started: received N KiB and sent N KiB; N operations, writing N commits, came in, and N went out; N pushes moved the head, and N found it moved first.
      MACHINE  HEARD  AT  MUSUBI  STATE
      alpha  N ago  #N  N.N  up to date
      beta  N ago  #N  N.N  up to date
    "));

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
    insta::assert_snapshot!(err, @"Error: musubi.forget-after in your user config is neither `never` nor a duration such as `6h`; fix it and run this again");
    assert!(!delta.exists());
    beta.jj(&["config", "unset", "--user", "musubi.forget-after"]);

    // The hive's trunk is alpha's main, which a clone checks out.
    alpha.jj(&[
        "config",
        "set",
        "--repo",
        r#"revset-aliases."trunk()""#,
        "main",
    ]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    // A new machine clones the hive by a prefix of its name.
    let gamma = env.repo_handle("gamma");
    let mut clone = alpha.program(musubi());
    // A relative destination, through a parent, lands where it says.
    clone.args(["clone", "proj", "../gamma", "--machine", "gamma"]);
    clone.current_dir(env.root().join("home"));
    // An agent clones it, so the hive forgets gamma's copy once it goes unused for 6h.
    clone.env("CLAUDE_CODE_SESSION_ID", "a session");
    let out = run(&env, &logs, clone);
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
    assert_eq!(
        fs::read_to_string(gamma.path().join("a")).unwrap(),
        "from alpha"
    );
    assert!(log(&gamma).contains("picked up by the daemon"));
    insta::assert_snapshot!(out, @"
    The hive forgets this copy once it goes unused for 6h.
    Cloned hive project into ../gamma
    ");
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

    // A renamed hive goes by its new name on every machine, once its daemon next syncs.
    let out = musubi_in(
        &env,
        &logs,
        &alpha,
        &["hub", "rename", "project", "renamed"],
    );
    insta::assert_snapshot!(out, @"Renamed hive project to renamed");
    let out = musubi_in(
        &env,
        &logs,
        &alpha,
        &["hub", "rename", "renamed", "renamed"],
    );
    insta::assert_snapshot!(out, @"Hive renamed already has that name");
    musubi_in(&env, &logs, &beta, &["sync"]);
    wait_for(&logs, "beta's daemon to hear the hive's new name", || {
        status_in(&env, &logs, &beta)
            .0
            .contains("Hive: renamed on ")
    });

    // Leaving takes the copy out of the hive, and stops the syncing.
    let out = musubi_in(&env, &logs, &beta, &["leave"]);
    insta::assert_snapshot!(out, @"This repository has left hive renamed.");
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
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      renamed  1 machine: alpha
    Daemon: running, serving 0 repositories; doesn't start at login; `musubi daemon install` makes it
    ");
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
    let _filters = snapshot_filters(&env);
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
    insta::assert_snapshot!(hives, @"
    alpha
    second
    --hub	The hub, as `musubi hub` prints it [default: this machine's default hub]
    --machine	This machine's name in the hive. Defaults to jj's `operation.hostname`
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
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  1 machine: alpha
        here: $ROOT/alpha  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    // Listed once, through the workspace it joined from, so a daemon starting serves it once.
    let state_path = state_dir(&env, &alpha).join("state.toml");
    let state = fs::read_to_string(&state_path).unwrap();
    assert!(!state.contains("alpha-second"), "{state}");
    let status = run(&env, &logs, in_second(&["status"]));
    insta::assert_snapshot!(status, @"
    Hive: alpha on $ROOT/hub
    This machine: alpha, synced N ago; the hub has all its work
    Working copies:
    alpha@: zsuskuln 95c553be (no description set)
    alpha-second@: nppvrztz b9a19b48 (no description set)
    Copies:
    alpha (this machine): used N ago, never forgotten
    Daemon: running (pid N), serving this repository; doesn't start at login
    Daemon socket: [daemon socket]
    Daemon log: $ROOT/home/musubi-alpha/daemon.log
    ");

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
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let mut hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
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
    let _filters = snapshot_filters(&env);
    let mut logs = Logs::default();
    let mut old = Hub::start(&env, &mut logs);
    let new = Hub::start_in(&env, &mut logs, "newhub");
    // Stopped before the hubs.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &old);
    old.kill();
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
    // Alpha's daemon hears when it next syncs, as after an operation here.
    alpha.write_file("after", "after");
    alpha.jj(&["status"]);
    wait_for(&logs, "alpha's daemon to leave the hive", || {
        membership(&alpha) == "removed"
    });
    let list = musubi_in(&env, &logs, &alpha, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
    Daemon: running, serving 0 repositories; doesn't start at login; `musubi daemon install` makes it
    ");
    assert!(log(&alpha).contains("start"));
}

/// Whether the repository is part of the hive its record names: `joined`, `left`, or
/// `removed`.
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
#[test]
fn a_sync_says_at_once_that_the_hub_is_gone() {
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
    // As soon as the hub is back, a sync goes through: what the daemon knew is not stale.
    hub = Hub::start(&env, &mut logs);
    insta::assert_snapshot!(hub.greeting, @"Serving 1 hive from $ROOT/hub");
    let out = musubi_in(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(out, @"");
}

/// A daemon whose hub runs a newer release runs `musubi.upgrade-command`, telling it the
/// release, and once its binary is that release, starts again from it, in place. Here the
/// command first installs a stand-in that says it is musubi 99.0.0, and runs the real binary;
/// the daemon run from that runs the command again, which installs nothing this time, so the
/// daemon carries on as it is, and `musubi status` says why.
#[cfg(unix)]
#[test]
fn the_daemon_upgrades_towards_a_newer_hub() {
    let env = TestEnv::with_real_op_times();
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(&regex_escape(musubi().to_str().unwrap()), "[musubi]");
    settings.add_filter(
        &regex_escape(&format!("musubi {}", env!("CARGO_PKG_VERSION"))),
        "musubi [this release]",
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
printf '#!/bin/sh\n[ "$1" = --version ] && exec echo musubi 99.0.0\nexec "%s" "$@"\n' \
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
    hub.kill();
    let _newer = serve_newer_hub(&hub.dir);
    musubi_fails(&env, &logs, &alpha, &["sync"]);
    let failed = state.join("upgrade-failed");
    wait_for(&logs, "the upgrade to fail", || failed.exists());
    assert_eq!(fs::read_to_string(&ran).unwrap(), "99.0.0\n99.0.0\n");
    assert_eq!(
        daemon_pid(&state).unwrap(),
        pid,
        "the daemon is another process"
    );
    assert!(daemon_logged(
        &env,
        &alpha,
        "upgraded to musubi 99.0.0; starting again"
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
    Upgrade: upgrading to musubi 99.0.0 failed: musubi.upgrade-command succeeded, but [musubi] is musubi [this release], not musubi 99.0.0
    ");
    insta::assert_snapshot!(stderr, @"
    Hint: Once that's fixed, `musubi daemon restart` tries again.
    Warning: Syncing fails: incompatible peer: protocol N with jj-lib 0.46.0 (musubi 99.0.0), but this is protocol N with jj-lib 0.46.0 (musubi [this release]); run the same release of musubi on the hub and every machine
    Hint: The daemon keeps trying. Its log: $ROOT/home/musubi-alpha/daemon.log
    ");
}

/// Serves the hub's socket in `dir` as a hub of musubi 99.0.0, on another protocol, would:
/// answering every request with a message this release refuses. Serves until the runtime it
/// returns is dropped.
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
            release: "99.0.0".to_owned(),
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

/// `musubi leave` with its hub gone fails, leaving the repository part of its hive, served
/// and with its working copy; `--force` leaves without telling the hive.
#[test]
fn leaving_needs_the_hub_unless_forced() {
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
    let err = musubi_fails(&env, &logs, &alpha, &["leave"]);
    insta::assert_snapshot!(err, @"
    Error: couldn't tell hive alpha that this repository leaves: no hub is serving $ROOT/hub
    Hint: `musubi leave --force` leaves without telling the hive
    ");
    assert_eq!(membership(&alpha), "joined");
    // It keeps its working copy, though on the empty commit its forget abandoned.
    let workspaces = alpha.jj(&["workspace", "list", "--ignore-working-copy"]);
    assert!(
        workspaces.lines().any(|line| line.starts_with("alpha: ")),
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

/// A copy moved with `mv` syncs again once jj has run in it, which records where it went.
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
    wait_for(&logs, "the moved copy's work to reach beta", || {
        try_log(&beta).is_some_and(|log| log.contains("after the move"))
    });
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
}

/// A copy deleted while its daemon runs can be deleted: the daemon writes nothing there,
/// and stops syncing it until it comes back. `musubi list` says so, and a clone made in its
/// place, or `musubi leave` with its path, puts an end to it.
// Moving and deleting a repository whose files the daemon has open is for Unix only
// (docs/internals/copies.md, "Out of scope").
#[cfg(unix)]
#[test]
fn deleted_copies_stop_syncing() {
    let env = TestEnv::new();
    let _filters = snapshot_filters(&env);
    // The clone's machine key is new, and the start of it shows in the hive's names for it.
    let mut settings = insta::Settings::clone_current();
    settings.add_filter(r"\balpha-[0-9a-f]{4}\b", "alpha-XXXX");
    let _keys = settings.bind_to_scope();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    settled(&env, &logs, &alpha, alpha.path());
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
    // A clone in its place takes over its entry.
    musubi_at(&env, &logs, &alpha, root, &["clone", "alpha", path]);
    let list = musubi_at(&env, &logs, &alpha, root, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  3 machines: alpha-XXXX, alpha-XXXX, beta
        here: $ROOT/alpha  synced N ago
    Daemon: running, serving 1 repository; doesn't start at login; `musubi daemon install` makes it
    ");
    musubi_at(&env, &logs, &alpha, alpha.path(), &["daemon", "stop"]);
    fs::remove_dir_all(alpha.path()).unwrap();
    let out = musubi_at(&env, &logs, &alpha, root, &["leave", path]);
    insta::assert_snapshot!(out, @"This machine no longer syncs the copy at $ROOT/alpha.");
    let list = musubi_at(&env, &logs, &alpha, root, &["list"]);
    insta::assert_snapshot!(list, @"
    Hub $ROOT/hub:
      alpha  3 machines: alpha-XXXX, alpha-XXXX, beta
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
    musubi_in(&env, &logs, &beta, &["create", "other"]);
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

/// Once `jj op abandon` pauses syncing, the error says how to carry on, and `musubi status`,
/// reading what the daemon recorded, says that retrying won't help.
#[test]
fn status_says_when_retrying_cannot_help() {
    let env = TestEnv::with_real_op_times();
    let _filters = snapshot_filters(&env);
    // Whether the join's first sync meets the abandoned history, or the daemon's, depends on
    // how the syncs fell.
    let mut settings = insta::Settings::clone_current();
    settings.add_filter("the first sync failed: ", "");
    let _checks = settings.bind_to_scope();
    let mut logs = Logs::default();
    let hub = Hub::start(&env, &mut logs);
    // Stopped before the hub.
    let mut daemons = Daemons::default();
    let (alpha, _beta) = two_machines(&env, &mut logs, &mut daemons, &hub);
    alpha.write_file("b", "b");
    alpha.jj(&["commit", "-m", "second"]);
    let accepted = alpha.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    musubi_in(&env, &logs, &alpha, &["sync"]);
    alpha.jj(&["describe", "-m", "third"]);
    alpha.jj(&["op", "abandon", &format!("..{accepted}")]);
    let err = musubi_fails(&env, &logs, &alpha, &["sync"]);
    insta::assert_snapshot!(err, @"Error: this repository lost history the hive has (was `jj op abandon` run?), so it can't sync again: make a new copy with `musubi clone`, bring this one's work across to it, then run `musubi leave --force` here");
    let (_, hints) = status_in(&env, &logs, &alpha);
    insta::assert_snapshot!(hints, @"
    Warning: Syncing fails: this repository lost history the hive has (was `jj op abandon` run?), so it can't sync again: make a new copy with `musubi clone`, bring this one's work across to it, then run `musubi leave --force` here
    Hint: Retrying won't get past this; the warning says what will.
    ");

    // Nor does joining again, which says so, though the copy joins.
    musubi_in(&env, &logs, &alpha, &["leave", "--force"]);
    let err = musubi_fails(&env, &logs, &alpha, &["join"]);
    insta::assert_snapshot!(err, @"Error: this repository lost history the hive has (was `jj op abandon` run?), so it can't sync again: make a new copy with `musubi clone`, bring this one's work across to it, then run `musubi leave --force` here");
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
    Hub $ROOT/home/musubi-hub:
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
    // Run in a repository, the hub still lives in ~/musubi-hub.
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
    alpha.write_file("b", "later");
    alpha.jj(&["commit", "-m", "later"]);
    wait_for(&logs, "beta's daemon to bring alpha's commit", || {
        try_log(&beta).is_some_and(|log| log.contains("later"))
    });
    let gamma = env.repo_handle("gamma");
    let dir = gamma.path().to_str().unwrap();
    let args: Vec<&str> = strs(&clone)
        .into_iter()
        .map(|arg| match arg {
            "<name>" => "alpha",
            "<dir>" => dir,
            arg => arg,
        })
        .collect();
    musubi_on(&beta, &args, true);
    assert!(log(&gamma).contains("later"));

    let _filters = snapshot_filters(&env);
    insta::assert_snapshot!(transcript, @"
    $ musubi hub
    Created a new hub in $ROOT/home/musubi-hub
    To share a repository:               musubi create --hub $HOST
    To add another machine's copy of it: musubi join --hub $HOST
    To make a new copy of a hive:        musubi clone <name> <dir> --hub $HOST
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
