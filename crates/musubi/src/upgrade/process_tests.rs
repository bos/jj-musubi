//! Real shell children and separate daemon lifetimes, without a service, repository or hub.
//! The helpers run in this test binary, with private config and state. Sockets acknowledge
//! that the installer is running and let a test finish it or expire the worker's wait.

#![allow(clippy::unwrap_used)]

use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Read as _;
use std::io::Write as _;
use std::os::unix::fs::PermissionsExt as _;
use std::os::unix::net::UnixListener;
use std::os::unix::net::UnixStream;
use std::process::Stdio;

use serde_json::Value;
use serde_json::json;

use super::*;

const RELEASE_TO_INSTALL: &str = "99.0.0";
const LIMIT: Duration = Duration::from_secs(10);

fn until(mut condition: impl FnMut() -> bool) {
    let deadline = Instant::now() + LIMIT;
    let mut backoff = Duration::from_millis(1);
    while !condition() {
        assert!(Instant::now() < deadline, "condition did not become true");
        std::thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_millis(20));
    }
}

fn accept(listener: &UnixListener) -> UnixStream {
    listener.set_nonblocking(true).unwrap();
    let mut stream = None;
    until(|| match listener.accept() {
        Ok((connected, _)) => {
            stream = Some(connected);
            true
        }
        Err(err) if err.kind() == std::io::ErrorKind::WouldBlock => false,
        Err(err) => panic!("accepting helper: {err}"),
    });
    let stream = stream.unwrap();
    stream.set_nonblocking(false).unwrap();
    stream.set_read_timeout(Some(LIMIT)).unwrap();
    stream.set_write_timeout(Some(LIMIT)).unwrap();
    stream
}

fn line(stream: &mut UnixStream) -> Value {
    let mut text = String::new();
    BufReader::new(stream).read_line(&mut text).unwrap();
    serde_json::from_str(&text).unwrap()
}

fn reply(stream: &mut UnixStream, value: Value) {
    writeln!(stream, "{value}").unwrap();
}

fn quote(path: &Path) -> String {
    format!("'{}'", path.to_str().unwrap().replace('\'', "'\\''"))
}

struct Fixture {
    dir: tempfile::TempDir,
    daemons: UnixListener,
    installers: UnixListener,
    deadlines: UnixListener,
}

impl Fixture {
    fn new() -> Self {
        let dir = musubi_testutil::tempdir();
        // Shell commands are real processes, but the installed executable only answers the
        // version check. The existing CLI test covers actually restarting the daemon.
        let exe = dir.path().join("musubi");
        fs::write(&exe, "#!/bin/sh\necho musubi 99.0.0\n").unwrap();
        fs::set_permissions(&exe, fs::Permissions::from_mode(0o755)).unwrap();
        let command = format!(
            "{} --exact upgrade::process_tests::installer_process --nocapture --ignored; status=$?; exit \"$status\"",
            quote(&std::env::current_exe().unwrap())
        );
        fs::write(
            dir.path().join("config.toml"),
            format!("[musubi]\nupgrade-command = {}\n", json!(command)),
        )
        .unwrap();
        Self {
            daemons: UnixListener::bind(dir.path().join("daemon.sock")).unwrap(),
            installers: UnixListener::bind(dir.path().join("installer.sock")).unwrap(),
            deadlines: UnixListener::bind(dir.path().join("deadline.sock")).unwrap(),
            dir,
        }
    }

    fn daemon(&self, expire: bool) -> Daemon {
        let child = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "upgrade::process_tests::daemon_process",
                "--nocapture",
                "--ignored",
            ])
            .env_clear()
            .env("PATH", std::env::var_os("PATH").unwrap_or_default())
            .env("HOME", self.dir.path())
            .env("JJ_CONFIG", self.dir.path().join("config.toml"))
            .env("MUSUBI_STATE_DIR", self.dir.path())
            .env("MUSUBI_UPGRADE_TEST_ROOT", self.dir.path())
            .env(
                "MUSUBI_UPGRADE_TEST_EXPIRE",
                if expire { "yes" } else { "no" },
            )
            .current_dir(self.dir.path())
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let stream = accept(&self.daemons);
        Daemon { child, stream }
    }

    fn installer(&self) -> UnixStream {
        let mut stream = accept(&self.installers);
        let info = line(&mut stream);
        assert_eq!(info["release"], RELEASE_TO_INSTALL);
        assert_eq!(
            info["cwd"],
            self.dir.path().canonicalize().unwrap().to_str().unwrap()
        );
        stream
    }

    fn attempts(&self) -> String {
        fs::read_to_string(self.dir.path().join("attempts")).unwrap()
    }

    fn unlocked(&self) -> bool {
        crate::lock::try_lock(&self.dir.path().join("upgrade.lock"))
            .unwrap()
            .is_some()
    }

    fn log(&self) -> String {
        fs::read_to_string(self.dir.path().join("upgrade.log")).unwrap()
    }
}

struct Daemon {
    child: Child,
    stream: UnixStream,
}

impl Daemon {
    fn begin(&mut self) {
        self.stream.write_all(b"t").unwrap();
    }

    fn done(&mut self) -> Value {
        line(&mut self.stream)
    }

    fn kill(&mut self) {
        self.child.kill().unwrap();
        self.child.wait().unwrap();
    }
}

impl Drop for Daemon {
    fn drop(&mut self) {
        if self.child.try_wait().unwrap().is_none() {
            self.child.kill().ok();
            self.child.wait().ok();
        }
    }
}

fn finish(installer: &mut UnixStream, outcome: u8) {
    installer.write_all(&[outcome]).unwrap();
    // Exit of the process closes the socket; no arbitrary delay before checking the lock.
    assert_eq!(installer.read(&mut [0]).unwrap(), 0);
}

/// The only process with an upgrade worker dies while its command holds the lock. A fresh
/// worker defers without consuming its attempt; in that same lifetime it can retry later.
#[test]
fn an_upgrade_outlives_its_daemon_and_contention_can_retry() {
    let fixture = Fixture::new();
    let mut first = fixture.daemon(false);
    first.begin();
    let mut installer = fixture.installer();
    assert!(!fixture.unlocked());
    first.kill();
    assert!(
        !fixture.unlocked(),
        "the daemon owned the lock, not its command"
    );

    let mut next = fixture.daemon(false);
    next.begin();
    let deferred = next.done();
    assert_eq!(deferred["tried"], Value::Null);
    assert_eq!(deferred["failure"], Value::Null);
    assert_eq!(deferred["installed"], false);
    assert_eq!(fixture.attempts(), "attempt\n");

    finish(&mut installer, b's');
    until(|| fixture.unlocked());
    next.begin();
    let mut installer = fixture.installer();
    finish(&mut installer, b's');
    let installed = next.done();
    assert_eq!(installed["tried"], RELEASE_TO_INSTALL);
    assert_eq!(installed["failure"], Value::Null);
    assert_eq!(installed["installed"], true);
    assert_eq!(fixture.attempts(), "attempt\nattempt\n");
}

/// A deadline is released only after the shell's foreground child is running. Stopping
/// just the shell strands that child with the lock and prevents the next daemon's retry.
#[test]
fn timeout_stops_the_command_and_its_child_before_retry() {
    let fixture = Fixture::new();
    let mut first = fixture.daemon(true);
    first.begin();
    let mut deadline = accept(&fixture.deadlines);
    let mut installer = fixture.installer();
    assert!(!fixture.unlocked());
    deadline.write_all(b"x").unwrap();
    let failed = first.done();
    assert_eq!(failed["tried"], RELEASE_TO_INSTALL);
    assert_eq!(failed["installed"], false);
    assert_eq!(
        failed["failure"],
        json!([
            RELEASE_TO_INSTALL,
            "musubi.upgrade-command ran for over 0 minutes, so it was stopped"
        ])
    );
    assert_eq!(
        installer
            .read(&mut [0])
            .expect("timed-out installer is still running"),
        0,
        "installer survived timeout"
    );
    until(|| fixture.unlocked());
    assert!(fixture.log().contains("installer output"));

    // A genuine failure is tried once per daemon lifetime, unlike lock contention.
    first.begin();
    assert_eq!(first.done(), failed);
    assert_eq!(fixture.attempts(), "attempt\n");
    let mut next = fixture.daemon(false);
    next.begin();
    let mut installer = fixture.installer();
    finish(&mut installer, b's');
    let installed = next.done();
    assert_eq!(installed["installed"], true);
    assert_eq!(installed["failure"], Value::Null);
    assert!(!fixture.dir.path().join("upgrade-failed").exists());
    assert_eq!(fixture.attempts(), "attempt\nattempt\n");
}

/// A command's nonzero status is recorded, with its output's path, until a fresh daemon
/// retries; success clears it and requests a restart from the installed executable.
#[test]
fn a_failed_command_is_reported_and_a_fresh_daemon_can_retry() {
    let fixture = Fixture::new();
    let mut first = fixture.daemon(false);
    first.begin();
    let mut installer = fixture.installer();
    finish(&mut installer, b'f');
    let failed = first.done();
    assert_eq!(failed["tried"], RELEASE_TO_INSTALL);
    assert_eq!(failed["installed"], false);
    let why = failed["failure"][1].as_str().unwrap();
    assert!(
        why.starts_with("musubi.upgrade-command failed (exit status: 7)"),
        "{why}"
    );
    assert!(
        why.ends_with(&format!(
            "its output is in {}",
            fixture.dir.path().join("upgrade.log").display()
        )),
        "{why}"
    );
    assert!(fixture.log().contains("installer output"));
    assert!(fixture.unlocked());
    first.begin();
    assert_eq!(first.done(), failed);
    assert_eq!(fixture.attempts(), "attempt\n");

    let mut next = fixture.daemon(false);
    next.begin();
    let mut installer = fixture.installer();
    finish(&mut installer, b's');
    let installed = next.done();
    assert_eq!(installed["installed"], true);
    assert_eq!(installed["failure"], Value::Null);
    assert!(!fixture.dir.path().join("upgrade-failed").exists());
    assert_eq!(fixture.attempts(), "attempt\nattempt\n");
}

/// Entrypoint for a disposable process containing the real upgrade worker and its statics.
#[test]
#[ignore = "helper process launched by upgrade process tests"]
fn daemon_process() {
    let Some(root) = std::env::var_os("MUSUBI_UPGRADE_TEST_ROOT").map(PathBuf::from) else {
        return;
    };
    EXE.set(root.join("musubi")).unwrap();
    let mut stream = UnixStream::connect(root.join("daemon.sock")).unwrap();
    let mut request = [0];
    while stream.read(&mut request).unwrap() != 0 {
        assert_eq!(request[0], b't');
        consider_with_wait(RELEASE_TO_INSTALL, controlled_wait);
        until(|| !lock_tried().running);
        let tried = lock_tried();
        reply(
            &mut stream,
            json!({
                "tried": tried.release.as_ref().map(ToString::to_string),
                "installed": RESTART.get().is_some(),
                "failure": failure(),
            }),
        );
    }
}

fn controlled_wait(child: &mut Child) -> anyhow::Result<ExitStatus> {
    if std::env::var("MUSUBI_UPGRADE_TEST_EXPIRE").unwrap() == "yes" {
        let root = std::env::var_os("MUSUBI_UPGRADE_TEST_ROOT").unwrap();
        let mut deadline = UnixStream::connect(Path::new(&root).join("deadline.sock")).unwrap();
        deadline.set_read_timeout(Some(LIMIT)).unwrap();
        deadline.read_exact(&mut [0]).unwrap();
        wait(child, Duration::ZERO)
    } else {
        wait(child, TIMEOUT)
    }
}

/// Entrypoint for the command's foreground child. It inherits the actual locked stdin.
#[test]
#[ignore = "helper process launched by upgrade process tests"]
fn installer_process() {
    let Some(root) = std::env::var_os("MUSUBI_UPGRADE_TEST_ROOT").map(PathBuf::from) else {
        return;
    };
    let mut attempts = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(root.join("attempts"))
        .unwrap();
    writeln!(attempts, "attempt").unwrap();
    println!("installer output");
    let mut stream = UnixStream::connect(root.join("installer.sock")).unwrap();
    stream.set_read_timeout(Some(LIMIT * 6)).unwrap();
    reply(
        &mut stream,
        json!({
            "release": std::env::var("MUSUBI_UPGRADE_TO").unwrap(),
            "cwd": std::env::current_dir().unwrap(),
        }),
    );
    let mut outcome = [0];
    stream.read_exact(&mut outcome).unwrap();
    match outcome[0] {
        b's' => (),
        b'f' => std::process::exit(7),
        _ => panic!("unknown installer outcome"),
    }
}
