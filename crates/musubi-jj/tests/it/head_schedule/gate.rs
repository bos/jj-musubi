//! Stop a jj subprocess just before unlinking one operation head.

use std::hash::{DefaultHasher, Hash as _, Hasher as _};
use std::io::{self, Write as _};
use std::os::linux::net::SocketAddrExt as _;
use std::os::unix::net::{SocketAddr, UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

const TIMEOUT: Duration = Duration::from_secs(30);

pub(super) struct Gate {
    library: PathBuf,
}

impl Gate {
    pub(super) fn compile(directory: &Path) -> Self {
        let gate = Self::load(directory);
        let mut compiler = Command::new("cc")
            .args([
                "-std=c11", "-shared", "-fPIC", "-Wall", "-Wextra", "-Werror",
            ])
            .arg("-o")
            .arg(&gate.library)
            .args(["-x", "c", "-", "-ldl"])
            .stdin(Stdio::piped())
            .spawn()
            .expect("start C compiler for the jj operation-head gate");
        compiler
            .stdin
            .take()
            .unwrap()
            .write_all(include_bytes!("gate.c"))
            .expect("write the jj operation-head gate to cc");
        let status = compiler.wait().unwrap();
        assert!(
            status.success(),
            "compile the jj operation-head gate: {status}"
        );
        gate
    }

    pub(super) fn load(directory: &Path) -> Self {
        let library = directory
            .canonicalize()
            .unwrap()
            .join("head-schedule-gate.so");
        Self { library }
    }

    pub(super) fn spawn(
        &self,
        command: &mut Command,
        old_head: &Path,
        socket: &Path,
    ) -> PausedCommand {
        let old_head = old_head.canonicalize().unwrap();
        // Abstract sockets leave no file in the repository and fit even when a fixture path
        // exceeds Linux's limit on Unix socket names.
        let mut hasher = DefaultHasher::new();
        socket.hash(&mut hasher);
        let name = format!(
            "musubi-head-{}-{:016x}",
            std::process::id(),
            hasher.finish()
        );
        let address = SocketAddr::from_abstract_name(name.as_bytes()).unwrap();
        let listener = UnixListener::bind_addr(&address).expect("bind the jj operation-head gate");
        listener.set_nonblocking(true).unwrap();
        let child = command
            .env("LD_PRELOAD", &self.library)
            .env("MUSUBI_TEST_HEAD_GATE_PATH", &old_head)
            .env("MUSUBI_TEST_HEAD_GATE_SOCKET", name)
            .spawn()
            .expect("start jj with the operation-head gate");
        let mut paused = PausedCommand {
            child,
            stream: None,
            old_head,
        };
        let mut backoff = Backoff::new();
        loop {
            match listener.accept() {
                Ok((stream, _)) => {
                    paused.stream = Some(stream);
                    return paused;
                }
                Err(err) if err.kind() == io::ErrorKind::WouldBlock => {}
                Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
                Err(err) => panic!("accept the jj operation-head gate: {err}"),
            }
            if let Some(status) = paused.child.try_wait().unwrap() {
                panic!(
                    "{command:?} exited with {status} before unlinking {:?}",
                    paused.old_head
                );
            }
            assert!(
                backoff.wait(),
                "{command:?} did not reach unlink of {:?} within {TIMEOUT:?}",
                paused.old_head
            );
        }
    }
}

pub(super) struct PausedCommand {
    child: Child,
    stream: Option<UnixStream>,
    old_head: PathBuf,
}

impl PausedCommand {
    pub(super) fn release(mut self) {
        self.stream
            .take()
            .unwrap()
            .write_all(&[1])
            .expect("release the jj operation-head gate");
        let mut backoff = Backoff::new();
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(
                    status.success(),
                    "jj failed with {status} after reaching unlink of {:?}",
                    self.old_head
                );
                return;
            }
            assert!(
                backoff.wait(),
                "jj did not exit within {TIMEOUT:?} after reaching unlink of {:?}",
                self.old_head
            );
        }
    }
}

impl Drop for PausedCommand {
    fn drop(&mut self) {
        drop(self.child.kill());
        drop(self.child.wait());
    }
}

struct Backoff {
    deadline: Instant,
    delay: Duration,
}

impl Backoff {
    fn new() -> Self {
        Self {
            deadline: Instant::now() + TIMEOUT,
            delay: Duration::from_millis(1),
        }
    }

    fn wait(&mut self) -> bool {
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return false;
        }
        thread::sleep(self.delay.min(remaining));
        self.delay = (self.delay * 2).min(Duration::from_millis(20));
        true
    }
}
