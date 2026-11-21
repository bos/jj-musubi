//! Stop a jj subprocess just before creating its new operation head and unlinking its old one.

use std::hash::{DefaultHasher, Hash as _, Hasher as _};
use std::io::{self, Read as _, Write as _};
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
        let mut paused = self.start(command, old_head, socket);
        paused.wait_for(Phase::BeforeCreate);
        paused
    }

    /// Starts a command that may add and remove any head, as loading the repository at
    /// several heads does, pausing before it adds one; or `None` once it has exited without
    /// adding any, as it does when the heads settled before it took jj's op-heads lock.
    pub(super) fn spawn_loader(
        &self,
        command: &mut Command,
        old_head: &Path,
        socket: &Path,
    ) -> Option<PausedCommand> {
        command.env("MUSUBI_TEST_HEAD_GATE_ANY", "1");
        let mut paused = self.start(command, old_head, socket);
        paused.try_wait_for(Phase::BeforeCreate).then_some(paused)
    }

    fn start(&self, command: &mut Command, old_head: &Path, socket: &Path) -> PausedCommand {
        let old_head = old_head
            .parent()
            .unwrap()
            .canonicalize()
            .unwrap()
            .join(old_head.file_name().unwrap());
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
        let output = tempfile::tempfile_in(socket.parent().unwrap())
            .expect("capture jj diagnostics at the gate");
        let child = command
            .env("LD_PRELOAD", &self.library)
            .env("MUSUBI_TEST_HEAD_GATE_PATH", &old_head)
            .env("MUSUBI_TEST_HEAD_GATE_SOCKET", name)
            .stdout(Stdio::null())
            .stderr(output.try_clone().unwrap())
            .spawn()
            .expect("start jj with the operation-head gate");
        PausedCommand {
            child,
            listener,
            pause: None,
            old_head,
            output,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    BeforeCreate,
    BeforeUnlink,
}

pub(super) struct PausedCommand {
    child: Child,
    listener: UnixListener,
    pause: Option<(Phase, UnixStream)>,
    old_head: PathBuf,
    output: std::fs::File,
}

impl PausedCommand {
    fn diagnostics(&self) -> String {
        use std::io::{Seek as _, SeekFrom};
        let mut output = &self.output;
        output.seek(SeekFrom::Start(0)).unwrap();
        let mut text = String::new();
        output.read_to_string(&mut text).unwrap();
        text
    }

    fn wait_for(&mut self, phase: Phase) {
        assert!(
            self.try_wait_for(phase),
            "jj exited while waiting for {phase:?} at {:?}: {}",
            self.old_head,
            self.diagnostics()
        );
    }

    /// Waits until jj pauses at `phase`: true, or false if it exited successfully first.
    fn try_wait_for(&mut self, phase: Phase) -> bool {
        let mut backoff = Backoff::new();
        loop {
            match self.listener.accept() {
                Ok((stream, _)) => {
                    self.receive_phase(phase, stream);
                    return true;
                }
                Err(err) if err.kind() == io::ErrorKind::WouldBlock => {}
                Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
                Err(err) => panic!("accept the jj operation-head gate: {err}"),
            }
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(
                    status.success(),
                    "jj exited with {status} while waiting for {phase:?} at {:?}: {}",
                    self.old_head,
                    self.diagnostics()
                );
                return false;
            }
            assert!(
                backoff.wait(),
                "jj did not reach {phase:?} at {:?} within {TIMEOUT:?}",
                self.old_head
            );
        }
    }

    fn receive_phase(&mut self, expected: Phase, mut stream: UnixStream) {
        stream.set_read_timeout(Some(TIMEOUT)).unwrap();
        let mut message = [0];
        stream.read_exact(&mut message).unwrap_or_else(|err| {
            panic!(
                "read the jj operation-head gate phase while waiting for {expected:?} at {:?}: {err}",
                self.old_head
            )
        });
        let phase = match message[0] {
            b'C' => Phase::BeforeCreate,
            b'U' => Phase::BeforeUnlink,
            byte => panic!("invalid jj operation-head gate phase byte {byte}"),
        };
        assert_eq!(
            phase, expected,
            "jj operation-head gate at {:?}",
            self.old_head
        );
        self.pause = Some((phase, stream));
    }

    fn resume(&mut self, expected: Phase) {
        let (phase, mut stream) = self
            .pause
            .take()
            .expect("jj is paused at the operation-head gate");
        assert_eq!(
            phase, expected,
            "jj operation-head gate at {:?}",
            self.old_head
        );
        stream
            .write_all(&[1])
            .expect("release the jj operation-head gate");
    }

    pub(super) fn publish(&mut self) {
        self.resume(Phase::BeforeCreate);
        self.wait_for(Phase::BeforeUnlink);
    }

    /// As [`Self::publish`], for a command that may add a head and remove none: true if it
    /// paused before an unlink, false if it exited.
    pub(super) fn publish_or_exit(&mut self) -> bool {
        self.resume(Phase::BeforeCreate);
        self.try_wait_for(Phase::BeforeUnlink)
    }

    pub(super) fn kill(mut self) {
        self.child
            .kill()
            .expect("kill jj at the operation-head gate");
        self.child
            .wait()
            .expect("reap jj at the operation-head gate");
    }

    pub(super) fn release(mut self) {
        self.resume(Phase::BeforeUnlink);
        let mut backoff = Backoff::new();
        loop {
            if let Some(status) = self.child.try_wait().unwrap() {
                assert!(
                    status.success(),
                    "jj failed with {status} after reaching unlink of {:?}: {}",
                    self.old_head,
                    self.diagnostics()
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
