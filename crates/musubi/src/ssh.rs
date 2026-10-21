//! Reaching a hub on another machine over ssh: a hub listens only on its own.
//!
//! The machine gets a key of its own (`hub_key` in the state directory), which joining
//! adds to `~/.ssh/authorized_keys` on the hub's machine, allowed only to run
//! `musubi hub connect`. Each connection to the hub is an ssh of its own running that, and
//! the [`StreamTransport`](musubi_transport::StreamTransport) speaks to the hub through its
//! standard input and output. Nothing lasts longer than a connection, so after the machine
//! sleeps, connecting again is a fresh ssh.
//!
//! The ssh is the user's own `ssh` (or `$MUSUBI_SSH`), so `~/.ssh/config` applies: host
//! aliases, `ProxyCommand`, and the rest.

use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::pin::Pin;
use std::process::ExitStatus;
use std::process::Stdio;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::task::Context;
use std::task::Poll;
use std::time::Duration;
use std::time::Instant;
use std::time::SystemTime;

use anyhow::Context as _;
use async_trait::async_trait;
use musubi_transport::stream::Connector;
use musubi_transport::stream::GREETING;
use musubi_transport::stream::Reader;
use musubi_transport::stream::Writer;
use musubi_transport::stream::await_greeting;
use tokio::io::AsyncRead;
use tokio::io::AsyncReadExt as _;
use tokio::io::AsyncWriteExt as _;
use tokio::io::ReadBuf;
use tokio::process::Child;
use tokio::process::ChildStderr;
use tokio::process::ChildStdout;
use tokio::process::Command;
use tokio::sync::oneshot;
use tokio::sync::watch;

use crate::config;

/// What the machine's key may run on the hub's machine.
const REMOTE_COMMAND: &str = "musubi hub connect";

/// How long a failing ssh waits before the next try, at most.
const MAX_BACKOFF: Duration = Duration::from_secs(60);

/// How often to look for the machine having slept.
const WAKE_CHECK: Duration = Duration::from_secs(5);

/// How much of what ssh says on stderr to keep: the end says why it failed.
const MAX_SAID: usize = 16 * 1024;

/// The ssh to run: `ssh`, or `$MUSUBI_SSH`, as tests set.
fn program() -> OsString {
    std::env::var_os("MUSUBI_SSH").unwrap_or_else(|| "ssh".into())
}

/// The machine's own key for reaching hubs.
fn key_path() -> anyhow::Result<PathBuf> {
    Ok(config::state_dir()?.join("hub_key"))
}

/// ssh as the daemon runs it: with the machine's key, never prompting, without compression
/// (musubi compresses what it sends), and giving up on a link that stops answering.
fn connect_command(dest: &str, key: &Path) -> Command {
    let mut command = Command::new(program());
    command
        .arg("-i")
        .arg(key)
        .args([
            "-o",
            "IdentitiesOnly=yes",
            "-o",
            "BatchMode=yes",
            "-o",
            "Compression=no",
            "-o",
            "ConnectTimeout=20",
            "-o",
            "ServerAliveInterval=10",
            "-o",
            "ServerAliveCountMax=2",
            "-T",
            "--",
            dest,
            REMOTE_COMMAND,
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true);
    command
}

/// What a failed ssh means, from how it exited and the last thing it said.
fn describe_failure(dest: &str, status: Option<ExitStatus>, stderr: &str) -> String {
    let said = stderr.trim().lines().last().unwrap_or_default().trim();
    match status.and_then(|status| status.code()) {
        Some(127) => format!(
            "`musubi` is not on the PATH of non-interactive shells on {dest}; put it there (in \
             ~/.zshenv, or near the top of ~/.bashrc), or give its absolute path in the \
             `{REMOTE_COMMAND}` line of ~/.ssh/authorized_keys on {dest}"
        ),
        Some(255) => format!("ssh to {dest} failed: {said}"),
        // Finished, though the hub never greeted: it closed first, or didn't answer in time.
        Some(0) => format!("the hub on {dest} ended the connection before greeting"),
        // musubi's own error leads with what went wrong; its causes follow.
        Some(_) => {
            let error = stderr
                .lines()
                .find_map(|line| line.strip_prefix("Error: "))
                .unwrap_or(said);
            format!("`{REMOTE_COMMAND}` on {dest} failed: {error}")
        }
        None if said.is_empty() => format!("ssh to {dest} did not connect"),
        None => format!("ssh to {dest} did not connect: {said}"),
    }
}

#[derive(Default)]
struct State {
    /// Failed connections since the last that worked.
    failures: u32,
    /// Until when to refuse connections, after failures.
    retry_at: Option<Instant>,
    /// What the last failure was, until a connection works.
    problem: Option<String>,
}

/// How a link's ssh connections are going.
#[derive(Clone, Default)]
pub struct Health(Arc<Mutex<State>>);

impl Health {
    fn lock(&self) -> std::sync::MutexGuard<'_, State> {
        self.0.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// What is wrong, while the connections fail.
    pub fn problem(&self) -> Option<String> {
        self.lock().problem.clone()
    }

    fn failed(&self, problem: String) {
        let mut state = self.lock();
        state.failures += 1;
        let backoff = Duration::from_secs(1) * 2u32.saturating_pow(state.failures - 1);
        state.retry_at = Some(Instant::now() + backoff.min(MAX_BACKOFF));
        tracing::warn!("{problem}");
        state.problem = Some(problem);
    }

    fn worked(&self) {
        *self.lock() = State::default();
    }

    fn refusing(&self) -> bool {
        self.lock().retry_at.is_some_and(|at| Instant::now() < at)
    }
}

/// Opens connections to a hub over ssh, each through an ssh of its own; and after the
/// machine sleeps, ends them all, since their links are likely dead, and forgets past
/// failures.
pub struct Link {
    dest: String,
    key: PathBuf,
    health: Health,
    woke: watch::Sender<u64>,
    /// Whether how the last connection opened went is known yet (see [`Ssh::settled`]).
    latest: Mutex<Option<Arc<AtomicBool>>>,
    task: tokio::task::JoinHandle<()>,
}

impl Drop for Link {
    fn drop(&mut self) {
        self.task.abort();
    }
}

impl Link {
    pub fn new(dest: &str) -> anyhow::Result<Self> {
        let health = Health::default();
        let woke = watch::channel(0).0;
        let task = tokio::spawn(watch_for_waking(
            dest.to_owned(),
            health.clone(),
            woke.clone(),
        ));
        Ok(Self {
            dest: dest.to_owned(),
            key: key_path()?,
            health,
            woke,
            latest: Mutex::new(None),
            task,
        })
    }

    pub fn health(&self) -> Health {
        self.health.clone()
    }
}

#[async_trait]
impl Connector for Link {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        // After failures, trying again at once would run ssh, and maybe a login prompt in a
        // browser, every few seconds.
        if self.health.refusing() {
            return Err(io::Error::other("waiting to try ssh again"));
        }
        let mut child = connect_command(&self.dest, &self.key)
            .spawn()
            .inspect_err(|err| self.health.failed(format!("cannot run ssh: {err}")))?;
        let (Some(stdin), Some(stdout), Some(stderr)) =
            (child.stdin.take(), child.stdout.take(), child.stderr.take())
        else {
            return Err(io::Error::other("ssh's pipes went missing"));
        };
        let settled = Arc::new(AtomicBool::new(false));
        *self.latest.lock().unwrap_or_else(PoisonError::into_inner) = Some(settled.clone());
        let (closed, let_go) = oneshot::channel();
        tokio::spawn(supervise(Ssh {
            child,
            stderr,
            dest: self.dest.clone(),
            health: self.health.clone(),
            settled: settled.clone(),
            woke: self.woke.subscribe(),
            let_go,
        }));
        let output = Output {
            stdout,
            tail: vec![],
            settled,
            health: self.health.clone(),
            _closed: closed,
        };
        Ok((Box::new(output), Box::new(stdin)))
    }

    fn not_hub(&self, why: &io::Error) {
        let latest = self
            .latest
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        if let Some(settled) = latest {
            settled.store(true, Ordering::Relaxed);
        }
        self.health
            .failed(format!("ssh to {} worked, but {why}", self.dest));
    }
}

/// After the machine sleeps, ends every connection, since their links are likely dead, and
/// forgets past failures.
async fn watch_for_waking(dest: String, health: Health, woke: watch::Sender<u64>) {
    let mut check = tokio::time::interval(WAKE_CHECK);
    let (mut wall, mut clock) = (SystemTime::now(), Instant::now());
    loop {
        check.tick().await;
        // `Instant` stops while the machine sleeps; the wall clock doesn't.
        let (now_wall, now_clock) = (SystemTime::now(), Instant::now());
        let slept = now_wall
            .duration_since(wall)
            .unwrap_or_default()
            .saturating_sub(now_clock - clock);
        if slept > 2 * WAKE_CHECK {
            tracing::info!(
                "woke after about {}s asleep; reconnecting to {dest}",
                slept.as_secs()
            );
            health.worked();
            woke.send_modify(|n| *n += 1);
        }
        (wall, clock) = (now_wall, now_clock);
    }
}

/// ssh's standard output, which notes when the hub's greeting has come through it, and whose
/// dropping tells the ssh's supervisor that the connection has been let go.
struct Output {
    stdout: ChildStdout,
    /// The end of what has come so far, until the greeting has: what a shell's startup files
    /// print comes first, and isn't the hub answering.
    tail: Vec<u8>,
    settled: Arc<AtomicBool>,
    health: Health,
    _closed: oneshot::Sender<()>,
}

impl AsyncRead for Output {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let this = self.get_mut();
        let before = buf.filled().len();
        let poll = Pin::new(&mut this.stdout).poll_read(cx, buf);
        if !this.settled.load(Ordering::Relaxed) {
            this.tail.extend_from_slice(&buf.filled()[before..]);
            if this.tail.windows(GREETING.len()).any(|w| w == GREETING) {
                this.settled.store(true, Ordering::Relaxed);
                this.health.worked();
                this.tail = vec![];
            } else {
                let passed = this.tail.len().saturating_sub(GREETING.len() - 1);
                this.tail.drain(..passed);
            }
        }
        poll
    }
}

/// One connection's ssh, and what its supervisor needs to know.
struct Ssh {
    child: Child,
    stderr: ChildStderr,
    dest: String,
    health: Health,
    /// Whether how the connection went is known: the hub greeted through it, or the transport
    /// gave up on it and said why.
    settled: Arc<AtomicBool>,
    woke: watch::Receiver<u64>,
    /// Ends when the connection is let go.
    let_go: oneshot::Receiver<()>,
}

/// Waits for a connection's ssh to finish, ending it once the connection is let go, or at
/// once when the machine wakes; and if the hub never greeted, and the transport didn't say
/// why, records what ssh says.
async fn supervise(mut ssh: Ssh) {
    let said = Arc::new(Mutex::new(vec![]));
    let mut reading = tokio::spawn(read_stderr(ssh.stderr, said.clone()));
    enum Ended {
        Exited(Option<ExitStatus>),
        LetGo,
        Woke,
    }
    let ended = tokio::select! {
        status = ssh.child.wait() => Ended::Exited(status.ok()),
        _ = ssh.let_go => Ended::LetGo,
        _ = ssh.woke.changed() => Ended::Woke,
    };
    let status = match ended {
        Ended::Exited(status) => status,
        // Its standard input closed with the connection, so it should finish by itself; one
        // still going is one the machine's sleeping broke.
        Ended::LetGo => {
            match tokio::time::timeout(Duration::from_secs(1), ssh.child.wait()).await {
                Ok(status) => status.ok(),
                Err(_) => {
                    ssh.child.start_kill().ok();
                    ssh.child.wait().await.ok();
                    None
                }
            }
        }
        Ended::Woke => {
            ssh.child.start_kill().ok();
            ssh.child.wait().await.ok();
            reading.abort();
            return;
        }
    };
    if ssh.settled.load(Ordering::Relaxed) {
        reading.abort();
        return;
    }
    let said = said_so_far(&mut reading, &said).await;
    // Settled meanwhile, perhaps by a greeting read just as ssh exited.
    if !ssh.settled.load(Ordering::Relaxed) {
        ssh.health
            .failed(describe_failure(&ssh.dest, status, &said));
    }
}

/// Reads ssh's stderr into `said` as it comes, so that a chatty ssh never blocks on a full
/// pipe, keeping the end of it.
async fn read_stderr(mut stderr: ChildStderr, said: Arc<Mutex<Vec<u8>>>) {
    let mut buf = [0; 4096];
    while let Ok(n) = stderr.read(&mut buf).await
        && n > 0
    {
        let mut said = said.lock().unwrap_or_else(PoisonError::into_inner);
        said.extend_from_slice(&buf[..n]);
        if said.len() > MAX_SAID {
            let cut = said.len() - MAX_SAID / 2;
            said.drain(..cut);
        }
    }
}

/// What ssh has said on stderr, once it has exited. What it ran may hold stderr open after
/// it has gone, as a `ProxyCommand` can, so this waits for the end only a moment.
async fn said_so_far(reading: &mut tokio::task::JoinHandle<()>, said: &Mutex<Vec<u8>>) -> String {
    tokio::time::timeout(Duration::from_secs(1), &mut *reading)
        .await
        .ok();
    reading.abort();
    let said = said.lock().unwrap_or_else(PoisonError::into_inner);
    String::from_utf8_lossy(&said).into_owned()
}

/// How one try of the machine's key went wrong.
struct Failure {
    status: Option<ExitStatus>,
    said: String,
    /// Why what answered can't be talked to, when ssh worked but it isn't a hub of this
    /// version.
    not_hub: Option<String>,
}

impl Failure {
    /// Whether ssh refused the key: most likely, it isn't on the hub's machine yet.
    fn refused(&self) -> bool {
        self.status.and_then(|status| status.code()) == Some(255)
    }

    fn describe(&self, dest: &str) -> String {
        match &self.not_hub {
            Some(why) => format!("ssh to {dest} worked, but {why}"),
            None => describe_failure(dest, self.status, &self.said),
        }
    }
}

/// Runs `musubi hub connect` on `dest` with the machine's key, to see whether a hub answers.
async fn probe(dest: &str, key: &Path) -> Result<(), Failure> {
    let failure = |said: String| Failure {
        status: None,
        said,
        not_hub: None,
    };
    let mut child = connect_command(dest, key)
        .spawn()
        .map_err(|err| failure(format!("cannot run ssh: {err}")))?;
    let (Some(stdout), Some(stderr)) = (child.stdout.take(), child.stderr.take()) else {
        return Err(failure(String::new()));
    };
    let said = Arc::new(Mutex::new(vec![]));
    let mut reading = tokio::spawn(read_stderr(stderr, said.clone()));
    // A hub speaks first, after whatever the shell's startup files there print.
    let mut stdout = tokio::io::BufReader::new(stdout);
    let greeted = tokio::time::timeout(Duration::from_secs(60), await_greeting(&mut stdout)).await;
    let not_hub = match greeted {
        Ok(Ok(())) => {
            reading.abort();
            return Ok(());
        }
        Ok(Err(err)) if err.kind() == io::ErrorKind::InvalidData => Some(err.to_string()),
        // ssh ended, and how it did says why.
        Ok(Err(_)) => None,
        Err(_) => {
            child.start_kill().ok();
            None
        }
    };
    if not_hub.is_some() {
        child.start_kill().ok();
    }
    let status = child.wait().await.ok();
    let said = said_so_far(&mut reading, &said).await;
    Err(Failure {
        status,
        said,
        not_hub,
    })
}

/// Makes sure this machine can reach the hub at `dest` with its own key: creating the key
/// if need be, and adding it to `~/.ssh/authorized_keys` there, through the user's own
/// ssh, which may ask for a password, if it doesn't work yet.
pub async fn prepare(dest: &str) -> anyhow::Result<()> {
    let key = key_path()?;
    if key.exists() {
        match probe(dest, &key).await {
            Ok(()) => return Ok(()),
            Err(failure) if failure.refused() => {}
            Err(failure) => anyhow::bail!(failure.describe(dest)),
        }
    } else {
        create_key(&key)?;
        println!("Created an ssh key for musubi: {}", key.display());
    }
    authorize(dest, &key).await?;
    probe(dest, &key)
        .await
        .map_err(|failure| anyhow::anyhow!(failure.describe(dest)))
}

fn create_key(key: &Path) -> anyhow::Result<()> {
    if let Some(dir) = key.parent() {
        fs::create_dir_all(dir)?;
    }
    let host = whoami::hostname().unwrap_or_else(|_| "localhost".to_owned());
    let output = std::process::Command::new("ssh-keygen")
        .args([
            "-q",
            "-t",
            "ed25519",
            "-N",
            "",
            "-C",
            &format!("musubi@{host}"),
            "-f",
        ])
        .arg(key)
        .stdin(Stdio::null())
        .output()
        .context("running ssh-keygen")?;
    anyhow::ensure!(
        output.status.success(),
        "ssh-keygen failed: {}",
        String::from_utf8_lossy(&output.stderr).trim()
    );
    Ok(())
}

/// Appends the key to `~/.ssh/authorized_keys` on `dest`, unless it is there already. The
/// script runs in `sh`, whatever the user's shell is there.
const AUTHORIZE: &str = "sh -c 'umask 077; mkdir -p ~/.ssh; read -r line; \
     grep -qxF \"$line\" ~/.ssh/authorized_keys 2>/dev/null || \
     printf \"%s\\n\" \"$line\" >> ~/.ssh/authorized_keys'";

async fn authorize(dest: &str, key: &Path) -> anyhow::Result<()> {
    let public = key.with_extension("pub");
    let public = fs::read_to_string(&public).with_context(|| format!("reading {public:?}"))?;
    let line = format!("restrict,command=\"{REMOTE_COMMAND}\" {}\n", public.trim());
    println!(
        "Adding it to ~/.ssh/authorized_keys on {dest}, allowed only to run `{REMOTE_COMMAND}`. \
         ssh may ask for your password."
    );
    let mut child = Command::new(program())
        .args(["--", dest, AUTHORIZE])
        .stdin(Stdio::piped())
        .spawn()
        .context("running ssh")?;
    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(line.as_bytes()).await?;
    }
    let status = child.wait().await?;
    anyhow::ensure!(
        status.success(),
        "could not add musubi's key on {dest} (ssh exited with {status})"
    );
    Ok(())
}
