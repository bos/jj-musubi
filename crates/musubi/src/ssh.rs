//! Reaching a hub over ssh, for a hub whose NATS server listens only on its own machine.
//!
//! The machine gets a key of its own (`hub_key` in the state directory), which joining
//! adds to `~/.ssh/authorized_keys` on the hub's machine, allowed only to run
//! `musubi hub connect`. A [`Tunnel`] listens on this machine's loopback, and for each
//! connection the NATS client makes, runs `ssh <hub> musubi hub connect` and relays the
//! connection through it. Nothing lasts longer than a connection, so after the machine
//! sleeps, the NATS client's reconnecting is a fresh ssh.
//!
//! The ssh is the user's own `ssh` (or `$MUSUBI_SSH`), so `~/.ssh/config` applies: host
//! aliases, `ProxyCommand`, and the rest.

use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitStatus;
use std::process::Stdio;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::Instant;
use std::time::SystemTime;

use anyhow::Context as _;
use async_trait::async_trait;
use bytes::Bytes;
use musubi_transport::NatsTransport;
use musubi_transport::Subscription;
use musubi_transport::Transport;
use musubi_transport::TransportError;
use tokio::io::AsyncReadExt as _;
use tokio::io::AsyncWriteExt as _;
use tokio::net::TcpListener;
use tokio::net::TcpStream;
use tokio::process::Command;
use tokio::sync::watch;

use crate::config;

/// What the machine's key may run on the hub's machine.
const REMOTE_COMMAND: &str = "musubi hub connect";

/// How long a failing ssh waits before the next try, at most.
const MAX_BACKOFF: Duration = Duration::from_secs(60);

/// How often to look for the machine having slept.
const WAKE_CHECK: Duration = Duration::from_secs(5);

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
        Some(_) => format!("`{REMOTE_COMMAND}` on {dest} failed: {said}"),
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

/// How a tunnel's ssh connections are going.
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

/// A loopback port whose connections go to a hub over ssh, one ssh for each.
pub struct Tunnel {
    port: u16,
    health: Health,
    task: tokio::task::JoinHandle<()>,
}

impl Drop for Tunnel {
    fn drop(&mut self) {
        self.task.abort();
    }
}

impl Tunnel {
    pub async fn open(dest: &str) -> anyhow::Result<Self> {
        let listener = TcpListener::bind(("127.0.0.1", 0)).await?;
        let port = listener.local_addr()?.port();
        let health = Health::default();
        let task = tokio::spawn(serve(
            listener,
            dest.to_owned(),
            key_path()?,
            health.clone(),
        ));
        Ok(Self { port, health, task })
    }

    pub fn port(&self) -> u16 {
        self.port
    }

    pub fn health(&self) -> Health {
        self.health.clone()
    }
}

/// Accepts connections, each relayed through an ssh of its own; and after the machine
/// sleeps, ends them all, since their links are likely dead, and forgets past failures.
async fn serve(listener: TcpListener, dest: String, key: PathBuf, health: Health) {
    let (woke, _) = watch::channel(0u64);
    let mut check = tokio::time::interval(WAKE_CHECK);
    let (mut wall, mut clock) = (SystemTime::now(), Instant::now());
    loop {
        tokio::select! {
            accepted = listener.accept() => {
                let Ok((stream, _)) = accepted else {
                    // Out of file descriptors, say: don't spin.
                    tokio::time::sleep(Duration::from_millis(100)).await;
                    continue;
                };
                // After failures, the NATS client's own retries would run ssh, and maybe
                // a login prompt in a browser, every few seconds.
                if health.refusing() {
                    continue;
                }
                tokio::spawn(relay(
                    stream,
                    dest.clone(),
                    key.clone(),
                    health.clone(),
                    woke.subscribe(),
                ));
            }
            _ = check.tick() => {
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
    }
}

/// Relays `stream` through an ssh to `dest`, until either end closes or the machine wakes.
async fn relay(
    stream: TcpStream,
    dest: String,
    key: PathBuf,
    health: Health,
    mut woke: watch::Receiver<u64>,
) {
    let mut child = match connect_command(&dest, &key).spawn() {
        Ok(child) => child,
        Err(err) => {
            health.failed(format!("cannot run ssh: {err}"));
            return;
        }
    };
    let (Some(mut stdin), Some(mut stdout), Some(mut stderr)) =
        (child.stdin.take(), child.stdout.take(), child.stderr.take())
    else {
        return;
    };
    // Read as it comes, so a chatty ssh never blocks on a full pipe.
    let said = tokio::spawn(async move {
        let mut said = String::new();
        stderr.read_to_string(&mut said).await.ok();
        said
    });
    stream.set_nodelay(true).ok();
    let (mut from_client, mut to_client) = stream.into_split();
    let answered = AtomicBool::new(false);
    let up = tokio::io::copy(&mut from_client, &mut stdin);
    let down = async {
        let mut buf = vec![0; 64 * 1024];
        loop {
            let n = stdout.read(&mut buf).await?;
            if n == 0 {
                return Ok::<_, io::Error>(());
            }
            if !answered.swap(true, Ordering::Relaxed) {
                health.worked();
            }
            to_client.write_all(&buf[..n]).await?;
        }
    };
    let mut slept = false;
    tokio::select! {
        _ = up => {}
        _ = down => {}
        _ = woke.changed() => slept = true,
    }
    drop(to_client);
    drop(stdin);
    // An ssh still going is one the client gave up on, or one the machine's sleeping broke.
    let status = match tokio::time::timeout(Duration::from_secs(1), child.wait()).await {
        Ok(status) => status.ok(),
        Err(_) => {
            child.start_kill().ok();
            child.wait().await.ok();
            None
        }
    };
    if !answered.load(Ordering::Relaxed) && !slept {
        let said = said.await.unwrap_or_default();
        health.failed(describe_failure(&dest, status, &said));
    }
}

/// The NATS transport over a tunnel, which lives as long as it.
pub struct SshTransport {
    nats: NatsTransport,
    _tunnel: Tunnel,
}

impl SshTransport {
    pub fn new(nats: NatsTransport, tunnel: Tunnel) -> Self {
        Self {
            nats,
            _tunnel: tunnel,
        }
    }
}

#[async_trait]
impl Transport for SshTransport {
    fn max_payload(&self) -> usize {
        self.nats.max_payload()
    }

    async fn publish(&self, subject: &str, payload: Bytes) -> Result<(), TransportError> {
        self.nats.publish(subject, payload).await
    }

    async fn subscribe(&self, subject: &str) -> Result<Subscription, TransportError> {
        self.nats.subscribe(subject).await
    }

    async fn request(
        &self,
        subject: &str,
        payload: Bytes,
        timeout: Duration,
    ) -> Result<Bytes, TransportError> {
        self.nats.request(subject, payload, timeout).await
    }
}

/// How one try of the machine's key went.
struct Failure {
    status: Option<ExitStatus>,
    said: String,
}

/// Runs `musubi hub connect` on `dest` with the machine's key, to see whether a hub answers.
async fn probe(dest: &str, key: &Path) -> Result<(), Failure> {
    let failure = |said: String| Failure { status: None, said };
    let mut child = connect_command(dest, key)
        .spawn()
        .map_err(|err| failure(format!("cannot run ssh: {err}")))?;
    let (Some(mut stdout), Some(mut stderr)) = (child.stdout.take(), child.stderr.take()) else {
        return Err(failure(String::new()));
    };
    // A NATS server speaks first.
    let mut first = [0; 4];
    let read = tokio::time::timeout(Duration::from_secs(60), stdout.read_exact(&mut first)).await;
    if matches!(read, Ok(Ok(_))) && &first == b"INFO" {
        return Ok(());
    }
    if read.is_err() {
        child.start_kill().ok();
    }
    let status = child.wait().await.ok();
    let mut said = String::new();
    stderr.read_to_string(&mut said).await.ok();
    Err(Failure { status, said })
}

/// Makes sure this machine can reach the hub at `dest` with its own key: creating the key
/// if need be, and adding it to `~/.ssh/authorized_keys` there, through the user's own
/// ssh, which may ask for a password, if it doesn't work yet.
pub async fn prepare(dest: &str) -> anyhow::Result<()> {
    let key = key_path()?;
    if key.exists() {
        match probe(dest, &key).await {
            Ok(()) => return Ok(()),
            // Most likely the key isn't on the hub's machine yet.
            Err(failure) if failure.status.and_then(|status| status.code()) == Some(255) => {}
            Err(failure) => anyhow::bail!(describe_failure(dest, failure.status, &failure.said)),
        }
    } else {
        create_key(&key)?;
        println!("Created an ssh key for musubi: {}", key.display());
    }
    authorize(dest, &key).await?;
    probe(dest, &key)
        .await
        .map_err(|failure| anyhow::anyhow!(describe_failure(dest, failure.status, &failure.said)))
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
