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
use std::io::Write as _;
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
use tokio::time::Instant;

use crate::config;
use crate::ui::Ui;

/// What the machine's key may run on the hub's machine.
const REMOTE_COMMAND: &str = "musubi hub connect";

/// How long a failing ssh waits before the next try, at most.
const MAX_BACKOFF: Duration = Duration::from_secs(60);

/// How often to look for the machine having slept.
const WAKE_CHECK: Duration = Duration::from_secs(5);

/// How much of what ssh says on stderr to keep: the end says why it failed.
const MAX_SAID: usize = 16 * 1024;

/// How long to wait for ssh to say why a connection let go before the hub greeted didn't
/// connect: a supervisor gives ssh a second to finish, and what it says a second more.
const SAYING: Duration = Duration::from_secs(3);

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
///
/// It is ssh that tells a dead link, which fails every request in flight on it at once: ssh
/// ends a connection that hears nothing from the hub's machine for (`ServerAliveCountMax` + 1)
/// `ServerAliveInterval`s, a minute, probing it every ten seconds, often enough to keep a NAT's
/// mapping. While a node uploads, the hub answers nothing until a chunk has all come, and ssh's
/// probes wait behind the chunks queued on the link, so what keeps the connection is the hub
/// machine's sshd saying how much more it may send, about every 100 KB it takes in. Ending a
/// connection after 30 seconds of that silence, as ssh did with a `ServerAliveCountMax` of 2, cut
/// short uploads that still moved on links under about 40 kbit/s; a minute leaves room for the
/// slowest link a request's deadline lets carry a chunk (`musubi_sync::remote::REQUEST_TIMEOUT`),
/// even when what else shares it takes most of it for a while.
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
            "ServerAliveCountMax=5",
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
        Some(127) => format!("`musubi` is not on the PATH of non-interactive shells on {dest}"),
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
    /// The latest connection, while how it went may not be known.
    latest: Option<Attempt>,
}

/// A connection, and whether its supervisor is done with it.
#[derive(Clone)]
struct Attempt {
    /// See [`Ssh::settled`].
    settled: Arc<AtomicBool>,
    /// Closed once its supervisor is done, having recorded any failure.
    supervised: watch::Receiver<()>,
}

impl State {
    fn failed(&mut self, problem: String) {
        self.failures += 1;
        let backoff = Duration::from_secs(1) * 2u32.saturating_pow(self.failures - 1);
        self.retry_at = Some(Instant::now() + backoff.min(MAX_BACKOFF));
        tracing::warn!("{problem}");
        self.problem = Some(problem);
    }
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

    /// [`Health::problem`], once ssh has said why the latest connection didn't connect, if it
    /// was let go before the hub greeted through it, as when the hub didn't greet in time: its
    /// supervisor says so only once ssh has finished, while what failed reports at once.
    pub async fn problem_once_known(&self) -> Option<String> {
        let latest = self.lock().latest.clone();
        if let Some(Attempt {
            settled,
            mut supervised,
        }) = latest
            && !settled.load(Ordering::Relaxed)
        {
            // Until the supervisor drops its sender, or the hub greets after all.
            let known = async {
                loop {
                    tokio::select! {
                        _ = supervised.changed() => return,
                        () = tokio::time::sleep(Duration::from_millis(50)) => {
                            if settled.load(Ordering::Relaxed) {
                                return;
                            }
                        }
                    }
                }
            };
            tokio::time::timeout(SAYING, known).await.ok();
        }
        self.problem()
    }

    /// Records a connection as the latest, `settled` once how it went is known; returns what
    /// its supervisor holds until it's done.
    fn attempt(&self, settled: &Arc<AtomicBool>) -> watch::Sender<()> {
        let (supervising, supervised) = watch::channel(());
        self.lock().latest = Some(Attempt {
            settled: settled.clone(),
            supervised,
        });
        supervising
    }

    fn failed(&self, problem: String) {
        self.lock().failed(problem);
    }

    fn failed_unless_woke(&self, problem: String, woke: &watch::Receiver<u64>) {
        let mut state = self.lock();
        if !woke.has_changed().unwrap_or(true) {
            state.failed(problem);
        }
    }

    fn woke(&self, woke: &watch::Sender<u64>) {
        // Publish the wake and clear failures under the same lock that records failures:
        // an old supervisor must not restore its error after this reset on another thread.
        let mut state = self.lock();
        *state = State::default();
        woke.send_modify(|n| *n += 1);
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

    async fn connect_using(&self, mut command: Command) -> io::Result<(Reader, Writer)> {
        // After failures, trying again at once would run ssh, and maybe a login prompt in a
        // browser, every few seconds.
        if self.health.refusing() {
            return Err(io::Error::other("waiting to try ssh again"));
        }
        let mut child = command
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
            _supervising: self.health.attempt(&settled),
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
}

#[async_trait]
impl Connector for Link {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        self.connect_using(connect_command(&self.dest, &self.key))
            .await
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
    let (mut wall, mut clock) = (SystemTime::now(), std::time::Instant::now());
    loop {
        check.tick().await;
        // `Instant` stops while the machine sleeps; the wall clock doesn't.
        let (now_wall, now_clock) = (SystemTime::now(), std::time::Instant::now());
        let slept = now_wall
            .duration_since(wall)
            .unwrap_or_default()
            .saturating_sub(now_clock - clock);
        if slept > 2 * WAKE_CHECK {
            tracing::info!(
                "woke after about {}s asleep; reconnecting to {dest}",
                slept.as_secs()
            );
            health.woke(&woke);
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
    /// Dropped once the supervisor is done ([`Health::problem_once_known`]).
    _supervising: watch::Sender<()>,
}

/// Waits for a connection's ssh to finish, ending it once the connection is let go, or at
/// once when the machine wakes; and if the hub never greeted, and the transport didn't say
/// why, records what ssh says.
async fn supervise(mut ssh: Ssh) {
    let said = Arc::new(Mutex::new(vec![]));
    let mut reading = tokio::spawn(read_stderr(ssh.stderr, said.clone()));
    let connected_before_wake = ssh.woke.clone();
    tokio::select! {
        biased;
        _ = ssh.woke.changed() => {
            ssh.child.start_kill().ok();
            ssh.child.wait().await.ok();
        }
        () = async {
            let status = tokio::select! {
                status = ssh.child.wait() => status.ok(),
                _ = ssh.let_go => {
                    // stdin closed with the connection. Give ssh a moment to finish,
                    // then kill and reap one that stays alive after EOF.
                    match tokio::time::timeout(Duration::from_secs(1), ssh.child.wait()).await {
                        Ok(status) => status.ok(),
                        Err(_) => {
                            ssh.child.start_kill().ok();
                            ssh.child.wait().await.ok();
                            None
                        }
                    }
                }
            };
            if !ssh.settled.load(Ordering::Relaxed) {
                let said = said_so_far(&mut reading, &said).await;
                // A greeting or wake can arrive while stderr drains. The wake stays
                // selectable throughout cleanup; its health reset also excludes a stale
                // failure racing with it on another runtime thread.
                if !ssh.settled.load(Ordering::Relaxed) {
                    ssh.health.failed_unless_woke(
                        describe_failure(&ssh.dest, status, &said),
                        &connected_before_wake,
                    );
                }
            }
        } => {}
    }
    reading.abort();
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
pub async fn prepare(ui: &Ui, dest: &str) -> anyhow::Result<()> {
    let key = key_path()?;
    if ensure_key(&key)? {
        writeln!(
            ui.stdout(),
            "Created an ssh key for musubi: {}",
            key.display()
        )?;
    } else {
        match probe(dest, &key).await {
            Ok(()) => return Ok(()),
            Err(failure) if failure.refused() => {}
            Err(failure) => anyhow::bail!(failure.describe(dest)),
        }
    }
    authorize(ui, dest, &key).await?;
    probe(dest, &key)
        .await
        .map_err(|failure| anyhow::anyhow!(failure.describe(dest)))
}

/// Waits for another first join to finish both key files before probing or authorizing.
/// Returns whether this call published a new pair.
fn ensure_key(key: &Path) -> anyhow::Result<bool> {
    let _lock = crate::lock::lock(&key.with_extension("lock"))?;
    if key.exists() {
        let public = key.with_extension("pub");
        if !fs::metadata(&public).is_ok_and(|metadata| metadata.len() > 0) {
            // ssh-keygen saves the private key first. A failed public-file write must not
            // rotate that identity or leave every later authorization unable to read it.
            let output = std::process::Command::new("ssh-keygen")
                .args(["-y", "-P", "", "-f"])
                .arg(key)
                .stdin(Stdio::null())
                .output()
                .context("deriving the missing public SSH key")?;
            anyhow::ensure!(
                output.status.success(),
                "ssh-keygen could not derive the missing public key: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            );
            let derived = String::from_utf8(output.stdout)?;
            let host = whoami::hostname().unwrap_or_else(|_| "localhost".to_owned());
            let contents = format!("{} musubi@{host}\n", derived.trim());
            musubi_jj::files::replace(&public, contents.as_bytes())?;
        }
        return Ok(false);
    }
    let mut temporary = tempfile::Builder::new();
    temporary.prefix("hub-key-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        temporary.permissions(fs::Permissions::from_mode(0o700));
    }
    let temporary = temporary.tempdir_in(key.parent().context("SSH key path has no parent")?)?;
    let temporary_key = temporary.path().join("key");
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
        .arg(&temporary_key)
        .stdin(Stdio::null())
        .output()
        .context("running ssh-keygen")?;
    anyhow::ensure!(
        output.status.success(),
        "ssh-keygen failed: {}",
        String::from_utf8_lossy(&output.stderr).trim()
    );
    // The private filename is the publication point: whenever it exists, its public
    // half is ready. A failed keygen or public write leaves no published identity.
    let public = fs::read(temporary_key.with_extension("pub"))?;
    let public_path = key.with_extension("pub");
    musubi_jj::files::replace(&public_path, &public).map_err(|err| {
        anyhow::anyhow!(
            "could not save musubi's public SSH key {}: {err}",
            public_path.display()
        )
    })?;
    tempfile::TempPath::try_from_path(temporary_key)?
        .persist_noclobber(key)
        .map_err(|err| {
            anyhow::anyhow!(
                "could not save musubi's private SSH key {}: {}",
                key.display(),
                err.error
            )
        })?;
    Ok(true)
}

/// Appends the key to `~/.ssh/authorized_keys` on `dest`, unless it is there already. The
/// script runs in `sh`, whatever the user's shell is there. A file that doesn't end in a
/// newline, as some tools that provision machines write it, gets one first: appended to its
/// last line, the key would spoil that line's key as well as its own.
const AUTHORIZE: &str = "sh -c 'umask 077; mkdir -p ~/.ssh; read -r line; \
     f=~/.ssh/authorized_keys; grep -qxF \"$line\" \"$f\" 2>/dev/null && exit; \
     [ -s \"$f\" ] && [ -n \"$(tail -c 1 \"$f\")\" ] && echo >> \"$f\"; \
     printf \"%s\\n\" \"$line\" >> \"$f\"'";

async fn authorize(ui: &Ui, dest: &str, key: &Path) -> anyhow::Result<()> {
    let public = key.with_extension("pub");
    let public = fs::read_to_string(&public).with_context(|| format!("reading {public:?}"))?;
    let line = format!("restrict,command=\"{REMOTE_COMMAND}\" {}\n", public.trim());
    writeln!(
        ui.stdout(),
        "Adding it to ~/.ssh/authorized_keys on {dest}, allowed only to run `{REMOTE_COMMAND}`. \
         ssh may ask for your password."
    )?;
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

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    /// A failed public-file publication leaves no private identity that could block a
    /// retry. Existing keys survive public-file repair, and stale public files are replaced.
    #[test]
    fn key_setup_retries_after_the_public_file_could_not_be_written() {
        use std::os::unix::fs::PermissionsExt as _;

        let mut previous_public = String::new();
        for failure in 0..3 {
            let dir = musubi_testutil::tempdir();
            let key = dir.path().join("hub_key");
            let public = key.with_extension("pub");
            if failure == 0 {
                fs::create_dir(&public).unwrap();
                assert!(ensure_key(&key).is_err());
                assert!(!key.exists(), "a failed setup published a private key");
                fs::remove_dir(&public).unwrap();
            } else {
                fs::write(&public, if failure == 1 { "" } else { &previous_public }).unwrap();
                fs::set_permissions(&public, fs::Permissions::from_mode(0o400)).unwrap();
            }
            assert!(
                ensure_key(&key).unwrap(),
                "retry must publish a complete pair"
            );
            let private = fs::read(&key).unwrap();
            let derived = std::process::Command::new("ssh-keygen")
                .args(["-y", "-f"])
                .arg(&key)
                .output()
                .unwrap();
            assert!(derived.status.success());
            let derived = String::from_utf8(derived.stdout).unwrap();
            let published = fs::read_to_string(&public).unwrap();
            assert_eq!(
                published.split_whitespace().take(2).collect::<Vec<_>>(),
                derived.split_whitespace().take(2).collect::<Vec<_>>()
            );
            fs::remove_file(&public).unwrap();
            assert!(
                !ensure_key(&key).unwrap(),
                "public-file repair rotated the key"
            );
            assert!(
                fs::read(&key).unwrap() == private,
                "the private key changed"
            );
            let public = fs::read_to_string(public).unwrap();
            assert_eq!(
                public.split_whitespace().take(2).collect::<Vec<_>>(),
                derived.split_whitespace().take(2).collect::<Vec<_>>()
            );
            previous_public = public;
        }
    }

    /// Two first joins on one machine can both find no key before either creates it.
    /// They must reuse one complete key pair rather than overwrite it or fail a join.
    #[test]
    fn concurrent_first_joins_share_one_key() {
        let dir = musubi_testutil::tempdir();
        let key = dir.path().join("hub_key");
        let start = std::sync::Barrier::new(2);
        let created = std::thread::scope(|scope| {
            let joins: Vec<_> = (0..2)
                .map(|_| {
                    scope.spawn(|| {
                        assert!(!key.exists());
                        start.wait();
                        ensure_key(&key)
                    })
                })
                .collect();
            joins
                .into_iter()
                .map(|join| join.join().unwrap().unwrap())
                .collect::<Vec<_>>()
        });
        assert_eq!(created.into_iter().filter(|created| *created).count(), 1);
        let derived = std::process::Command::new("ssh-keygen")
            .args(["-y", "-f"])
            .arg(&key)
            .output()
            .unwrap();
        assert!(derived.status.success());
        let public = fs::read_to_string(key.with_extension("pub")).unwrap();
        let derived = String::from_utf8(derived.stdout).unwrap();
        assert_eq!(
            public.split_whitespace().take(2).collect::<Vec<_>>(),
            derived.split_whitespace().take(2).collect::<Vec<_>>()
        );
    }

    #[test]
    fn authorizing_keeps_other_keys_on_lines_of_their_own() {
        let home = musubi_testutil::tempdir();
        let keys = home.path().join(".ssh/authorized_keys");
        // Runs the script as the hub's machine would, through a shell.
        let authorize = |line: &str| {
            let mut child = std::process::Command::new("sh")
                .args(["-c", AUTHORIZE])
                .env("HOME", home.path())
                .stdin(Stdio::piped())
                .spawn()
                .unwrap();
            child
                .stdin
                .take()
                .unwrap()
                .write_all(line.as_bytes())
                .unwrap();
            assert!(child.wait().unwrap().success());
        };
        let musubi = "restrict,command=\"musubi hub connect\" ssh-ed25519 AAAAmusubi musubi@a\n";
        authorize(musubi);
        assert_eq!(fs::read_to_string(&keys).unwrap(), musubi);

        // A file that doesn't end in a newline keeps its last key whole, and a key that is
        // there already isn't added again.
        fs::write(&keys, "ssh-ed25519 AAAA1234").unwrap();
        authorize(musubi);
        authorize(musubi);
        assert_eq!(
            fs::read_to_string(&keys).unwrap(),
            format!("ssh-ed25519 AAAA1234\n{musubi}")
        );
    }
}

#[cfg(all(test, unix))]
mod supervisor_tests;
