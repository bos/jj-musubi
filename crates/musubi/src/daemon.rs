//! The node daemon: one per user, serving every repository in config.toml, each on a
//! thread of its own that syncs whenever its op heads change, a head announcement
//! arrives, the poll timer fires, or a command asks. Commands reach it over the control
//! socket (see [`crate::control`]); `add` starts serving a newly joined repository without
//! a restart.

use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Duration;
use std::time::SystemTime;

use anyhow::Context as _;
use futures::StreamExt as _;
use interprocess::local_socket::traits::tokio::Listener as _;
use jj_lib::object_id::ObjectId as _;
use musubi_sync::driver::NodeDriver;
use musubi_sync::remote::RemoteHub;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HeadNotice;
use serde::Deserialize;
use serde::Serialize;
use tarpc::server::Channel as _;
use tokio::sync::mpsc;
use tokio::sync::oneshot;
use tokio::sync::watch;

use crate::config;
use crate::config::HiveConfig;
use crate::config::UserConfig;
use crate::control;
use crate::control::Control;
use crate::control::ControlClient;
use crate::control::RepoStatus;
use crate::control::Synced;
use crate::login;
use crate::repo::Located;
use crate::socket::Socket;
use crate::watch::OpHeadsWatcher;

const POLL_INTERVAL: Duration = Duration::from_secs(30);
const REQUEST_TIMEOUT: Duration = Duration::from_secs(30);
const MAX_BACKOFF: Duration = Duration::from_secs(60);

/// A repository's replication state, written by the daemon after every sync attempt.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Status {
    pub last_attempt: Option<u64>,
    pub last_success: Option<u64>,
    pub known_seq: Option<u64>,
    pub known_head: Option<String>,
    pub error: Option<String>,
}

impl Status {
    pub fn path(repo_path: &Path) -> PathBuf {
        repo_path.join("musubi/status.json")
    }

    pub fn load(repo_path: &Path) -> Option<Self> {
        serde_json::from_slice(&fs::read(Self::path(repo_path)).ok()?).ok()
    }

    fn save(&self, repo_path: &Path) {
        if let Ok(json) = serde_json::to_vec_pretty(self) {
            fs::write(Self::path(repo_path), json).ok();
        }
    }
}

pub fn now() -> u64 {
    SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

enum Command {
    /// Sync now, and say how it went.
    Sync(oneshot::Sender<Result<Synced, String>>),
}

struct Served {
    commands: mpsc::UnboundedSender<Command>,
    /// Set to stop serving, abandoning whatever is in progress: a sync stopped partway is
    /// a crash the protocol recovers from.
    stop: watch::Sender<bool>,
    status: Arc<Mutex<Status>>,
    thread: std::thread::JoinHandle<()>,
}

/// The repositories being served.
#[derive(Default)]
struct Supervisor {
    repos: Mutex<HashMap<PathBuf, Served>>,
}

impl Supervisor {
    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<PathBuf, Served>> {
        self.repos.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Starts serving `workspace`, unless it already is.
    fn start(&self, workspace: PathBuf) {
        let mut repos = self.lock();
        if repos.contains_key(&workspace) {
            return;
        }
        let (commands, receiver) = mpsc::unbounded_channel();
        let (stop, stopped) = watch::channel(false);
        let initial = Located::find(&workspace)
            .ok()
            .and_then(|located| Status::load(&located.repo_path))
            .unwrap_or_default();
        let status = Arc::new(Mutex::new(initial));
        let thread = {
            let (workspace, status) = (workspace.clone(), status.clone());
            std::thread::Builder::new()
                .name(format!("serve {}", workspace.display()))
                .spawn(move || serve(&workspace, receiver, stopped, &status))
                .expect("spawning a thread")
        };
        repos.insert(
            workspace,
            Served {
                commands,
                stop,
                status,
                thread,
            },
        );
    }

    async fn sync(&self, workspace: &Path) -> Result<Synced, String> {
        let (reply, result) = oneshot::channel();
        let sent = self
            .lock()
            .get(workspace)
            .map(|served| served.commands.send(Command::Sync(reply)).is_ok());
        match sent {
            None => Err(format!("the daemon does not serve {}", workspace.display())),
            Some(false) => Err(format!(
                "the daemon stopped serving {}",
                workspace.display()
            )),
            Some(true) => result
                .await
                .unwrap_or_else(|_| Err("the repository's thread stopped".to_owned())),
        }
    }

    /// Stops serving `workspace`, waiting for its thread to finish.
    async fn remove(&self, workspace: &Path) -> bool {
        let Some(served) = self.lock().remove(workspace) else {
            return false;
        };
        served.stop.send(true).ok();
        tokio::task::spawn_blocking(move || served.thread.join().ok())
            .await
            .ok();
        true
    }

    async fn stop_all(&self) {
        let workspaces: Vec<PathBuf> = self.lock().keys().cloned().collect();
        for workspace in workspaces {
            self.remove(&workspace).await;
        }
    }

    fn statuses(&self) -> Vec<RepoStatus> {
        let mut statuses: Vec<RepoStatus> = self
            .lock()
            .iter()
            .map(|(workspace, served)| RepoStatus {
                workspace: workspace.clone(),
                status: served
                    .status
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .clone(),
            })
            .collect();
        statuses.sort_by(|a, b| a.workspace.cmp(&b.workspace));
        statuses
    }
}

#[derive(Clone)]
struct Daemon {
    supervisor: Arc<Supervisor>,
    stop: Arc<tokio::sync::Notify>,
}

impl Control for Daemon {
    async fn version(self, _: tarpc::context::Context) -> String {
        control::VERSION.to_owned()
    }

    async fn add(self, _: tarpc::context::Context, workspace: PathBuf) -> Result<Synced, String> {
        tracing::info!("serving {} from now on", workspace.display());
        self.supervisor.start(workspace.clone());
        self.supervisor.sync(&workspace).await
    }

    async fn remove(self, _: tarpc::context::Context, workspace: PathBuf) -> Result<(), String> {
        if self.supervisor.remove(&workspace).await {
            tracing::info!("stopped serving {}", workspace.display());
        }
        Ok(())
    }

    async fn sync(self, _: tarpc::context::Context, workspace: PathBuf) -> Result<Synced, String> {
        self.supervisor.sync(&workspace).await
    }

    async fn status(self, _: tarpc::context::Context) -> Vec<RepoStatus> {
        self.supervisor.statuses()
    }

    async fn stop(self, _: tarpc::context::Context) {
        tracing::info!("asked to stop");
        self.stop.notify_one();
    }
}

/// Runs the daemon until it is stopped or interrupted.
pub fn run(socket: &Socket) -> anyhow::Result<()> {
    let lock_path = socket.lock_path()?;
    if let Some(dir) = lock_path.parent() {
        fs::create_dir_all(dir)?;
    }
    let lock = fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(&lock_path)
        .with_context(|| format!("opening {lock_path:?}"))?;
    if let Err(err) = lock.try_lock() {
        match err {
            fs::TryLockError::WouldBlock => {
                anyhow::bail!("a musubi daemon is already running (its socket is {socket})")
            }
            fs::TryLockError::Error(err) => {
                return Err(err).with_context(|| format!("locking {lock_path:?}"));
            }
        }
    }
    // Beside the lock, for finding the daemon's process.
    let pid_path = lock_path.with_extension("pid");
    fs::write(&pid_path, std::process::id().to_string())?;
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    let result = runtime.block_on(listen(socket, &lock_path));
    if let Socket::Path(path) = socket {
        fs::remove_file(path).ok();
    }
    fs::remove_file(&pid_path).ok();
    drop(lock);
    result
}

async fn listen(socket: &Socket, lock_path: &Path) -> anyhow::Result<()> {
    let listener = socket.listen()?;
    let daemon = Daemon {
        supervisor: Arc::new(Supervisor::default()),
        stop: Arc::new(tokio::sync::Notify::new()),
    };
    for workspace in UserConfig::load()?.repos {
        daemon.supervisor.start(workspace);
    }
    tracing::info!("listening on {socket}");
    // A daemon whose lock file was deleted, as by cleaning up its directory, has nothing to
    // stop a second one starting, and no business running on.
    let mut check = tokio::time::interval(Duration::from_secs(5));
    loop {
        tokio::select! {
            connection = listener.accept() => match connection {
                Ok(stream) => {
                    let channel = tarpc::server::BaseChannel::with_defaults(
                        control::transport(stream),
                    );
                    let serve = channel.execute(daemon.clone().serve()).for_each(|request| async {
                        tokio::spawn(request);
                    });
                    tokio::spawn(serve);
                }
                Err(err) => tracing::warn!("accepting a connection: {err}"),
            },
            () = daemon.stop.notified() => break,
            () = crate::hub::interrupted() => break,
            _ = check.tick() => if !lock_path.exists() {
                tracing::warn!("{} is gone; stopping", lock_path.display());
                break;
            },
        }
    }
    daemon.supervisor.stop_all().await;
    tracing::info!("stopped");
    Ok(())
}

/// Serves one repository until told to stop: a single-threaded runtime, since jj-lib's
/// repository handles are used from one thread.
fn serve(
    workspace: &Path,
    commands: mpsc::UnboundedReceiver<Command>,
    stop: watch::Receiver<bool>,
    status: &Mutex<Status>,
) {
    // Everything this thread logs is about this workspace. At error level, the span stays
    // on under any filter that shows anything.
    let _span = tracing::error_span!("sync", repo = %workspace.display()).entered();
    let runtime = match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(err) => {
            tracing::error!("{err}");
            return;
        }
    };
    runtime.block_on(async {
        let mut stop = stop;
        tokio::select! {
            () = serve_retrying(workspace, commands, status) => {}
            () = stopped(&mut stop) => {}
        }
    });
}

/// Waits until told to stop, or until nothing can tell it anything any more.
async fn stopped(stop: &mut watch::Receiver<bool>) {
    stop.wait_for(|stop| *stop).await.ok();
}

/// Serves a repository, starting over after anything goes wrong, such as the hub being
/// out of reach or the repository's git store moving: it may be servable soon.
async fn serve_retrying(
    workspace: &Path,
    mut commands: mpsc::UnboundedReceiver<Command>,
    status: &Mutex<Status>,
) {
    let mut waiting = vec![];
    let mut backoff = Duration::from_secs(1);
    loop {
        let started = now();
        match serve_async(workspace, &mut commands, status, &mut waiting).await {
            Ok(()) => return,
            Err(err) => {
                let message = format!("{err:#}");
                tracing::error!("{message}; retrying in {backoff:?}");
                record(workspace, status, |status| {
                    status.last_attempt = Some(now());
                    status.error = Some(message.clone());
                });
                for waiter in waiting.drain(..) {
                    waiter.send(Err(message.clone())).ok();
                }
            }
        }
        let succeeded = status
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .last_success
            .is_some_and(|t| t >= started);
        if succeeded {
            backoff = Duration::from_secs(1);
        }
        if pause(backoff, &mut commands, &mut waiting).await {
            return;
        }
        backoff = (backoff * 2).min(MAX_BACKOFF);
    }
}

/// Waits `delay`, answering commands meanwhile. Returns whether nothing can send commands
/// any more; a sync request ends the wait early.
async fn pause(
    delay: Duration,
    commands: &mut mpsc::UnboundedReceiver<Command>,
    waiting: &mut Vec<oneshot::Sender<Result<Synced, String>>>,
) -> bool {
    let sleep = tokio::time::sleep(delay);
    tokio::pin!(sleep);
    tokio::select! {
        () = &mut sleep => false,
        command = commands.recv() => match command {
            None => true,
            Some(Command::Sync(reply)) => {
                waiting.push(reply);
                false
            }
        },
    }
}

fn record(workspace: &Path, status: &Mutex<Status>, change: impl FnOnce(&mut Status)) {
    let mut status = status.lock().unwrap_or_else(PoisonError::into_inner);
    change(&mut status);
    if let Ok(located) = Located::find(workspace) {
        status.save(&located.repo_path);
    }
}

async fn serve_async(
    workspace: &Path,
    commands: &mut mpsc::UnboundedReceiver<Command>,
    status: &Mutex<Status>,
    waiting: &mut Vec<oneshot::Sender<Result<Synced, String>>>,
) -> anyhow::Result<()> {
    let located = Located::find(workspace)?;
    let hive = HiveConfig::load(&located.repo_path)?
        .with_context(|| format!("{} is not part of a hive", workspace.display()))?;
    let connection = crate::hub::connect(&hive.hub, REQUEST_TIMEOUT).await?;
    let transport = connection.transport.clone();
    let mut notices = transport.subscribe(&hive.head_subject()).await?;
    let mut reconnections = transport.reconnections();
    let mut watcher = OpHeadsWatcher::new(&located.repo_path)?;
    let blobs = located.repo_path.join("musubi/blobs");
    let remote = RemoteHub::new(transport, hive.rpc_subject(), &blobs, REQUEST_TIMEOUT)?;
    let mut driver = NodeDriver::new(located.open()?, remote)?;
    let mut poll = tokio::time::interval(POLL_INTERVAL);
    let mut backoff = Duration::from_millis(500);
    let mut retry = false;
    tracing::info!("serving in hive {}", hive.display_name());
    loop {
        // After a failure, try again once the backoff has passed, rather than waiting for
        // something to change; and sync at once when asked.
        let trigger = if retry {
            "a retry".to_owned()
        } else if !waiting.is_empty() {
            "a request".to_owned()
        } else {
            tokio::select! {
                _ = poll.tick() => "the poll interval".to_owned(),
                () = watcher.changed() => "a local operation".to_owned(),
                // Announcements made while it was disconnected, as while the machine
                // slept, are lost.
                () = reconnections.next() => "reconnecting to the hub".to_owned(),
                notice = notices.next() => {
                    let Some(notice) = notice else { anyhow::bail!("lost the head subscription") };
                    match Envelope::<HeadNotice>::decode(&notice.payload) {
                        Ok(notice) => {
                            let seq = notice.seq;
                            driver.notice(notice)?;
                            format!("the hub announcing {seq}")
                        }
                        Err(err) => {
                            tracing::warn!("ignoring announcement: {err:#}");
                            "an unreadable announcement".to_owned()
                        }
                    }
                }
                command = commands.recv() => match command {
                    None => return Ok(()),
                    Some(Command::Sync(reply)) => {
                        waiting.push(reply);
                        "a request".to_owned()
                    }
                },
            }
        };
        tracing::debug!("syncing after {trigger}");
        let started = std::time::Instant::now();
        // Reconnecting during the sync, which may miss announcements, calls for another.
        reconnections.seen();
        let result = driver.sync().await;
        tracing::debug!("sync took {:?}", started.elapsed());
        let (seq, head) = driver.known();
        let synced = Synced {
            seq: *seq,
            head: head.hex(),
        };
        // Over ssh, why the hub is out of reach says more than a timeout.
        let result = result.map_err(|err| connection.explain(err));
        let reply = match &result {
            Ok(_) => Ok(synced.clone()),
            Err(err) => Err(format!("{err:#}")),
        };
        record(workspace, status, |status| {
            status.last_attempt = Some(now());
            match &result {
                Ok(_) => {
                    status.last_success = Some(now());
                    status.error = None;
                }
                Err(err) => status.error = Some(format!("{err:#}")),
            }
            status.known_seq = Some(synced.seq);
            status.known_head = Some(synced.head.clone());
        });
        for waiter in waiting.drain(..) {
            waiter.send(reply.clone()).ok();
        }
        match result {
            Ok(_) => {
                backoff = Duration::from_millis(500);
                retry = false;
            }
            Err(err) => {
                tracing::warn!("{err:#}");
                // Lost replies are indistinguishable from lost requests, and the open
                // repository's cached state may be what failed: start over, reopened.
                if let Err(err) = located.open().and_then(|repo| driver.reopen(repo)) {
                    tracing::warn!("cannot reopen: {err:#}");
                    driver.restart();
                }
                retry = true;
                if pause(backoff, commands, waiting).await {
                    return Ok(());
                }
                backoff = (backoff * 2).min(MAX_BACKOFF);
            }
        }
    }
}

/// A running daemon that speaks this build's control protocol, if there is one.
pub async fn running(socket: &Socket) -> anyhow::Result<Option<ControlClient>> {
    let Some(client) = socket.connect().await? else {
        return Ok(None);
    };
    let version = client
        .version(control::context(Duration::from_secs(10)))
        .await
        .context("asking the daemon its version")?;
    anyhow::ensure!(
        version == control::VERSION,
        "the running daemon is musubi {version}, but this is {}; restart it with `musubi \
         daemon restart`",
        control::VERSION
    );
    Ok(Some(client))
}

/// The running daemon, starting one in the background if there is none.
pub async fn ensure(socket: &Socket) -> anyhow::Result<ControlClient> {
    if let Some(client) = running(socket).await? {
        return Ok(client);
    }
    // Where a service manager runs the daemon, it starts it, so that there is only one.
    let (mut child, log) = if login::managed() {
        login::start()?;
        (None, login::log_hint())
    } else {
        let (child, log) = spawn(socket)?;
        (Some(child), log.display().to_string())
    };
    let deadline = std::time::Instant::now() + Duration::from_secs(20);
    // A child that exits may have lost a race with another command's daemon, which is as
    // good: keep looking for one until the deadline.
    let mut exited = None;
    loop {
        if let Some(client) = running(socket).await? {
            return Ok(client);
        }
        if exited.is_none()
            && let Some(child) = &mut child
        {
            exited = child.try_wait()?;
        }
        if std::time::Instant::now() >= deadline {
            let Some(status) = exited else {
                anyhow::bail!("the daemon did not start listening on {socket}; see {log}");
            };
            let tail = fs::read_to_string(&log).unwrap_or_default();
            let tail: Vec<&str> = tail.lines().rev().take(5).collect();
            let tail: Vec<&str> = tail.into_iter().rev().collect();
            anyhow::bail!(
                "the daemon exited ({status}) before it was ready; from {log}:\n{}",
                tail.join("\n")
            );
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
}

/// Starts `musubi daemon` in the background, detached from this terminal, logging to the
/// state directory.
fn spawn(socket: &Socket) -> anyhow::Result<(std::process::Child, PathBuf)> {
    let dir = config::state_dir()?;
    fs::create_dir_all(&dir)?;
    let log = dir.join("daemon.log");
    // A log that has grown large starts over.
    if fs::metadata(&log).is_ok_and(|m| m.len() > 10 << 20) {
        fs::remove_file(&log).ok();
    }
    let file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&log)
        .with_context(|| format!("opening {log:?}"))?;
    let mut command = std::process::Command::new(std::env::current_exe()?);
    command
        .args(["daemon", "--socket", &socket.to_string()])
        .stdin(std::process::Stdio::null())
        .stdout(file.try_clone()?)
        .stderr(file);
    detach(&mut command);
    let child = command.spawn().context("starting the daemon")?;
    Ok((child, log))
}

#[cfg(unix)]
fn detach(command: &mut std::process::Command) {
    use std::os::unix::process::CommandExt as _;
    // Its own process group, so that ^C in this terminal doesn't reach it.
    command.process_group(0);
}

#[cfg(windows)]
fn detach(command: &mut std::process::Command) {
    use std::os::windows::process::CommandExt as _;
    const DETACHED_PROCESS: u32 = 0x0000_0008;
    const CREATE_NEW_PROCESS_GROUP: u32 = 0x0000_0200;
    command.creation_flags(DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP);
}

/// Stops the running daemon, if any, and waits for it to go. Returns whether one was
/// running.
pub async fn stop(socket: &Socket) -> anyhow::Result<bool> {
    let Some(client) = socket.connect().await? else {
        return Ok(false);
    };
    // The daemon may be gone before its reply arrives.
    client
        .stop(control::context(Duration::from_secs(10)))
        .await
        .ok();
    let deadline = std::time::Instant::now() + Duration::from_secs(30);
    // Gone once it has let go of its lock, which it does after closing its socket.
    while socket.connect().await?.is_some() || socket.is_locked()? {
        anyhow::ensure!(
            std::time::Instant::now() < deadline,
            "the daemon on {socket} did not stop"
        );
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    Ok(true)
}
