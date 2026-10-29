//! The node daemon: one per user, serving every copy in state.toml, each on a thread of its
//! own that syncs whenever its op heads change, a head announcement arrives, the poll timer
//! fires, or a command asks. Commands reach it over the control socket (see
//! [`crate::control`]); `add` starts serving a newly joined copy without a restart.
//!
//! Before each sync it checks that the entry's path still holds the copy the entry names
//! ([`crate::copy`]). If not, it suspends the entry: it syncs nothing and writes nothing
//! there, and looks again, there and where jj last saw the repository, until the copy is
//! back.

use std::collections::HashMap;
use std::fs;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::Weak;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::SystemTime;

use anyhow::Context as _;
use bytes::Bytes;
use futures::FutureExt as _;
use futures::StreamExt as _;
use futures::future::BoxFuture;
use futures::future::Shared;
use jj_lib::object_id::ObjectId as _;
use musubi_hub::activity::Report;
use musubi_sync::driver::NodeDriver;
use musubi_sync::node::history_abandoned;
use musubi_sync::progress::Activity;
use musubi_sync::progress::Progress;
use musubi_sync::remote::HiveGone;
use musubi_sync::remote::OpenConnection;
use musubi_sync::remote::RemoteHub;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HUB_TOKEN;
use musubi_sync::wire::HeadNotice;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use musubi_sync::wire::rpc_subject;
use musubi_transport::stream::WhileDisconnected;
use serde::Deserialize;
use serde::Serialize;
use tarpc::server::Channel as _;
use tokio::sync::mpsc;
use tokio::sync::oneshot;
use tokio::sync::watch;

use crate::agent;
use crate::config;
use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::config::Settings;
use crate::config::UserState;
use crate::control;
use crate::control::Control;
use crate::control::ControlClient;
use crate::control::RepoStatus;
use crate::control::Synced;
use crate::copy;
use crate::hub::Connection;
use crate::login;
use crate::repo::Located;
use crate::socket::Socket;
use crate::watch::OpHeadsWatcher;

const POLL_INTERVAL: Duration = Duration::from_secs(30);
const REQUEST_TIMEOUT: Duration = Duration::from_secs(30);
/// How long a copy waits to open a connection of its own for a large transfer, before it
/// moves the transfer on the connection it shares.
const OWN_CONNECTION_TIMEOUT: Duration = Duration::from_secs(10);
const MAX_BACKOFF: Duration = Duration::from_secs(60);
const REPORT_TIMEOUT: Duration = Duration::from_secs(10);
/// How often a repository that syncs is checked for whether gc is due, which counts its
/// cruft, and on macOS starts a process to ask whether the machine is on battery.
const GC_CHECK_INTERVAL: Duration = Duration::from_secs(60 * 60);

/// A repository's replication state, written after every sync attempt, by the daemon or by
/// `musubi sync` without one.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Status {
    pub last_attempt: Option<u64>,
    pub last_success: Option<u64>,
    pub known_seq: Option<u64>,
    pub known_head: Option<String>,
    pub error: Option<String>,
    /// Whether the error is one that syncing again can't get past, as after `jj op abandon`.
    #[serde(default)]
    pub paused: bool,
}

impl Status {
    pub fn path(repo_path: &Path) -> PathBuf {
        repo_path.join("musubi/status.json")
    }

    pub fn load(repo_path: &Path) -> Option<Self> {
        serde_json::from_slice(&fs::read(Self::path(repo_path)).ok()?).ok()
    }

    /// Records a sync: its error, if it failed, and the hive's head as it left the node
    /// knowing it.
    fn synced(&mut self, error: Option<&anyhow::Error>, known: &Synced) {
        self.last_attempt = Some(now());
        if error.is_none() {
            self.last_success = self.last_attempt;
        }
        self.set_error(error);
        self.known_seq = Some(known.seq);
        self.known_head = Some(known.head.clone());
    }

    /// Records an attempt that failed before it could sync, as to reach the hub.
    fn failed(&mut self, error: &anyhow::Error) {
        self.last_attempt = Some(now());
        self.set_error(Some(error));
    }

    fn set_error(&mut self, error: Option<&anyhow::Error>) {
        self.error = error.map(|err| format!("{err:#}"));
        self.paused = error.is_some_and(history_abandoned);
    }

    /// Overwrites the status in place: it changes at every sync attempt, and ext4 writes out
    /// at once a file truncated to nothing, or renamed over another. A reader that comes
    /// while it is written may find no status.
    fn save(&self, repo_path: &Path) {
        let Ok(json) = serde_json::to_vec_pretty(self) else {
            return;
        };
        let write = || -> std::io::Result<()> {
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(false)
                .open(Self::path(repo_path))?;
            file.write_all(&json)?;
            file.set_len(json.len() as u64)
        };
        write().ok();
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
    /// What its sync is doing, for a command waiting on it.
    progress: Progress,
    thread: std::thread::JoinHandle<()>,
}

/// The daemon's connections to hubs: one to each, which every copy it serves there shares,
/// rather than one, and an ssh, a copy. Each runs on the runtime that made the registry, the
/// daemon's own, which outlives the copies', and ends once no copy holds it.
struct Hubs {
    runtime: tokio::runtime::Handle,
    hubs: Arc<Mutex<HashMap<String, HubConnection>>>,
    /// Whether a copy opens another connection for a large transfer
    /// (`musubi.daemon.connections`).
    own_connections: bool,
}

/// A hub's connection while a copy holds it, and the attempt to connect while one is under
/// way, which copies that ask meanwhile wait for rather than connecting too.
#[derive(Default)]
struct HubConnection {
    connection: Weak<Connection>,
    connecting: Option<Connecting>,
}

type Connecting = Shared<BoxFuture<'static, Result<Arc<Connection>, String>>>;

/// Records how an attempt to connect ended, however it ends, panicking included: what it
/// made, and that it is over, so that the next copy to ask connects afresh.
struct Attempted {
    hubs: Arc<Mutex<HashMap<String, HubConnection>>>,
    hub: String,
    connection: Weak<Connection>,
}

impl Attempted {
    fn made(&mut self, connection: &Arc<Connection>) {
        self.connection = Arc::downgrade(connection);
    }
}

impl Drop for Attempted {
    fn drop(&mut self) {
        let mut hubs = self.hubs.lock().unwrap_or_else(PoisonError::into_inner);
        let entry = hubs.entry(std::mem::take(&mut self.hub)).or_default();
        entry.connecting = None;
        entry.connection = std::mem::take(&mut self.connection);
    }
}

impl Hubs {
    fn new(runtime: tokio::runtime::Handle, own_connections: bool) -> Self {
        Self {
            runtime,
            hubs: Arc::default(),
            own_connections,
        }
    }

    /// Opens a connection of a copy's own to `hub`, for a large transfer, unless the daemon
    /// is to reach each hub over one. It runs on the copy's runtime, which the transfer
    /// keeps busy, and ends with the transfer.
    fn own_connections(&self, hub: &str) -> Option<OpenConnection> {
        let hub = hub.to_owned();
        self.own_connections.then(|| -> OpenConnection {
            Arc::new(move || {
                let hub = hub.clone();
                async move {
                    let next = WhileDisconnected::NextAttempt;
                    Ok(crate::hub::connect_with(&hub, OWN_CONNECTION_TIMEOUT, next)
                        .await?
                        .transport)
                }
                .boxed()
            })
        })
    }

    /// The connection to `hub`, connecting if no copy holds one. An attempt that fails
    /// fails every copy that waited for it.
    async fn connect(&self, hub: &str) -> anyhow::Result<Arc<Connection>> {
        let attempt = {
            let mut hubs = self.hubs.lock().unwrap_or_else(PoisonError::into_inner);
            let entry = hubs.entry(hub.to_owned()).or_default();
            if let Some(connection) = entry.connection.upgrade() {
                return Ok(connection);
            }
            entry
                .connecting
                .get_or_insert_with(|| self.attempt(hub))
                .clone()
        };
        attempt.await.map_err(anyhow::Error::msg)
    }

    /// Connects to `hub` on the daemon's runtime, and records the connection as it ends,
    /// for copies that ask afterwards: so that only the copies that waited hold what it
    /// made, which ends once none does.
    fn attempt(&self, hub: &str) -> Connecting {
        let mut ended = Attempted {
            hubs: self.hubs.clone(),
            hub: hub.to_owned(),
            connection: Weak::new(),
        };
        let task = self.runtime.spawn(async move {
            // A copy's sync fails once the connection is lost and connecting again fails,
            // rather than waiting out its timeouts, so that the copy says why at once and
            // waits for the hub itself.
            let next = WhileDisconnected::NextAttempt;
            let connected = crate::hub::connect_with(&ended.hub, REQUEST_TIMEOUT, next)
                .await
                .map(Arc::new)
                .map_err(|err| format!("{err:#}"));
            if let Ok(connection) = &connected {
                ended.made(connection);
            }
            connected
        });
        async move {
            task.await
                .unwrap_or_else(|err| Err(format!("connecting to the hub: {err}")))
        }
        .boxed()
        .shared()
    }
}

/// The copies being served, by machine key, and the connections to hubs they share.
struct Supervisor {
    repos: Mutex<HashMap<String, Served>>,
    hubs: Arc<Hubs>,
}

impl Supervisor {
    fn new(hubs: Hubs) -> Self {
        Self {
            repos: Mutex::default(),
            hubs: Arc::new(hubs),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<String, Served>> {
        self.repos.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Starts serving `key`'s copy, unless it already is.
    fn start(&self, key: String) {
        let mut repos = self.lock();
        // A thread that finished, as after its hive was removed, serves nothing.
        if repos
            .get(&key)
            .is_some_and(|served| !served.thread.is_finished())
        {
            return;
        }
        let (commands, receiver) = mpsc::unbounded_channel();
        let (stop, stopped) = watch::channel(false);
        let initial = UserState::load()
            .ok()
            .and_then(|state| state.entry(&key).cloned())
            .filter(|entry| copy::holds(entry, &entry.path))
            .and_then(|entry| Located::find(&entry.path).ok())
            .and_then(|located| Status::load(&located.repo_path))
            .unwrap_or_default();
        let status = Arc::new(Mutex::new(initial));
        let progress = Progress::default();
        let thread = {
            let (key, status, hubs) = (key.clone(), status.clone(), self.hubs.clone());
            let progress = progress.clone();
            std::thread::Builder::new()
                .name(format!("serve {key}"))
                .spawn(move || serve(&key, receiver, stopped, &status, &progress, &hubs))
                .expect("spawning a thread")
        };
        repos.insert(
            key,
            Served {
                commands,
                stop,
                status,
                progress,
                thread,
            },
        );
    }

    async fn sync(&self, key: &str) -> Result<Synced, String> {
        let (reply, result) = oneshot::channel();
        let sent = self
            .lock()
            .get(key)
            .map(|served| served.commands.send(Command::Sync(reply)).is_ok());
        match sent {
            None => Err("the daemon does not serve this repository".to_owned()),
            Some(false) => Err("the daemon stopped serving this repository".to_owned()),
            Some(true) => result
                .await
                .unwrap_or_else(|_| Err("the repository's thread stopped".to_owned())),
        }
    }

    /// Stops serving `key`'s copy, waiting for its thread to finish.
    async fn remove(&self, key: &str) -> bool {
        let Some(served) = self.lock().remove(key) else {
            return false;
        };
        served.stop.send(true).ok();
        tokio::task::spawn_blocking(move || served.thread.join().ok())
            .await
            .ok();
        true
    }

    async fn stop_all(&self) {
        let keys: Vec<String> = self.lock().keys().cloned().collect();
        for key in keys {
            self.remove(&key).await;
        }
    }

    /// What `key`'s sync is doing, if the daemon serves it.
    fn progress(&self, key: &str) -> Option<Activity> {
        self.lock().get(key).map(|served| served.progress.get())
    }

    fn statuses(&self) -> Vec<RepoStatus> {
        let mut statuses: Vec<RepoStatus> = self
            .lock()
            .iter()
            .filter(|(_, served)| !served.thread.is_finished())
            .map(|(key, served)| RepoStatus {
                key: key.clone(),
                status: served
                    .status
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .clone(),
            })
            .collect();
        statuses.sort_by(|a, b| a.key.cmp(&b.key));
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

    async fn add(self, _: tarpc::context::Context, key: String) -> Result<Synced, String> {
        tracing::info!("serving {key} from now on");
        // Starting over if it serves it already, with its entry as it is now, as after
        // joining again. On a task of its own, which finishes even if this request is
        // cancelled, as when the command asking gives up: else the copy could be left
        // unserved between stopping and starting.
        let supervisor = self.supervisor.clone();
        let restart = key.clone();
        tokio::spawn(async move {
            supervisor.remove(&restart).await;
            supervisor.start(restart.clone());
            // An entry it took the place of, at the same path, is no longer served. Looked
            // up afresh for each, so that one another command has just added is kept.
            let served: Vec<String> = supervisor.lock().keys().cloned().collect();
            for other in served.iter().filter(|other| **other != restart) {
                let entered = UserState::load()
                    .map(|state| state.entry(other).is_some())
                    .unwrap_or(true);
                if !entered {
                    supervisor.remove(other).await;
                }
            }
        })
        .await
        .ok();
        self.supervisor.sync(&key).await
    }

    async fn remove(self, _: tarpc::context::Context, key: String) -> Result<(), String> {
        if self.supervisor.remove(&key).await {
            tracing::info!("stopped serving {key}");
        }
        Ok(())
    }

    async fn sync(self, _: tarpc::context::Context, key: String) -> Result<Synced, String> {
        self.supervisor.sync(&key).await
    }

    async fn progress(self, _: tarpc::context::Context, key: String) -> Option<Activity> {
        self.supervisor.progress(&key)
    }

    async fn status(self, _: tarpc::context::Context) -> Vec<RepoStatus> {
        self.supervisor.statuses()
    }

    async fn stop(self, _: tarpc::context::Context) {
        tracing::info!("asked to stop");
        self.stop.notify_one();
    }
}

/// How large the daemon's log grows before a daemon starting starts it over.
const LOG_LIMIT: u64 = 10 << 20;

/// Starts the daemon's (or the hub's) log at `path` over if it has grown large: whether a
/// command started this daemon or launchd did at login, which never would. In place, since
/// whatever started it holds it open to append to: one deleted would take the rest of the log
/// with it.
pub fn trim_log(path: &Path) {
    if fs::metadata(path).is_ok_and(|m| m.len() > LOG_LIMIT)
        && let Ok(file) = fs::OpenOptions::new().write(true).open(path)
    {
        file.set_len(0).ok();
    }
}

/// Runs the daemon until it is stopped or interrupted.
pub fn run(socket: &Socket) -> anyhow::Result<()> {
    let lock_path = socket.lock_path()?;
    let Some(lock) = crate::lock::try_lock(&lock_path)? else {
        anyhow::bail!("a musubi daemon is already running (its socket is {socket})")
    };
    if let Ok(log) = config::daemon_log() {
        trim_log(&log);
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

/// Whether copies open another connection for a large transfer: unless
/// `musubi.daemon.connections` says `one`.
fn own_connections() -> bool {
    let setting = match Settings::load() {
        Ok(settings) => settings.daemon_connections,
        Err(err) => {
            tracing::warn!(
                "couldn't read musubi.daemon.connections ({err:#}); taking it for as-needed"
            );
            None
        }
    };
    match setting.as_deref() {
        None | Some("as-needed") => true,
        Some("one") => false,
        Some(other) => {
            tracing::warn!(
                "musubi.daemon.connections is {other:?}, neither `one` nor `as-needed`; taking \
                 it for as-needed"
            );
            true
        }
    }
}

async fn listen(socket: &Socket, lock_path: &Path) -> anyhow::Result<()> {
    let listener = socket.listen()?;
    let daemon = Daemon {
        supervisor: Arc::new(Supervisor::new(Hubs::new(
            tokio::runtime::Handle::current(),
            own_connections(),
        ))),
        stop: Arc::new(tokio::sync::Notify::new()),
    };
    for entry in UserState::load()?.copies {
        daemon.supervisor.start(entry.key);
    }
    tracing::info!("listening on {socket}");
    // A daemon whose lock file was deleted, as by cleaning up its directory, has nothing to
    // stop a second one starting, and no business running on.
    let mut check = tokio::time::interval(Duration::from_secs(5));
    loop {
        tokio::select! {
            stream = crate::socket::accept(&listener) => {
                let channel =
                    tarpc::server::BaseChannel::with_defaults(control::transport(stream));
                let serve = channel.execute(daemon.clone().serve()).for_each(|request| async {
                    tokio::spawn(request);
                });
                tokio::spawn(serve);
            }
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

/// Serves one copy until told to stop: a single-threaded runtime, since jj-lib's
/// repository handles are used from one thread.
fn serve(
    key: &str,
    commands: mpsc::UnboundedReceiver<Command>,
    stop: watch::Receiver<bool>,
    status: &Mutex<Status>,
    progress: &Progress,
    hubs: &Hubs,
) {
    // Everything this thread logs is about this copy. At error level, the span stays on
    // under any filter that shows anything.
    let _span = tracing::error_span!("sync", copy = %key).entered();
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
            () = serve_retrying(key, commands, status, progress, hubs) => {}
            () = stopped(&mut stop) => {}
        }
    });
}

/// Waits until told to stop, or until nothing can tell it anything any more.
async fn stopped(stop: &mut watch::Receiver<bool>) {
    stop.wait_for(|stop| *stop).await.ok();
}

/// Serves a copy, starting over after anything goes wrong, such as the hub being out of
/// reach, the repository's git store moving, or the copy not being where its entry says: it
/// may be servable soon.
async fn serve_retrying(
    key: &str,
    mut commands: mpsc::UnboundedReceiver<Command>,
    status: &Mutex<Status>,
    progress: &Progress,
    hubs: &Hubs,
) {
    let mut waiting = vec![];
    let mut backoff = Duration::from_secs(1);
    loop {
        let started = now();
        match serve_async(key, &mut commands, status, progress, &mut waiting, hubs).await {
            Ok(()) => return,
            Err(err) => {
                let message = format!("{err:#}");
                if err.downcast_ref::<Suspended>().is_some() {
                    tracing::warn!("{message}; looking again in {backoff:?}");
                } else {
                    tracing::error!("{message}; retrying in {backoff:?}");
                }
                // Into the copy, if it is where its entry says; never into what is there
                // instead.
                let copy = UserState::load()
                    .ok()
                    .and_then(|state| state.entry(key).cloned())
                    .filter(|entry| copy::holds(entry, &entry.path))
                    .and_then(|entry| Located::find(&entry.path).ok());
                record(copy.as_ref(), status, |status| status.failed(&err));
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

/// Records a change of status, for `musubi list`: in memory, and in `copy`, the copy being
/// served, if it was found.
fn record(copy: Option<&Located>, status: &Mutex<Status>, change: impl FnOnce(&mut Status)) {
    let mut status = status.lock().unwrap_or_else(PoisonError::into_inner);
    change(&mut status);
    if let Some(located) = copy {
        status.save(&located.repo_path);
    }
}

/// Why the daemon syncs nothing for an entry: its path doesn't hold the copy it names, and
/// jj hasn't seen the copy anywhere else.
#[derive(Debug)]
pub struct Suspended(String);

impl std::fmt::Display for Suspended {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "suspended: {}", self.0)
    }
}

impl std::error::Error for Suspended {}

/// Finds the copy `key`'s entry names: at its path, or where jj last saw it, which moves the
/// entry there.
fn find_copy(key: &str) -> anyhow::Result<Option<(Entry, Located)>> {
    let Some(entry) = UserState::load()?.entry(key).cloned() else {
        return Ok(None);
    };
    if copy::holds(&entry, &entry.path) {
        let located = Located::find(&entry.path)?;
        return Ok(Some((entry, located)));
    }
    if let Some(path) = copy::moved_to(&entry) {
        tracing::info!(
            "the copy moved from {} to {}; serving it there",
            entry.path.display(),
            path.display()
        );
        if !UserState::move_entry(&entry, path.clone())? {
            return Err(Suspended("its entry changed while the daemon found it".to_owned()).into());
        }
        let moved = Entry { path, ..entry };
        let located = Located::find(&moved.path)?;
        return Ok(Some((moved, located)));
    }
    let why = match Located::find(&entry.path) {
        Err(_) => format!("{} is missing", entry.path.display()),
        Ok(located) => {
            let found = copy::Found::read(&located.repo_path)?;
            let why = copy::check(&entry, &found)
                .err()
                .unwrap_or_else(|| "it changed".to_owned());
            format!(
                "the repository at {} isn't the copy: {why}",
                entry.path.display()
            )
        }
    };
    Err(Suspended(why).into())
}

/// The identity of `path`'s directory, which changes when it is replaced, as by restoring a
/// backup, though what is in it may not.
#[cfg(unix)]
fn identity(path: &Path) -> Option<(u64, u64)> {
    use std::os::unix::fs::MetadataExt as _;
    let metadata = fs::metadata(path).ok()?;
    Some((metadata.dev(), metadata.ino()))
}

#[cfg(not(unix))]
fn identity(_path: &Path) -> Option<(u64, u64)> {
    None
}

async fn serve_async(
    key: &str,
    commands: &mut mpsc::UnboundedReceiver<Command>,
    status: &Mutex<Status>,
    progress: &Progress,
    waiting: &mut Vec<oneshot::Sender<Result<Synced, String>>>,
    hubs: &Hubs,
) -> anyhow::Result<()> {
    // No entry: the copy left, or its hive was removed.
    let Some((entry, located)) = find_copy(key)? else {
        return Ok(());
    };
    let hive = HiveConfig::load(&located.repo_path)?
        .with_context(|| format!("{} is not part of a hive", entry.path.display()))?;
    let workspace = &entry.path;
    let mut opened = identity(&located.repo_path);
    let connection = hubs.connect(&hive.hub).await?;
    let own = hubs.own_connections(&hive.hub);
    let (mut driver, machine) = open_driver(&located, &hive, &connection, own, progress)?;
    let transport = connection.transport.clone();
    let mut notices = transport.subscribe(&hive.head_subject()).await?;
    let mut reconnections = transport.reconnections();
    let mut watcher = OpHeadsWatcher::new(&located.repo_path)?;
    let mut poll = tokio::time::interval(POLL_INTERVAL);
    let mut backoff = Duration::from_millis(500);
    let mut retry = false;
    // Whether the connection coming back has cut short a wait to retry since the last sync
    // that worked.
    let mut woke_early = false;
    // Why the hub was out of reach when last asked, to log once rather than at every retry.
    let mut unreachable: Option<String> = None;
    let mut gc_checked: Option<std::time::Instant> = None;
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
        // Still the copy, before anything is read from it or written to it, its status
        // included.
        let found = copy::Found::read(&located.repo_path)?;
        if let Err(why) = copy::check(&entry, &found) {
            let why = format!(
                "the repository at {} isn't the copy: {why}",
                workspace.display()
            );
            for waiter in waiting.drain(..) {
                waiter.send(Err(format!("suspended: {why}"))).ok();
            }
            return Err(Suspended(why).into());
        }
        // While the hub is out of reach, a sync could only wait for its requests to time
        // out. Say why instead, to `musubi status` and to any command waiting, and wait for
        // the connection to come back, or for the backoff to pass. A reconnection from now
        // on ends the wait.
        reconnections.seen();
        if !transport.connected()
            && let Some(why) = connection.out_of_reach().await
        {
            if unreachable.as_ref() != Some(&why) {
                tracing::warn!("{why}");
            }
            record(Some(&located), status, |status| {
                status.failed(&anyhow::anyhow!("{why}"));
            });
            for waiter in waiting.drain(..) {
                waiter.send(Err(why.clone())).ok();
            }
            unreachable = Some(why);
            retry = true;
            // Nothing failed here, so nothing need start over; and the connection coming
            // back always ends the wait, since no sync ran that could lose it again.
            let stopped = tokio::select! {
                stopped = pause(backoff, commands, waiting) => stopped,
                () = reconnections.next() => false,
            };
            if stopped {
                return Ok(());
            }
            backoff = (backoff * 2).min(MAX_BACKOFF);
            continue;
        }
        unreachable = None;
        // The copy, but in a directory that replaced the one opened, as after restoring a
        // backup: open it afresh, and watch it.
        let now_identity = identity(&located.repo_path);
        if now_identity != opened {
            tracing::info!("the repository's directory was replaced; opening it afresh");
            driver.reopen(located.open()?)?;
            watcher = OpHeadsWatcher::new(&located.repo_path)?;
            opened = now_identity;
        }
        tracing::debug!("syncing after {trigger}");
        let started = std::time::Instant::now();
        // Reconnecting during the sync, which may miss announcements, calls for another.
        reconnections.seen();
        let result = driver.sync().await;
        tracing::debug!("sync took {:?}", started.elapsed());
        let synced = known(&driver);
        // Why the hub is out of reach, if the connector knows, says more than a timeout.
        let result = result.map_err(|err| connection.explain(err));
        // The hive is over: leave it, then say so, so that whoever asked finds it left.
        if let Err(err) = &result
            && HiveGone::of(err) == Some(HiveGone::Removed)
        {
            let message = format!(
                "{err:#}, so this repository no longer syncs with it; everything it has stays"
            );
            // Changed meanwhile, as by `musubi join --hub`: start over with what it is now.
            anyhow::ensure!(
                leave_hive(&located, &hive, Membership::Removed)?,
                "this repository's hive or hub changed while it synced"
            );
            tracing::warn!("{message}");
            for waiter in waiting.drain(..) {
                waiter.send(Err(message.clone())).ok();
            }
            return Ok(());
        }
        let reply = match &result {
            Ok(_) => Ok(synced.clone()),
            Err(err) => Err(format!("{err:#}")),
        };
        record(Some(&located), status, |status| {
            status.synced(result.as_ref().err(), &synced);
        });
        report(
            &connection,
            &located.repo_path,
            &hive,
            &machine,
            synced.seq,
            reply.as_ref().err(),
        );
        for waiter in waiting.drain(..) {
            waiter.send(reply.clone()).ok();
        }
        match result {
            Ok(_) => {
                backoff = Duration::from_millis(500);
                retry = false;
                woke_early = false;
                if gc_checked.is_none_or(|checked| checked.elapsed() >= GC_CHECK_INTERVAL) {
                    gc_checked = Some(std::time::Instant::now());
                    collect_garbage(&located);
                }
            }
            Err(err) => {
                tracing::warn!("{err:#}");
                // What failed may be that the copy is no longer there, as when it was moved
                // or deleted during the sync: then open nothing there, which would write.
                if !copy::holds(&entry, workspace) {
                    return Err(Suspended(format!(
                        "the copy is no longer at {}",
                        workspace.display()
                    ))
                    .into());
                }
                // Lost replies are indistinguishable from lost requests, and the open
                // repository's cached state may be what failed: start over, reopened.
                if let Err(err) = located.open().and_then(|repo| driver.reopen(repo)) {
                    tracing::warn!("cannot reopen: {err:#}");
                    driver.restart();
                }
                // So too may the watcher, if the directory it watches was replaced, as by
                // restoring a backup: one watching a deleted directory never wakes.
                match OpHeadsWatcher::new(&located.repo_path) {
                    Ok(new) => watcher = new,
                    Err(err) => tracing::debug!("cannot watch afresh: {err:#}"),
                }
                retry = true;
                // The connection coming back while it waits, as after the machine slept, ends
                // the wait, but only once: a sync that itself loses the connection would
                // otherwise come straight back, again and again.
                reconnections.seen();
                let stopped = tokio::select! {
                    stopped = pause(backoff, commands, waiting) => stopped,
                    () = reconnections.next(), if !woke_early => {
                        woke_early = true;
                        false
                    }
                };
                if stopped {
                    return Ok(());
                }
                backoff = (backoff * 2).min(MAX_BACKOFF);
            }
        }
    }
}

/// Whether a gc runs, in any repository the daemon serves: one at a time is enough.
static COLLECTING: AtomicBool = AtomicBool::new(false);

/// Starts a gc in the repository on a thread of its own, if it is due (see `musubi_jj::gc`)
/// and none is running, so that syncs go on meanwhile.
fn collect_garbage(located: &Located) {
    if !musubi_jj::gc::due(&located.repo_path, SystemTime::now())
        || COLLECTING.swap(true, Ordering::AcqRel)
    {
        return;
    }
    let (workspace_root, repo_path) = (located.workspace_root.clone(), located.repo_path.clone());
    let spawned = std::thread::Builder::new()
        .name(format!("gc {}", repo_path.display()))
        .spawn(move || {
            /// Lets the next gc start once this one ends, however it ends.
            struct Done;
            impl Drop for Done {
                fn drop(&mut self) {
                    COLLECTING.store(false, Ordering::Release);
                }
            }
            let _done = Done;
            let collected = crate::settings::load(&workspace_root, &repo_path)
                .and_then(|settings| Ok(musubi_jj::gc::collect_if_due(&repo_path, &settings)?));
            match collected {
                Ok(true) => tracing::info!("collected garbage in {}", repo_path.display()),
                Ok(false) => {}
                Err(err) => {
                    tracing::warn!("collecting garbage in {}: {err:#}", repo_path.display());
                }
            }
        });
    if let Err(err) = spawned {
        COLLECTING.store(false, Ordering::Release);
        tracing::warn!("starting gc: {err}");
    }
}

/// Tells the hub how a sync went, for `musubi top`, without waiting for its answer: a sync
/// that failed may have failed to reach it. The answer, when it comes, has the hive's name,
/// recorded for `musubi status` should the hive have been renamed.
fn report(
    connection: &Arc<Connection>,
    repo_path: &Path,
    hive: &HiveConfig,
    machine: &str,
    seq: u64,
    error: Option<&String>,
) {
    let request = HubWideRequest::Report {
        hive: hive.hive.to_string(),
        report: Report {
            machine: machine.to_owned(),
            seq,
            error: error.cloned(),
            version: env!("CARGO_PKG_VERSION").to_owned(),
        },
    };
    let Ok(payload) = Envelope::encode(request) else {
        return;
    };
    // The connection, not just its transport, so that while the report waits, the daemon
    // shares it rather than connecting again.
    let connection = connection.clone();
    let (repo_path, hive) = (repo_path.to_owned(), hive.clone());
    tokio::spawn(async move {
        let subject = rpc_subject(HUB_TOKEN);
        match connection
            .transport
            .request(&subject, Bytes::from(payload), REPORT_TIMEOUT)
            .await
        {
            Ok(reply) => {
                if let Ok(HubWideReply::Hive(info)) = Envelope::decode(&reply)
                    && info.id == hive.hive.to_string()
                {
                    hive.note_name(&repo_path, &info.name);
                }
            }
            Err(err) => tracing::debug!("could not report to the hub: {err}"),
        }
    });
}

/// Makes the repository at `located` no longer part of `hive`, keeping everything it has:
/// marks its record `membership`, left as `musubi leave` leaves or removed as the hub said,
/// and stops this machine's daemon serving it. Returns false, doing nothing, if it isn't part
/// of `hive` through the same hub (any more), as when it left it, joined another, or moved
/// to another hub, meanwhile.
pub fn leave_hive(
    located: &Located,
    hive: &HiveConfig,
    membership: Membership,
) -> anyhow::Result<bool> {
    let _lock = HiveConfig::lock(&located.repo_path)?;
    let Some(now) = HiveConfig::load(&located.repo_path)?
        .filter(|now| now.joined() && now.hive == hive.hive && now.hub == hive.hub)
    else {
        return Ok(false);
    };
    let key = copy::Found::read(&located.repo_path)?.key;
    // The record first: an entry for a record that says it left is suspended, where a record
    // that says joined with no entry here would look like a duplicate, if this failed between.
    HiveConfig {
        state: membership,
        ..now
    }
    .save(&located.repo_path)?;
    if let Some(key) = key {
        UserState::remove_entry(&key)?;
    }
    fs::remove_file(Status::path(&located.repo_path)).ok();
    Ok(true)
}

/// Connects to the hive's hub, and opens the repository to sync with it there.
fn open_driver(
    located: &Located,
    hive: &HiveConfig,
    connection: &Connection,
    own_connections: Option<OpenConnection>,
    progress: &Progress,
) -> anyhow::Result<(NodeDriver, String)> {
    let blobs = located.repo_path.join("musubi/blobs");
    let mut remote = RemoteHub::new(
        connection.transport.clone(),
        hive.rpc_subject(),
        &blobs,
        REQUEST_TIMEOUT,
    )?
    .with_progress(progress.clone());
    if let Some(open) = own_connections {
        remote = remote.with_own_connections(open);
    }
    let repo = located.open()?;
    let machine = repo.machine().key().to_owned();
    let driver = NodeDriver::new(repo, remote)?;
    Ok((driver, machine))
}

/// The hive's head as `driver` knows it.
fn known(driver: &NodeDriver) -> Synced {
    let (seq, head) = driver.known();
    Synced {
        seq: *seq,
        head: head.hex(),
    }
}

/// Syncs once, in this process, as the daemon would, and records how it went for
/// `musubi status`.
/// `progress` records what it is doing.
pub async fn sync_once(
    located: &Located,
    hive: &HiveConfig,
    progress: &Progress,
) -> anyhow::Result<Synced> {
    let mut status = Status::load(&located.repo_path).unwrap_or_default();
    let opened = async {
        let connection = crate::hub::connect(&hive.hub, REQUEST_TIMEOUT).await?;
        let (driver, _) = open_driver(located, hive, &connection, None, progress)?;
        anyhow::Ok((connection, driver))
    };
    let (connection, mut driver) = match opened.await {
        Ok(opened) => opened,
        Err(err) => {
            status.failed(&err);
            status.save(&located.repo_path);
            return Err(err);
        }
    };
    let result = driver.sync().await.map_err(|err| connection.explain(err));
    let synced = known(&driver);
    status.synced(result.as_ref().err(), &synced);
    status.save(&located.repo_path);
    result.map(|_| synced)
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
        (None, login::log_hint(login::Service::Daemon))
    } else {
        let (child, log) = spawn(socket)?;
        (Some(child), log.display().to_string())
    };
    let deadline = std::time::Instant::now() + Duration::from_secs(20);
    // A child that exits may have lost a race with another command's daemon, which is as
    // good: keep looking for one until the deadline.
    let mut exited = None;
    let mut pause = FIRST_POLL;
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
        tokio::time::sleep(pause).await;
        pause = (pause * 2).min(LAST_POLL);
    }
}

/// How long to wait before looking again for a daemon starting or stopping, at first and at
/// most: one is ready in a few milliseconds, which a fixed 50 would add to every command
/// that starts it.
const FIRST_POLL: Duration = Duration::from_millis(2);
const LAST_POLL: Duration = Duration::from_millis(50);

/// Starts `musubi daemon` in the background, detached from this terminal, logging to the
/// state directory.
fn spawn(socket: &Socket) -> anyhow::Result<(std::process::Child, PathBuf)> {
    let state = std::path::absolute(config::state_dir()?)?;
    fs::create_dir_all(&state)?;
    let log = config::daemon_log()?;
    let file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&log)
        .with_context(|| format!("opening {log:?}"))?;
    let socket = match socket {
        Socket::Path(path) => Socket::Path(std::path::absolute(path)?),
        Socket::Pipe(_) => socket.clone(),
    };
    let mut command = std::process::Command::new(std::env::current_exe()?);
    command
        .args(["daemon", "--socket", &socket.to_string()])
        // Not the directory of the command that starts it, often a repository it serves,
        // which may be deleted or moved: gix needs the current directory whenever it opens
        // a repository, any repository. So the paths it is given are absolute.
        .current_dir(&state)
        .stdin(std::process::Stdio::null())
        .stdout(file.try_clone()?)
        .stderr(file);
    if std::env::var_os("MUSUBI_STATE_DIR").is_some() {
        command.env("MUSUBI_STATE_DIR", &state);
    }
    // Now that the state directory exists.
    if let Err(err) = agent::refresh() {
        tracing::debug!("not pointing the daemon at this ssh agent: {err:#}");
    }
    isolate(&mut command, agent::link()?.as_deref());
    detach(&mut command);
    let child = command.spawn().context("starting the daemon")?;
    Ok((child, log))
}

/// What a daemon takes from the command that starts it, which it outlives, serving every
/// repository on the machine: not git's variables naming the command's repository, as a git
/// hook has, and not the command's ssh agent, but `agent_link`, which commands keep pointed
/// at a live one ([`agent`]).
fn isolate(command: &mut std::process::Command, agent_link: Option<&Path>) {
    musubi_jj::git_command::without_repository_env(command);
    if let Some(link) = agent_link {
        command.env("SSH_AUTH_SOCK", link);
    }
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
    let mut pause = FIRST_POLL;
    // Gone once it has let go of its lock, which it does after closing its socket.
    while socket.connect().await?.is_some() || socket.is_locked()? {
        anyhow::ensure!(
            std::time::Instant::now() < deadline,
            "the daemon on {socket} did not stop"
        );
        tokio::time::sleep(pause).await;
        pause = (pause * 2).min(LAST_POLL);
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::ffi::OsStr;

    use super::*;

    /// A large log starts over, in place, so that a daemon launchd started, which writes to
    /// it through its own handle, goes on logging to it.
    #[test]
    fn a_large_log_starts_over_in_place() {
        use std::io::Write as _;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("daemon.log");
        let mut appending = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .unwrap();
        appending.write_all(b"small\n").unwrap();
        trim_log(&path);
        assert_eq!(fs::metadata(&path).unwrap().len(), 6);
        appending
            .write_all(&vec![b'x'; usize::try_from(LOG_LIMIT).unwrap()])
            .unwrap();
        trim_log(&path);
        appending.write_all(b"after\n").unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "after\n");
    }

    #[test]
    fn a_started_daemon_takes_nothing_of_where_it_was_started() {
        let mut command = std::process::Command::new("musubi");
        isolate(&mut command, Some(Path::new("/state/ssh-agent")));
        let envs: BTreeMap<&OsStr, Option<&OsStr>> = command.get_envs().collect();
        for name in musubi_jj::git_command::REPOSITORY_ENV {
            assert_eq!(envs.get(OsStr::new(name)), Some(&None), "{name}");
        }
        assert_eq!(
            envs.get(OsStr::new("SSH_AUTH_SOCK")),
            Some(&Some(OsStr::new("/state/ssh-agent")))
        );
    }
}
