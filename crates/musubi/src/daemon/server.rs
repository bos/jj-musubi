//! The daemon's control server and registry of copy workers.
//!
//! The registry owns registration and shutdown order; each `Worker` owns its thread and
//! command channel. This server does not read or mutate a worker's internal synchronization.

use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Duration;

use musubi_sync::progress::Activity;

use super::connections::Hubs;
use super::worker::FirstSync;
use super::worker::Worker;
use super::worker::leave_unsynced;
use crate::config::Settings;
use crate::config::UserState;
use crate::control;
use crate::control::Abandoned;
use crate::control::RepoStatus;
use crate::control::Request;
use crate::control::Response;
use crate::control::Synced;
use crate::socket::Socket;
use crate::watch::Watcher;

/// The copies being served, by machine key, and the connections to hubs they share.
struct Supervisor {
    repos: Mutex<HashMap<String, Worker>>,
    /// The first syncs commands asked for, by the token each `Join` names, which its `Cancel`
    /// names too. Kept, closed, once answered: a `Cancel` that comes late finds it so.
    first_syncs: Mutex<HashMap<String, FirstSync>>,
    hubs: Arc<Hubs>,
}

impl Supervisor {
    fn new(hubs: Hubs) -> Self {
        Self {
            repos: Mutex::default(),
            first_syncs: Mutex::default(),
            hubs: Arc::new(hubs),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<String, Worker>> {
        self.repos.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Starts serving `key`'s copy, unless it already is, its first sync stoppable as `first`
    /// says, unless the copy has `applied` some of the hive's history. Returns whether it
    /// started.
    ///
    /// Under the lock of the workers, as `remove` closes the first sync of the one it takes
    /// away: so a first sync is open, and stopping it leaves the hive, only while the worker
    /// serving the copy is the one its gate holds back. No other applies anything meanwhile.
    fn start(&self, key: String, first: FirstSync, applied: bool) -> bool {
        let mut repos = self.lock();
        // A thread that finished, as after its hive was removed, serves nothing.
        if repos.get(&key).is_some_and(|served| !served.is_finished()) {
            first.close();
            return false;
        }
        first.started(applied);
        repos.insert(key.clone(), Worker::start(key, self.hubs.clone(), first));
        true
    }

    /// The first sync of `key`'s copy that the `Join` of `token` asks for, whichever of it and
    /// its `Cancel` comes first.
    fn first_sync(&self, key: &str, token: String) -> FirstSync {
        self.first_syncs
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .entry(token)
            .or_insert_with(|| FirstSync::starting(key))
            .clone()
    }

    async fn sync(&self, key: &str) -> Result<Synced, String> {
        let result = self
            .lock()
            .get(key)
            .ok_or_else(|| "the daemon does not serve this repository".to_owned())?
            .request_sync()?;
        result
            .await
            .unwrap_or_else(|_| Err("the repository's thread stopped".to_owned()))
    }

    /// Stops serving `key`'s copy, waiting for its thread to finish.
    async fn remove(&self, key: &str) -> bool {
        let Some(served) = self.lock().remove(key) else {
            return false;
        };
        // No command can stop the sync of a worker no longer serving the copy: the one that
        // takes its place isn't held back by its gate.
        served.first_sync().close();
        served.stop().await;
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
        self.lock().get(key).map(|served| served.progress())
    }

    fn statuses(&self) -> Vec<RepoStatus> {
        let mut statuses: Vec<RepoStatus> = self
            .lock()
            .iter()
            .filter(|(_, served)| !served.is_finished())
            .map(|(key, served)| RepoStatus {
                key: key.clone(),
                status: served.status(),
                snapshot_issues: served.snapshot_issues(),
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

impl Daemon {
    /// Does what a command asks, given when it has gone away. (Each [`Request`] is
    /// documented where it is defined.)
    async fn answer(self, request: Request, abandoned: Abandoned) -> Response {
        match request {
            Request::Version => Response::Version(control::VERSION.to_owned()),
            Request::Add { key } => Response::Add(self.add(key).await),
            Request::Join { key, token } => Response::Join(self.join(key, token, abandoned).await),
            Request::Cancel { key, token } => Response::Cancel(
                self.supervisor
                    .first_sync(&key, token)
                    .stop("the command waiting on it was interrupted", leave_unsynced)
                    .await,
            ),
            Request::Remove { key } => {
                if self.supervisor.remove(&key).await {
                    tracing::info!("stopped serving {key}");
                }
                Response::Remove(Ok(()))
            }
            Request::Sync { key } => Response::Sync(self.supervisor.sync(&key).await),
            Request::Progress { key } => Response::Progress(self.supervisor.progress(&key)),
            Request::Status => Response::Status(self.supervisor.statuses()),
            Request::Stop => {
                tracing::info!("asked to stop");
                self.stop.notify_one();
                Response::Stop
            }
        }
    }

    /// [`Request::Join`]: as `add`, stopping the first sync if its command goes away first.
    async fn join(
        &self,
        key: String,
        token: String,
        abandoned: Abandoned,
    ) -> Result<Synced, String> {
        /// Lets no command stop the first sync once this ends: answered, or dropped, as when
        /// the request's deadline passes. One that has stopped it already, has.
        struct Closing(Option<FirstSync>);
        impl Drop for Closing {
            fn drop(&mut self) {
                if let Some(first) = &self.0 {
                    first.close();
                }
            }
        }
        // Known before the restart, so that a `Cancel` meanwhile waits for it.
        let first = self.supervisor.first_sync(&key, token);
        let _closing = Closing(Some(first.clone()));
        let synced = async {
            self.restart(&key, first.clone()).await;
            self.supervisor.sync(&key).await
        };
        tokio::select! {
            synced = synced => synced,
            () = abandoned => {
                first
                    .stop("the command waiting on it went away", leave_unsynced)
                    .await
                    .ok();
                Err("the command went away".to_owned())
            }
        }
    }

    async fn add(&self, key: String) -> Result<Synced, String> {
        self.restart(&key, FirstSync::closed(&key)).await;
        self.supervisor.sync(&key).await
    }

    /// Starts serving `key`'s copy, starting over if it serves it already, with its entry as
    /// it is now, as after joining again; its first sync stoppable as `first` says.
    async fn restart(&self, key: &str, first: FirstSync) {
        tracing::info!("serving {key} from now on");
        // On a task of its own, which finishes even if this request is cancelled, as when the
        // command asking gives up: else the copy could be left unserved between stopping and
        // starting.
        let supervisor = self.supervisor.clone();
        let restart = key.to_owned();
        tokio::spawn(async move {
            // A worker serving it already, as one a daemon starting just now does, may have
            // applied some of the hive's history to it: then the sync can't be stopped. Not one
            // that has finished, which served the copy before it last left its hive.
            let before = supervisor
                .lock()
                .get(&restart)
                .filter(|served| !served.is_finished())
                .map(Worker::first_sync);
            supervisor.remove(&restart).await;
            // Started by another command meanwhile, no worker ever has this first sync.
            let applied = before.is_some_and(|before| before.applied());
            supervisor.start(restart.clone(), first, applied);
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
    }
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

/// How long the daemon leaves between listening again on its socket and the next time, so
/// that whatever goes on deleting it, as a cleaner still running, doesn't keep it busy.
const RELISTEN_GAP: Duration = Duration::from_secs(1);

/// Watches for the daemon's socket going, where the system can say: a named pipe can't be
/// deleted. Without a watch, the daemon still looks every few seconds.
fn watch_socket(socket: &Socket) -> Option<Watcher> {
    let Socket::Path(path) = socket else {
        return None;
    };
    Watcher::removal(path)
        .inspect_err(|err| {
            tracing::debug!(
                "not watching for {socket} to go, only looking every few seconds: {err:#}"
            );
        })
        .ok()
}

/// Waits until it is time for the daemon to look at its lock file and socket: at `check`'s
/// next tick, once `gone` reports the socket gone, or at `soon`.
async fn look(
    check: &mut tokio::time::Interval,
    gone: Option<&mut Watcher>,
    soon: Option<tokio::time::Instant>,
) {
    let soon = async {
        match soon {
            Some(at) => tokio::time::sleep_until(at).await,
            None => std::future::pending().await,
        }
    };
    tokio::select! {
        _ = check.tick() => {}
        () = crate::watch::changed(gone) => {}
        () = soon => {}
    }
}

/// Serves until stopped. Returns the binary to start again from, if an upgrade installed it.
pub(super) async fn listen(
    socket: &Socket,
    lock_path: &Path,
) -> anyhow::Result<Option<&'static Path>> {
    let copies = UserState::load()?.copies;
    let mut listener = socket.listen()?;
    // Before reading what is bound, so that a deletion in between is news.
    let mut gone = watch_socket(socket);
    let mut bound = socket.file();
    let daemon = Daemon {
        supervisor: Arc::new(Supervisor::new(Hubs::new(
            tokio::runtime::Handle::current(),
            own_connections(),
        ))),
        stop: Arc::new(tokio::sync::Notify::new()),
    };
    let requests = control::service({
        let daemon = daemon.clone();
        move |request, abandoned| daemon.clone().answer(request, abandoned)
    })
    .await?;
    for entry in copies {
        let first = FirstSync::closed(&entry.key);
        daemon.supervisor.start(entry.key, first, false);
    }
    tracing::info!("listening on {socket}");
    // A daemon whose lock file was deleted, as by cleaning up its directory, has nothing to
    // stop a second one starting, and no business running on. One whose socket was deleted,
    // as temp cleaners do, can't be reached, so it listens again; but one whose socket
    // another process has taken leaves it be. It looks every few seconds, and at once when
    // its socket's directory reports the socket gone, so that a command run just after
    // doesn't wait for the next look; but it listens again at most once in `RELISTEN_GAP`.
    // A named pipe has no file to go, and lasts as long as its listener.
    let mut check = tokio::time::interval(Duration::from_secs(5));
    let path = matches!(socket, Socket::Path(_));
    // Gone before what was bound was read, and so before the watch saw it go.
    let mut soon = (path && bound.is_none()).then(tokio::time::Instant::now);
    // When the daemon may next listen again.
    let mut allowed: Option<tokio::time::Instant> = None;
    let mut upgraded = None;
    loop {
        tokio::select! {
            stream = crate::socket::accept(&listener) => {
                tokio::spawn(control::serve(requests.clone(), stream));
            }
            () = daemon.stop.notified() => break,
            exe = crate::upgrade::installed() => {
                upgraded = Some(exe);
                break;
            }
            () = crate::hub::interrupted() => break,
            () = look(&mut check, gone.as_mut(), soon) => {
                soon = None;
                if !lock_path.exists() {
                    tracing::warn!("{} is gone; stopping", lock_path.display());
                    break;
                }
                match socket.file() {
                    // Before `bound`, which is none if the socket went before it was read.
                    None if path => {
                        let now = tokio::time::Instant::now();
                        if let Some(next) = allowed.filter(|&next| next > now) {
                            soon = Some(next);
                            continue;
                        }
                        allowed = Some(now + RELISTEN_GAP);
                        tracing::warn!("{socket} is gone; listening there again");
                        match socket.listen() {
                            Ok(again) => {
                                listener = again;
                                // The watch ends only with the directory, which takes the
                                // socket with it, so that the daemon comes here: re-armed
                                // here, then, it covers the directory as made again. Before
                                // reading what is bound, so that a deletion in between is
                                // news.
                                gone = watch_socket(socket);
                                bound = socket.file();
                                if bound.is_none() {
                                    soon = allowed;
                                }
                            }
                            Err(err) => {
                                tracing::error!("{err:#}; stopping");
                                break;
                            }
                        }
                    }
                    now if now == bound => {}
                    // A file, since a pipe has none, which is never gone.
                    _ => {
                        tracing::warn!("{socket} is another process's now; stopping");
                        bound = None;
                        break;
                    }
                }
            }
        }
    }
    daemon.supervisor.stop_all().await;
    // Unless another process has put its own in its place.
    if bound.is_some()
        && socket.file() == bound
        && let Socket::Path(path) = socket
    {
        fs::remove_file(path).ok();
    }
    tracing::info!("stopped");
    Ok(upgraded)
}
