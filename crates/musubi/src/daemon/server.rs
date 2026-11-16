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

use futures::StreamExt as _;
use musubi_sync::progress::Activity;
use tarpc::server::Channel as _;

use super::connections::Hubs;
use super::worker::Worker;
use crate::config::Settings;
use crate::config::UserState;
use crate::control;
use crate::control::Control;
use crate::control::RepoStatus;
use crate::control::Synced;
use crate::socket::Socket;

/// The copies being served, by machine key, and the connections to hubs they share.
struct Supervisor {
    repos: Mutex<HashMap<String, Worker>>,
    hubs: Arc<Hubs>,
}

impl Supervisor {
    fn new(hubs: Hubs) -> Self {
        Self {
            repos: Mutex::default(),
            hubs: Arc::new(hubs),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HashMap<String, Worker>> {
        self.repos.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Starts serving `key`'s copy, unless it already is.
    fn start(&self, key: String) {
        let mut repos = self.lock();
        // A thread that finished, as after its hive was removed, serves nothing.
        if repos.get(&key).is_some_and(|served| !served.is_finished()) {
            return;
        }
        repos.insert(key.clone(), Worker::start(key, self.hubs.clone()));
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

/// Serves until stopped. Returns the binary to start again from, if an upgrade installed it.
pub(super) async fn listen(
    socket: &Socket,
    lock_path: &Path,
) -> anyhow::Result<Option<&'static Path>> {
    let copies = UserState::load()?.copies;
    let mut listener = socket.listen()?;
    let mut bound = socket.file();
    let daemon = Daemon {
        supervisor: Arc::new(Supervisor::new(Hubs::new(
            tokio::runtime::Handle::current(),
            own_connections(),
        ))),
        stop: Arc::new(tokio::sync::Notify::new()),
    };
    for entry in copies {
        daemon.supervisor.start(entry.key);
    }
    tracing::info!("listening on {socket}");
    // A daemon whose lock file was deleted, as by cleaning up its directory, has nothing to
    // stop a second one starting, and no business running on. One whose socket was deleted,
    // as temp cleaners do, can't be reached, so it listens again; but one whose socket
    // another process has taken leaves it be.
    let mut check = tokio::time::interval(Duration::from_secs(5));
    let mut upgraded = None;
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
            exe = crate::upgrade::installed() => {
                upgraded = Some(exe);
                break;
            }
            () = crate::hub::interrupted() => break,
            _ = check.tick() => {
                if !lock_path.exists() {
                    tracing::warn!("{} is gone; stopping", lock_path.display());
                    break;
                }
                match socket.file() {
                    now if now == bound => {}
                    None => {
                        tracing::warn!("{socket} is gone; listening there again");
                        match socket.listen() {
                            Ok(again) => {
                                listener = again;
                                bound = socket.file();
                            }
                            Err(err) => {
                                tracing::error!("{err:#}; stopping");
                                break;
                            }
                        }
                    }
                    Some(_) => {
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
