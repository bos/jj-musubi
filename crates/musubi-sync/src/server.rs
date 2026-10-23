//! A hub serving every hive in its directory (see `musubi_hub::hub_dir`).
//!
//! One subscription, `musubi.*.rpc`, takes every request. Those for a hive go to that
//! hive's own thread, which opens its store on the first request and then answers its
//! requests one at a time, as [`HubService`] does; different hives never wait for each
//! other. Requests to `musubi.hub.rpc` ([`HUB_TOKEN`]) are about the hub as a whole:
//! joining, listing, renaming, and removing hives. A request for a hive the hub doesn't
//! have gets an error: only a join creates a hive.
//!
//! The hub keeps account of what it serves, and of what machines report of their syncing,
//! in memory, for `musubi top` (see `musubi_hub::activity`).

use std::collections::HashMap;
use std::panic::AssertUnwindSafe;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::mpsc;
use std::time::Instant;

use bytes::Bytes;
use musubi_hub::activity::Activity;
use musubi_hub::activity::summarize;
use musubi_hub::hub_dir::HubDir;
use musubi_hub::hub_dir::Opened;
use musubi_hub::hub_dir::open_whole;
use musubi_hub::index::HiveIndex;
use musubi_hub::store::HubStore;
use musubi_transport::Message;
use musubi_transport::Transport;

use crate::OpId;
use crate::hub::HubAdapter;
use crate::service::HubService;
use crate::wire::Envelope;
use crate::wire::HUB_TOKEN;
use crate::wire::HubReply;
use crate::wire::HubWideReply;
use crate::wire::HubWideRequest;
use crate::wire::fit_error;
use crate::wire::head_subject;
use crate::wire::rpc_subject;
use crate::wire::rpc_token;

pub struct HubServer {
    hubs: Arc<Mutex<HubDir>>,
    activity: Arc<Mutex<Activity>>,
    workers: HashMap<String, Worker>,
}

struct Worker {
    requests: mpsc::Sender<Message>,
    thread: std::thread::JoinHandle<()>,
}

impl HubServer {
    /// Opens the hub directory `dir`, which must exist.
    pub fn open(dir: &Path) -> anyhow::Result<Self> {
        Ok(Self {
            hubs: Arc::new(Mutex::new(HubDir::open(dir)?)),
            activity: Arc::new(Mutex::new(Activity::new())),
            workers: HashMap::new(),
        })
    }

    pub fn hive_count(&self) -> usize {
        self.lock().len()
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HubDir> {
        self.hubs.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn activity(&self) -> std::sync::MutexGuard<'_, Activity> {
        lock_activity(&self.activity)
    }

    /// Serves until the transport's subscription ends, calling `ready` once subscribed.
    /// Needs a multi-threaded runtime: hive threads publish their replies through it.
    pub async fn run(
        mut self,
        transport: Arc<dyn Transport>,
        ready: impl FnOnce(),
    ) -> anyhow::Result<()> {
        let mut requests = transport.subscribe(&rpc_subject("*")).await?;
        ready();
        while let Some(message) = requests.next().await {
            let Some(reply_to) = message.reply.clone() else {
                continue;
            };
            let token = rpc_token(&message.subject).unwrap_or_default().to_owned();
            if token == HUB_TOKEN {
                let reply = self
                    .handle_hub_wide(&message.payload, transport.max_payload())
                    .await;
                let reply = Envelope::encode(reply)?;
                if let Err(err) = transport.publish(&reply_to, Bytes::from(reply)).await {
                    tracing::warn!("could not reply: {err}");
                }
                continue;
            }
            let dir = self.lock().hive_dir(&token).map(Path::to_owned);
            let Some(dir) = dir else {
                let reply = if self.lock().is_removed(&token) {
                    HubReply::Removed
                } else {
                    HubReply::NoHive
                };
                if let Err(err) = transport
                    .publish(&reply_to, Bytes::from(Envelope::encode(reply)?))
                    .await
                {
                    tracing::warn!("could not reply: {err}");
                }
                continue;
            };
            let spawn = || {
                spawn_worker(
                    token.clone(),
                    dir.clone(),
                    self.hubs.clone(),
                    self.activity.clone(),
                    transport.clone(),
                )
            };
            let worker = self.workers.entry(token.clone()).or_insert_with(spawn);
            if let Err(mpsc::SendError(message)) = worker.requests.send(message) {
                // Its thread has stopped, which a request's failing, or even panicking, can't
                // make it do: a fresh one takes the request.
                tracing::error!("hive {token}'s thread has stopped; starting another");
                let worker = spawn();
                if worker.requests.send(message).is_err() {
                    tracing::error!("hive {token}'s new thread has stopped too");
                }
                self.workers.insert(token, worker);
            }
        }
        Ok(())
    }

    async fn handle_hub_wide(&mut self, bytes: &[u8], max_payload: usize) -> HubWideReply {
        let request = match Envelope::<HubWideRequest>::decode(bytes) {
            Ok(request) => request,
            Err(err) => return HubWideReply::Error(fit_error(format!("{err:#}"), max_payload)),
        };
        let result = match request {
            HubWideRequest::Join(request) => self.lock().join(&request).map(|joined| {
                let verb = if joined.created { "created" } else { "joined" };
                tracing::info!(
                    "{} {verb} hive {} ({})",
                    request.machine,
                    joined.hive.name,
                    joined.reason
                );
                HubWideReply::Joined(joined)
            }),
            HubWideRequest::List => Ok(HubWideReply::Hives(self.lock().list())),
            HubWideRequest::Resolve { name } => {
                let hubs = self.lock();
                hubs.resolve(&name)
                    .map(|id| HubWideReply::Hive(hubs.info(&id).expect("resolved")))
            }
            HubWideRequest::Rename { name, to } => self.lock().rename(&name, &to).map(|info| {
                tracing::info!("renamed hive {name} to {to}");
                HubWideReply::Hive(info)
            }),
            HubWideRequest::Remove { name } => {
                let resolved = self.lock().resolve_exact(&name);
                match resolved {
                    Err(err) => Err(err),
                    Ok(id) => {
                        // Let the hive's thread finish what it has queued, and close its store.
                        if let Some(worker) = self.workers.remove(&id) {
                            drop(worker.requests);
                            tokio::task::spawn_blocking(move || worker.thread.join().ok())
                                .await
                                .ok();
                        }
                        self.activity().forget(&id);
                        self.lock().remove(&id).map(|info| {
                            tracing::info!("removed hive {}", info.name);
                            HubWideReply::Hive(info)
                        })
                    }
                }
            }
            HubWideRequest::Report { hive, report } => {
                if self.lock().hive_dir(&hive).is_some() {
                    self.activity().report(&hive, report, Instant::now());
                    Ok(HubWideReply::Noted)
                } else {
                    Err(format!("no hive {hive}"))
                }
            }
            HubWideRequest::Activity => {
                // Not both locks at once: the hives' threads take each alone.
                let hives = {
                    let hubs = self.lock();
                    hubs.list()
                        .into_iter()
                        .map(|info| {
                            let keys = hubs.machine_keys(&info.id).cloned().unwrap_or_default();
                            (info, keys)
                        })
                        .collect()
                };
                let version = env!("CARGO_PKG_VERSION");
                let mut activity = self.activity().snapshot(hives, version, Instant::now());
                // A reply too large to send would leave `musubi top` waiting for nothing.
                while Envelope::encode(HubWideReply::Activity(activity.clone()))
                    .is_ok_and(|reply| reply.len() > max_payload)
                    && activity.shrink()
                {}
                Ok(HubWideReply::Activity(activity))
            }
        };
        result.unwrap_or_else(|err| HubWideReply::Error(fit_error(err, max_payload)))
    }
}

fn lock_activity(activity: &Mutex<Activity>) -> std::sync::MutexGuard<'_, Activity> {
    activity.lock().unwrap_or_else(PoisonError::into_inner)
}

fn spawn_worker(
    id: String,
    dir: PathBuf,
    hubs: Arc<Mutex<HubDir>>,
    activity: Arc<Mutex<Activity>>,
    transport: Arc<dyn Transport>,
) -> Worker {
    let (requests, receiver) = mpsc::channel();
    let runtime = tokio::runtime::Handle::current();
    let head = head_subject(&id);
    let thread = std::thread::Builder::new()
        .name(format!("hive {id}"))
        .spawn(move || {
            // Everything this thread logs is about this hive. At error level, the span stays
            // on under any filter that shows anything.
            let _span = tracing::error_span!("hive", id = %id).entered();
            let mut service = None;
            while let Ok(message) = receiver.recv() {
                let limit = transport.max_payload();
                let started = Instant::now();
                // Whether the activity has counted the request, as it does once the request
                // is handled, even if what follows fails.
                let mut counted = false;
                let hive = Hive {
                    id: &id,
                    dir: &dir,
                    hubs: &hubs,
                    activity: &activity,
                };
                let served = std::panic::catch_unwind(AssertUnwindSafe(|| {
                    serve_one(&hive, &mut service, &message, limit, &mut counted)
                }));
                let reply = served.unwrap_or_else(|panic| {
                    // jj-lib panics on some malformed input, as a peer could send it. The
                    // hive's service may be left half-changed: the next request opens it
                    // afresh.
                    service = None;
                    Err(anyhow::anyhow!(
                        "the hub failed: {}",
                        panic_message(panic.as_ref())
                    ))
                });
                let (reply, notice, done) = match reply {
                    Ok(served) => (served.reply, served.notice, Ok(served.since)),
                    Err(err) => {
                        tracing::warn!("request failed: {err:#}");
                        let message = format!("{err:#}");
                        let error = HubReply::Error(fit_error(message.clone(), limit));
                        match Envelope::encode(error) {
                            Ok(reply) => (reply, None, Err(message)),
                            Err(_) => continue,
                        }
                    }
                };
                let (received, sent) = (message.payload.len(), reply.len());
                tracing::trace!(
                    "answered {received} bytes with {sent} in {:?}",
                    started.elapsed()
                );
                let reply_to = message.reply.as_deref().unwrap_or_default();
                if let Err(err) = runtime.block_on(transport.publish(reply_to, Bytes::from(reply)))
                {
                    tracing::warn!("could not reply: {err}");
                }
                if let Some(notice) = notice
                    && let Err(err) =
                        runtime.block_on(transport.publish(&head, Bytes::from(notice)))
                {
                    tracing::warn!("could not announce the new head: {err}");
                }
                let now = Instant::now();
                match done {
                    // What a new head brought takes reading its operations again, so it waits
                    // until the reply has gone.
                    Ok(Some(since)) => {
                        let summarized = std::panic::catch_unwind(AssertUnwindSafe(|| {
                            service
                                .as_ref()
                                .map(|service| summarize(service.hub().store(), &since))
                        }));
                        match summarized {
                            Ok(Some(Ok(accepted))) => {
                                lock_activity(&activity).summarized(&id, accepted, now);
                            }
                            Ok(Some(Err(err))) => {
                                tracing::warn!("could not summarize the new head: {err:#}");
                            }
                            Ok(None) => {}
                            Err(panic) => {
                                service = None;
                                tracing::warn!(
                                    "could not summarize the new head: {}",
                                    panic_message(panic.as_ref())
                                );
                            }
                        }
                    }
                    Ok(None) => {}
                    Err(message) => {
                        let (received, sent) = if counted { (0, 0) } else { (received, sent) };
                        lock_activity(&activity).failed(&id, received, sent, &message, now);
                    }
                }
            }
        })
        .expect("spawning a thread");
    Worker { requests, thread }
}

/// What a panic said, if it said it as text.
fn panic_message(panic: &(dyn std::any::Any + Send)) -> &str {
    panic
        .downcast_ref::<&str>()
        .copied()
        .or_else(|| panic.downcast_ref::<String>().map(String::as_str))
        .unwrap_or("a panic")
}

/// A request for a hive, answered.
struct Served {
    /// The encoded reply, and any encoded head notice.
    reply: Vec<u8>,
    notice: Option<Vec<u8>>,
    /// The head before it, if it accepted a new one.
    since: Option<OpId>,
}

/// What a hive's thread serves it with.
struct Hive<'a> {
    id: &'a str,
    dir: &'a Path,
    hubs: &'a Mutex<HubDir>,
    activity: &'a Mutex<Activity>,
}

/// Answers one request for a hive, opening its store first if need be, and updates the
/// hive's index when a new head is accepted. Counts the request in the hub's activity once
/// it is handled, and says so in `counted`.
fn serve_one(
    hive: &Hive<'_>,
    service: &mut Option<HubService>,
    message: &Message,
    max_payload: usize,
    counted: &mut bool,
) -> anyhow::Result<Served> {
    let Hive {
        id,
        dir,
        hubs,
        activity,
    } = *hive;
    let service = match service {
        Some(service) => service,
        None => {
            // Opened outside the lock, since opening reads every accepted operation, and made
            // again under it, if damaged.
            let store = match open_whole(dir)? {
                Opened::Whole(store) => *store,
                Opened::Damaged(why) => {
                    lock_activity(activity).troubled(
                        id,
                        &format!("its store was damaged, so the hub made it again: {why}"),
                        Instant::now(),
                    );
                    hubs.lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .remake(id, &why)?;
                    HubStore::open(dir)?
                }
            };
            tracing::info!("opened");
            service.insert(HubService::new(HubAdapter::new(store, dir)?, dir)?)
        }
    };
    let before = service.hub().store().head().1.clone();
    let (reply, notice) = service.handle_bytes(&message.payload, max_payload)?;
    let head = service.hub().store().head().0;
    let received = message.payload.len();
    lock_activity(activity).served(
        id,
        received,
        reply.len(),
        head,
        service.outcome(),
        Instant::now(),
    );
    *counted = true;
    let Some(notice) = notice else {
        return Ok(Served {
            reply,
            notice: None,
            since: None,
        });
    };
    let mut index = HiveIndex::default();
    match index.update(service.hub().store(), &before) {
        Ok(()) => {
            if let Err(err) = hubs
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .update_index(id, index)
            {
                tracing::warn!("could not save its index: {err:#}");
            }
        }
        Err(err) => tracing::warn!("could not index the new head: {err:#}"),
    }
    Ok(Served {
        reply,
        notice: Some(Envelope::encode(notice)?),
        since: Some(before),
    })
}
