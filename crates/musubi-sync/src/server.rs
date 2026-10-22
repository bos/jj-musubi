//! A hub serving every hive in its directory (see `musubi_hub::hub_dir`).
//!
//! One subscription, `musubi.*.rpc`, takes every request. Those for a hive go to that
//! hive's own thread, which opens its store on the first request and then answers its
//! requests one at a time, as [`HubService`] does; different hives never wait for each
//! other. Requests to `musubi.hub.rpc` ([`HUB_TOKEN`]) are about the hub as a whole:
//! joining, listing, renaming, and removing hives. A request for a hive the hub doesn't
//! have gets an error: only a join creates a hive.

use std::collections::HashMap;
use std::panic::AssertUnwindSafe;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::mpsc;

use bytes::Bytes;
use musubi_hub::hub_dir::HubDir;
use musubi_hub::index::HiveIndex;
use musubi_transport::Message;
use musubi_transport::Transport;

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
            workers: HashMap::new(),
        })
    }

    pub fn hive_count(&self) -> usize {
        self.lock().len()
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, HubDir> {
        self.hubs.lock().unwrap_or_else(PoisonError::into_inner)
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
                let error = format!("this hub has no hive {token}");
                let reply = HubReply::Error(fit_error(error, transport.max_payload()));
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
                let resolved = self.lock().resolve(&name);
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
                        self.lock().remove(&id).map(|info| {
                            tracing::info!("removed hive {}", info.name);
                            HubWideReply::Hive(info)
                        })
                    }
                }
            }
        };
        result.unwrap_or_else(|err| HubWideReply::Error(fit_error(err, max_payload)))
    }
}

fn spawn_worker(
    id: String,
    dir: PathBuf,
    hubs: Arc<Mutex<HubDir>>,
    transport: Arc<dyn Transport>,
) -> Worker {
    let (requests, receiver) = mpsc::channel();
    let runtime = tokio::runtime::Handle::current();
    let (rpc, head) = (rpc_subject(&id), head_subject(&id));
    let thread = std::thread::Builder::new()
        .name(format!("hive {id}"))
        .spawn(move || {
            // Everything this thread logs is about this hive. At error level, the span stays
            // on under any filter that shows anything.
            let _span = tracing::error_span!("hive", id = %id).entered();
            let mut service = None;
            while let Ok(message) = receiver.recv() {
                let limit = transport.max_payload();
                let started = std::time::Instant::now();
                let served = std::panic::catch_unwind(AssertUnwindSafe(|| {
                    serve_one(
                        &id,
                        &dir,
                        (&rpc, &head),
                        &mut service,
                        &hubs,
                        &message,
                        limit,
                    )
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
                let (reply, notice) = match reply {
                    Ok(result) => result,
                    Err(err) => {
                        tracing::warn!("request failed: {err:#}");
                        let error = HubReply::Error(fit_error(format!("{err:#}"), limit));
                        match Envelope::encode(error) {
                            Ok(reply) => (reply, None),
                            Err(_) => continue,
                        }
                    }
                };
                tracing::trace!(
                    "answered {} bytes with {} in {:?}",
                    message.payload.len(),
                    reply.len(),
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

/// Answers one request for a hive, opening its store first if need be, and updates the
/// hive's index when a new head is accepted. Returns the encoded reply and any encoded
/// head notice.
fn serve_one(
    id: &str,
    dir: &Path,
    (rpc, head): (&str, &str),
    service: &mut Option<HubService>,
    hubs: &Mutex<HubDir>,
    message: &Message,
    max_payload: usize,
) -> anyhow::Result<(Vec<u8>, Option<Vec<u8>>)> {
    let service = match service {
        Some(service) => service,
        None => {
            let adapter = HubAdapter::open(dir)?;
            tracing::info!("opened");
            service.insert(HubService::new(
                adapter,
                dir,
                rpc.to_owned(),
                head.to_owned(),
            )?)
        }
    };
    let before = service.hub().store().head().1.clone();
    let (reply, notice) = service.handle_bytes(&message.payload, max_payload)?;
    let Some(notice) = notice else {
        return Ok((reply, None));
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
    Ok((reply, Some(Envelope::encode(notice)?)))
}
