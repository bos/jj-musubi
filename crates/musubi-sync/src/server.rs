//! A hub serving every hive in its directory (see `musubi_hub::hub_dir`).
//!
//! One subscription, `<prefix>.*.rpc`, takes every request. Those for a hive go to that
//! hive's own thread, which opens its store on the first request and then answers its
//! requests one at a time, as [`HubService`] does; different hives never wait for each
//! other. Requests to `<prefix>.hub.rpc` ([`HUB_TOKEN`]) are about the hub as a whole:
//! joining, listing, renaming, and removing hives. A request for a hive the hub doesn't
//! have gets an error: only a join creates a hive.

use std::collections::HashMap;
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

pub struct HubServer {
    prefix: String,
    hubs: Arc<Mutex<HubDir>>,
    workers: HashMap<String, Worker>,
}

struct Worker {
    requests: mpsc::Sender<Message>,
    thread: std::thread::JoinHandle<()>,
}

impl HubServer {
    /// Opens the hub directory `dir`, which must exist.
    pub fn open(dir: &Path, prefix: &str) -> anyhow::Result<Self> {
        Ok(Self {
            prefix: prefix.to_owned(),
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
        let mut requests = transport
            .subscribe(&format!("{}.*.rpc", self.prefix))
            .await?;
        ready();
        while let Some(message) = requests.next().await {
            let Some(reply_to) = message.reply.clone() else {
                continue;
            };
            let token = message
                .subject
                .strip_prefix(&format!("{}.", self.prefix))
                .and_then(|rest| rest.strip_suffix(".rpc"))
                .unwrap_or_default()
                .to_owned();
            if token == HUB_TOKEN {
                let reply = self.handle_hub_wide(&message.payload).await;
                let reply = Envelope::encode(reply)?;
                if let Err(err) = transport.publish(&reply_to, Bytes::from(reply)).await {
                    tracing::warn!("could not reply: {err}");
                }
                continue;
            }
            let dir = self.lock().hive_dir(&token).map(Path::to_owned);
            let Some(dir) = dir else {
                let reply = HubReply::Error(format!("this hub has no hive {token}"));
                if let Err(err) = transport
                    .publish(&reply_to, Bytes::from(Envelope::encode(reply)?))
                    .await
                {
                    tracing::warn!("could not reply: {err}");
                }
                continue;
            };
            let worker = self.workers.entry(token.clone()).or_insert_with(|| {
                spawn_worker(
                    token.clone(),
                    dir,
                    &self.prefix,
                    self.hubs.clone(),
                    transport.clone(),
                )
            });
            if worker.requests.send(message).is_err() {
                tracing::error!("hive {token}'s thread has stopped");
                self.workers.remove(&token);
            }
        }
        Ok(())
    }

    async fn handle_hub_wide(&mut self, bytes: &[u8]) -> HubWideReply {
        let request = match Envelope::<HubWideRequest>::decode(bytes) {
            Ok(request) => request,
            Err(err) => return HubWideReply::Error(format!("{err:#}")),
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
        result.unwrap_or_else(HubWideReply::Error)
    }
}

fn spawn_worker(
    id: String,
    dir: PathBuf,
    prefix: &str,
    hubs: Arc<Mutex<HubDir>>,
    transport: Arc<dyn Transport>,
) -> Worker {
    let (requests, receiver) = mpsc::channel();
    let runtime = tokio::runtime::Handle::current();
    let rpc = format!("{prefix}.{id}.rpc");
    let head = format!("{prefix}.{id}.head");
    let thread = std::thread::Builder::new()
        .name(format!("hive {id}"))
        .spawn(move || {
            let mut service = None;
            while let Ok(message) = receiver.recv() {
                let limit = transport.max_payload();
                let reply = serve_one(
                    &id,
                    &dir,
                    (&rpc, &head),
                    &mut service,
                    &hubs,
                    &message,
                    limit,
                );
                let (reply, notice) = match reply {
                    Ok(result) => result,
                    Err(err) => {
                        tracing::warn!("hive {id}: request failed: {err:#}");
                        let error = HubReply::Error(format!("{err:#}"));
                        match Envelope::encode(error) {
                            Ok(reply) => (reply, None),
                            Err(_) => continue,
                        }
                    }
                };
                let reply_to = message.reply.as_deref().unwrap_or_default();
                if let Err(err) = runtime.block_on(transport.publish(reply_to, Bytes::from(reply)))
                {
                    tracing::warn!("hive {id}: could not reply: {err}");
                }
                if let Some(notice) = notice
                    && let Err(err) =
                        runtime.block_on(transport.publish(&head, Bytes::from(notice)))
                {
                    tracing::warn!("hive {id}: could not announce the new head: {err}");
                }
            }
        })
        .expect("spawning a thread");
    Worker { requests, thread }
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
            tracing::info!("opened hive {id}");
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
                tracing::warn!("hive {id}: could not save its index: {err:#}");
            }
        }
        Err(err) => tracing::warn!("hive {id}: could not index the new head: {err:#}"),
    }
    Ok((reply, Some(Envelope::encode(notice)?)))
}
