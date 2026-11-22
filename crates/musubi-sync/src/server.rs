//! A hub serving every hive in its directory (see `musubi_hub::hub_dir`).
//!
//! One subscription, `musubi.*.rpc`, takes every request. Those for a hive go to that hive's own
//! thread, which opens its store on the first request and then answers its requests one at a
//! time, as [`HubService`] does; different hives never wait for each other. A request whose
//! sender has stopped waiting for it by the time the thread comes to it goes unanswered, as if
//! lost, unless it uploads a chunk. Requests to `musubi.hub.rpc` ([`HUB_TOKEN`]) are about the
//! hub as a whole: joining, listing, renaming, pausing, resetting and removing hives. A request
//! for a hive the hub doesn't have gets an error: only a join creates a hive. One for a paused
//! hive gets [`HubReply::Paused`], and one for a hive reset since gets [`HubReply::Reset`].
//!
//! The hub keeps account of what it serves, and of what machines report of their syncing,
//! in memory, for `musubi top` (see `musubi_hub::activity`).

use std::collections::HashMap;
use std::collections::HashSet;
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
use musubi_hub::hub_dir::HiveId;
use musubi_hub::hub_dir::HiveInfo;
use musubi_hub::hub_dir::HubDir;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::JoinRefused;
use musubi_hub::hub_dir::JoinRequest;
use musubi_hub::hub_dir::Opened;
use musubi_hub::hub_dir::Refusal;
use musubi_hub::hub_dir::ResetOutcome;
use musubi_hub::hub_dir::open_whole;
use musubi_hub::index::HiveIndex;
use musubi_hub::store::HubStore;
use musubi_hub::store::StoreError;
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
use crate::wire::RELEASE;
use crate::wire::fit_error;
use crate::wire::head_subject;
use crate::wire::rpc_subject;
use crate::wire::rpc_token;

#[derive(Clone)]
pub struct HubServer {
    hubs: Arc<Mutex<HubDir>>,
    activity: Arc<Mutex<Activity>>,
    /// Taken before `hubs` when both are held, as a request for a hive is dispatched and a
    /// hive is taken out of service, so that no thread starts on a hive being removed.
    workers: Arc<Mutex<Workers>>,
    #[cfg(test)]
    hold: Option<Arc<tests::Hold>>,
}

#[derive(Default)]
struct Workers {
    serving: HashMap<HiveId, Worker>,
    /// The hives being removed or reset: their threads are finishing what they have queued,
    /// and requests for them are refused until they are gone.
    removing: HashSet<HiveId>,
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
            workers: Arc::default(),
            #[cfg(test)]
            hold: None,
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

    fn workers(&self) -> std::sync::MutexGuard<'_, Workers> {
        self.workers.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Serves until the transport's subscription ends, calling `ready` once subscribed.
    /// Needs a multi-threaded runtime: hive threads publish their replies through it.
    ///
    /// Requests about the hub as a whole are each answered by a task of their own, since
    /// some take a while: a removal waits for the hive's thread to finish, and a join looks
    /// in every hive's store. Meanwhile, every hive's requests go on being dispatched.
    pub async fn run(
        self,
        transport: Arc<dyn Transport>,
        ready: impl FnOnce(),
    ) -> anyhow::Result<()> {
        let mut requests = transport.subscribe(&rpc_subject("*")).await?;
        ready();
        let mut hub_wide = tokio::task::JoinSet::new();
        while let Some(message) = requests.next().await {
            while hub_wide.try_join_next().is_some() {}
            let Some(reply_to) = message.reply.clone() else {
                continue;
            };
            let token = rpc_token(&message.subject).unwrap_or_default().to_owned();
            if token == HUB_TOKEN {
                let server = self.clone();
                let transport = transport.clone();
                hub_wide.spawn(async move {
                    let max_payload = transport.max_payload();
                    let answered = tokio::task::spawn_blocking(move || {
                        server.handle_hub_wide(&message.payload, max_payload)
                    })
                    .await;
                    let reply = answered.unwrap_or_else(|err| {
                        let why = if err.is_panic() {
                            panic_message(err.into_panic().as_ref()).to_owned()
                        } else {
                            err.to_string()
                        };
                        tracing::error!("answering failed: {why}");
                        HubWideReply::Error(fit_error(
                            format!("the hub failed: {why}"),
                            max_payload,
                        ))
                    });
                    let reply = match Envelope::encode(reply) {
                        Ok(reply) => reply,
                        Err(err) => return tracing::error!("could not encode a reply: {err:#}"),
                    };
                    if let Err(err) = transport.publish(&reply_to, Bytes::from(reply)).await {
                        tracing::warn!("could not reply: {err}");
                    }
                });
                continue;
            }
            if let Some(reply) = self.route(&token, message, &transport)
                && let Err(err) = transport
                    .publish(&reply_to, Bytes::from(Envelope::encode(reply)?))
                    .await
            {
                tracing::warn!("could not reply: {err}");
            }
        }
        while hub_wide.join_next().await.is_some() {}
        Ok(())
    }

    /// Hands a request for hive `token` to its thread, starting one if need be, or returns
    /// the answer if the hub doesn't serve the hive.
    fn route(
        &self,
        token: &str,
        message: Message,
        transport: &Arc<dyn Transport>,
    ) -> Option<HubReply> {
        let id = HiveId::from(token.to_owned());
        let mut workers = self.workers();
        if workers.removing.contains(&id) {
            // Not `Removed` or `Reset` yet, which tell its machines to leave: it may fail.
            return Some(HubReply::Error(
                "this hive is being removed or reset".to_owned(),
            ));
        }
        let dir = {
            let hubs = self.lock();
            match hubs.hive_dir(&id) {
                Some(dir) => dir.to_owned(),
                None if let Some(reset) = hubs.reset_of(&id) => {
                    return Some(HubReply::Reset(reset));
                }
                None if hubs.is_removed(&id) => return Some(HubReply::Removed),
                None => return Some(HubReply::NoHive),
            }
        };
        let spawn = || {
            spawn_worker(
                id.clone(),
                dir.clone(),
                self.hubs.clone(),
                self.activity.clone(),
                transport.clone(),
                #[cfg(test)]
                None,
                #[cfg(test)]
                self.hold.clone(),
            )
        };
        let worker = workers.serving.entry(id.clone()).or_insert_with(spawn);
        if let Err(mpsc::SendError(message)) = worker.requests.send(message) {
            // Its thread has stopped, which a request's failing, or even panicking, can't
            // make it do: a fresh one takes the request.
            tracing::error!("hive {token}'s thread has stopped; starting another");
            let worker = spawn();
            if worker.requests.send(message).is_err() {
                tracing::error!("hive {token}'s new thread has stopped too");
            }
            workers.serving.insert(id, worker);
        }
        None
    }

    /// Answers a request about the hub as a whole. Blocks, perhaps for long: see
    /// [`Self::run`].
    fn handle_hub_wide(&self, bytes: &[u8], max_payload: usize) -> HubWideReply {
        let request = match Envelope::<HubWideRequest>::decode(bytes) {
            Ok(request) => request,
            Err(err) => return HubWideReply::Error(fit_error(format!("{err:#}"), max_payload)),
        };
        let result = match request {
            HubWideRequest::Join(request) if matches!(request.choice, JoinChoice::Reset { .. }) => {
                self.reset(&request)
            }
            HubWideRequest::Join(request)
                if let Some(reset) = self.lock().reset_among(&request) =>
            {
                Ok(HubWideReply::Reset(reset))
            }
            // The copy that reset the hive, finishing what a crash stopped, as a reset does.
            HubWideRequest::Join(request) if self.lock().finishing_reset(&request) => {
                let finish = match request.choice.clone() {
                    JoinChoice::Remake { id, .. } => JoinRequest {
                        choice: JoinChoice::Reset {
                            id,
                            base: String::new(),
                            force: true,
                        },
                        ..request
                    },
                    _ => request,
                };
                self.reset(&finish)
            }
            HubWideRequest::Join(request) => {
                // Looking in the stores takes a while, and needn't hold up the hub.
                let probe = self.lock().probe(&request);
                let probed = probe.run();
                // A reset can land between the check above and this lock.
                match self.lock().join_probed(&request, &probed) {
                    Ok(joined) => {
                        let verb = if joined.created { "created" } else { "joined" };
                        tracing::info!(
                            "{} {verb} hive {} ({})",
                            request.machine,
                            joined.hive.name,
                            joined.reason
                        );
                        Ok(HubWideReply::Joined(joined))
                    }
                    Err(JoinRefused::Reset(reset)) => Ok(HubWideReply::Reset(reset)),
                    Err(JoinRefused::Refused(message)) => Err(message),
                }
            }
            HubWideRequest::PrepareClone {
                hive,
                backend,
                remote_bindings,
            } => self
                .lock()
                .prepare_clone(&hive, backend, &remote_bindings)
                .map(HubWideReply::Hive),
            HubWideRequest::List => Ok(HubWideReply::Hives(self.lock().list())),
            HubWideRequest::Resolve { name } => {
                let hubs = self.lock();
                hubs.resolve(&name).and_then(|id| {
                    hubs.check_remote_consistency(&id)?;
                    Ok(HubWideReply::Hive(hubs.info(&id).expect("resolved")))
                })
            }
            HubWideRequest::Rename { name, to } => {
                self.lock().rename(&name, &to).map(|(from, hive)| {
                    tracing::info!("renamed hive {from} to {to}");
                    HubWideReply::Renamed { from, hive }
                })
            }
            HubWideRequest::Remove { name } => self.remove(&name).map(HubWideReply::Hive),
            HubWideRequest::Pause { hive, .. } | HubWideRequest::Unpause { hive }
                if let Some(reset) = self.lock().reset_of(&hive) =>
            {
                Ok(HubWideReply::Reset(reset))
            }
            HubWideRequest::Pause { hive, machine } => {
                self.lock().pause(&hive, &machine).map(|(hive, before)| {
                    if before.is_none() {
                        tracing::info!("{machine} paused hive {}", hive.name);
                    }
                    HubWideReply::PauseChanged { hive, before }
                })
            }
            HubWideRequest::Unpause { hive } => self.lock().unpause(&hive).map(|(hive, before)| {
                if before.is_some() {
                    tracing::info!("hive {} is no longer paused", hive.name);
                }
                HubWideReply::PauseChanged { hive, before }
            }),
            HubWideRequest::Report { hive, report } => {
                // Under the hub, so that a removal can't forget the hive's activity between
                // the two: nothing takes the hub while holding the activity.
                let hubs = self.lock();
                match hubs.info(&hive) {
                    Some(info) => {
                        self.activity().report(&hive, report, Instant::now());
                        Ok(HubWideReply::Hive(info))
                    }
                    None => Err(format!("no hive {hive}")),
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
                let mut activity = self.activity().snapshot(hives, RELEASE, Instant::now());
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

    /// Removes the hive whose name or id is exactly `name`, once its thread has finished
    /// what it has queued and closed its store.
    fn remove(&self, name: &str) -> Result<HiveInfo, Refusal> {
        let (id, worker) = {
            let mut workers = self.workers();
            let id = self.lock().resolve_exact(name)?;
            if !workers.removing.insert(id.clone()) {
                return Err(format!("hive {name} is already being removed"));
            }
            let worker = workers.serving.remove(&id);
            (id, worker)
        };
        // However the removal ends: failing, the hive is served again, by a new thread.
        let _removing = Removing {
            server: self,
            id: &id,
        };
        if let Some(worker) = worker {
            drop(worker.requests);
            worker.thread.join().ok();
        }
        let removed = self.lock().remove(&id);
        if let Ok(info) = &removed {
            self.activity().forget(&id);
            tracing::info!("removed hive {}", info.name);
        }
        removed
    }
}

impl HubServer {
    /// Resets the hive `request` asks to (`HubDir::reset`), once its thread has finished what
    /// it has queued, as a push the hub took before the hive was paused, and closed its store.
    fn reset(&self, request: &JoinRequest) -> Result<HubWideReply, Refusal> {
        let JoinChoice::Reset { id, .. } = &request.choice else {
            return Err("not a reset".to_owned());
        };
        let worker = {
            let mut workers = self.workers();
            // A hive reset already answers at once.
            if self.lock().hive_dir(id).is_some() {
                if !workers.removing.insert(id.clone()) {
                    return Err("this hive is being removed or reset".to_owned());
                }
                Some(workers.serving.remove(id))
            } else {
                None
            }
        };
        let removing = worker.is_some().then_some(Removing { server: self, id });
        if let Some(Some(worker)) = worker {
            drop(worker.requests);
            worker.thread.join().ok();
        }
        let outcome = self.lock().reset(request)?;
        Ok(match outcome {
            ResetOutcome::Joined(joined) => {
                if removing.is_some() {
                    self.activity().forget(id);
                }
                tracing::info!(
                    "{} reset hive {} as {}",
                    request.machine,
                    joined.hive.name,
                    joined.hive.id
                );
                HubWideReply::Joined(joined)
            }
            ResetOutcome::Reset(reset) => HubWideReply::Reset(reset),
        })
    }
}

/// A hive being removed, which stops being so when this is dropped.
struct Removing<'a> {
    server: &'a HubServer,
    id: &'a HiveId,
}

impl Drop for Removing<'_> {
    fn drop(&mut self) {
        self.server.workers().removing.remove(self.id);
    }
}

fn lock_activity(activity: &Mutex<Activity>) -> std::sync::MutexGuard<'_, Activity> {
    activity.lock().unwrap_or_else(PoisonError::into_inner)
}

fn spawn_worker(
    id: HiveId,
    dir: PathBuf,
    hubs: Arc<Mutex<HubDir>>,
    activity: Arc<Mutex<Activity>>,
    transport: Arc<dyn Transport>,
    #[cfg(test)] hooks: Option<Arc<tests::WorkerHooks>>,
    #[cfg(test)] hold: Option<Arc<tests::Hold>>,
) -> Worker {
    let (requests, receiver) = mpsc::channel::<Message>();
    let runtime = tokio::runtime::Handle::current();
    let head = head_subject(id.as_str());
    let thread = std::thread::Builder::new()
        .name(format!("hive {id}"))
        .spawn(move || {
            // Everything this thread logs is about this hive. At error level, the span stays
            // on under any filter that shows anything.
            let _span = tracing::error_span!("hive", id = %id).entered();
            let mut slot = Slot::Closed;
            while let Ok(message) = receiver.recv() {
                #[cfg(test)]
                if let Some(hold) = &hold {
                    hold.wait(&id);
                }
                // A request that waited here, behind others, past its sender's deadline has
                // nobody to answer: its sender has asked again, or given up. Working it out
                // anyway, as for a fetch that takes long to prepare, would hold up the repeat
                // and the requests of other machines, and could take as long again for each
                // repeat that waited behind it. A chunk of an upload is still taken: its bytes
                // have crossed the link already.
                if message.abandoned(Instant::now())
                    && !HubService::worth_handling_unheard(&message.payload)
                {
                    tracing::debug!("let go of a request its sender stopped waiting for");
                    continue;
                }
                let limit = transport.max_payload();
                // Checked here, rather than as the request is dispatched, so that a request
                // queued before a pause and taken after it is refused too.
                let paused = hubs
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .paused(&id)
                    .cloned();
                if let Some(pause) = paused {
                    answer_paused(&runtime, &*transport, &message, pause);
                    continue;
                }
                let started = Instant::now();
                // Whether the activity has counted the request, as it does once the request
                // is handled, even if what follows fails.
                let mut counted = false;
                let hive = Hive {
                    id: &id,
                    dir: &dir,
                    hubs: &hubs,
                    activity: &activity,
                    #[cfg(test)]
                    hooks: hooks.as_deref(),
                };
                let served = std::panic::catch_unwind(AssertUnwindSafe(|| {
                    serve_one(&hive, &mut slot, &message, limit, &mut counted)
                }));
                let reply = served.unwrap_or_else(|panic| {
                    // jj-lib and jj-core panic on some malformed input, as a peer could send
                    // it. The hive's service may be left half-changed: the next request opens
                    // it afresh.
                    slot.let_go();
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
                // A failure is counted before the reply goes, so that whoever asks next, as
                // `musubi top` does, finds it counted.
                if let Err(message) = &done {
                    let (received, sent) = if counted { (0, 0) } else { (received, sent) };
                    lock_activity(&activity).failed(&id, received, sent, message, Instant::now());
                }
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
                // What a new head brought takes reading its operations again, so it waits
                // until the reply has gone.
                if let Ok(Some(since)) = done {
                    let summarized = std::panic::catch_unwind(AssertUnwindSafe(|| {
                        slot.service()
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
                            slot.let_go();
                            tracing::warn!(
                                "could not summarize the new head: {}",
                                panic_message(panic.as_ref())
                            );
                        }
                    }
                }
            }
        })
        .expect("spawning a thread");
    Worker { requests, thread }
}

/// Answers `message`, a request for a paused hive, that it is paused, without opening the
/// hive's store.
fn answer_paused(
    runtime: &tokio::runtime::Handle,
    transport: &dyn Transport,
    message: &Message,
    pause: musubi_hub::hub_dir::Pause,
) {
    let Ok(reply) = Envelope::encode(HubReply::Paused(pause)) else {
        return;
    };
    let reply_to = message.reply.as_deref().unwrap_or_default();
    if let Err(err) = runtime.block_on(transport.publish(reply_to, Bytes::from(reply))) {
        tracing::warn!("could not reply: {err}");
    }
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
    id: &'a HiveId,
    dir: &'a Path,
    hubs: &'a Mutex<HubDir>,
    activity: &'a Mutex<Activity>,
    #[cfg(test)]
    hooks: Option<&'a tests::WorkerHooks>,
}

/// A hive's service, as its thread holds it between requests.
enum Slot {
    Closed,
    Open(Box<HubService>),
}

impl Slot {
    fn service(&self) -> Option<&HubService> {
        match self {
            Self::Closed => None,
            Self::Open(service) => Some(service),
        }
    }

    /// The hive's service, opening its store first if need be.
    fn open(&mut self, hive: &Hive<'_>) -> anyhow::Result<&mut HubService> {
        if let Self::Closed = self {
            *self = Self::Open(Box::new(open_service(hive)?));
            #[cfg(test)]
            if let Some(hooks) = hive.hooks {
                hooks.opened();
            }
        }
        let Self::Open(service) = self else {
            unreachable!("opened above")
        };
        Ok(service)
    }

    /// Drops the service, which a panic may have left half-changed: the next request opens
    /// the store afresh.
    fn let_go(&mut self) {
        *self = Self::Closed;
    }
}

/// Opens a hive's store, outside the lock, since opening reads every accepted operation, and
/// makes it again under the lock, if damaged.
fn open_service(hive: &Hive<'_>) -> anyhow::Result<HubService> {
    let Hive {
        id,
        dir,
        hubs,
        activity,
        ..
    } = *hive;
    let store = match open_whole(dir)? {
        Opened::Whole(store) => *store,
        Opened::Damaged(why) => {
            // Compatibility until 2027-02-21: remove with `StoreError::RecordsLog`, keeping
            // the second message.
            let what = if matches!(why, StoreError::RecordsLog(_)) {
                "the hub made it again for this release"
            } else {
                "its store was damaged, so the hub made it again"
            };
            lock_activity(activity).troubled(id, &format!("{what}: {why}"), Instant::now());
            hubs.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .remake(id, &why)?;
            HubStore::open(dir)?
        }
    };
    tracing::info!("opened");
    HubService::new(HubAdapter::new(store, dir)?, dir)
}

/// Answers one request for a hive, opening its store first if need be, and updates the hive's
/// index when a new head is accepted. Counts the request in the hub's activity once it is
/// handled, and says so in `counted`, which outlives a panic.
fn serve_one(
    hive: &Hive<'_>,
    slot: &mut Slot,
    message: &Message,
    max_payload: usize,
    counted: &mut bool,
) -> anyhow::Result<Served> {
    let Hive {
        id,
        hubs,
        activity,
        #[cfg(test)]
        hooks,
        ..
    } = *hive;
    let service = slot.open(hive)?;
    let before = service.hub().store().head().1.clone();
    let (reply, notice) = service.handle_bytes(&message.payload, max_payload)?;
    #[cfg(test)]
    if let Some(hooks) = hooks {
        hooks.handled(service, notice.as_ref());
    }
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

#[cfg(test)]
mod tests;
