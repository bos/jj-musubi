//! A node's view of a remote hub: protocol requests in, replies out, with attachments and
//! oversized messages moved underneath. A small attachment travels inline in its message; a
//! larger one as a chunked blob, with several chunks in flight at once, so that a transfer
//! costs about one round trip per window of chunks rather than one per chunk.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::SystemTime;

use bytes::Bytes;
use futures::StreamExt as _;
use futures::future::BoxFuture;
use futures::stream::FuturesOrdered;
use jj_lib::object_id::ObjectId as _;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_transport::Transport;
use musubi_transport::TransportError;

use crate::Attachment;
use crate::OpId;
use crate::blobs::BlobId;
use crate::blobs::BlobStore;
use crate::blobs::Received;
use crate::progress::Activity;
use crate::progress::Progress;
use crate::wire::Envelope;
use crate::wire::HubReply;
use crate::wire::HubRequest;
use crate::wire::WireAttachment;
use crate::wire::chunk_size;
use crate::wire::inline_limit;
use crate::wire::map_reply;
use crate::wire::map_request;

/// Chunks of one blob in flight at once, at most: enough to keep a link with a long round trip
/// busy, without queueing much at the hub, which answers one request at a time. Fewer on a
/// link too slow to carry this many before their deadline (`RemoteHub::window`).
pub const WINDOW: usize = 8;

/// How many windows in a row must all come back for the next to have one more chunk, once
/// one has been cut short: growing at once would cut every other window short, on a link
/// that carries fewer than [`WINDOW`] chunks before their deadline.
const GROW_AFTER: usize = 4;

/// How many uploads a node remembers how far the hub had got with, for calls that failed
/// before the hub had all of them.
const TOLD: usize = 32;

/// Windows of chunks a call moves at which it opens a connection of its own for them, if it
/// may: below that, the transfer is over about as soon as a new connection, an ssh, would
/// have started.
const OWN_CONNECTION_WINDOWS: u64 = 2;

/// Opens a connection to the hub of the call's own, for a call that moves enough chunks to be
/// worth it, so that a large transfer neither holds up the small requests of others sharing
/// the node's connection nor waits behind theirs, and transfers at once each have one.
pub type OpenConnection =
    Arc<dyn Fn() -> BoxFuture<'static, anyhow::Result<Arc<dyn Transport>>> + Send + Sync>;

/// That the hub doesn't have the hive asked about: the error a sync fails with then, which
/// the daemon looks for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HiveGone {
    /// The hub has no record of it: it lost it, or isn't the hub the repository was part of.
    Missing,
    /// `musubi hub remove` removed it.
    Removed,
}

impl std::fmt::Display for HiveGone {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Missing => {
                "the hub has no record of this repository's hive; if it's the right hub, \
                 `musubi join` in this repository makes the hive again"
            }
            Self::Removed => "this repository's hive was removed from the hub",
        })
    }
}

impl std::error::Error for HiveGone {}

impl HiveGone {
    /// Whether `err` comes of the hub not having the hive, and which way.
    pub fn of(err: &anyhow::Error) -> Option<Self> {
        err.chain()
            .find_map(|cause| cause.downcast_ref::<Self>().copied())
    }
}

/// The error a reply stands for when it isn't one the request expects.
fn unexpected(reply: HubReply) -> anyhow::Error {
    match reply {
        HubReply::Error(err) => anyhow::anyhow!("hub: {err}"),
        HubReply::NoHive => HiveGone::Missing.into(),
        HubReply::Removed => HiveGone::Removed.into(),
        other => anyhow::anyhow!("unexpected reply {other:?}"),
    }
}

/// How many times a transfer may start over. The hub starts an upload over only after
/// discarding it as abandoned, or when what it has fails the hash check, and a download
/// starts over only when what came fails it; a blob that keeps failing it won't pass by being
/// sent again.
const RESTARTS: usize = 3;

/// How many times in a row a node sends a protocol request again when no reply comes in
/// time, and how many times in a row it tries a download again that timed out, without a
/// blob going further meanwhile. The hub answers one at a time, and a reply can take it
/// longer than the timeout to prepare, as for a node catching up on a large history: it
/// answers the repeat with the reply it prepared, once it has, so a repeat that comes then
/// gets it at once. A transfer that times out having gone further than ever, on a link too
/// slow to carry a window before its deadline, goes on as long as it does.
const RESENDS: u32 = 19;

/// Whether `err` is a request timing out.
fn timed_out(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| {
        matches!(
            cause.downcast_ref::<TransportError>(),
            Some(TransportError::Timeout)
        )
    })
}

/// How long a node keeps a blob nothing has touched: a partial download, which a later call
/// can resume if the hub prepares the same blob again, as after a night asleep, or a blob a
/// crash left behind.
const UNUSED_BLOB_LIFETIME: Duration = Duration::from_secs(24 * 3600);

pub struct RemoteHub {
    transport: Arc<dyn Transport>,
    /// Opens a call's own connection, for a large transfer; without it, every transfer
    /// shares `transport`.
    open: Option<OpenConnection>,
    rpc_subject: String,
    blobs: BlobStore,
    timeout: Duration,
    progress: Progress,
    /// How much of each blob being uploaded the hub last said it had, or that it had all of
    /// it, most recent last, for the upload's next attempt to go on from: from the start, a
    /// link too slow to carry a window of chunks before their deadline would carry again,
    /// each time, chunks the hub has, and time out before any it lacks. A download goes on
    /// from what it has received.
    told: Mutex<Vec<(BlobId, u64)>>,
    /// How many chunks to keep in flight: [`WINDOW`], or as many as came back before their
    /// deadline when last some didn't, growing again by one after each [`GROW_AFTER`]
    /// windows in a row that all come back, counted in `full`. Chunks that miss their
    /// deadline still take the link's time, delaying the next attempt's.
    window: AtomicUsize,
    full: AtomicUsize,
}

impl RemoteHub {
    pub fn new(
        transport: Arc<dyn Transport>,
        rpc_subject: String,
        blob_dir: &Path,
        timeout: Duration,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            transport,
            open: None,
            rpc_subject,
            blobs: BlobStore::open(blob_dir)?,
            timeout,
            progress: Progress::default(),
            told: Mutex::new(vec![]),
            window: AtomicUsize::new(WINDOW),
            full: AtomicUsize::new(0),
        })
    }

    /// Records what its calls are doing in `progress`.
    #[must_use]
    pub fn with_progress(mut self, progress: Progress) -> Self {
        self.progress = progress;
        self
    }

    pub fn progress(&self) -> &Progress {
        &self.progress
    }

    /// Moves a large transfer on a connection of its own, which `open` opens.
    #[must_use]
    pub fn with_own_connections(mut self, open: OpenConnection) -> Self {
        self.open = Some(open);
        self
    }

    /// Sends one protocol request and returns the reply, with any bundle in it downloaded,
    /// and deleted once nothing refers to it. A download the call leaves partway stays for a
    /// later call to resume, for a day. Be done with one reply before a call that may
    /// download the same blob: the two would share its file.
    pub async fn call(
        &self,
        request: Request<OpId, Attachment>,
    ) -> anyhow::Result<Reply<OpId, Attachment>> {
        self.blobs.sweep(SystemTime::now() - UNUSED_BLOB_LIFETIME);
        let mut inline_left = inline_limit(self.transport.max_payload());
        let mut uploads = Uploads {
            blobs: &self.blobs,
            ids: vec![],
        };
        let mut upload_len = 0;
        let request = map_request(
            request,
            |id| id.to_bytes(),
            |attachment| {
                WireAttachment::of(&attachment, &mut inline_left, |path| {
                    let (blob, len) = self.blobs.insert_file(path)?;
                    // Once, though the request names it twice: the hub takes it once.
                    if !uploads.ids.contains(&blob) {
                        upload_len += len;
                    }
                    uploads.ids.push(blob);
                    Ok((blob, len))
                })
            },
        )?;
        let bytes = Envelope::encode(HubRequest::Protocol(request))?;
        // A request too large to send whole goes as a blob.
        let mut whole = None;
        if bytes.len() > self.transport.max_payload() {
            let (blob, len) = self.blobs.insert_bytes(&bytes)?;
            let upload = Uploads {
                blobs: &self.blobs,
                ids: vec![blob],
            };
            whole = Some((upload, len));
        }
        let mut attempt = Attempt {
            bytes: &bytes,
            uploads: &uploads.ids,
            upload_len,
            whole: whole.as_ref().map(|(upload, len)| (upload.ids[0], *len)),
        };
        let mut lanes = Lanes::new(self);
        let mut furthest = Furthest::default();
        let mut resends = 0;
        let mut asked = false;
        let reply = loop {
            let further = furthest.further;
            match self
                .ask(&attempt, &mut lanes, &mut asked, &mut furthest)
                .await
            {
                Err(err) if timed_out(&err) && furthest.further > further => {
                    resends = 0;
                    tracing::debug!("no reply in time, having moved some chunks; going on");
                }
                Err(err) if resends < RESENDS && timed_out(&err) => {
                    resends += 1;
                    tracing::debug!("no reply in time; asking again ({resends} of {RESENDS})");
                }
                reply => break reply?,
            }
            // Once the request has gone, the hub has what it names, until it answers it, and
            // answers a repeat as before without them, unless the hive has changed since: then
            // the call fails, and the sync starts over.
            if asked {
                attempt.uploads = &[];
                attempt.upload_len = 0;
            }
        };
        self.receive(reply, &mut lanes, &mut furthest).await
    }

    /// Sends a request once, with what it uploads, and returns the hub's reply, which may
    /// be a blob to download. A request too large to send whole goes again each time: the
    /// hub lets go of it once it has it. Sets `asked` once the request goes.
    async fn ask(
        &self,
        attempt: &Attempt<'_>,
        lanes: &mut Lanes<'_>,
        asked: &mut bool,
        furthest: &mut Furthest,
    ) -> anyhow::Result<HubReply> {
        let lane = lanes.lane(attempt.upload_len).await;
        if attempt.upload_len > 0 {
            self.progress.set(Activity::Sending {
                done: 0,
                total: attempt.upload_len,
            });
        }
        let mut kept = Kept::default();
        self.upload_all(attempt.uploads, &*lane, 0, &mut kept, furthest)
            .await?;
        let bytes = match attempt.whole {
            None => attempt.bytes.to_vec(),
            Some((blob, len)) => {
                self.progress.set(Activity::Sending {
                    done: 0,
                    total: len,
                });
                self.upload_all(&[blob], &*lanes.lane(len).await, 0, &mut kept, furthest)
                    .await?;
                Envelope::encode(HubRequest::Indirect { blob })?
            }
        };
        self.progress.set(Activity::Asking);
        *asked = true;
        // The hub lets go of them once it has the request.
        self.forget(attempt.uploads);
        if let Some((blob, _)) = attempt.whole {
            self.forget(&[blob]);
        }
        self.exchange(&*self.transport, bytes).await
    }

    /// Downloads what the hub's `reply` names, and returns it, as [`Self::call`] does. A
    /// download that times out goes on where it left off ([`Self::download_patiently`]),
    /// rather than asking again, which once the hive has moved on would have the hub work the
    /// reply out afresh, in blobs of its own.
    async fn receive(
        &self,
        mut reply: HubReply,
        lanes: &mut Lanes<'_>,
        furthest: &mut Furthest,
    ) -> anyhow::Result<Reply<OpId, Attachment>> {
        // Deleted when the call ends, but for those the reply refers to, which go once the
        // caller is done with it.
        let mut downloads = Downloads::default();
        if let HubReply::Indirect { blob, len } = reply {
            self.progress.set(Activity::Receiving {
                done: 0,
                total: len,
            });
            let lane = lanes.lane(len).await;
            let path = self
                .download_patiently(&blob, len, &*lane, 0, &[], furthest)
                .await?;
            let path = downloads.hold(blob, path)?;
            reply = Envelope::<HubReply>::decode(&std::fs::read(&*path)?)?;
        }
        let reply = match reply {
            HubReply::Protocol(reply) => reply,
            other => return Err(unexpected(other)),
        };
        let mut blobs = reply_blobs(&reply);
        // Once, though the reply names it twice: each path deletes its file.
        blobs.sort();
        blobs.dedup();
        // The lengths the hub claims set progress, the lane, and which chunks a download asks
        // for, but a download ends by the chunks it gets, so a claim past `u64::MAX` saturates.
        let total = blobs
            .iter()
            .fold(0, |total: u64, (_, len)| total.saturating_add(*len));
        let lane = lanes.lane(total).await;
        if total > 0 {
            self.progress.set(Activity::Receiving { done: 0, total });
        }
        let mut received = 0;
        for (at, &(blob, len)) in blobs.iter().enumerate() {
            let later: Vec<BlobId> = blobs[at + 1..].iter().map(|(id, _)| *id).collect();
            let path = self
                .download_patiently(&blob, len, &*lane, received, &later, furthest)
                .await?;
            received = received.saturating_add(len);
            downloads.hold(blob, path)?;
        }
        // Handling the reply imports its bundles.
        if total > 0 {
            self.progress.set(Activity::Importing);
        }
        map_reply(reply, OpId::new, |attachment| {
            attachment.into_attachment(&self.blobs, |blob| {
                let path = downloads.held(&blob).expect("downloaded above");
                Ok(Attachment::Bundle(path))
            })
        })
    }

    async fn exchange(
        &self,
        transport: &dyn Transport,
        bytes: Vec<u8>,
    ) -> anyhow::Result<HubReply> {
        let reply = transport
            .request(&self.rpc_subject, Bytes::from(bytes), self.timeout)
            .await?;
        Envelope::<HubReply>::decode(&reply)
    }

    /// Uploads `blobs`, one after another, as [`Self::upload`] does, then any of those
    /// uploaded before that the hub lost meanwhile, keeping them all in `kept`. `sent` bytes of
    /// the transfer went before them.
    async fn upload_all(
        &self,
        blobs: &[BlobId],
        transport: &dyn Transport,
        mut sent: u64,
        kept: &mut Kept,
        furthest: &mut Furthest,
    ) -> anyhow::Result<()> {
        let mut queue: Vec<BlobId> = blobs.iter().rev().copied().collect();
        let mut lost = 0;
        while let Some(blob) = queue.pop() {
            sent += self.upload(&blob, transport, sent, kept, furthest).await?;
            for blob in kept.lost.drain(..) {
                lost += 1;
                anyhow::ensure!(
                    lost <= RESTARTS,
                    "the hub lost {lost} uploads while others went"
                );
                queue.push(blob);
            }
        }
        Ok(())
    }

    /// Uploads a blob in chunks, a window at a time, from where the hub last said it was in
    /// it, as when an earlier attempt timed out, or the start. Every reply says how far the
    /// hub has got, so a window from too far back, as when replies were lost, and one from too
    /// far on, as when the hub started over, after a hash mismatch or after discarding the
    /// upload as abandoned, goes on from what it reports. Keeps the blobs in `kept`, uploaded
    /// already for the same request, at the hub meanwhile ([`Self::beside`]), and puts this
    /// one among them once the hub has it. Records in `furthest` how far it got. Returns its
    /// length; `sent` bytes of the transfer went before it.
    async fn upload(
        &self,
        blob: &BlobId,
        transport: &dyn Transport,
        sent: u64,
        kept: &mut Kept,
        furthest: &mut Furthest,
    ) -> anyhow::Result<u64> {
        let chunk = chunk_size(transport.max_payload());
        let (total, _) = self.blobs.read(blob, 0, 0)?;
        let mut offset = self.told(blob);
        let mut restarts = 0;
        loop {
            let mut acks = FuturesOrdered::new();
            for next in window(offset, total, chunk as u64, self.window()) {
                let (_, data) = self.blobs.read_chunk(blob, next, chunk)?;
                let request = HubRequest::PutChunk {
                    blob: *blob,
                    total,
                    offset: next,
                    data,
                };
                acks.push_back(self.exchange(transport, Envelope::encode(request)?));
            }
            // The hub may take a window's chunks in any order, so go on from the furthest it
            // reported, or none once it has the blob. If it started over during the window,
            // that is too far, and the next window, none of which it can take, finds out.
            let acked = async {
                let mut reported = 0;
                let mut heard = 0;
                while let Some(ack) = acks.next().await {
                    let ack = ack.inspect_err(|err| self.missed(heard, err))?;
                    heard += 1;
                    match ack {
                        HubReply::ChunkAck { complete: true, .. } => {
                            furthest.raise(*blob, total);
                            self.tell(blob, total);
                            self.progress.moved(sent + total);
                            return Ok(None);
                        }
                        HubReply::ChunkAck { received, .. } => {
                            anyhow::ensure!(
                                received <= total,
                                "the hub claims {received} bytes of {blob:?}, which is {total} \
                                 bytes long"
                            );
                            furthest.raise(*blob, received);
                            reported = reported.max(received);
                            self.tell(blob, reported);
                            self.progress.moved(sent + reported);
                        }
                        other => return Err(unexpected(other)),
                    }
                }
                Ok(Some(reported))
            };
            let keeps = kept
                .blobs
                .iter()
                .map(|&(blob, total)| HubRequest::PutChunk {
                    blob,
                    total,
                    offset: total,
                    data: vec![],
                })
                .collect();
            let (replies, acked) = self.beside(transport, keeps, acked).await;
            kept.check(self, replies);
            let Some(reported) = acked? else {
                kept.add(*blob, total);
                return Ok(total);
            };
            self.widen();
            // The chunk at `offset` takes the hub further, unless it started over.
            if reported <= offset {
                restarts += 1;
                anyhow::ensure!(
                    restarts <= RESTARTS,
                    "the hub started over on {blob:?} {restarts} times"
                );
            }
            offset = reported;
        }
    }

    /// Runs `work`, which moves chunks of one blob, with requests in flight beside it, and
    /// ahead of its own, each a chunk that moves nothing of another blob, which the hub takes
    /// as it takes any chunk: it renews the blob ([`crate::blobs::RENEW_AFTER`]), and says
    /// whether it has it. The hub sweeps a blob that no chunk has touched for an hour, and on
    /// a slow link moving one blob of a request or a reply can take longer, while the others
    /// wait. Returns the replies to `keeps`, and what `work` returns.
    async fn beside<T>(
        &self,
        transport: &dyn Transport,
        keeps: Vec<HubRequest>,
        work: impl Future<Output = T>,
    ) -> (Vec<anyhow::Result<HubReply>>, T) {
        let keeps = futures::future::join_all(keeps.into_iter().map(|request| async move {
            self.exchange(transport, Envelope::encode(request)?).await
        }));
        futures::join!(keeps, work)
    }

    /// [`Self::download`], again after a timeout, for as long as each try takes the blob
    /// further than ever in the call, or [`RESENDS`] times in a row that don't.
    async fn download_patiently(
        &self,
        blob: &BlobId,
        total: u64,
        transport: &dyn Transport,
        received: u64,
        later: &[BlobId],
        furthest: &mut Furthest,
    ) -> anyhow::Result<PathBuf> {
        let mut tries = 0;
        loop {
            let further = furthest.further;
            match self
                .download(blob, total, transport, received, later, furthest)
                .await
            {
                Err(err) if timed_out(&err) && furthest.further > further => tries = 0,
                Err(err) if tries < RESENDS && timed_out(&err) => tries += 1,
                result => return result,
            }
            tracing::debug!("no chunk in time; going on with {blob:?} ({tries} of {RESENDS})");
        }
    }

    /// Downloads a blob of `total` bytes in chunks, a window at a time, into the local blob
    /// store, returning its file, from what the store has of it, as when an earlier try timed
    /// out. Keeps `later`, the reply's blobs to download after it, at the hub meanwhile
    /// ([`Self::beside`]). Records in `furthest` how far it got. `received` bytes of the
    /// transfer came before it.
    async fn download(
        &self,
        blob: &BlobId,
        total: u64,
        transport: &dyn Transport,
        received: u64,
        later: &[BlobId],
        furthest: &mut Furthest,
    ) -> anyhow::Result<PathBuf> {
        let chunk = chunk_size(transport.max_payload()) as u64;
        let mut offset = self.blobs.prefix(blob);
        let mut restarts = 0;
        loop {
            if let Some(path) = self.blobs.get(blob) {
                self.progress.moved(received.saturating_add(total));
                return Ok(path);
            }
            let start = offset;
            let mut chunks = FuturesOrdered::new();
            for at in window(offset, total, chunk, self.window()) {
                let request = Envelope::encode(HubRequest::GetChunk {
                    blob: *blob,
                    offset: at,
                    len: chunk,
                })?;
                chunks.push_back(async move { (at, self.exchange(transport, request).await) });
            }
            let taken = async {
                let mut heard = 0;
                while let Some((at, reply)) = chunks.next().await {
                    let reply = reply.inspect_err(|err| self.missed(heard, err))?;
                    heard += 1;
                    let (total, data) = match reply {
                        HubReply::Chunk { total, data } => (total, data),
                        other => return Err(unexpected(other)),
                    };
                    offset = match self.blobs.receive(blob, total, at, &data)? {
                        Received::Complete => {
                            furthest.raise(*blob, total);
                            self.progress.moved(received.saturating_add(total));
                            break;
                        }
                        Received::Prefix(have) => {
                            furthest.raise(*blob, have);
                            have
                        }
                    };
                    self.progress.moved(received.saturating_add(offset));
                }
                anyhow::Ok(())
            };
            // What the hub has of them is no business of this download's.
            let keeps = later
                .iter()
                .map(|&blob| HubRequest::GetChunk {
                    blob,
                    offset: 0,
                    len: 0,
                })
                .collect();
            self.beside(transport, keeps, taken).await.1?;
            self.widen();
            // A window takes the download further, unless what came failed the hash check
            // and it started over.
            if offset <= start && self.blobs.get(blob).is_none() {
                restarts += 1;
                anyhow::ensure!(
                    restarts <= RESTARTS,
                    "{blob:?} failed its hash check {restarts} times"
                );
            }
        }
    }

    /// How many chunks to keep in flight.
    fn window(&self) -> usize {
        self.window.load(Ordering::Relaxed)
    }

    /// Takes failing with `err`, after `heard` replies of a window, into account: a timeout
    /// says the link carried only those before their deadline, so the next window has that
    /// many, or one.
    fn missed(&self, heard: usize, err: &anyhow::Error) {
        if timed_out(err) {
            self.window.store(heard.max(1), Ordering::Relaxed);
            self.full.store(0, Ordering::Relaxed);
        }
    }

    /// Takes a window all of whose replies came into account: after [`GROW_AFTER`] in a row,
    /// the next can have one more.
    fn widen(&self) {
        if self.full.fetch_add(1, Ordering::Relaxed) + 1 >= GROW_AFTER {
            self.full.store(0, Ordering::Relaxed);
            let widened = (self.window() + 1).min(WINDOW);
            self.window.store(widened, Ordering::Relaxed);
        }
    }

    fn told_list(&self) -> std::sync::MutexGuard<'_, Vec<(BlobId, u64)>> {
        self.told.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// How much of `blob` the hub last said it had, or none.
    fn told(&self, blob: &BlobId) -> u64 {
        self.told_list()
            .iter()
            .find(|(id, _)| id == blob)
            .map_or(0, |(_, received)| *received)
    }

    /// Records that the hub said it had `received` bytes of `blob`.
    fn tell(&self, blob: &BlobId, received: u64) {
        let mut told = self.told_list();
        told.retain(|(id, _)| id != blob);
        if told.len() >= TOLD {
            told.remove(0);
        }
        told.push((*blob, received));
    }

    /// Forgets how far the hub had got with `blobs`, which it lets go of once it has the
    /// request that names them.
    fn forget(&self, blobs: &[BlobId]) {
        self.told_list().retain(|(id, _)| !blobs.contains(id));
    }
}

/// The offsets of one window's chunks of `chunk` bytes, of a blob of `total` bytes, from
/// `offset`: that one, and those after it short of the end, up to `size` in all.
fn window(offset: u64, total: u64, chunk: u64, size: usize) -> impl Iterator<Item = u64> {
    std::iter::successors(Some(offset), move |&at| {
        at.checked_add(chunk).filter(|&next| next < total)
    })
    .take(size.max(1))
}

/// The blobs a call has downloaded, kept until it ends: those the reply refers to stay with
/// it.
#[derive(Default)]
struct Downloads(Vec<(BlobId, Arc<tempfile::TempPath>)>);

/// How far each blob a call moves has got, at most, and how many times one has gone further
/// than before: a timeout after that is no reason to give up, where one after a blob got
/// only as far as before again, as a request too large to send whole does each time it
/// goes, or a blob that failed its hash check, is.
#[derive(Default)]
struct Furthest {
    at: Vec<(BlobId, u64)>,
    further: u64,
}

impl Furthest {
    /// Records that `blob` has got to `to` bytes.
    fn raise(&mut self, blob: BlobId, to: u64) {
        match self.at.iter_mut().find(|(id, _)| *id == blob) {
            Some((_, at)) if *at >= to => return,
            Some((_, at)) => *at = to,
            None if to == 0 => return,
            None => self.at.push((blob, to)),
        }
        self.further += 1;
    }
}

impl Downloads {
    /// `blob`'s file, at `path`, held until the call ends.
    fn hold(&mut self, blob: BlobId, path: PathBuf) -> anyhow::Result<Arc<tempfile::TempPath>> {
        if let Some(held) = self.held(&blob) {
            return Ok(held);
        }
        let held = Arc::new(tempfile::TempPath::try_from_path(path)?);
        self.0.push((blob, Arc::clone(&held)));
        Ok(held)
    }

    fn held(&self, blob: &BlobId) -> Option<Arc<tempfile::TempPath>> {
        self.0
            .iter()
            .find(|(id, _)| id == blob)
            .map(|(_, held)| Arc::clone(held))
    }
}

/// The blobs an attempt at a call has uploaded, and their lengths, to keep at the hub until
/// the request goes ([`RemoteHub::beside`]).
#[derive(Default)]
struct Kept {
    blobs: Vec<(BlobId, u64)>,
    /// Those the hub no longer has, to upload again.
    lost: Vec<BlobId>,
}

impl Kept {
    /// Keeps `blob`, `total` bytes long, once, though a request names it twice.
    fn add(&mut self, blob: BlobId, total: u64) {
        if !self.blobs.iter().any(|(id, _)| *id == blob) {
            self.blobs.push((blob, total));
        }
    }

    /// Takes the hub's `replies` to keeping `blobs` into account: one that the hub no longer
    /// has all of, as when it was made again, is lost, and goes on from what it has. A reply
    /// that didn't come, or that says something else, is the next window's to find out about.
    fn check(&mut self, hub: &RemoteHub, replies: Vec<anyhow::Result<HubReply>>) {
        let mut at = 0;
        for reply in replies {
            let (blob, total) = self.blobs[at];
            match reply {
                Ok(HubReply::ChunkAck {
                    complete: false,
                    received,
                }) if received <= total => {
                    hub.tell(&blob, received);
                    self.blobs.remove(at);
                    self.lost.push(blob);
                }
                _ => at += 1,
            }
        }
    }
}

/// What each attempt at a call sends.
struct Attempt<'a> {
    /// The encoded request.
    bytes: &'a [u8],
    /// The blobs it names, and their length, until the request has gone.
    uploads: &'a [BlobId],
    upload_len: u64,
    /// The request as a blob, and its length, if it is too large to send whole.
    whole: Option<(BlobId, u64)>,
}

/// Blobs put in the store to upload, removed when this is dropped: as the call ends, however
/// it ends, as when it fails or the caller drops it partway. Kept until then, for a repeat.
struct Uploads<'a> {
    blobs: &'a BlobStore,
    ids: Vec<BlobId>,
}

impl Drop for Uploads<'_> {
    fn drop(&mut self) {
        for id in &self.ids {
            self.blobs.remove(id);
        }
    }
}

/// The connections a call moves chunks on: the one it shares, and one of its own, opened the
/// first time it moves enough chunks to be worth it, and closed with the call.
struct Lanes<'a> {
    hub: &'a RemoteHub,
    own: Option<Arc<dyn Transport>>,
    /// Whether the call tried to open its own: once, though it failed.
    tried: bool,
}

impl<'a> Lanes<'a> {
    fn new(hub: &'a RemoteHub) -> Self {
        Self {
            hub,
            own: None,
            tried: false,
        }
    }

    /// The connection to move `len` bytes of chunks on.
    async fn lane(&mut self, len: u64) -> Arc<dyn Transport> {
        let hub = self.hub;
        let chunk = chunk_size(hub.transport.max_payload()) as u64;
        let worth = OWN_CONNECTION_WINDOWS * WINDOW as u64 * chunk;
        if !self.tried
            && len >= worth
            && let Some(open) = &hub.open
        {
            self.tried = true;
            match open().await {
                Ok(own) => self.own = Some(own),
                // The shared connection still works, if more slowly for this.
                Err(err) => tracing::debug!("moving {len} bytes on the shared connection: {err:#}"),
            }
        }
        self.own.clone().unwrap_or_else(|| hub.transport.clone())
    }
}

/// The blobs a reply's attachments refer to, with their lengths.
fn reply_blobs(reply: &Reply<Vec<u8>, WireAttachment>) -> Vec<(BlobId, u64)> {
    let attachments: Vec<&WireAttachment> = match reply {
        Reply::Fetched {
            ops_attachment,
            objects,
            ..
        } => vec![ops_attachment, objects],
        Reply::Objects { attachment, .. } => vec![attachment],
        Reply::Head { .. } | Reply::Refused { .. } => vec![],
    };
    attachments
        .into_iter()
        .filter_map(|attachment| match attachment {
            WireAttachment::Blob { blob, len } => Some((*blob, *len)),
            _ => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::cell::Cell;
    use std::collections::VecDeque;
    use std::pin::Pin;
    use std::task::Context;
    use std::task::Poll;

    use hegel::HealthCheck;
    use hegel::TestCase;
    use hegel::generators as gs;
    use musubi_jj::objects::Backend;
    use musubi_transport::Subscription;
    use serde_json::Value;
    use serde_json::json;

    use super::*;
    use crate::hub::HubAdapter;
    use crate::oracle::Oracle;
    use crate::service::HubService;

    /// A hub whose every chunk fails the hash check.
    struct Corrupting {
        chunks: AtomicUsize,
    }

    #[async_trait::async_trait]
    impl Transport for Corrupting {
        fn max_payload(&self) -> usize {
            1 << 20
        }

        async fn publish(&self, _: &str, _: Bytes) -> Result<(), TransportError> {
            Ok(())
        }

        async fn subscribe(&self, _: &str) -> Result<Subscription, TransportError> {
            unimplemented!("a node subscribes to no subject here")
        }

        async fn request(
            &self,
            _: &str,
            payload: Bytes,
            _: Duration,
        ) -> Result<Bytes, TransportError> {
            let reply = match Envelope::<HubRequest>::decode(&payload).unwrap() {
                HubRequest::GetChunk { .. } => {
                    self.chunks.fetch_add(1, Ordering::SeqCst);
                    HubReply::Chunk {
                        total: 5,
                        data: b"wrong".to_vec(),
                    }
                }
                other => panic!("asked for {other:?}"),
            };
            Ok(Bytes::from(Envelope::encode(reply).unwrap()))
        }
    }

    /// A download that keeps failing its hash check gives up, rather than starting over
    /// forever.
    #[tokio::test]
    async fn downloads_give_up_on_a_blob_that_keeps_failing() {
        let dir = tempfile::tempdir().unwrap();
        let transport = Arc::new(Corrupting {
            chunks: AtomicUsize::new(0),
        });
        let remote = RemoteHub::new(
            transport.clone(),
            "rpc".into(),
            dir.path(),
            Duration::from_secs(5),
        )
        .unwrap();
        let mut lanes = Lanes::new(&remote);
        let reply = HubReply::Indirect {
            blob: BlobId::of_bytes(b"right"),
            len: 5,
        };
        let err = remote
            .receive(reply, &mut lanes, &mut Furthest::default())
            .await
            .unwrap_err();
        assert!(err.to_string().contains("failed its hash check"), "{err:#}");
        assert_eq!(transport.chunks.load(Ordering::SeqCst), RESTARTS + 1);
    }

    /// Small, so that a blob of a few kilobytes is many windows of chunks.
    const MAX_PAYLOAD: usize = 512;

    /// Ready the second time it is polled: a request that waits on it lets the sender put the
    /// rest of its window in flight before any reply comes.
    #[derive(Default)]
    struct YieldOnce(bool);

    impl Future for YieldOnce {
        type Output = ();

        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
            if self.0 {
                return Poll::Ready(());
            }
            self.0 = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }

    /// A window of chunk requests, as a [`Deadlines`] link carried it.
    #[derive(Default)]
    struct Window {
        /// The offsets of its chunks.
        offsets: Vec<u64>,
        /// How many of them reached the hub, and how many replies came back in time.
        delivered: usize,
        heard: usize,
        /// The hub's replies to an upload's chunks that reached it: how much it had, or none
        /// once it had the blob.
        replies: Vec<Option<u64>>,
        /// The receiver's partial blob after the window, and whether it had stored the blob.
        after: Option<(Vec<u8>, bool)>,
    }

    /// A link to a hub on which each window of chunk requests, all in flight at once, meets a
    /// deadline: of the chunks it carries, the first so many reach the hub, and replies to the
    /// first so many of those come back in time, the rest timing out, as on a link too slow to
    /// carry the window before the deadline. `plans` holds how many for the windows to come;
    /// those beyond it all come back.
    struct Deadlines {
        hub: Mutex<HubService>,
        plans: Mutex<VecDeque<(usize, usize)>>,
        windows: Mutex<Vec<Window>>,
        /// Requests of the current window still in flight: a window starts once none are.
        in_flight: AtomicUsize,
        /// The receiver's blob store, and the blob.
        receiver: PathBuf,
        blob: BlobId,
    }

    /// A request in flight on a [`Deadlines`] link, until it is answered or dropped.
    struct InFlight<'a>(&'a AtomicUsize);

    impl Drop for InFlight<'_> {
        fn drop(&mut self) {
            self.0.fetch_sub(1, Ordering::SeqCst);
        }
    }

    impl Deadlines {
        /// The receiver's partial blob, and whether it has stored the blob.
        fn receiver(&self) -> (Vec<u8>, bool) {
            let hex = self.blob.hex();
            (
                std::fs::read(self.receiver.join("partial").join(&hex)).unwrap_or_default(),
                self.receiver.join("complete").join(&hex).exists(),
            )
        }

        /// Takes a request, delivering it to the hub if its window's plan says so, and returns
        /// the reply, if one comes in time. The sender has done with a window's replies by
        /// the time it sends the next.
        fn take(&self, payload: &[u8]) -> Result<Bytes, TransportError> {
            let mut windows = self.windows.lock().unwrap();
            if self.in_flight.load(Ordering::SeqCst) == 0 {
                if let Some(last) = windows.last_mut() {
                    last.after.get_or_insert_with(|| self.receiver());
                }
                let (delivered, heard) = self
                    .plans
                    .lock()
                    .unwrap()
                    .pop_front()
                    .unwrap_or((usize::MAX, usize::MAX));
                windows.push(Window {
                    delivered,
                    heard,
                    ..Window::default()
                });
            }
            let window = windows.last_mut().unwrap();
            let at = window.offsets.len();
            window
                .offsets
                .push(match Envelope::decode(payload).unwrap() {
                    HubRequest::PutChunk { offset, .. } | HubRequest::GetChunk { offset, .. } => {
                        offset
                    }
                    other => panic!("not a chunk: {other:?}"),
                });
            if at >= window.delivered {
                return Err(TransportError::Timeout);
            }
            let (reply, _) = self
                .hub
                .lock()
                .unwrap()
                .handle_bytes(payload, MAX_PAYLOAD)
                .unwrap();
            if let HubReply::ChunkAck { received, complete } = Envelope::decode(&reply).unwrap() {
                window.replies.push((!complete).then_some(received));
            }
            if at >= window.heard {
                return Err(TransportError::Timeout);
            }
            Ok(Bytes::from(reply))
        }

        /// The windows carried since last asked, each with what its plan made of it.
        fn carried(&self) -> Vec<Window> {
            let mut windows = std::mem::take(&mut *self.windows.lock().unwrap());
            for window in &mut windows {
                window.after.get_or_insert_with(|| self.receiver());
                window.delivered = window.delivered.min(window.offsets.len());
                window.heard = window.heard.min(window.delivered);
            }
            windows
        }
    }

    #[async_trait::async_trait]
    impl Transport for Deadlines {
        fn max_payload(&self) -> usize {
            MAX_PAYLOAD
        }

        async fn publish(&self, _: &str, _: Bytes) -> Result<(), TransportError> {
            Ok(())
        }

        async fn subscribe(&self, _: &str) -> Result<Subscription, TransportError> {
            unimplemented!("a node subscribes to no subject here")
        }

        async fn request(
            &self,
            _: &str,
            payload: Bytes,
            _: Duration,
        ) -> Result<Bytes, TransportError> {
            let reply = self.take(&payload);
            self.in_flight.fetch_add(1, Ordering::SeqCst);
            let _in_flight = InFlight(&self.in_flight);
            YieldOnce::default().await;
            reply
        }
    }

    /// `upload` and `download` send, window by window, what the sender of
    /// `formal/Musubi/Chunks.lean`'s attempts sends ("Attempts under a deadline"): each window
    /// from where the hub last said it was in the blob, for an upload, or from what the node
    /// has of it, for a download, so that every attempt goes on from where the last left off,
    /// across attempts cut short by deadlines, sweeps of what the receiver has, and senders
    /// started afresh. After each window, its offsets, the hub's replies to an upload's chunks,
    /// the receiver's partial blob and whether it has stored the blob are the model's, which
    /// the oracle works out. A sender that starts each attempt from the beginning fails once
    /// an attempt is cut short after a chunk reaches the receiver and, for an upload, the
    /// sender has heard so. Each window has as many chunks as came back in time from the last
    /// cut short, or one, and one more after each [`GROW_AFTER`] in a row that all came back,
    /// up to [`WINDOW`], short of the blob's end.
    #[hegel::test(test_cases = 100, suppress_health_check = [HealthCheck::TooSlow])]
    fn transfers_follow_the_attempt_model(tc: TestCase) {
        let upload = tc.draw(gs::booleans());
        let len = tc.draw(gs::integers::<usize>().min_value(1).max_value(4000));
        let seed = tc.draw(gs::integers::<usize>().max_value(250));
        let blob: Vec<u8> = (0..len).map(|i| ((i * 7 + seed) % 251) as u8).collect();
        let id = BlobId::of_bytes(&blob);
        let plans: VecDeque<(usize, usize)> = (0..tc.draw(gs::integers::<usize>().max_value(12)))
            .map(|_| {
                let delivered = tc.draw(gs::integers::<usize>().max_value(WINDOW));
                // A download's chunk reaches the node only with its reply.
                let heard = if upload {
                    tc.draw(gs::integers::<usize>().max_value(delivered))
                } else {
                    delivered
                };
                (delivered, heard)
            })
            .collect();
        // Each call but the last ends with a window cut short.
        let calls = plans.len() + 1;

        let dir = musubi_testutil::tempdir();
        let hub_dir = dir.path().join("hub");
        let mut hub = HubService::new(
            HubAdapter::init(&hub_dir, Backend::Simple).unwrap(),
            &hub_dir,
        )
        .unwrap();
        let node_dir = dir.path().join("node");
        if !upload {
            assert_eq!(hub.prepare(&blob).unwrap().0, id);
        }
        let link = Arc::new(Deadlines {
            hub: Mutex::new(hub),
            plans: Mutex::new(plans),
            windows: Mutex::new(vec![]),
            in_flight: AtomicUsize::new(0),
            receiver: if upload {
                hub_dir.join("blobs")
            } else {
                node_dir.clone()
            },
            blob: id,
        });
        let start = || {
            RemoteHub::new(
                link.clone(),
                "rpc".into(),
                &node_dir,
                Duration::from_secs(5),
            )
            .unwrap()
        };
        let mut remote = start();
        if upload {
            remote.blobs.insert_bytes(&blob).unwrap();
        }
        let runtime = tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap();
        // The oracle's steps, and the windows the attempts among them stand for.
        let mut steps: Vec<Value> = vec![];
        let mut windows: Vec<Option<Window>> = vec![];
        for call in 1.. {
            let done = runtime.block_on(async {
                if upload {
                    let mut kept = Kept::default();
                    remote
                        .upload(&id, &*link, 0, &mut kept, &mut Furthest::default())
                        .await
                        .map(drop)
                } else {
                    remote
                        .download(&id, len as u64, &*link, 0, &[], &mut Furthest::default())
                        .await
                        .map(drop)
                }
            });
            for window in link.carried() {
                steps.push(json!({"attempt": {
                    "window": window.offsets.len(),
                    "delivered": window.delivered,
                    "heard": window.heard,
                }}));
                windows.push(Some(window));
            }
            match done {
                Ok(()) => break,
                Err(err) => assert!(timed_out(&err), "{err:#}"),
            }
            assert!(call < calls, "the transfer did not finish in {calls} calls");
            if tc.draw(gs::integers::<u8>().max_value(5)) == 0 {
                // What a sweep of the receiver's partial blob leaves.
                std::fs::remove_file(link.receiver.join("partial").join(id.hex())).ok();
                steps.push(json!({"sweep": {"partial": true, "stored": false}}));
                windows.push(None);
            }
            if tc.draw(gs::integers::<u8>().max_value(5)) == 0 {
                remote = start();
                steps.push(json!({"restart": true}));
                windows.push(None);
            }
        }

        // One oracle for every case: attempts requests leave it as they found it.
        thread_local!(static ORACLE: Cell<Option<Oracle>> = const { Cell::new(None) });
        let mut oracle = ORACLE.take().unwrap_or_else(Oracle::spawn);
        let reply = oracle.call(&json!({
            "op": "attempts",
            "blob": blob,
            "limit": chunk_size(MAX_PAYLOAD),
            "sender": if upload { "upload" } else { "download" },
            "steps": steps,
        }));
        ORACLE.set(Some(oracle));
        assert_eq!(reply["ok"], true, "the oracle refused the steps: {reply}");
        let modelled = reply["steps"].as_array().unwrap();
        // How many chunks a window has, which the model leaves to the sender, and how many
        // windows in a row have all come back.
        let (mut size, mut full) = (WINDOW, 0);
        let chunk = chunk_size(MAX_PAYLOAD) as u64;
        for (at, (window, model)) in windows.iter().zip(modelled).enumerate() {
            let step = &steps[at];
            let Some(window) = window else {
                if step.get("restart").is_some() {
                    (size, full) = (WINDOW, 0);
                }
                continue;
            };
            let left = (len as u64)
                .saturating_sub(window.offsets[0])
                .div_ceil(chunk);
            assert_eq!(
                window.offsets.len() as u64,
                (size as u64).min(left.max(1)),
                "step {at}: {step}, after windows of {size}"
            );
            if window.heard < window.offsets.len() {
                // As many as came back before their deadline, or one.
                (size, full) = (window.heard.max(1), 0);
            } else {
                full += 1;
                if full == GROW_AFTER {
                    (size, full) = ((size + 1).min(WINDOW), 0);
                }
            }
            assert_eq!(json!(window.offsets), model["offsets"], "step {at}: {step}");
            if upload {
                assert_eq!(json!(window.replies), model["replies"], "step {at}: {step}");
            }
            let (pre, stored) = window.after.as_ref().unwrap();
            assert_eq!(json!(pre), model["pre"], "step {at}: {step}");
            assert_eq!(*stored, model["stored"], "step {at}: {step}");
        }
        let stored = link.receiver.join("complete").join(id.hex());
        assert_eq!(std::fs::read(stored).unwrap(), blob);
    }

    /// What a [`Direct`] link does before the hub takes each request.
    type Before = Box<dyn Fn(&mut HubService, &HubRequest) + Send + Sync>;

    /// A hub in `dir`, reached directly, which `before` sees each request before it takes it.
    struct Direct {
        hub: Mutex<HubService>,
        before: Before,
        /// The chunks of data sent or asked for, by blob and offset.
        chunks: Mutex<Vec<(BlobId, u64)>>,
    }

    impl Direct {
        fn new(
            dir: &Path,
            before: impl Fn(&mut HubService, &HubRequest) + Send + Sync + 'static,
        ) -> Arc<Self> {
            let hub =
                HubService::new(HubAdapter::init(dir, Backend::Simple).unwrap(), dir).unwrap();
            Arc::new(Self {
                hub: Mutex::new(hub),
                before: Box::new(before),
                chunks: Mutex::new(vec![]),
            })
        }

        /// How many times a chunk of `blob` at `offset` was sent or asked for.
        fn moved(&self, blob: BlobId, offset: u64) -> usize {
            let chunks = self.chunks.lock().unwrap();
            chunks
                .iter()
                .filter(|&&chunk| chunk == (blob, offset))
                .count()
        }
    }

    #[async_trait::async_trait]
    impl Transport for Direct {
        fn max_payload(&self) -> usize {
            MAX_PAYLOAD
        }

        async fn publish(&self, _: &str, _: Bytes) -> Result<(), TransportError> {
            Ok(())
        }

        async fn subscribe(&self, _: &str) -> Result<Subscription, TransportError> {
            unimplemented!("a node subscribes to no subject here")
        }

        async fn request(
            &self,
            _: &str,
            payload: Bytes,
            _: Duration,
        ) -> Result<Bytes, TransportError> {
            let request = Envelope::decode(&payload).unwrap();
            match request {
                HubRequest::PutChunk {
                    blob,
                    offset,
                    ref data,
                    ..
                } if !data.is_empty() => self.chunks.lock().unwrap().push((blob, offset)),
                HubRequest::GetChunk { blob, offset, len } if len > 0 => {
                    self.chunks.lock().unwrap().push((blob, offset));
                }
                _ => {}
            }
            let mut hub = self.hub.lock().unwrap();
            (self.before)(&mut hub, &request);
            // As the hub's server answers an error.
            let reply = match hub.handle_bytes(&payload, MAX_PAYLOAD) {
                Ok((reply, _)) => reply,
                Err(err) => Envelope::encode(HubReply::Error(format!("{err:#}"))).unwrap(),
            };
            Ok(Bytes::from(reply))
        }
    }

    /// Bytes no other test's blob has, `len` of them.
    fn content(seed: u8, len: usize) -> Vec<u8> {
        (0..len)
            .map(|i| (i as u8).wrapping_mul(31) ^ seed)
            .collect()
    }

    /// A request's upload that the hub loses while the next uploads, as a hub made again
    /// would, goes again, from what the hub has of it, once a chunk that moves nothing finds
    /// it gone; but a hub that loses each as the other goes is given up on.
    #[tokio::test]
    async fn uploads_the_hub_loses_go_again() {
        for losing in ["once", "always"] {
            let dir = musubi_testutil::tempdir();
            let hub_dir = dir.path().join("hub");
            let (a, b) = (content(1, 3000), content(2, 3000));
            let (ida, idb) = (BlobId::of_bytes(&a), BlobId::of_bytes(&b));
            let complete = hub_dir.join("blobs/complete");
            let lost = AtomicUsize::new(0);
            let link = Direct::new(&hub_dir, move |_, request| {
                if let HubRequest::PutChunk { blob, data, .. } = request
                    && !data.is_empty()
                    && (losing == "always" || lost.load(Ordering::SeqCst) == 0)
                {
                    let other = if *blob == ida { idb } else { ida };
                    if std::fs::remove_file(complete.join(other.hex())).is_ok() {
                        lost.fetch_add(1, Ordering::SeqCst);
                    }
                }
            });
            let remote = RemoteHub::new(
                link.clone(),
                "rpc".into(),
                &dir.path().join("node"),
                Duration::from_secs(5),
            )
            .unwrap();
            remote.blobs.insert_bytes(&a).unwrap();
            remote.blobs.insert_bytes(&b).unwrap();
            let uploaded = remote
                .upload_all(
                    &[ida, idb],
                    &*link,
                    0,
                    &mut Kept::default(),
                    &mut Furthest::default(),
                )
                .await;
            if losing == "always" {
                let err = uploaded.unwrap_err();
                assert!(err.to_string().contains("lost"), "{err:#}");
                continue;
            }
            uploaded.unwrap();
            for (id, bytes) in [(ida, &a), (idb, &b)] {
                assert_eq!(
                    &std::fs::read(hub_dir.join("blobs/complete").join(id.hex())).unwrap(),
                    bytes
                );
            }
            assert_eq!(
                link.moved(ida, 0),
                2,
                "the lost upload went again from the start"
            );
            assert_eq!(link.moved(idb, 0), 1);
        }
    }
}

#[cfg(kani)]
mod proofs {
    use super::*;

    /// For any offset, length, chunk size and window size, a window starts where it is asked
    /// to, goes up a chunk at a time without overflowing, and ends either at the end of the
    /// blob or after a full window.
    #[kani::proof]
    #[kani::unwind(10)]
    fn a_window_goes_on_from_its_offset() {
        let (offset, total, chunk, size): (u64, u64, u64, usize) = kani::any();
        kani::assume(chunk > 0 && size <= WINDOW);
        let mut count = 0;
        let mut last = offset;
        for at in window(offset, total, chunk, size) {
            if count == 0 {
                assert_eq!(at, offset);
            } else {
                assert_eq!(at - last, chunk);
                assert!(at < total);
            }
            last = at;
            count += 1;
        }
        assert!(count >= 1 && count <= size.max(1));
        assert!(count == size.max(1) || last.saturating_add(chunk) >= total);
    }
}
