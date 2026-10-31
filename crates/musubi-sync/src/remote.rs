//! A node's view of a remote hub: protocol requests in, replies out, with attachments and
//! oversized messages moved underneath. A small attachment travels inline in its message; a
//! larger one as a chunked blob, with several chunks in flight at once, so that a transfer
//! costs about one round trip per window of chunks rather than one per chunk.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
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

/// Chunks of one blob in flight at once: enough to keep a link with a long round trip
/// busy, without queueing much at the hub, which answers one request at a time.
pub const WINDOW: usize = 8;

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
        let mut lanes = Lanes::new(self);
        let lane = lanes.lane(upload_len).await;
        if upload_len > 0 {
            self.progress.set(Activity::Sending {
                done: 0,
                total: upload_len,
            });
        }
        let mut sent = 0;
        for blob in &uploads.ids {
            sent += self.upload(blob, &*lane, sent).await?;
        }
        self.progress.set(Activity::Asking);
        let reply = self.send(HubRequest::Protocol(request), &mut lanes).await;
        drop(uploads);
        let reply = match reply? {
            HubReply::Protocol(reply) => reply,
            other => return Err(unexpected(other)),
        };
        // Deleted here if a later download fails or the call is dropped, and otherwise once
        // the caller is done with the reply.
        let mut blobs = reply_blobs(&reply);
        // Once, though the reply names it twice: each path deletes its file.
        blobs.sort();
        blobs.dedup();
        let total = blobs.iter().map(|(_, len)| len).sum();
        let lane = lanes.lane(total).await;
        if total > 0 {
            self.progress.set(Activity::Receiving { done: 0, total });
        }
        let mut downloads = vec![];
        let mut received = 0;
        for (blob, len) in blobs {
            let path = self.download(&blob, len, &*lane, received).await?;
            received += len;
            downloads.push((blob, Arc::new(tempfile::TempPath::try_from_path(path)?)));
        }
        // Handling the reply imports its bundles.
        if total > 0 {
            self.progress.set(Activity::Importing);
        }
        map_reply(reply, OpId::new, |attachment| {
            attachment.into_attachment(&self.blobs, |blob| {
                let path = downloads
                    .iter()
                    .find(|(id, _)| *id == blob)
                    .map(|(_, path)| Arc::clone(path))
                    .expect("downloaded above");
                Ok(Attachment::Bundle(path))
            })
        })
    }

    async fn send(&self, request: HubRequest, lanes: &mut Lanes<'_>) -> anyhow::Result<HubReply> {
        let mut bytes = Envelope::encode(request)?;
        if bytes.len() > self.transport.max_payload() {
            let (blob, len) = self.blobs.insert_bytes(&bytes)?;
            let upload = Uploads {
                blobs: &self.blobs,
                ids: vec![blob],
            };
            self.progress.set(Activity::Sending {
                done: 0,
                total: len,
            });
            self.upload(&blob, &*lanes.lane(len).await, 0).await?;
            self.progress.set(Activity::Asking);
            drop(upload);
            bytes = Envelope::encode(HubRequest::Indirect { blob })?;
        }
        let reply = self.exchange(&*self.transport, bytes).await?;
        if let HubReply::Indirect { blob, len } = reply {
            self.progress.set(Activity::Receiving {
                done: 0,
                total: len,
            });
            let path = self
                .download(&blob, len, &*lanes.lane(len).await, 0)
                .await?;
            let path = tempfile::TempPath::try_from_path(path)?;
            return Envelope::<HubReply>::decode(&std::fs::read(&path)?);
        }
        Ok(reply)
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

    /// Uploads a blob in chunks, [`WINDOW`] at a time, resuming from whatever the hub
    /// reports it has. That is less than before only if the hub started over, after a hash
    /// mismatch or after discarding the upload as abandoned, and then so does the upload.
    /// Returns its length; `sent` bytes of the transfer went before it.
    async fn upload(
        &self,
        blob: &BlobId,
        transport: &dyn Transport,
        sent: u64,
    ) -> anyhow::Result<u64> {
        let chunk = chunk_size(transport.max_payload());
        let (total, _) = self.blobs.read(blob, 0, 0)?;
        let mut offset = 0;
        let mut restarts = 0;
        loop {
            let mut acks = FuturesOrdered::new();
            for next in window(offset, total, chunk as u64) {
                let (_, data) = self.blobs.read(blob, next, chunk)?;
                let request = HubRequest::PutChunk {
                    blob: *blob,
                    total,
                    offset: next,
                    data,
                };
                acks.push_back(self.exchange(transport, Envelope::encode(request)?));
            }
            // The hub may take a window's chunks in any order, so go on from the furthest it
            // reported. If it started over during the window, that is too far, and the next
            // window, none of which it can take, finds out.
            let mut furthest = 0;
            while let Some(ack) = acks.next().await {
                match ack? {
                    HubReply::ChunkAck { complete: true, .. } => {
                        self.progress.moved(sent + total);
                        return Ok(total);
                    }
                    HubReply::ChunkAck { received, .. } => {
                        furthest = furthest.max(received);
                        self.progress.moved(sent + furthest);
                    }
                    other => return Err(unexpected(other)),
                }
            }
            // The chunk at `offset` takes the hub further, unless it started over.
            if furthest <= offset {
                restarts += 1;
                anyhow::ensure!(
                    restarts <= RESTARTS,
                    "the hub started over on {blob:?} {restarts} times"
                );
            }
            offset = furthest;
        }
    }

    /// Downloads a blob of `total` bytes in chunks, [`WINDOW`] at a time, into the local
    /// blob store, returning its file. `received` bytes of the transfer came before it.
    async fn download(
        &self,
        blob: &BlobId,
        total: u64,
        transport: &dyn Transport,
        received: u64,
    ) -> anyhow::Result<PathBuf> {
        let chunk = chunk_size(transport.max_payload()) as u64;
        let mut offset = 0;
        let mut restarts = 0;
        loop {
            if let Some(path) = self.blobs.get(blob) {
                self.progress.moved(received + total);
                return Ok(path);
            }
            let start = offset;
            let mut chunks = FuturesOrdered::new();
            for at in window(offset, total, chunk) {
                let request = Envelope::encode(HubRequest::GetChunk {
                    blob: *blob,
                    offset: at,
                    len: chunk,
                })?;
                chunks.push_back(async move { (at, self.exchange(transport, request).await) });
            }
            while let Some((at, reply)) = chunks.next().await {
                let (total, data) = match reply? {
                    HubReply::Chunk { total, data } => (total, data),
                    other => return Err(unexpected(other)),
                };
                offset = match self.blobs.receive(blob, total, at, &data)? {
                    Received::Complete => {
                        self.progress.moved(received + total);
                        break;
                    }
                    Received::Prefix(have) => have,
                };
                self.progress.moved(received + offset);
            }
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
}

/// The offsets of one window's chunks of `chunk` bytes, of a blob of `total` bytes, from
/// `offset`: that one, and those after it short of the end, up to [`WINDOW`] in all.
fn window(offset: u64, total: u64, chunk: u64) -> impl Iterator<Item = u64> {
    std::iter::successors(Some(offset), move |&at| {
        at.checked_add(chunk).filter(|&next| next < total)
    })
    .take(WINDOW)
}

/// Blobs put in the store to upload, removed when this is dropped: once the hub has them,
/// and however else the call ends, as when it fails, or when it is dropped partway, as the
/// daemon drops a sync when the connection to the hub comes back.
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
        Reply::Head { .. } => vec![],
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

    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;

    use musubi_transport::Subscription;
    use musubi_transport::TransportError;

    use super::*;

    /// A hub whose every chunk of the blob it names fails the hash check.
    struct Corrupting {
        blob: BlobId,
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
                _ => HubReply::Indirect {
                    blob: self.blob,
                    len: 5,
                },
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
            blob: BlobId::of_bytes(b"right"),
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
        let err = remote
            .send(
                HubRequest::Indirect {
                    blob: BlobId::of_bytes(b"other"),
                },
                &mut lanes,
            )
            .await
            .unwrap_err();
        assert!(err.to_string().contains("failed its hash check"), "{err:#}");
        assert_eq!(transport.chunks.load(Ordering::SeqCst), RESTARTS + 1);
    }
}

#[cfg(kani)]
mod proofs {
    use super::*;

    /// For any offset, length and chunk size, a window starts where it is asked to, goes up
    /// a chunk at a time without overflowing, and ends either at the end of the blob or after
    /// a full window.
    #[kani::proof]
    #[kani::unwind(10)]
    fn a_window_goes_on_from_its_offset() {
        let (offset, total, chunk): (u64, u64, u64) = kani::any();
        kani::assume(chunk > 0);
        let mut count = 0;
        let mut last = offset;
        for at in window(offset, total, chunk) {
            if count == 0 {
                assert_eq!(at, offset);
            } else {
                assert_eq!(at - last, chunk);
                assert!(at < total);
            }
            last = at;
            count += 1;
        }
        assert!(count >= 1 && count <= WINDOW);
        assert!(count == WINDOW || last.saturating_add(chunk) >= total);
    }
}
