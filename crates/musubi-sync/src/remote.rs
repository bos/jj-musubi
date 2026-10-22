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
use futures::stream::FuturesOrdered;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_transport::Transport;

use crate::Attachment;
use crate::OpId;
use crate::blobs::BlobId;
use crate::blobs::BlobStore;
use crate::blobs::Received;
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
    rpc_subject: String,
    blobs: BlobStore,
    timeout: Duration,
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
            rpc_subject,
            blobs: BlobStore::open(blob_dir)?,
            timeout,
        })
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
        let request = map_request(
            request,
            |id| id.to_bytes(),
            |attachment| {
                Ok(match attachment {
                    Attachment::None => WireAttachment::None,
                    Attachment::Bundle(_) | Attachment::File(_) => {
                        let path = attachment.bundle_path()?;
                        let len = std::fs::metadata(path)?.len();
                        if len <= inline_left {
                            inline_left -= len;
                            WireAttachment::Inline(std::fs::read(path)?)
                        } else {
                            let (blob, len) = self.blobs.insert_file(path)?;
                            uploads.ids.push(blob);
                            WireAttachment::Blob { blob, len }
                        }
                    }
                    Attachment::Haves(ids) => {
                        WireAttachment::Haves(ids.iter().map(|id| id.to_bytes()).collect())
                    }
                })
            },
        )?;
        for blob in &uploads.ids {
            self.upload(blob).await?;
        }
        let reply = self.send(HubRequest::Protocol(request)).await;
        drop(uploads);
        let reply = match reply? {
            HubReply::Protocol(reply) => reply,
            HubReply::Error(err) => anyhow::bail!("hub: {err}"),
            other => anyhow::bail!("unexpected reply {other:?}"),
        };
        // Deleted here if a later download fails or the call is dropped, and otherwise once
        // the caller is done with the reply.
        let mut downloads = vec![];
        for (blob, len) in reply_blobs(&reply) {
            // Once, though the reply names it twice: each path deletes its file.
            if downloads.iter().any(|(id, _)| *id == blob) {
                continue;
            }
            let path = tempfile::TempPath::try_from_path(self.download(&blob, len).await?)?;
            downloads.push((blob, Arc::new(path)));
        }
        map_reply(reply, OpId::new, |attachment| {
            Ok(match attachment {
                WireAttachment::None => Attachment::None,
                WireAttachment::Blob { blob, .. } => {
                    let path = downloads
                        .iter()
                        .find(|(id, _)| *id == blob)
                        .map(|(_, path)| Arc::clone(path))
                        .expect("downloaded above");
                    Attachment::Bundle(path)
                }
                WireAttachment::Inline(bytes) => {
                    // Not reopened truncating (see `BundleWriter::create`).
                    let mut file = self.blobs.temp_file()?;
                    std::io::Write::write_all(&mut file, &bytes)?;
                    Attachment::bundle(file.into_temp_path())
                }
                WireAttachment::Haves(ids) => {
                    Attachment::Haves(ids.into_iter().map(CommitId::new).collect())
                }
            })
        })
    }

    async fn send(&self, request: HubRequest) -> anyhow::Result<HubReply> {
        let mut bytes = Envelope::encode(request)?;
        if bytes.len() > self.transport.max_payload() {
            let (blob, _) = self.blobs.insert_bytes(&bytes)?;
            let upload = Uploads {
                blobs: &self.blobs,
                ids: vec![blob],
            };
            self.upload(&blob).await?;
            drop(upload);
            bytes = Envelope::encode(HubRequest::Indirect { blob })?;
        }
        let reply = self.exchange(bytes).await?;
        if let HubReply::Indirect { blob, len } = reply {
            let path = tempfile::TempPath::try_from_path(self.download(&blob, len).await?)?;
            return Envelope::<HubReply>::decode(&std::fs::read(&path)?);
        }
        Ok(reply)
    }

    async fn exchange(&self, bytes: Vec<u8>) -> anyhow::Result<HubReply> {
        let reply = self
            .transport
            .request(&self.rpc_subject, Bytes::from(bytes), self.timeout)
            .await?;
        Envelope::<HubReply>::decode(&reply)
    }

    /// Uploads a blob in chunks, [`WINDOW`] at a time, resuming from whatever the hub
    /// reports it has. That is less than before only if the hub started over, after a hash
    /// mismatch or after discarding the upload as abandoned, and then so does the upload.
    async fn upload(&self, blob: &BlobId) -> anyhow::Result<()> {
        let chunk = chunk_size(self.transport.max_payload());
        let (total, _) = self.blobs.read(blob, 0, 0)?;
        let mut offset = 0;
        let mut restarts = 0;
        loop {
            let mut acks = FuturesOrdered::new();
            let mut next = offset;
            loop {
                let (_, data) = self.blobs.read(blob, next, chunk)?;
                let request = HubRequest::PutChunk {
                    blob: *blob,
                    total,
                    offset: next,
                    data,
                };
                acks.push_back(self.exchange(Envelope::encode(request)?));
                next += chunk as u64;
                if next >= total || acks.len() == WINDOW {
                    break;
                }
            }
            // The hub may take a window's chunks in any order, so go on from the furthest it
            // reported. If it started over during the window, that is too far, and the next
            // window, none of which it can take, finds out.
            let mut furthest = 0;
            while let Some(ack) = acks.next().await {
                match ack? {
                    HubReply::ChunkAck { complete: true, .. } => return Ok(()),
                    HubReply::ChunkAck { received, .. } => furthest = furthest.max(received),
                    HubReply::Error(err) => anyhow::bail!("hub: {err}"),
                    other => anyhow::bail!("unexpected reply {other:?}"),
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
    /// blob store, returning its file.
    async fn download(&self, blob: &BlobId, total: u64) -> anyhow::Result<PathBuf> {
        let chunk = chunk_size(self.transport.max_payload()) as u64;
        let mut offset = 0;
        let mut restarts = 0;
        loop {
            if let Some(path) = self.blobs.get(blob) {
                return Ok(path);
            }
            let start = offset;
            let mut chunks = FuturesOrdered::new();
            let mut next = offset;
            loop {
                let request = Envelope::encode(HubRequest::GetChunk {
                    blob: *blob,
                    offset: next,
                    len: chunk,
                })?;
                let at = next;
                chunks.push_back(async move { (at, self.exchange(request).await) });
                next += chunk;
                if next >= total || chunks.len() == WINDOW {
                    break;
                }
            }
            while let Some((at, reply)) = chunks.next().await {
                let (total, data) = match reply? {
                    HubReply::Chunk { total, data } => (total, data),
                    HubReply::Error(err) => anyhow::bail!("hub: {err}"),
                    other => anyhow::bail!("unexpected reply {other:?}"),
                };
                offset = match self.blobs.receive(blob, total, at, &data)? {
                    Received::Complete => break,
                    Received::Prefix(have) => have,
                };
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
        let err = remote
            .send(HubRequest::Indirect {
                blob: BlobId::of_bytes(b"other"),
            })
            .await
            .unwrap_err();
        assert!(err.to_string().contains("failed its hash check"), "{err:#}");
        assert_eq!(transport.chunks.load(Ordering::SeqCst), RESTARTS + 1);
    }
}
