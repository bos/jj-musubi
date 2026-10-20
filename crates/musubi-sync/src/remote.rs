//! A node's view of a remote hub: protocol requests in, replies out, with attachments and
//! oversized messages moved underneath. A small attachment travels inline in its message; a
//! larger one as a chunked blob, with several chunks in flight at once, so that a transfer
//! costs about one round trip per window of chunks rather than one per chunk.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

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

pub struct RemoteHub {
    transport: Arc<dyn Transport>,
    rpc_subject: String,
    blobs: BlobStore,
    dir: PathBuf,
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
            dir: blob_dir.to_owned(),
            timeout,
        })
    }

    /// Sends one protocol request and returns the reply, with any bundle in it downloaded.
    pub async fn call(
        &self,
        request: Request<OpId, Attachment>,
    ) -> anyhow::Result<Reply<OpId, Attachment>> {
        let mut inline_left = inline_limit(self.transport.max_payload());
        let mut uploads = vec![];
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
                            uploads.push(blob);
                            WireAttachment::Blob { blob, len }
                        }
                    }
                    Attachment::Haves(ids) => {
                        WireAttachment::Haves(ids.iter().map(|id| id.to_bytes()).collect())
                    }
                })
            },
        )?;
        for blob in &uploads {
            self.upload(blob).await?;
        }
        let reply = self.send(HubRequest::Protocol(request)).await;
        for blob in &uploads {
            self.blobs.remove(blob);
        }
        let reply = match reply? {
            HubReply::Protocol(reply) => reply,
            HubReply::Error(err) => anyhow::bail!("hub: {err}"),
            other => anyhow::bail!("unexpected reply {other:?}"),
        };
        let mut downloads = vec![];
        for (blob, len) in reply_blobs(&reply) {
            downloads.push((blob, self.download(&blob, len).await?));
        }
        map_reply(reply, OpId::new, |attachment| {
            Ok(match attachment {
                WireAttachment::None => Attachment::None,
                WireAttachment::Blob { blob, .. } => {
                    let path = downloads
                        .iter()
                        .find(|(id, _)| *id == blob)
                        .map(|(_, path)| path.clone())
                        .expect("downloaded above");
                    Attachment::File(path)
                }
                WireAttachment::Inline(bytes) => {
                    let file = tempfile::NamedTempFile::new_in(&self.dir)?;
                    std::fs::write(file.path(), bytes)?;
                    Attachment::bundle(file.into_temp_path())
                }
                WireAttachment::Haves(ids) => {
                    Attachment::Haves(ids.into_iter().map(CommitId::new).collect())
                }
            })
        })
    }

    /// Releases a downloaded bundle once its contents have been imported.
    pub fn release(&self, attachment: &Attachment) {
        if let Attachment::File(path) = attachment {
            std::fs::remove_file(path).ok();
        }
    }

    async fn send(&self, request: HubRequest) -> anyhow::Result<HubReply> {
        let mut bytes = Envelope::encode(request)?;
        if bytes.len() > self.transport.max_payload() {
            let (blob, _) = self.blobs.insert_bytes(&bytes)?;
            self.upload(&blob).await?;
            self.blobs.remove(&blob);
            bytes = Envelope::encode(HubRequest::Indirect { blob })?;
        }
        let reply = self.exchange(bytes).await?;
        if let HubReply::Indirect { blob, len } = reply {
            let path = self.download(&blob, len).await?;
            let reply = Envelope::<HubReply>::decode(&std::fs::read(&path)?)?;
            self.blobs.remove(&blob);
            return Ok(reply);
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
    /// reports it has.
    async fn upload(&self, blob: &BlobId) -> anyhow::Result<()> {
        let chunk = chunk_size(self.transport.max_payload());
        let (total, _) = self.blobs.read(blob, 0, 0)?;
        let mut offset = 0;
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
            while let Some(ack) = acks.next().await {
                match ack? {
                    HubReply::ChunkAck { complete: true, .. } => return Ok(()),
                    HubReply::ChunkAck { received, .. } => offset = offset.max(received),
                    HubReply::Error(err) => anyhow::bail!("hub: {err}"),
                    other => anyhow::bail!("unexpected reply {other:?}"),
                }
            }
        }
    }

    /// Downloads a blob of `total` bytes in chunks, [`WINDOW`] at a time, into the local
    /// blob store, returning its file.
    async fn download(&self, blob: &BlobId, total: u64) -> anyhow::Result<PathBuf> {
        let chunk = chunk_size(self.transport.max_payload()) as u64;
        let mut offset = 0;
        loop {
            if let Some(path) = self.blobs.get(blob) {
                return Ok(path);
            }
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
