//! The hub as a network service: answers requests on the hive's RPC subject, one at a
//! time, and announces new heads on its head subject.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;
use std::time::SystemTime;

use bytes::Bytes;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_core::hub;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_transport::Transport;

use crate::Attachment;
use crate::OpId;
use crate::blobs::BlobId;
use crate::blobs::BlobStore;
use crate::blobs::Received;
use crate::hub::HubAdapter;
use crate::short;
use crate::temp_bundle;
use crate::wire::Envelope;
use crate::wire::HeadNotice;
use crate::wire::HubReply;
use crate::wire::HubRequest;
use crate::wire::WireAttachment;
use crate::wire::inline_limit;
use crate::wire::map_reply;
use crate::wire::map_request;

/// How long the hub keeps a blob it prepared for a node that never downloaded all of it,
/// and an abandoned partial upload.
const PREPARED_BLOB_LIFETIME: Duration = Duration::from_secs(3600);

/// How long the hub keeps a prepared blob after serving its last chunk, in case the node
/// asks for a chunk again because a reply was lost.
const SERVED_BLOB_LIFETIME: Duration = Duration::from_secs(60);

pub struct HubService {
    hub: HubAdapter,
    blobs: BlobStore,
    blobs_dir: std::path::PathBuf,
    tmp: std::path::PathBuf,
    rpc_subject: String,
    head_subject: String,
    handled: u64,
    /// Prepared blobs whose last chunk has been served, and when.
    served: HashMap<BlobId, Instant>,
    served_lifetime: Duration,
}

impl HubService {
    pub fn new(
        hub: HubAdapter,
        dir: &std::path::Path,
        rpc_subject: String,
        head_subject: String,
    ) -> anyhow::Result<Self> {
        let blobs_dir = dir.join("blobs");
        let tmp = dir.join("tmp");
        std::fs::create_dir_all(&tmp)?;
        Ok(Self {
            hub,
            blobs: BlobStore::open(&blobs_dir)?,
            blobs_dir,
            tmp,
            rpc_subject,
            head_subject,
            handled: 0,
            served: HashMap::new(),
            served_lifetime: SERVED_BLOB_LIFETIME,
        })
    }

    /// How long to keep a prepared blob after serving its last chunk, for tests.
    pub fn with_served_blob_lifetime(mut self, lifetime: Duration) -> Self {
        self.served_lifetime = lifetime;
        self
    }

    pub fn hub(&self) -> &HubAdapter {
        &self.hub
    }

    /// Serves until the transport's subscription ends, calling `ready` once subscribed, when
    /// requests start being answered. Requests are handled strictly one at a time, which is
    /// what makes every `Push` atomic.
    pub async fn run(
        mut self,
        transport: Arc<dyn Transport>,
        ready: impl FnOnce(),
    ) -> anyhow::Result<()> {
        let mut requests = transport.subscribe(&self.rpc_subject).await?;
        ready();
        while let Some(message) = requests.next().await {
            let Some(reply_to) = message.reply else {
                continue;
            };
            let (reply, notice) = match self.handle_bytes(&message.payload, transport.max_payload())
            {
                Ok(result) => result,
                Err(err) => {
                    tracing::warn!("request failed: {err:#}");
                    (Envelope::encode(HubReply::Error(format!("{err:#}")))?, None)
                }
            };
            if let Err(err) = transport.publish(&reply_to, Bytes::from(reply)).await {
                tracing::warn!("could not reply: {err}");
            }
            if let Some(notice) = notice {
                let notice = Bytes::from(Envelope::encode(notice)?);
                if let Err(err) = transport.publish(&self.head_subject, notice).await {
                    tracing::warn!("could not announce the new head: {err}");
                }
            }
        }
        Ok(())
    }

    /// Handles one encoded request, returning the encoded reply and any head to announce.
    pub fn handle_bytes(
        &mut self,
        bytes: &[u8],
        max_payload: usize,
    ) -> anyhow::Result<(Vec<u8>, Option<HeadNotice>)> {
        self.handled += 1;
        self.forget_served();
        if self.handled.is_multiple_of(100) {
            self.sweep();
        }
        let request = Envelope::<HubRequest>::decode(bytes)?;
        let (reply, notice) = self.handle(request, max_payload)?;
        let encoded = Envelope::encode(reply.clone())?;
        if encoded.len() <= max_payload {
            return Ok((encoded, notice));
        }
        let (blob, len) = self.blobs.insert_bytes(&encoded)?;
        Ok((Envelope::encode(HubReply::Indirect { blob, len })?, notice))
    }

    fn handle(
        &mut self,
        request: HubRequest,
        max_payload: usize,
    ) -> anyhow::Result<(HubReply, Option<HeadNotice>)> {
        match request {
            HubRequest::PutChunk {
                blob,
                total,
                offset,
                data,
            } => {
                let received = self.blobs.receive(&blob, total, offset, &data)?;
                let (received, complete) = match received {
                    Received::Prefix(have) => (have, false),
                    Received::Complete => (total, true),
                };
                Ok((HubReply::ChunkAck { received, complete }, None))
            }
            HubRequest::GetChunk { blob, offset, len } => {
                let len = usize::try_from(len)?;
                let (total, data) = self.blobs.read(&blob, offset, len)?;
                if offset + data.len() as u64 >= total {
                    self.served.insert(blob, Instant::now());
                }
                Ok((HubReply::Chunk { total, data }, None))
            }
            HubRequest::Indirect { blob } => {
                let path = self
                    .blobs
                    .get(&blob)
                    .ok_or_else(|| anyhow::anyhow!("no blob {blob:?}"))?;
                let inner = Envelope::<HubRequest>::decode(&std::fs::read(path)?)?;
                self.blobs.remove(&blob);
                anyhow::ensure!(
                    matches!(inner, HubRequest::Protocol(_)),
                    "nested indirection"
                );
                self.handle(inner, max_payload)
            }
            HubRequest::Protocol(request) => {
                let mut uploaded = vec![];
                let request = map_request(request, OpId::new, |attachment| {
                    Ok(match attachment {
                        WireAttachment::None => Attachment::None,
                        WireAttachment::Blob { blob, .. } => {
                            uploaded.push(blob);
                            let path = self.blobs.get(&blob).ok_or_else(|| {
                                anyhow::anyhow!("attachment {blob:?} was not uploaded")
                            })?;
                            Attachment::File(path)
                        }
                        WireAttachment::Inline(bytes) => {
                            let path = temp_bundle(&self.tmp)?;
                            std::fs::write(&path, bytes)?;
                            Attachment::bundle(path)
                        }
                        WireAttachment::Haves(ids) => {
                            Attachment::Haves(ids.into_iter().map(CommitId::new).collect())
                        }
                    })
                })?;
                let pushed = log_request(&request);
                let handled = hub::handle(&mut self.hub, request);
                // Uploaded bundles are imported (or rejected) now; either way they are done.
                for blob in uploaded {
                    self.blobs.remove(&blob);
                }
                let handled = handled?;
                log_reply(&handled.reply);
                if let Some((seq, head)) = &handled.publish {
                    tracing::info!(
                        "accepted {pushed} operations; the head is now {seq} ({})",
                        short(head)
                    );
                }
                let mut inline_left = inline_limit(max_payload);
                let reply = map_reply(
                    handled.reply,
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
                                    WireAttachment::Blob { blob, len }
                                }
                            }
                            Attachment::Haves(ids) => {
                                WireAttachment::Haves(ids.iter().map(|id| id.to_bytes()).collect())
                            }
                        })
                    },
                )?;
                let notice = handled.publish.map(|(seq, head)| HeadNotice {
                    seq,
                    head: head.to_bytes(),
                });
                Ok((HubReply::Protocol(reply), notice))
            }
        }
    }

    /// Deletes prepared blobs a while after their last chunk was served.
    fn forget_served(&mut self) {
        let now = Instant::now();
        let (blobs, lifetime) = (&self.blobs, self.served_lifetime);
        self.served.retain(|blob, served| {
            let keep = now.duration_since(*served) < lifetime;
            if !keep {
                blobs.remove(blob);
            }
            keep
        });
    }

    /// Deletes prepared blobs nobody downloaded in time, and abandoned partial uploads.
    fn sweep(&self) {
        let cutoff = SystemTime::now() - PREPARED_BLOB_LIFETIME;
        for sub in ["complete", "partial"] {
            let Ok(entries) = std::fs::read_dir(self.blobs_dir.join(sub)) else {
                continue;
            };
            for entry in entries.flatten() {
                let old = entry
                    .metadata()
                    .and_then(|m| m.modified())
                    .is_ok_and(|t| t < cutoff);
                if old {
                    std::fs::remove_file(entry.path()).ok();
                }
            }
        }
    }
}

/// Logs a protocol request, returning how many operations it pushes.
fn log_request(request: &Request<OpId, Attachment>) -> usize {
    match request {
        Request::Fetch { base, .. } => {
            tracing::debug!("asked for what follows {}", short(base));
            0
        }
        Request::GetObjects { for_ops, .. } => {
            tracing::debug!("asked for the objects of {} operations", for_ops.len());
            0
        }
        Request::Push {
            ops, expected, new, ..
        } => {
            tracing::debug!(
                "asked to store {} operations and move the head from {} to {}",
                ops.len(),
                short(expected),
                short(new)
            );
            ops.len()
        }
    }
}

fn log_reply(reply: &Reply<OpId, Attachment>) {
    match reply {
        Reply::Head { kind, seq, head } => {
            let kind = format!("{kind:?}").to_lowercase();
            tracing::debug!("answered {kind}: {seq} ({})", short(head));
        }
        Reply::Fetched { seq, head, ops, .. } => tracing::debug!(
            "sent {} operations, up to {seq} ({})",
            ops.len(),
            short(head)
        ),
        Reply::Objects { for_ops, .. } => {
            tracing::debug!("sent the objects of {} operations", for_ops.len());
        }
    }
}

/// Re-exported for tests that drive the service directly.
pub fn blob_of(bytes: &[u8]) -> BlobId {
    BlobId::of_bytes(bytes)
}
