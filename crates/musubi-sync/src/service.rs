//! The hub as a network service: answers requests on the hive's RPC subject, one at a
//! time, and announces new heads on its head subject.

use std::sync::Arc;
use std::time::Duration;
use std::time::SystemTime;

use bytes::Bytes;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_core::hub;
use musubi_transport::Transport;

use crate::Attachment;
use crate::OpId;
use crate::blobs::BlobId;
use crate::blobs::BlobStore;
use crate::blobs::Received;
use crate::hub::HubAdapter;
use crate::wire::Envelope;
use crate::wire::HeadNotice;
use crate::wire::HubReply;
use crate::wire::HubRequest;
use crate::wire::WireAttachment;
use crate::wire::map_reply;
use crate::wire::map_request;

/// How long the hub keeps a bundle it prepared for a node to download.
const PREPARED_BLOB_LIFETIME: Duration = Duration::from_secs(3600);

pub struct HubService {
    hub: HubAdapter,
    blobs: BlobStore,
    blobs_dir: std::path::PathBuf,
    rpc_subject: String,
    head_subject: String,
    handled: u64,
}

impl HubService {
    pub fn new(
        hub: HubAdapter,
        dir: &std::path::Path,
        rpc_subject: String,
        head_subject: String,
    ) -> anyhow::Result<Self> {
        let blobs_dir = dir.join("blobs");
        Ok(Self {
            hub,
            blobs: BlobStore::open(&blobs_dir)?,
            blobs_dir,
            rpc_subject,
            head_subject,
            handled: 0,
        })
    }

    pub fn hub(&self) -> &HubAdapter {
        &self.hub
    }

    /// Serves until the transport's subscription ends, calling `ready` once subscribed, when
    /// requests start being answered. Requests are handled strictly one at a time, which is
    /// what makes every `Cas` atomic.
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
        if self.handled.is_multiple_of(100) {
            self.sweep();
        }
        let request = Envelope::<HubRequest>::decode(bytes)?;
        let (reply, notice) = self.handle(request)?;
        let encoded = Envelope::encode(reply.clone())?;
        if encoded.len() <= max_payload {
            return Ok((encoded, notice));
        }
        let (blob, len) = self.blobs.insert_bytes(&encoded)?;
        Ok((Envelope::encode(HubReply::Indirect { blob, len })?, notice))
    }

    fn handle(&mut self, request: HubRequest) -> anyhow::Result<(HubReply, Option<HeadNotice>)> {
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
                self.handle(inner)
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
                        WireAttachment::Haves(ids) => {
                            Attachment::Haves(ids.into_iter().map(CommitId::new).collect())
                        }
                    })
                })?;
                let handled = hub::handle(&mut self.hub, request);
                // Uploaded bundles are imported (or rejected) now; either way they are done.
                for blob in uploaded {
                    self.blobs.remove(&blob);
                }
                let handled = handled?;
                let reply = map_reply(
                    handled.reply,
                    |id| id.to_bytes(),
                    |attachment| {
                        Ok(match attachment {
                            Attachment::None => WireAttachment::None,
                            Attachment::Bundle(path) => {
                                let (blob, len) = self.blobs.insert_file(&path)?;
                                WireAttachment::Blob { blob, len }
                            }
                            Attachment::File(path) => {
                                let (blob, len) = self.blobs.insert_file(&path)?;
                                WireAttachment::Blob { blob, len }
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

/// Re-exported for tests that drive the service directly.
pub fn blob_of(bytes: &[u8]) -> BlobId {
    BlobId::of_bytes(bytes)
}
