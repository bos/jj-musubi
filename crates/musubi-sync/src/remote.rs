//! A node's view of a remote hub: protocol requests in, replies out, with attachments and
//! oversized messages moved as chunked blobs underneath.

use std::sync::Arc;
use std::time::Duration;

use bytes::Bytes;
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
use crate::wire::map_reply;
use crate::wire::map_request;

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
        blob_dir: &std::path::Path,
        timeout: Duration,
    ) -> anyhow::Result<Self> {
        Ok(Self {
            transport,
            rpc_subject,
            blobs: BlobStore::open(blob_dir)?,
            timeout,
        })
    }

    /// Sends one protocol request and returns the reply, with any bundle in it downloaded.
    pub async fn call(
        &self,
        request: Request<OpId, Attachment>,
    ) -> anyhow::Result<Reply<OpId, Attachment>> {
        let mut uploads = vec![];
        let request = map_request(
            request,
            |id| id.to_bytes(),
            |attachment| {
                Ok(match attachment {
                    Attachment::None => WireAttachment::None,
                    Attachment::Bundle(path) => {
                        let (blob, len) = self.blobs.insert_file(&path)?;
                        uploads.push(blob);
                        WireAttachment::Blob { blob, len }
                    }
                    Attachment::File(path) => {
                        let (blob, len) = self.blobs.insert_file(&path)?;
                        uploads.push(blob);
                        WireAttachment::Blob { blob, len }
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
        for blob in reply_blobs(&reply) {
            downloads.push((blob, self.download(&blob).await?));
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
        if let HubReply::Indirect { blob, .. } = reply {
            let path = self.download(&blob).await?;
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

    /// Uploads a blob in chunks, resuming from whatever the hub reports it has.
    async fn upload(&self, blob: &BlobId) -> anyhow::Result<()> {
        let chunk = chunk_size(self.transport.max_payload());
        let mut offset = 0;
        loop {
            let (total, data) = self.blobs.read(blob, offset, chunk)?;
            let request = HubRequest::PutChunk {
                blob: *blob,
                total,
                offset,
                data,
            };
            match self.exchange(Envelope::encode(request)?).await? {
                HubReply::ChunkAck { complete: true, .. } => return Ok(()),
                HubReply::ChunkAck { received, .. } => offset = received,
                HubReply::Error(err) => anyhow::bail!("hub: {err}"),
                other => anyhow::bail!("unexpected reply {other:?}"),
            }
        }
    }

    /// Downloads a blob in chunks into the local blob store, returning its file.
    async fn download(&self, blob: &BlobId) -> anyhow::Result<std::path::PathBuf> {
        let chunk = chunk_size(self.transport.max_payload()) as u64;
        let mut offset = 0;
        loop {
            if let Some(path) = self.blobs.get(blob) {
                return Ok(path);
            }
            let request = HubRequest::GetChunk {
                blob: *blob,
                offset,
                len: chunk,
            };
            let (total, data) = match self.exchange(Envelope::encode(request)?).await? {
                HubReply::Chunk { total, data } => (total, data),
                HubReply::Error(err) => anyhow::bail!("hub: {err}"),
                other => anyhow::bail!("unexpected reply {other:?}"),
            };
            offset = match self.blobs.receive(blob, total, offset, &data)? {
                Received::Complete => continue,
                Received::Prefix(have) => have,
            };
        }
    }
}

fn reply_blobs(reply: &Reply<Vec<u8>, WireAttachment>) -> Vec<BlobId> {
    match reply {
        Reply::Ops {
            attachment: WireAttachment::Blob { blob, .. },
            ..
        }
        | Reply::Objects {
            attachment: WireAttachment::Blob { blob, .. },
            ..
        } => vec![*blob],
        _ => vec![],
    }
}
