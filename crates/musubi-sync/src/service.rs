//! A hive's side of the wire: each encoded request answered, one at a time, with the head
//! to announce if it accepted one. `server::HubServer` serves it on a transport.

use std::collections::HashMap;
use std::time::Duration;
use std::time::Instant;
use std::time::SystemTime;

use jj_lib::object_id::ObjectId as _;
use musubi_core::hub;
use musubi_core::message::Reply;
use musubi_core::message::Request;

use crate::Attachment;
use crate::OpId;
use crate::blobs::BlobId;
use crate::blobs::BlobStore;
use crate::blobs::Received;
use crate::hub::HubAdapter;
use crate::short;
use crate::wire::Envelope;
use crate::wire::HeadNotice;
use crate::wire::HubReply;
use crate::wire::HubRequest;
use crate::wire::WireAttachment;
use crate::wire::chunk_size;
use crate::wire::inline_limit;
use crate::wire::map_reply;
use crate::wire::map_request;

/// How long the hub keeps a blob it prepared for a node that never downloaded all of it,
/// and an abandoned upload.
const PREPARED_BLOB_LIFETIME: Duration = Duration::from_secs(3600);

/// How long the hub keeps a prepared blob after serving its last chunk, in case the node
/// asks for a chunk again because a reply was lost.
const SERVED_BLOB_LIFETIME: Duration = Duration::from_secs(60);

pub struct HubService {
    hub: HubAdapter,
    /// Blobs nodes upload: bundles attached to their requests, and requests too large to
    /// send whole.
    uploads: BlobStore,
    /// Blobs prepared for nodes to download. They are kept apart from uploads, which can
    /// have the same content, so that deleting one never takes away the other.
    prepared: BlobStore,
    handled: u64,
    /// Prepared blobs whose last chunk has been served, and when a chunk of them was last
    /// asked for. A blob prepared again, for another reply with the same content, is taken
    /// out: that reply's download has only begun.
    served: HashMap<BlobId, Instant>,
    served_lifetime: Duration,
}

impl HubService {
    pub fn new(hub: HubAdapter, dir: &std::path::Path) -> anyhow::Result<Self> {
        let blobs = dir.join("blobs");
        Ok(Self {
            hub,
            uploads: BlobStore::open(&blobs)?,
            // Inside `blobs/`, so that it still holds every transfer, and so that a hub
            // upgraded from before sweeps the prepared blobs it left in `blobs/complete` as
            // old uploads.
            prepared: BlobStore::open(&blobs.join("prepared"))?,
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

    /// Makes it as if `elapsed` had passed since each served blob's last chunk, for tests
    /// that would otherwise sleep through the time the hub keeps one. Panics where the clock
    /// can't go back that far, as within a minute of booting: aging nothing, the test would
    /// test nothing.
    pub fn age_served_blobs(&mut self, elapsed: Duration) {
        for served in self.served.values_mut() {
            *served = served
                .checked_sub(elapsed)
                .expect("the clock goes back as far as the time to age");
        }
    }

    pub fn hub(&self) -> &HubAdapter {
        &self.hub
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
        let encoded = Envelope::encode(reply)?;
        if encoded.len() <= max_payload {
            return Ok((encoded, notice));
        }
        let (blob, len) = self.prepared.insert_bytes(&encoded)?;
        self.served.remove(&blob);
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
                let received = self.uploads.receive(&blob, total, offset, &data)?;
                let (received, complete) = match received {
                    Received::Prefix(have) => (have, false),
                    Received::Complete => (total, true),
                };
                Ok((HubReply::ChunkAck { received, complete }, None))
            }
            HubRequest::GetChunk { blob, offset, len } => {
                // Not the whole of a large blob in memory, for a reply that couldn't carry it.
                let len = usize::try_from(len)
                    .unwrap_or(usize::MAX)
                    .min(chunk_size(max_payload));
                let (total, data) = self.prepared.read(&blob, offset, len)?;
                // Once one download has finished, another may still be going: the minute
                // runs from the last chunk anyone asks for.
                if offset + data.len() as u64 >= total || self.served.contains_key(&blob) {
                    self.served.insert(blob, Instant::now());
                }
                Ok((HubReply::Chunk { total, data }, None))
            }
            HubRequest::Indirect { blob } => {
                let path = self
                    .uploads
                    .get(&blob)
                    .ok_or_else(|| anyhow::anyhow!("no blob {blob:?}"))?;
                let inner = Envelope::<HubRequest>::decode(&std::fs::read(path)?)?;
                self.uploads.remove(&blob);
                anyhow::ensure!(
                    matches!(inner, HubRequest::Protocol(_)),
                    "nested indirection"
                );
                self.handle(inner, max_payload)
            }
            HubRequest::Protocol(request) => {
                let mut uploaded = vec![];
                let request = map_request(request, OpId::new, |attachment| {
                    attachment.into_attachment(&self.uploads, |blob| {
                        uploaded.push(blob);
                        let path = self.uploads.get(&blob).ok_or_else(|| {
                            anyhow::anyhow!("attachment {blob:?} was not uploaded")
                        })?;
                        Ok(Attachment::File(path))
                    })
                })?;
                let pushed = log_request(&request);
                let handled = hub::handle(&mut self.hub, request);
                // Uploaded bundles are imported (or rejected) now; either way they are done.
                for blob in uploaded {
                    self.uploads.remove(&blob);
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
                        WireAttachment::of(&attachment, &mut inline_left, |path| {
                            let (blob, len) = self.prepared.insert_file(path)?;
                            self.served.remove(&blob);
                            Ok((blob, len))
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
        let (prepared, lifetime) = (&self.prepared, self.served_lifetime);
        self.served.retain(|blob, served| {
            let keep = now.duration_since(*served) < lifetime;
            if !keep {
                prepared.remove(blob);
            }
            keep
        });
    }

    /// Deletes prepared blobs nobody downloaded in time, and abandoned uploads.
    fn sweep(&self) {
        let cutoff = SystemTime::now() - PREPARED_BLOB_LIFETIME;
        self.uploads.sweep(cutoff);
        self.prepared.sweep(cutoff);
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
