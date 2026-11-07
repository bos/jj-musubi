//! A hive's side of the wire: each encoded request answered, one at a time, with the head
//! to announce if it accepted one. `server::HubServer` serves it on a transport.

use std::collections::HashMap;
use std::time::Duration;
use std::time::Instant;
use std::time::SystemTime;

use jj_lib::object_id::ObjectId as _;
use musubi_core::hub;
use musubi_core::hub::HubStorage as _;
use musubi_core::message::HeadKind;
use musubi_core::message::RecordState;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_hub::activity::Outcome;

use crate::Attachment;
use crate::OpId;
use crate::blobs::BlobId;
use crate::blobs::BlobStore;
use crate::blobs::Received;
use crate::hub::HubAdapter;
use crate::remote::REQUEST_TIMEOUT;
use crate::remote::WINDOW;
use crate::remote::chunk_deadline;
use crate::short;
use crate::wire::Envelope;
use crate::wire::HeadNotice;
use crate::wire::HubReply;
use crate::wire::HubRequest;
use crate::wire::WireAttachment;
use crate::wire::WireRequest;
use crate::wire::chunk_size;
use crate::wire::inline_limit;
use crate::wire::map_reply;
use crate::wire::map_request;

/// How long the hub keeps a blob it prepared, or a node's upload, that no chunk has moved to
/// or from: one a node is still downloading or uploading is renewed as chunks of it move
/// ([`crate::blobs::RENEW_AFTER`]), so that this sweeps only blobs nobody went on with.
const PREPARED_BLOB_LIFETIME: Duration = Duration::from_secs(3600);

/// How long the hub answers a repeated protocol request with the reply it gave before, and
/// how many such replies it keeps. A node asks again at once when no reply comes in time, for
/// about ten minutes, and its daemon starts the sync over within a minute after that.
const REPLAY_LIFETIME: Duration = Duration::from_secs(600);
const REPLAYS: usize = 8;

/// How long the hub keeps a prepared blob after serving its last chunk, in case the node
/// asks for a chunk again because a reply didn't come in time: the requests of a window reach
/// the hub together, but the node waits for the last of their replies as long as for a chunk
/// one past the window's last ([`chunk_deadline`]), the time to ask again included.
const SERVED_BLOB_LIFETIME: Duration = chunk_deadline(REQUEST_TIMEOUT, WINDOW);

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
    /// What the latest request did.
    outcome: Outcome,
    /// Recent answers to protocol requests, oldest first, to answer a repeat with.
    answered: Vec<Answered>,
    /// How many protocol requests the hub has worked out an answer to, rather than replayed.
    #[cfg(test)]
    afresh: u64,
}

/// A protocol request answered, kept to answer the same request with while the hive is as it
/// was ([`HubService::replay`]).
struct Answered {
    /// The id of the request's encoding.
    key: BlobId,
    /// The hive as the reply left it.
    hive: HiveState,
    max_payload: usize,
    at: Instant,
    /// The encoded reply.
    reply: Vec<u8>,
    /// The prepared blobs it names.
    blobs: Vec<BlobId>,
    outcome: Outcome,
}

#[derive(PartialEq, Eq)]
struct HiveState {
    seq: u64,
    head: OpId,
    records: RecordState,
    pruned: RecordState,
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
            outcome: Outcome::Other,
            answered: vec![],
            #[cfg(test)]
            afresh: 0,
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

    /// Prepares `bytes` for nodes to download, as for a reply too large to send whole, for
    /// tests of downloading.
    #[cfg(test)]
    pub(crate) fn prepare(&mut self, bytes: &[u8]) -> anyhow::Result<(BlobId, u64)> {
        let (blob, len) = self.prepared.insert_bytes(bytes)?;
        self.served.remove(&blob);
        Ok((blob, len))
    }

    /// Prunes the hive's records, once every machine it waits for has taken them
    /// ([`HubAdapter::prune`]). Returns how many it has pruned, if it pruned any now.
    pub fn prune(&mut self) -> anyhow::Result<Option<u64>> {
        self.hub.prune()
    }

    /// How many protocol requests the hub has worked out an answer to, rather than replayed.
    #[cfg(test)]
    pub(crate) fn afresh(&self) -> u64 {
        self.afresh
    }

    /// What the latest request did, for the hub's activity.
    pub fn outcome(&self) -> Outcome {
        self.outcome
    }

    /// Whether a request whose sender has stopped waiting for the reply is still worth
    /// handling: a chunk of an upload, whose bytes have crossed the link already, and take the
    /// upload further for the sender's next attempt. Any other answer would go to nobody.
    pub fn worth_handling_unheard(bytes: &[u8]) -> bool {
        matches!(
            Envelope::<HubRequest>::decode(bytes),
            Ok(HubRequest::PutChunk { data, .. }) if !data.is_empty()
        )
    }

    /// Handles one encoded request, returning the encoded reply and any head to announce.
    pub fn handle_bytes(
        &mut self,
        bytes: &[u8],
        max_payload: usize,
    ) -> anyhow::Result<(Vec<u8>, Option<HeadNotice>)> {
        self.handled += 1;
        self.outcome = Outcome::Other;
        self.forget_served();
        if self.handled.is_multiple_of(100) {
            self.sweep();
        }
        // A protocol request is known by the id of its encoding, whether it came whole or as
        // an upload, which has that id.
        let (request, key) = match Envelope::<HubRequest>::decode(bytes)? {
            HubRequest::Protocol(request) => (request, BlobId::of_bytes(bytes)),
            HubRequest::Indirect { blob } => (self.uploaded_request(&blob)?, blob),
            transfer => {
                let reply = self.transfer(transfer, max_payload)?;
                return Ok((self.encode_reply(reply, max_payload, &mut vec![])?, None));
            }
        };
        let hive = self.hive_state();
        if let Some(reply) = self.replay(&key, &hive, max_payload, &request)? {
            return Ok((reply, None));
        }
        let mut blobs = vec![];
        let (reply, notice) = self.protocol(request, max_payload, &mut blobs)?;
        // Whether `Incomplete` still holds can change while the head doesn't: a push that the
        // hub rejects stores its operations and objects all the same.
        let replayable = !matches!(
            &reply,
            HubReply::Protocol(Reply::Head {
                kind: HeadKind::Incomplete,
                ..
            })
        );
        let encoded = self.encode_reply(reply, max_payload, &mut blobs)?;
        if replayable {
            self.remember(Answered {
                key,
                hive: self.hive_state(),
                max_payload,
                at: Instant::now(),
                reply: encoded.clone(),
                blobs,
                outcome: self.outcome,
            });
        }
        Ok((encoded, notice))
    }

    /// `reply`, encoded, as a prepared blob it names if it is too large to send whole.
    /// Prepared blobs it names are added to `blobs`.
    fn encode_reply(
        &mut self,
        reply: HubReply,
        max_payload: usize,
        blobs: &mut Vec<BlobId>,
    ) -> anyhow::Result<Vec<u8>> {
        let encoded = Envelope::encode(reply)?;
        if encoded.len() <= max_payload {
            return Ok(encoded);
        }
        let (blob, len) = self.prepared.insert_bytes(&encoded)?;
        self.served.remove(&blob);
        blobs.push(blob);
        Envelope::encode(HubReply::Indirect { blob, len })
    }

    /// The protocol request a node uploaded as `blob`, which it no longer needs.
    fn uploaded_request(&mut self, blob: &BlobId) -> anyhow::Result<WireRequest> {
        let path = self
            .uploads
            .get(blob)
            .ok_or_else(|| anyhow::anyhow!("no blob {blob:?}"))?;
        let inner = Envelope::<HubRequest>::decode(&std::fs::read(path)?)?;
        self.uploads.remove(blob);
        match inner {
            HubRequest::Protocol(request) => Ok(request),
            _ => anyhow::bail!("nested indirection"),
        }
    }

    /// What a protocol request's answer depends on, besides the request: the hive's head and
    /// records. The operations and objects in `closure(head)` don't change while the head
    /// doesn't, and the hub only ever adds the rest.
    fn hive_state(&self) -> HiveState {
        let (seq, head) = self.hub.head();
        HiveState {
            seq,
            head,
            records: self.hub.records(),
            pruned: self.hub.pruned(),
        }
    }

    /// The reply the hub gave to the same request, if it gave one recently, the hive is as
    /// it was then, and the blobs the reply names are still here: what answering again would
    /// say, without the work. A node sends a request again when the reply didn't come in
    /// time, as when the hub took longer than that to prepare it. Whatever the repeat
    /// uploaded is let go, and its machine counts as having reported again.
    fn replay(
        &mut self,
        key: &BlobId,
        hive: &HiveState,
        max_payload: usize,
        request: &WireRequest,
    ) -> anyhow::Result<Option<Vec<u8>>> {
        let now = Instant::now();
        self.answered
            .retain(|answered| now.duration_since(answered.at) < REPLAY_LIFETIME);
        let Some(at) = self.answered.iter().position(|answered| {
            answered.key == *key && answered.hive == *hive && answered.max_payload == max_payload
        }) else {
            return Ok(None);
        };
        let answered = self.answered.remove(at);
        for blob in &answered.blobs {
            if !self.prepared.renew(blob)? {
                return Ok(None);
            }
            self.served.remove(blob);
        }
        let (machine, records) = match request {
            Request::Fetch {
                machine, records, ..
            }
            | Request::Push {
                machine, records, ..
            } => (Some(machine), Some(records)),
            Request::GetObjects { .. } => (None, None),
        };
        if let (Some(machine), Some(records)) = (machine, records) {
            self.hub.report(machine, records);
        }
        for blob in request_blobs(request) {
            self.uploads.remove(&blob);
        }
        tracing::debug!("answered a repeated request as before");
        // The head moved once, whatever the replies to the push.
        self.outcome = match answered.outcome {
            Outcome::Accepted => Outcome::Other,
            outcome => outcome,
        };
        let reply = answered.reply.clone();
        self.answered.push(answered);
        Ok(Some(reply))
    }

    /// Keeps `answered` to replay, in place of any older answer to the same request, and
    /// forgetting the oldest beyond [`REPLAYS`].
    fn remember(&mut self, answered: Answered) {
        self.answered.retain(|old| old.key != answered.key);
        if self.answered.len() >= REPLAYS {
            self.answered.remove(0);
        }
        self.answered.push(answered);
    }

    /// Answers a request that moves part of a blob.
    fn transfer(&mut self, request: HubRequest, max_payload: usize) -> anyhow::Result<HubReply> {
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
                Ok(HubReply::ChunkAck { received, complete })
            }
            HubRequest::GetChunk { blob, offset, len } => {
                // Not the whole of a large blob in memory, for a reply that couldn't carry it.
                let len = usize::try_from(len)
                    .unwrap_or(usize::MAX)
                    .min(chunk_size(max_payload));
                let (total, data) = self.prepared.read_chunk(&blob, offset, len)?;
                // Once one download has finished, another may still be going: the time it is
                // kept runs from the last chunk anyone asks for.
                if reaches_end(offset, data.len(), total) || self.served.contains_key(&blob) {
                    self.served.insert(blob, Instant::now());
                }
                Ok(HubReply::Chunk { total, data })
            }
            HubRequest::Protocol(_) | HubRequest::Indirect { .. } => {
                unreachable!("handled as a protocol request")
            }
        }
    }

    /// Answers a protocol request. Prepared blobs the reply names are added to `blobs`.
    fn protocol(
        &mut self,
        request: WireRequest,
        max_payload: usize,
        blobs: &mut Vec<BlobId>,
    ) -> anyhow::Result<(HubReply, Option<HeadNotice>)> {
        #[cfg(test)]
        {
            self.afresh += 1;
        }
        let mut uploaded = vec![];
        let request = map_request(request, OpId::new, |attachment| {
            attachment.into_attachment(&self.uploads, |blob| {
                uploaded.push(blob);
                let path = self
                    .uploads
                    .get(&blob)
                    .ok_or_else(|| anyhow::anyhow!("attachment {blob:?} was not uploaded"))?;
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
        self.outcome = match &handled.reply {
            Reply::Head {
                kind: HeadKind::Accepted,
                ..
            } if handled.publish.is_some() => Outcome::Accepted,
            Reply::Head {
                kind: HeadKind::Rejected,
                ..
            } => Outcome::Rejected,
            Reply::Head {
                kind: HeadKind::Incomplete,
                ..
            } => Outcome::Incomplete,
            Reply::Fetched { ops, .. } => Outcome::Sent(ops.len() as u64),
            _ => Outcome::Other,
        };
        if let Some((seq, head, _)) = &handled.publish {
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
                    blobs.push(blob);
                    Ok((blob, len))
                })
            },
        )?;
        let notice = handled.publish.map(|(seq, head, records)| HeadNotice {
            seq,
            head: head.to_bytes(),
            records,
        });
        Ok((HubReply::Protocol(reply), notice))
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

    /// Deletes prepared blobs and uploads that no chunk has moved for an hour.
    fn sweep(&self) {
        let cutoff = SystemTime::now() - PREPARED_BLOB_LIFETIME;
        self.uploads.sweep(cutoff);
        self.prepared.sweep(cutoff);
    }
}

/// Whether a chunk of `got` bytes read from `offset` of a blob of `total` bytes is the last a
/// download asks for: it ends the blob, or the download asked past the end.
fn reaches_end(offset: u64, got: usize, total: u64) -> bool {
    offset + got as u64 >= total
}

/// The uploaded blobs a protocol request names.
fn request_blobs(request: &WireRequest) -> Vec<BlobId> {
    let attachments = match request {
        Request::Fetch { haves, .. } => vec![haves],
        Request::GetObjects { haves, .. } => vec![haves],
        Request::Push {
            ops_attachment,
            objects,
            ..
        } => vec![ops_attachment, objects],
    };
    attachments
        .into_iter()
        .filter_map(|attachment| match attachment {
            WireAttachment::Blob { blob, .. } => Some(*blob),
            _ => None,
        })
        .collect()
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
        Reply::Head {
            kind, seq, head, ..
        } => {
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
        Reply::Refused { .. } => tracing::debug!("refused a push: other records"),
    }
}

#[cfg(kani)]
mod proofs {
    use super::*;
    use crate::blobs::span;

    /// For any offset and length a node asks for, however hostile, the check after a read
    /// can't overflow, and holds exactly when the read reached the end of the blob.
    #[kani::proof]
    fn a_download_ends_where_the_blob_does() {
        let (total, offset, len): (u64, u64, usize) = kani::any();
        let span = span(total, offset, len);
        assert!(span.start <= span.end && span.end <= total);
        let got = usize::try_from(span.end - span.start).unwrap();
        assert_eq!(reaches_end(offset, got, total), span.end == total);
    }
}
