//! The bytes on the wire between nodes and a hub.
//!
//! Messages are postcard-encoded [`Envelope`]s. Every envelope carries the protocol version
//! and the jj-lib version, and the hub refuses to talk across a mismatch: canonical
//! operation ids are hashes of jj-lib's structs, so peers must agree on jj-lib exactly
//! (docs/design.md, "Compatibility").
//!
//! A small bundle travels inline, in the message that refers to it; a larger one as a blob,
//! in chunks, several of them in flight at once. A message that would itself exceed the
//! transport's payload limit (a long list of operation ids, say) is stored as a blob and
//! sent as [`HubRequest::Indirect`] or [`HubReply::Indirect`].

use musubi_core::message::OpEntry;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_hub::hub_dir::HiveInfo;
use musubi_hub::hub_dir::JoinRequest;
use musubi_hub::hub_dir::Joined;
use serde::Deserialize;
use serde::Serialize;

use crate::blobs::BlobId;

pub const PROTOCOL_VERSION: u32 = 4;
pub const JJ_LIB_VERSION: &str = "0.46.0";

/// An operation or commit id on the wire.
pub type WireId = Vec<u8>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WireAttachment {
    None,
    Blob { blob: BlobId, len: u64 },
    // As bytes, which postcard copies at once, rather than a sequence it takes one at a
    // time: attachments and chunks run to a megabyte.
    Inline(#[serde(with = "serde_bytes")] Vec<u8>),
    Haves(Vec<WireId>),
}

pub type WireRequest = Request<WireId, WireAttachment>;
pub type WireReply = Reply<WireId, WireAttachment>;
pub type WireOpEntry = OpEntry<WireId>;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HubRequest {
    Protocol(WireRequest),
    /// The real request is the content of this blob, already uploaded.
    Indirect {
        blob: BlobId,
    },
    PutChunk {
        blob: BlobId,
        total: u64,
        offset: u64,
        #[serde(with = "serde_bytes")]
        data: Vec<u8>,
    },
    GetChunk {
        blob: BlobId,
        offset: u64,
        len: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HubReply {
    Protocol(WireReply),
    /// The real reply is the content of this blob; fetch it with `GetChunk`.
    Indirect {
        blob: BlobId,
        len: u64,
    },
    /// After `PutChunk`: the receiver has the first `received` bytes, or all of them.
    ChunkAck {
        received: u64,
        complete: bool,
    },
    Chunk {
        total: u64,
        #[serde(with = "serde_bytes")]
        data: Vec<u8>,
    },
    Error(String),
}

/// What stands in for a hive id in the subject of requests to the hub as a whole:
/// `musubi.hub.rpc`.
pub const HUB_TOKEN: &str = "hub";

/// A request about the hub's hives rather than within one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HubWideRequest {
    /// Find the hive a repository belongs to, creating it if need be.
    Join(JoinRequest),
    List,
    /// Look up a hive by name, name prefix, or id.
    Resolve {
        name: String,
    },
    Rename {
        name: String,
        to: String,
    },
    Remove {
        name: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HubWideReply {
    Joined(Joined),
    Hives(Vec<HiveInfo>),
    Hive(HiveInfo),
    Error(String),
}

/// Published on the head subject whenever the hub accepts a new head.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HeadNotice {
    pub seq: u64,
    pub head: WireId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Envelope<T> {
    pub protocol: u32,
    pub jj_lib: String,
    pub body: T,
}

impl<T: Serialize> Envelope<T> {
    pub fn encode(body: T) -> anyhow::Result<Vec<u8>> {
        let envelope = Self {
            protocol: PROTOCOL_VERSION,
            jj_lib: JJ_LIB_VERSION.to_owned(),
            body,
        };
        Ok(postcard::to_stdvec(&envelope)?)
    }
}

impl<T: for<'de> Deserialize<'de>> Envelope<T> {
    /// Decodes and checks versions.
    pub fn decode(bytes: &[u8]) -> anyhow::Result<T> {
        let envelope: Self = postcard::from_bytes(bytes)?;
        anyhow::ensure!(
            envelope.protocol == PROTOCOL_VERSION && envelope.jj_lib == JJ_LIB_VERSION,
            "incompatible peer: protocol {} with jj-lib {}, but this is protocol {} with \
             jj-lib {}",
            envelope.protocol,
            envelope.jj_lib,
            PROTOCOL_VERSION,
            JJ_LIB_VERSION
        );
        Ok(envelope.body)
    }
}

/// The largest chunk to put in one message, leaving room for the envelope.
pub fn chunk_size(max_payload: usize) -> usize {
    max_payload.saturating_sub(1024).max(1024)
}

/// An error's message, cut short to fit in one reply: it can quote what the peer sent, and
/// a reply too large to send leaves the peer waiting for its timeout.
pub fn fit_error(mut message: String, max_payload: usize) -> String {
    let limit = chunk_size(max_payload);
    if message.len() > limit {
        message.truncate(message.floor_char_boundary(limit));
        message.push('…');
    }
    message
}

/// How many bytes of attachments one message carries inline, leaving room for the rest of
/// it. Larger attachments travel as blobs.
pub fn inline_limit(max_payload: usize) -> u64 {
    (max_payload / 4) as u64
}

/// Converts ids and attachments of a request.
pub fn map_request<O, A, P, B>(
    request: Request<O, A>,
    mut id: impl FnMut(O) -> P,
    mut attachment: impl FnMut(A) -> anyhow::Result<B>,
) -> anyhow::Result<Request<P, B>> {
    Ok(match request {
        Request::Fetch { base, haves } => Request::Fetch {
            base: id(base),
            haves: attachment(haves)?,
        },
        Request::GetObjects {
            for_ops,
            base,
            haves,
        } => Request::GetObjects {
            for_ops: for_ops.into_iter().map(&mut id).collect(),
            base: id(base),
            haves: attachment(haves)?,
        },
        Request::Push {
            ops,
            ops_attachment,
            objects,
            expected,
            new,
        } => Request::Push {
            ops: ops.into_iter().map(&mut id).collect(),
            ops_attachment: attachment(ops_attachment)?,
            objects: attachment(objects)?,
            expected: id(expected),
            new: id(new),
        },
    })
}

/// Converts ids and attachments of a reply.
pub fn map_reply<O, A, P, B>(
    reply: Reply<O, A>,
    mut id: impl FnMut(O) -> P,
    mut attachment: impl FnMut(A) -> anyhow::Result<B>,
) -> anyhow::Result<Reply<P, B>> {
    Ok(match reply {
        Reply::Head { kind, seq, head } => Reply::Head {
            kind,
            seq,
            head: id(head),
        },
        Reply::Fetched {
            seq,
            head,
            ops,
            ops_attachment,
            objects,
        } => Reply::Fetched {
            seq,
            head: id(head),
            ops: ops
                .into_iter()
                .map(|entry| OpEntry {
                    id: id(entry.id),
                    parents: entry.parents.into_iter().map(&mut id).collect(),
                })
                .collect(),
            ops_attachment: attachment(ops_attachment)?,
            objects: attachment(objects)?,
        },
        Reply::Objects {
            for_ops,
            attachment: a,
        } => Reply::Objects {
            for_ops: for_ops.into_iter().map(&mut id).collect(),
            attachment: attachment(a)?,
        },
    })
}
