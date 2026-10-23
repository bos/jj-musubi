//! The bytes on the wire between nodes and a hub.
//!
//! Messages are postcard-encoded [`Envelope`]s. Every envelope starts with the protocol
//! version and the jj-lib version, and each side refuses to talk across a mismatch: canonical
//! operation ids are hashes of jj-lib's structs, so peers must agree on jj-lib exactly
//! (docs/design.md, "Compatibility"). Those two versions are read before the rest, which
//! another release may encode differently, so no release may change how they're encoded.
//!
//! A small bundle travels inline, in the message that refers to it; a larger one as a blob,
//! in chunks, several of them in flight at once. A message that would itself exceed the
//! transport's payload limit (a long list of operation ids, say) is stored as a blob and
//! sent as [`HubRequest::Indirect`] or [`HubReply::Indirect`].

use std::io;
use std::io::Write as _;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_core::message::OpEntry;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_hub::hub_dir::HiveInfo;
use musubi_hub::hub_dir::JoinRequest;
use musubi_hub::hub_dir::Joined;
use serde::Deserialize;
use serde::Serialize;

use crate::Attachment;
use crate::blobs::BlobId;
use crate::blobs::BlobStore;

pub const PROTOCOL_VERSION: u32 = 5;
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

impl WireAttachment {
    /// `attachment` as it travels: inline if it fits in what `inline_left` leaves of the
    /// message, which it then takes, and otherwise as a blob, which `store` stores.
    pub fn of(
        attachment: &Attachment,
        inline_left: &mut u64,
        store: impl FnOnce(&Path) -> io::Result<(BlobId, u64)>,
    ) -> anyhow::Result<Self> {
        Ok(match attachment {
            Attachment::None => Self::None,
            Attachment::Bundle(_) | Attachment::File(_) => {
                let path = attachment.bundle_path()?;
                let len = std::fs::metadata(path)?.len();
                if len <= *inline_left {
                    *inline_left -= len;
                    Self::Inline(std::fs::read(path)?)
                } else {
                    let (blob, len) = store(path)?;
                    Self::Blob { blob, len }
                }
            }
            Attachment::Haves(ids) => Self::Haves(ids.iter().map(|id| id.to_bytes()).collect()),
        })
    }

    /// The attachment this stands for: inline bytes in a temporary file in `blobs`, and a
    /// blob as `find` makes it.
    pub fn into_attachment(
        self,
        blobs: &BlobStore,
        find: impl FnOnce(BlobId) -> anyhow::Result<Attachment>,
    ) -> anyhow::Result<Attachment> {
        Ok(match self {
            Self::None => Attachment::None,
            Self::Blob { blob, .. } => find(blob)?,
            Self::Inline(bytes) => {
                // Not reopened truncating (see `BundleWriter::create`).
                let mut file = blobs.temp_file()?;
                file.write_all(&bytes)?;
                Attachment::bundle(file.into_temp_path())
            }
            Self::Haves(ids) => Attachment::Haves(ids.into_iter().map(CommitId::new).collect()),
        })
    }
}

pub type WireRequest = Request<WireId, WireAttachment>;
pub type WireReply = Reply<WireId, WireAttachment>;

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

/// The first token of every subject the hub serves (docs/design.md, "Transport").
const SUBJECT_PREFIX: &str = "musubi";

/// What stands in for a hive id in the subject of requests to the hub as a whole:
/// `musubi.hub.rpc`.
pub const HUB_TOKEN: &str = "hub";

/// The subject of requests to the hive `hive`; with [`HUB_TOKEN`], to the hub as a whole,
/// and with `*`, a pattern for all of them.
pub fn rpc_subject(hive: &str) -> String {
    format!("{SUBJECT_PREFIX}.{hive}.rpc")
}

/// The subject the hub announces the hive `hive`'s new heads on.
pub fn head_subject(hive: &str) -> String {
    format!("{SUBJECT_PREFIX}.{hive}.head")
}

/// What a request's subject names in place of a hive id (see [`rpc_subject`]).
pub fn rpc_token(subject: &str) -> Option<&str> {
    subject
        .strip_prefix(SUBJECT_PREFIX)?
        .strip_prefix('.')?
        .strip_suffix(".rpc")
}

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

/// The start of an [`Envelope`], the same in every release.
#[derive(Deserialize)]
struct Versions<'a> {
    protocol: u32,
    jj_lib: &'a str,
}

impl<T: for<'de> Deserialize<'de>> Envelope<T> {
    /// Checks versions, then decodes the body, which may not decode across them.
    pub fn decode(bytes: &[u8]) -> anyhow::Result<T> {
        let (versions, body) = postcard::take_from_bytes::<Versions<'_>>(bytes)?;
        anyhow::ensure!(
            versions.protocol == PROTOCOL_VERSION && versions.jj_lib == JJ_LIB_VERSION,
            "incompatible peer: protocol {} with jj-lib {}, but this is protocol {} with \
             jj-lib {}; run the same release of musubi on the hub and every machine",
            versions.protocol,
            versions.jj_lib,
            PROTOCOL_VERSION,
            JJ_LIB_VERSION
        );
        let (body, rest) = postcard::take_from_bytes(body)?;
        anyhow::ensure!(
            rest.is_empty(),
            "a message with {} bytes after its end",
            rest.len()
        );
        Ok(body)
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

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

    fn envelope<T: Serialize>(protocol: u32, jj_lib: &str, body: T) -> Vec<u8> {
        let envelope = Envelope {
            protocol,
            jj_lib: jj_lib.to_owned(),
            body,
        };
        postcard::to_stdvec(&envelope).unwrap()
    }

    /// Messages carry the jj-lib version musubi is built with, as the workspace pins it, and
    /// tests run the jj of that version: peers on different ones must refuse each other,
    /// since canonical operation ids are hashes of jj-lib's structs.
    #[test]
    fn jj_lib_version_is_the_pinned_one() {
        let manifest = concat!(env!("CARGO_MANIFEST_DIR"), "/../../Cargo.toml");
        let manifest = std::fs::read_to_string(manifest).unwrap();
        let pin = format!(r#"jj-lib = {{ version = "={JJ_LIB_VERSION}""#);
        assert!(
            manifest.contains(&pin),
            "jj-lib isn't pinned to {JJ_LIB_VERSION}"
        );
        assert_eq!(musubi_testutil::JJ_VERSION, JJ_LIB_VERSION);
    }

    #[test]
    fn a_reply_decodes() {
        let reply = HubReply::Error("no".to_owned());
        let bytes = Envelope::encode(reply.clone()).unwrap();
        assert_eq!(Envelope::<HubReply>::decode(&bytes).unwrap(), reply);
    }

    /// Nothing may follow a message, as nothing honest sends.
    #[test]
    fn bytes_after_a_message_are_refused() {
        let mut bytes = Envelope::encode(HubReply::Error("no".to_owned())).unwrap();
        bytes.push(0);
        let err = Envelope::<HubReply>::decode(&bytes).unwrap_err();
        assert!(err.to_string().contains("1 bytes after its end"), "{err}");
    }

    /// A message from another release is refused for its versions, even where this release
    /// can't decode the rest of it.
    #[test]
    fn another_release_is_refused_whatever_it_sends() {
        let unknown_variant = u32::MAX;
        let bytes = envelope(PROTOCOL_VERSION + 1, "9.9.9", unknown_variant);
        let err = Envelope::<HubReply>::decode(&bytes).unwrap_err();
        assert!(
            err.to_string().starts_with(&format!(
                "incompatible peer: protocol {} with jj-lib 9.9.9",
                PROTOCOL_VERSION + 1
            )),
            "{err}"
        );
        let bytes = envelope(PROTOCOL_VERSION, JJ_LIB_VERSION, unknown_variant);
        let err = Envelope::<HubReply>::decode(&bytes).unwrap_err();
        assert!(!err.to_string().contains("incompatible"), "{err}");
    }
}
