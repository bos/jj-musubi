//! Protocol messages between nodes and the hub (docs/protocol.md, "Hub").
//!
//! Operation ids are generic so the same core serves real jj operation ids and the small
//! integers of the conformance tests. Bulky content (operation and object bundles) travels
//! as an opaque attachment, `A`: in production a reference to a chunked blob, in tests `()`.

use serde::Deserialize;
use serde::Serialize;

/// Which kind of message carried a `(seq, head)` pair. All are learned the same way.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum HeadKind {
    Head,
    Accepted,
    Rejected,
    Notify,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Request<O, A> {
    GetHead,
    /// Store these operations; the attachment carries their content.
    PutOps {
        ops: Vec<O>,
        attachment: A,
    },
    /// Store the objects these operations require; the attachment carries them.
    PutObjects {
        for_ops: Vec<O>,
        attachment: A,
    },
    /// The stored operations in `anc*(head) \ anc*(base)`. Sent only with `head` equal to
    /// the node's `known.head`, and `base` an operation the hub accepted.
    GetOpsSince {
        head: O,
        base: O,
    },
    /// The stored objects these operations require. The attachment can describe what the
    /// node already has, so the hub can send less.
    GetObjects {
        for_ops: Vec<O>,
        attachment: A,
    },
    Cas {
        expected: O,
        new: O,
    },
}

/// An operation in an [`Reply::Ops`] reply, with its parents, so the node can check it is
/// an ancestor of the head it asked about before staging it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpEntry<O> {
    pub id: O,
    pub parents: Vec<O>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Reply<O, A> {
    Head {
        kind: HeadKind,
        seq: u64,
        head: O,
    },
    Stored,
    /// Answer to `GetOpsSince { head, .. }`, ancestors first.
    Ops {
        head: O,
        ops: Vec<OpEntry<O>>,
        attachment: A,
    },
    Objects {
        for_ops: Vec<O>,
        attachment: A,
    },
}
