//! Protocol messages between nodes and the hub (docs/protocol.md, "Hub").
//!
//! Operation ids are generic so the same core serves real jj operation ids and the small
//! integers of the conformance tests. Bulky content (operation and object bundles) travels
//! as an opaque attachment, `A`: in production a bundle file, carried inline or as a chunked
//! blob; in tests the object ids themselves.

use serde::Deserialize;
use serde::Serialize;

/// Which kind of message carried a `(seq, head)` pair. All are learned the same way.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum HeadKind {
    Head,
    Accepted,
    /// A push that can't move the head: the head isn't the one it expected, as when another
    /// push came first, or its new head doesn't descend from that.
    Rejected,
    /// A push from the hub's head that the hub still can't close, whatever the node sends
    /// again, since the node lacks what its operation requires (docs/protocol.md).
    Incomplete,
    Notify,
}

/// A request. Each takes one round trip: `Fetch` and `Push` each do what used to take
/// several.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Request<O, A> {
    /// The hub's head, with the stored operations in `anc*(head) \ anc*(base)` and the
    /// stored objects they require. `base` is an operation the hub accepted that the node
    /// has, so the hub leaves out `closure(base)`; `haves` says what else the node has.
    Fetch { base: O, haves: A },
    /// The stored objects these operations require, less `closure(base)` and what `haves`
    /// says the node has.
    GetObjects { for_ops: Vec<O>, base: O, haves: A },
    /// Store these operations and objects, then `Cas(expected, new)`, in one critical
    /// section. The attachments carry the operations and the objects they require.
    Push {
        ops: Vec<O>,
        ops_attachment: A,
        objects: A,
        expected: O,
        new: O,
    },
}

/// An operation in a [`Reply::Fetched`] reply, with its parents, so the node can check it
/// is an ancestor of the head before staging it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpEntry<O> {
    pub id: O,
    pub parents: Vec<O>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Reply<O, A> {
    /// Answer to `Push` (`Accepted`, `Rejected` or `Incomplete`), and the hub's announcements
    /// (`Notify`).
    Head {
        kind: HeadKind,
        seq: u64,
        head: O,
    },
    /// Answer to `Fetch`: the hub's `(seq, head)`, and the operations since the base,
    /// ancestors first, with their objects.
    Fetched {
        seq: u64,
        head: O,
        ops: Vec<OpEntry<O>>,
        ops_attachment: A,
        objects: A,
    },
    Objects {
        for_ops: Vec<O>,
        attachment: A,
    },
}
