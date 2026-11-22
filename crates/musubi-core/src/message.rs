//! Protocol messages between nodes and the hub (docs/internals/protocol.md, "Hub").
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
    /// again, since the node lacks what its operation requires (docs/internals/protocol.md).
    Incomplete,
    Notify,
}

/// The lowercase name logs use.
impl std::fmt::Display for HeadKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Head => "head",
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::Incomplete => "incomplete",
            Self::Notify => "notify",
        })
    }
}

/// A `(seq, head)` pair: the hub's `seq`th head, `head`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Head<O> {
    pub seq: u64,
    pub head: O,
}

/// A request. Each takes one round trip.
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

impl<O, A> Request<O, A> {
    /// Every attachment the request carries, in field order. Code that only needs to see the
    /// attachments uses this, so that a new variant is listed here and nowhere else.
    pub fn attachments(&self) -> Vec<&A> {
        match self {
            Self::Fetch { haves, .. } | Self::GetObjects { haves, .. } => vec![haves],
            Self::Push {
                ops_attachment,
                objects,
                ..
            } => vec![ops_attachment, objects],
        }
    }
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

impl<O, A> Reply<O, A> {
    /// Every attachment the reply carries, in field order; see [`Request::attachments`].
    pub fn attachments(&self) -> Vec<&A> {
        match self {
            Self::Fetched {
                ops_attachment,
                objects,
                ..
            } => vec![ops_attachment, objects],
            Self::Objects { attachment, .. } => vec![attachment],
            Self::Head { .. } => vec![],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::HeadKind;

    /// Logs name the kind of a reply's head in lowercase.
    #[test]
    fn head_kinds_print_their_lowercase_names() {
        let kinds = [
            HeadKind::Head,
            HeadKind::Accepted,
            HeadKind::Rejected,
            HeadKind::Incomplete,
            HeadKind::Notify,
        ];
        let names: Vec<String> = kinds.iter().map(ToString::to_string).collect();
        assert_eq!(
            names,
            ["head", "accepted", "rejected", "incomplete", "notify"]
        );
    }
}
