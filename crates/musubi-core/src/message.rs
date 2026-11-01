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

/// The hub's records as a party took them: how many, and a digest of them all, so that two
/// parties can tell whether they took the same ones (docs/internals/protocol.md,
/// "Supersedes"). A record is a set of operations the hive dropped at once.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RecordState {
    pub count: u64,
    /// Opaque to the core: only compared.
    pub digest: Vec<u8>,
}

/// The hub's records as a party holds them: the first ones known only by their count and
/// digest, `base`, as a machine that joined after the hub pruned them holds them, then the
/// rest, oldest first, each sorted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Records<O> {
    pub base: RecordState,
    pub records: Vec<Vec<O>>,
}

impl<O> Records<O> {
    /// How many records these are, `base` included.
    pub fn count(&self) -> u64 {
        self.base.count + self.records.len() as u64
    }
}

/// A request. Each takes one round trip.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Request<O, A> {
    /// The hub's head, with the stored operations in `anc*(head) \ anc*(base)` and the
    /// stored objects they require. `base` is an operation the hub accepted that the node
    /// has, so the hub leaves out `closure(base)`; `haves` says what else the node has. The
    /// hub sends the records the node lacks, of its own, with them. `machine` is the node's
    /// key: the hub prunes its records once every machine it waits for has said it took them.
    Fetch {
        machine: String,
        base: O,
        haves: A,
        records: RecordState,
    },
    /// The stored objects these operations require, less `closure(base)` and what `haves`
    /// says the node has.
    GetObjects { for_ops: Vec<O>, base: O, haves: A },
    /// Store these operations and objects, then `Cas(expected, new)`, in one critical
    /// section. The attachments carry the operations and the objects they require. The hub
    /// refuses it unless `records` are its own. A supersede drops `dropped` too, which the
    /// hub then takes as its next record; an ordinary push drops nothing. `machine` is the
    /// node's key, as in `Fetch`.
    Push {
        machine: String,
        ops: Vec<O>,
        ops_attachment: A,
        objects: A,
        expected: O,
        new: O,
        records: RecordState,
        dropped: Vec<O>,
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
    /// (`Notify`), with the hub's records as of `head`.
    Head {
        kind: HeadKind,
        seq: u64,
        head: O,
        records: RecordState,
    },
    /// Answer to `Fetch`: the hub's `(seq, head)`, and the operations since the base,
    /// ancestors first, with their objects. With the hub's records: `new_records` are those
    /// from the `records_from`th on: the ones the node lacks, or, if the node's aren't the
    /// first of the hub's, all those the hub hasn't pruned. `pruned` is the count and digest
    /// of those it has: a node whose records don't start with them can never take the hub's.
    Fetched {
        seq: u64,
        head: O,
        ops: Vec<OpEntry<O>>,
        ops_attachment: A,
        objects: A,
        records: RecordState,
        records_from: u64,
        new_records: Vec<Vec<O>>,
        pruned: RecordState,
    },
    /// Answer to a `Push` whose records aren't the hub's, so that its ids aren't either, or
    /// whose new head is dropped: the hub took nothing of it.
    Refused {
        records: RecordState,
    },
    Objects {
        for_ops: Vec<O>,
        attachment: A,
    },
}
