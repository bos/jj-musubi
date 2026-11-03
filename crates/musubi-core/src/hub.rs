//! The hub's request handling (docs/internals/protocol.md, "Hub" and "Supersedes").
//!
//! The hub is a function of its storage: [`handle`] answers one request. Callers must run it
//! for one request at a time per hive, which makes every `Push` atomic.

use crate::message::HeadKind;
use crate::message::OpEntry;
use crate::message::RecordState;
use crate::message::Reply;
use crate::message::Request;

/// The hub's state, which outlives a restart.
pub trait HubStorage {
    type Op: Clone + Eq;
    type Attachment;
    type Error;

    /// The current `(seq, head)`.
    fn head(&self) -> (u64, Self::Op);

    /// Replaces the head, which must be stored before this returns. A supersede's `dropped`
    /// becomes the next record, less what the records drop already, if that leaves any: the
    /// storage computes its history with them dropped (docs/internals/design.md, "Abandoning
    /// operations"), and keeps the records it had as of each head.
    fn set_head(
        &mut self,
        seq: u64,
        head: &Self::Op,
        dropped: &[Self::Op],
    ) -> Result<(), Self::Error>;

    /// The hub's records as of its head.
    fn records(&self) -> RecordState;

    /// How many of its first records the hub has pruned, keeping of them only this, and their
    /// digest.
    fn pruned(&self) -> RecordState;

    /// The hub's records that a party with `records` lacks: those from the returned index on.
    /// That is `records.count` where the party's records are the hub's first ones, and
    /// otherwise how many it has pruned, all those it remembers.
    #[expect(clippy::type_complexity)]
    fn records_since(
        &self,
        records: &RecordState,
    ) -> Result<(u64, Vec<Vec<Self::Op>>), Self::Error>;

    /// Whether `op` is dropped, by the records the hub remembers or by `dropped`.
    fn is_dropped(&self, op: &Self::Op, dropped: &[Self::Op]) -> Result<bool, Self::Error>;

    /// Remembers that `machine` said it took `records`, in a request. Kept only in memory: a
    /// hub that restarts waits to hear from every machine again.
    fn report(&mut self, machine: &str, records: &RecordState);

    /// What `machine` last said it took, since the hub started.
    fn reported(&self, machine: &str) -> Option<RecordState>;

    /// Prunes the first `count` records, which the hub has, and at least as many as it has
    /// pruned: forgets their ids, and the ids they superseded, keeping their count and digest.
    fn prune(&mut self, count: u64) -> Result<(), Self::Error>;

    fn store_ops(
        &mut self,
        ops: &[Self::Op],
        attachment: &Self::Attachment,
    ) -> Result<(), Self::Error>;

    fn store_objects(
        &mut self,
        for_ops: &[Self::Op],
        attachment: &Self::Attachment,
    ) -> Result<(), Self::Error>;

    /// The stored operations in `anc*(head) \ anc*(base)`, ancestors first, with an
    /// attachment carrying their content.
    #[expect(clippy::type_complexity)]
    fn ops_since(
        &self,
        head: &Self::Op,
        base: &Self::Op,
    ) -> Result<(Vec<OpEntry<Self::Op>>, Self::Attachment), Self::Error>;

    /// As `ops_since`, also carrying the canonical bodies and parent closure of the
    /// records sent with this reply. Only the returned entries are current-head history.
    /// A backend whose ids describe immutable operations needs no extra bodies.
    #[expect(clippy::type_complexity)]
    fn ops_with_records(
        &self,
        head: &Self::Op,
        base: &Self::Op,
        _records: &[Vec<Self::Op>],
    ) -> Result<(Vec<OpEntry<Self::Op>>, Self::Attachment), Self::Error> {
        self.ops_since(head, base)
    }

    /// An attachment carrying the stored objects that `for_ops` require, omitting what the
    /// node has: `closure(base)`, and what `haves` says.
    fn objects_for(
        &self,
        for_ops: &[Self::Op],
        base: &Self::Op,
        haves: &Self::Attachment,
    ) -> Result<Self::Attachment, Self::Error>;

    /// Whether `closure(op) ⊆ ops ∪ objects`, once the history drops `dropped` too.
    fn is_closed(&self, op: &Self::Op, dropped: &[Self::Op]) -> Result<bool, Self::Error>;

    /// Whether `ancestor ∈ anc*(op)`, judged from stored operations, once the history drops
    /// `dropped` too, as `ancestor` is then named. Only asked once `is_closed(op, dropped)`
    /// holds.
    fn descends(
        &self,
        ancestor: &Self::Op,
        op: &Self::Op,
        dropped: &[Self::Op],
    ) -> Result<bool, Self::Error>;
}

/// The result of handling a request.
#[derive(Debug, PartialEq, Eq)]
pub struct Handled<O, A> {
    pub reply: Reply<O, A>,
    /// A new head to publish to every node, after the reply, with the hub's records as of it.
    pub publish: Option<(u64, O, RecordState)>,
}

/// [`Handled`] for a given storage.
pub type HandledBy<S> = Handled<<S as HubStorage>::Op, <S as HubStorage>::Attachment>;

/// How the hub answered a `Push`, for tests that check each decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CasOutcome {
    /// `new` was already the head.
    Idempotent,
    Accepted,
    Rejected,
    /// `expected` was the head, but `closure(new)` isn't stored.
    Incomplete,
    /// The push's records aren't the hub's, or its new head is dropped.
    Refused,
}

pub fn handle<S: HubStorage>(
    storage: &mut S,
    request: Request<S::Op, S::Attachment>,
) -> Result<HandledBy<S>, S::Error> {
    let reply = |reply| {
        Ok(Handled {
            reply,
            publish: None,
        })
    };
    match request {
        Request::Fetch {
            machine,
            base,
            haves,
            records,
        } => {
            storage.report(&machine, &records);
            let (seq, head) = storage.head();
            let (records_from, new_records) = storage.records_since(&records)?;
            let (ops, ops_attachment) = storage.ops_with_records(&head, &base, &new_records)?;
            let ids: Vec<S::Op> = ops.iter().map(|entry| entry.id.clone()).collect();
            let objects = storage.objects_for(&ids, &base, &haves)?;
            reply(Reply::Fetched {
                seq,
                head,
                ops,
                ops_attachment,
                objects,
                records: storage.records(),
                records_from,
                new_records,
                pruned: storage.pruned(),
            })
        }
        Request::GetObjects {
            for_ops,
            base,
            haves,
        } => {
            let attachment = storage.objects_for(&for_ops, &base, &haves)?;
            reply(Reply::Objects {
                for_ops,
                attachment,
            })
        }
        Request::Push {
            machine,
            ops,
            ops_attachment,
            objects,
            expected,
            new,
            records,
            dropped,
        } => {
            let push = Push {
                machine: &machine,
                ops: &ops,
                ops_attachment: &ops_attachment,
                objects: &objects,
                expected: &expected,
                new: &new,
                records: &records,
                dropped: &dropped,
            };
            push.answer(storage).map(|(_, handled)| handled)
        }
    }
}

/// Prunes all of the hub's records once every machine in `waited` has said it took every
/// one, and it remembers any (docs/internals/design.md, "What an abandon costs the hub"):
/// pruning only what every machine has taken keeps every machine converging
/// (`Exec.sexec_allPruned`). The caller says which machines to wait for: every copy the hive
/// hasn't forgotten. Returns how many records the hub has pruned, if it pruned any now.
pub fn prune<S: HubStorage>(
    storage: &mut S,
    waited: impl IntoIterator<Item = impl AsRef<str>>,
) -> Result<Option<u64>, S::Error> {
    let records = storage.records();
    if storage.pruned().count == records.count {
        return Ok(None);
    }
    for machine in waited {
        if storage.reported(machine.as_ref()).as_ref() != Some(&records) {
            return Ok(None);
        }
    }
    storage.prune(records.count)?;
    Ok(Some(records.count))
}

/// A `Push`, borrowed.
pub struct Push<'a, O, A> {
    pub machine: &'a str,
    pub ops: &'a [O],
    pub ops_attachment: &'a A,
    pub objects: &'a A,
    pub expected: &'a O,
    pub new: &'a O,
    pub records: &'a RecordState,
    pub dropped: &'a [O],
}

impl<O: Clone + Eq, A> Push<'_, O, A> {
    /// Answers the push. It is refused, storing nothing, unless its records are the hub's and
    /// `new` isn't dropped, by the records the hub remembers or by the push: its ids aren't
    /// the hub's. Once the hub has pruned a record, only the push's records keep out a head
    /// it dropped: a node never pushes one that a record it took drops. Otherwise it
    /// stores the operations and objects, then is idempotent if `new` is already the head,
    /// and otherwise accepted exactly when `head = expected`, `closure(new)` is stored, and
    /// `expected ∈ anc*(new)`, all once the history drops what the push drops. Where `head =
    /// expected` but `closure(new)` isn't stored, the node lacks what `new` requires, and the
    /// answer says so.
    pub fn answer<S>(&self, storage: &mut S) -> Result<(CasOutcome, HandledBy<S>), S::Error>
    where
        S: HubStorage<Op = O, Attachment = A>,
    {
        storage.report(self.machine, self.records);
        let records = storage.records();
        if *self.records != records || storage.is_dropped(self.new, self.dropped)? {
            return Ok((
                CasOutcome::Refused,
                Handled {
                    reply: Reply::Refused { records },
                    publish: None,
                },
            ));
        }
        storage.store_ops(self.ops, self.ops_attachment)?;
        storage.store_objects(self.ops, self.objects)?;
        let (seq, head) = storage.head();
        let answer = |outcome, kind, seq, head, records| {
            let reply = Reply::Head {
                kind,
                seq,
                head,
                records,
            };
            Ok((
                outcome,
                Handled {
                    reply,
                    publish: None,
                },
            ))
        };
        if *self.new == head {
            return answer(
                CasOutcome::Idempotent,
                HeadKind::Accepted,
                seq,
                head,
                records,
            );
        }
        if head == *self.expected && !storage.is_closed(self.new, self.dropped)? {
            return answer(
                CasOutcome::Incomplete,
                HeadKind::Incomplete,
                seq,
                head,
                records,
            );
        }
        // Closed, if `head = expected`: the ancestry check needs every operation stored.
        if head == *self.expected && storage.descends(self.expected, self.new, self.dropped)? {
            storage.set_head(seq + 1, self.new, self.dropped)?;
            let records = storage.records();
            let reply = Reply::Head {
                kind: HeadKind::Accepted,
                seq: seq + 1,
                head: self.new.clone(),
                records: records.clone(),
            };
            let publish = Some((seq + 1, self.new.clone(), records));
            return Ok((CasOutcome::Accepted, Handled { reply, publish }));
        }
        answer(CasOutcome::Rejected, HeadKind::Rejected, seq, head, records)
    }
}
