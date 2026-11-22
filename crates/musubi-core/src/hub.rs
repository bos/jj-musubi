//! The hub's request handling (docs/internals/protocol.md, "Hub").
//!
//! The hub is a function of its storage: [`handle`] answers one request. Callers must run it
//! for one request at a time per hive, which makes every `Push` atomic.

use crate::message::Head;
use crate::message::HeadKind;
use crate::message::OpEntry;
use crate::message::Reply;
use crate::message::Request;

/// The hub's state, which outlives a restart.
pub trait HubStorage {
    type Op: Clone + Eq;
    type Attachment;
    type Error;

    /// The current `(seq, head)`.
    fn head(&self) -> Head<Self::Op>;

    /// Replaces the head, which must be stored before this returns.
    fn set_head(&mut self, seq: u64, head: &Self::Op) -> Result<(), Self::Error>;

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

    /// An attachment carrying the stored objects that `for_ops` require, omitting what the
    /// node has: `closure(base)`, and what `haves` says.
    fn objects_for(
        &self,
        for_ops: &[Self::Op],
        base: &Self::Op,
        haves: &Self::Attachment,
    ) -> Result<Self::Attachment, Self::Error>;

    /// Whether `closure(op) ⊆ ops ∪ objects`.
    fn is_closed(&self, op: &Self::Op) -> Result<bool, Self::Error>;

    /// Whether `ancestor ∈ anc*(op)`, judged from stored operations. Only asked once
    /// `is_closed(op)` holds.
    fn descends(&self, ancestor: &Self::Op, op: &Self::Op) -> Result<bool, Self::Error>;
}

/// The result of handling a request.
#[derive(Debug, PartialEq, Eq)]
pub struct Handled<O, A> {
    pub reply: Reply<O, A>,
    /// A new head to publish to every node, after the reply.
    pub publish: Option<Head<O>>,
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
        Request::Fetch { base, haves } => {
            let Head { seq, head } = storage.head();
            let (ops, ops_attachment) = storage.ops_since(&head, &base)?;
            let ids: Vec<S::Op> = ops.iter().map(|entry| entry.id.clone()).collect();
            let objects = storage.objects_for(&ids, &base, &haves)?;
            reply(Reply::Fetched {
                seq,
                head,
                ops,
                ops_attachment,
                objects,
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
            ops,
            ops_attachment,
            objects,
            expected,
            new,
        } => {
            let push = Push {
                ops: &ops,
                ops_attachment: &ops_attachment,
                objects: &objects,
                expected: &expected,
                new: &new,
            };
            push.answer(storage).map(|(_, handled)| handled)
        }
    }
}

/// A `Push`, borrowed.
pub struct Push<'a, O, A> {
    pub ops: &'a [O],
    pub ops_attachment: &'a A,
    pub objects: &'a A,
    pub expected: &'a O,
    pub new: &'a O,
}

impl<O: Clone + Eq, A> Push<'_, O, A> {
    /// Answers the push: stores the operations and objects, then is idempotent if `new` is
    /// already the head, and otherwise accepted exactly when `head = expected`, `closure(new)`
    /// is stored, and `expected ∈ anc*(new)`. Where `head = expected` but `closure(new)` isn't
    /// stored, the node lacks what `new` requires, and the answer says so.
    pub fn answer<S>(&self, storage: &mut S) -> Result<(CasOutcome, HandledBy<S>), S::Error>
    where
        S: HubStorage<Op = O, Attachment = A>,
    {
        storage.store_ops(self.ops, self.ops_attachment)?;
        storage.store_objects(self.ops, self.objects)?;
        let Head { seq, head } = storage.head();
        let answer = |outcome, kind, seq, head| {
            let reply = Reply::Head { kind, seq, head };
            Ok((
                outcome,
                Handled {
                    reply,
                    publish: None,
                },
            ))
        };
        if *self.new == head {
            return answer(CasOutcome::Idempotent, HeadKind::Accepted, seq, head);
        }
        if head == *self.expected && !storage.is_closed(self.new)? {
            return answer(CasOutcome::Incomplete, HeadKind::Incomplete, seq, head);
        }
        // Closed, if `head = expected`: the ancestry check needs every operation stored.
        if head == *self.expected && storage.descends(self.expected, self.new)? {
            storage.set_head(seq + 1, self.new)?;
            let reply = Reply::Head {
                kind: HeadKind::Accepted,
                seq: seq + 1,
                head: self.new.clone(),
            };
            let publish = Some(Head {
                seq: seq + 1,
                head: self.new.clone(),
            });
            return Ok((CasOutcome::Accepted, Handled { reply, publish }));
        }
        answer(CasOutcome::Rejected, HeadKind::Rejected, seq, head)
    }
}
