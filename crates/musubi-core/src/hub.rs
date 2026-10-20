//! The hub's request handling (docs/protocol.md, "Hub").
//!
//! The hub is a function of its storage: [`handle`] answers one request. Callers must run it
//! for one request at a time per hive, which makes every `Cas` check-and-set atomic.

use crate::message::HeadKind;
use crate::message::OpEntry;
use crate::message::Reply;
use crate::message::Request;

/// The hub's durable state.
pub trait HubStorage {
    type Op: Clone + Eq;
    type Attachment;
    type Error;

    /// The current `(seq, head)`.
    fn head(&self) -> (u64, Self::Op);

    /// Durably replaces the head. Must be persisted before returning.
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
    /// request's attachment says the node has.
    fn objects_for(
        &self,
        for_ops: &[Self::Op],
        request: &Self::Attachment,
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
    pub publish: Option<(u64, O)>,
}

/// [`Handled`] for a given storage.
pub type HandledBy<S> = Handled<<S as HubStorage>::Op, <S as HubStorage>::Attachment>;

/// How the hub answered a `Cas`, for tests that check each decision.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CasOutcome {
    /// `new` was already the head.
    Idempotent,
    Accepted,
    Rejected,
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
        Request::GetHead => {
            let (seq, head) = storage.head();
            reply(Reply::Head {
                kind: HeadKind::Head,
                seq,
                head,
            })
        }
        Request::PutOps { ops, attachment } => {
            storage.store_ops(&ops, &attachment)?;
            reply(Reply::Stored)
        }
        Request::PutObjects {
            for_ops,
            attachment,
        } => {
            storage.store_objects(&for_ops, &attachment)?;
            reply(Reply::Stored)
        }
        Request::GetOpsSince { head, base } => {
            let (ops, attachment) = storage.ops_since(&head, &base)?;
            reply(Reply::Ops {
                head,
                ops,
                attachment,
            })
        }
        Request::GetObjects {
            for_ops,
            attachment,
        } => {
            let attachment = storage.objects_for(&for_ops, &attachment)?;
            reply(Reply::Objects {
                for_ops,
                attachment,
            })
        }
        Request::Cas { expected, new } => cas(storage, &expected, &new).map(|(_, handled)| handled),
    }
}

/// Answers `Cas(expected, new)`: idempotent if `new` is already the head; otherwise accepted
/// exactly when `head = expected`, `closure(new)` is stored, and `expected ∈ anc*(new)`.
pub fn cas<S: HubStorage>(
    storage: &mut S,
    expected: &S::Op,
    new: &S::Op,
) -> Result<(CasOutcome, HandledBy<S>), S::Error> {
    let (seq, head) = storage.head();
    if *new == head {
        let reply = Reply::Head {
            kind: HeadKind::Accepted,
            seq,
            head,
        };
        return Ok((
            CasOutcome::Idempotent,
            Handled {
                reply,
                publish: None,
            },
        ));
    }
    if head == *expected && storage.is_closed(new)? && storage.descends(expected, new)? {
        storage.set_head(seq + 1, new)?;
        let reply = Reply::Head {
            kind: HeadKind::Accepted,
            seq: seq + 1,
            head: new.clone(),
        };
        let publish = Some((seq + 1, new.clone()));
        return Ok((CasOutcome::Accepted, Handled { reply, publish }));
    }
    let reply = Reply::Head {
        kind: HeadKind::Rejected,
        seq,
        head,
    };
    Ok((
        CasOutcome::Rejected,
        Handled {
            reply,
            publish: None,
        },
    ))
}
