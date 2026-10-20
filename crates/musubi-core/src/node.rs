//! A node's side of the protocol (docs/protocol.md, "Node").
//!
//! [`NodeCore`] holds the node's volatile protocol state and implements the policy. Its
//! persistent state lives in the [`LocalRepo`]: the jj repository in production, a model of
//! it in tests. Neither performs I/O on the network: [`NodeCore::step`] returns requests to
//! send, and [`NodeCore::handle`] consumes replies.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use crate::message::HeadKind;
use crate::message::OpEntry;
use crate::message::Reply;
use crate::message::Request;

/// A node's persistent state, in canonical terms.
pub trait LocalRepo {
    type Op: Clone + Ord + Hash + Debug;
    type Attachment;
    type Error;

    /// The canonical forms of the local op heads (canonicalizing any new local operations).
    fn heads(&mut self) -> Result<Vec<Self::Op>, Self::Error>;

    /// Whether `op` is present locally, as an original or a realization.
    fn is_local(&self, op: &Self::Op) -> Result<bool, Self::Error>;

    /// Whether `ancestor ∈ anc*(op)`, for local `op`.
    fn is_ancestor(&self, ancestor: &Self::Op, op: &Self::Op) -> Result<bool, Self::Error>;

    /// Has jj merge the op heads, as any `jj` command would.
    fn merge_heads(&mut self) -> Result<(), Self::Error>;

    /// `anc*(head) \ anc*(base)`, ancestors first, for local `head` and `base`.
    fn ops_between(&self, head: &Self::Op, base: &Self::Op) -> Result<Vec<Self::Op>, Self::Error>;

    /// The content of `ops`, for `PutOps`.
    fn ops_attachment(&self, ops: &[Self::Op]) -> Result<Self::Attachment, Self::Error>;

    /// The objects `ops` require, for `PutObjects`, omitting what the hub has because it
    /// holds `closure(base)`.
    fn objects_attachment(
        &self,
        ops: &[Self::Op],
        base: &Self::Op,
    ) -> Result<Self::Attachment, Self::Error>;

    /// What to tell the hub in `GetObjects` about the objects this node already has.
    fn objects_request(&self, ops: &[Self::Op]) -> Result<Self::Attachment, Self::Error>;

    /// Stores received operations without realizing them.
    fn stage_ops(
        &mut self,
        ops: &[OpEntry<Self::Op>],
        attachment: &Self::Attachment,
    ) -> Result<(), Self::Error>;

    /// Stores received objects for `for_ops`.
    fn stage_objects(
        &mut self,
        for_ops: &[Self::Op],
        attachment: &Self::Attachment,
    ) -> Result<(), Self::Error>;

    /// The parents of a staged operation, or `None` if it is not staged.
    fn staged_parents(&self, op: &Self::Op) -> Result<Option<Vec<Self::Op>>, Self::Error>;

    /// Whether the objects `op` requires are all present, locally or staged.
    fn objects_available(&self, op: &Self::Op) -> Result<bool, Self::Error>;

    /// Realizes a staged operation whose parents are local and whose objects are available.
    fn realize(&mut self, op: &Self::Op) -> Result<(), Self::Error>;

    /// Makes a local operation an op head (`heads := max(heads ∪ {op})`).
    fn advance(&mut self, op: &Self::Op) -> Result<(), Self::Error>;

    /// A local operation the hub has accepted, used as the base of `GetOpsSince` so a node
    /// is not sent history it already has. The root operation is always valid.
    fn accepted_base(&self) -> Result<Self::Op, Self::Error>;

    fn set_accepted_base(&mut self, op: &Self::Op) -> Result<(), Self::Error>;
}

/// What [`NodeCore::step`] did.
#[derive(Debug, PartialEq, Eq)]
pub enum Step<O, A> {
    /// Nothing to do until a reply, a notification, or a local change.
    Idle,
    /// Asked jj to merge the op heads.
    Merged,
    Realized(O),
    Advanced(O),
    Send(Vec<Request<O, A>>),
}

/// What [`NodeCore::handle`] did with a reply.
#[derive(Debug, PartialEq, Eq)]
pub enum Handled<O> {
    /// Adopted a newer `(seq, head)`.
    Learned { kind: HeadKind, seq: u64, head: O },
    /// Staged the operations of an `Ops` reply.
    StagedOps(Vec<O>),
    /// Staged the objects of an `Objects` reply.
    StagedObjects(Vec<O>),
    /// Counted a `Stored` acknowledgement.
    Acknowledged,
    /// Ignored: stale, unrequested, or not an ancestor of the head it claims.
    Ignored,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Upload<O> {
    None,
    /// `PutOps` and `PutObjects` for `head` were sent; `acks` counts `Stored` replies.
    Sent {
        head: O,
        acks: u8,
    },
    /// Both were acknowledged; push next.
    Stored {
        head: O,
    },
}

pub struct NodeCore<O> {
    known: (u64, O),
    /// Heads this node sent `GetOpsSince` for; replies about any other head are ignored.
    requested: BTreeSet<O>,
    upload: Upload<O>,
}

impl<O: Clone + Ord + Hash + Debug> NodeCore<O> {
    /// A node that has just started: it knows only the root operation.
    pub fn new(root: O) -> Self {
        Self {
            known: (0, root),
            requested: BTreeSet::new(),
            upload: Upload::None,
        }
    }

    pub fn known(&self) -> &(u64, O) {
        &self.known
    }

    /// Takes the next policy step (docs/protocol.md, "Policy").
    pub fn step<R>(&mut self, repo: &mut R) -> Result<Step<O, R::Attachment>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        let heads = repo.heads()?;
        if heads.len() >= 2 {
            repo.merge_heads()?;
            return Ok(Step::Merged);
        }
        let known = self.known.1.clone();
        if !repo.is_local(&known)? {
            if let Some(op) = self.next_to_realize(repo, &known)? {
                repo.realize(&op)?;
                return Ok(Step::Realized(op));
            }
            return self.fetch(repo, &known);
        }
        let mut descends = false;
        for head in &heads {
            descends |= repo.is_ancestor(&known, head)?;
        }
        if !descends {
            repo.advance(&known)?;
            repo.set_accepted_base(&known)?;
            return Ok(Step::Advanced(known));
        }
        // The hub accepted `known`, and this node has it: fetch from here next time, so
        // that nothing is fetched twice, even when `known` is this node's own push. A
        // restart forgets `known`, so its root says nothing.
        if self.known.0 > 0 && repo.accepted_base()? != known {
            repo.set_accepted_base(&known)?;
        }
        // Not two or more heads, and op heads are never empty.
        let head = &heads[0];
        if *head == known {
            return Ok(Step::Idle);
        }
        // `known ∈ anc*(head)`: upload what the hub lacks, then push.
        if self.upload == (Upload::Stored { head: head.clone() }) {
            return Ok(Step::Send(vec![Request::Cas {
                expected: known,
                new: head.clone(),
            }]));
        }
        let ops = repo.ops_between(head, &known)?;
        let requests = vec![
            Request::PutOps {
                attachment: repo.ops_attachment(&ops)?,
                ops: ops.clone(),
            },
            Request::PutObjects {
                attachment: repo.objects_attachment(&ops, &known)?,
                for_ops: ops,
            },
        ];
        self.upload = Upload::Sent {
            head: head.clone(),
            acks: 0,
        };
        Ok(Step::Send(requests))
    }

    /// A staged operation in `anc*(known)` that can be realized now: its parents are local
    /// and its objects are available.
    fn next_to_realize<R>(&self, repo: &R, known: &O) -> Result<Option<O>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        let mut seen = HashSet::new();
        let mut stack = vec![known.clone()];
        while let Some(op) = stack.pop() {
            if !seen.insert(op.clone()) || repo.is_local(&op)? {
                continue;
            }
            let Some(parents) = repo.staged_parents(&op)? else {
                continue;
            };
            let mut all_local = true;
            for parent in &parents {
                if !repo.is_local(parent)? {
                    all_local = false;
                    stack.push(parent.clone());
                }
            }
            if all_local && repo.objects_available(&op)? {
                return Ok(Some(op));
            }
        }
        Ok(None)
    }

    /// Requests whatever `closure(known)` still lacks.
    fn fetch<R>(&mut self, repo: &R, known: &O) -> Result<Step<O, R::Attachment>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        let mut missing_ops = false;
        let mut missing_objects = vec![];
        let mut seen = HashSet::new();
        let mut stack = vec![known.clone()];
        while let Some(op) = stack.pop() {
            if !seen.insert(op.clone()) || repo.is_local(&op)? {
                continue;
            }
            match repo.staged_parents(&op)? {
                None => missing_ops = true,
                Some(parents) => {
                    if !repo.objects_available(&op)? {
                        missing_objects.push(op.clone());
                    }
                    stack.extend(parents);
                }
            }
        }
        let mut requests = vec![];
        if missing_ops {
            self.requested.insert(known.clone());
            let base = repo.accepted_base()?;
            requests.push(Request::GetOpsSince {
                head: known.clone(),
                base,
            });
        }
        if !missing_objects.is_empty() {
            missing_objects.sort();
            let attachment = repo.objects_request(&missing_objects)?;
            requests.push(Request::GetObjects {
                for_ops: missing_objects,
                attachment,
            });
        }
        Ok(if requests.is_empty() {
            Step::Idle
        } else {
            Step::Send(requests)
        })
    }

    pub fn handle<R>(
        &mut self,
        repo: &mut R,
        reply: Reply<O, R::Attachment>,
    ) -> Result<Handled<O>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        match reply {
            Reply::Head { kind, seq, head } => {
                if kind == HeadKind::Rejected
                    || matches!(&self.upload, Upload::Stored { head: h } if *h == head)
                {
                    // Rejected: the upload may not have landed, or the hub moved on; either
                    // way the next push starts over. Accepted: done with this upload.
                    self.upload = Upload::None;
                }
                if seq > self.known.0 {
                    self.known = (seq, head.clone());
                    Ok(Handled::Learned { kind, seq, head })
                } else {
                    Ok(Handled::Ignored)
                }
            }
            Reply::Stored => {
                if let Upload::Sent { head, acks } = &mut self.upload {
                    *acks += 1;
                    if *acks >= 2 {
                        self.upload = Upload::Stored { head: head.clone() };
                    }
                }
                Ok(Handled::Acknowledged)
            }
            Reply::Ops {
                head,
                ops,
                attachment,
            } => {
                if !self.requested.contains(&head) || !all_reach(&head, &ops) {
                    return Ok(Handled::Ignored);
                }
                repo.stage_ops(&ops, &attachment)?;
                Ok(Handled::StagedOps(
                    ops.into_iter().map(|entry| entry.id).collect(),
                ))
            }
            Reply::Objects {
                for_ops,
                attachment,
            } => {
                repo.stage_objects(&for_ops, &attachment)?;
                Ok(Handled::StagedObjects(for_ops))
            }
        }
    }

    /// Forgets everything volatile, as a restart does.
    pub fn restart(&mut self, root: O) {
        *self = Self::new(root);
    }
}

/// Whether every entry is reachable from `head` through parents among the entries: the
/// check that keeps operations the hub has not accepted out of `staged` (docs/protocol.md,
/// "Fetch").
fn all_reach<O: Hash + Eq>(head: &O, ops: &[OpEntry<O>]) -> bool {
    let parents: HashMap<&O, &[O]> = ops
        .iter()
        .map(|entry| (&entry.id, entry.parents.as_slice()))
        .collect();
    let mut reached = HashSet::new();
    let mut stack = vec![head];
    while let Some(op) = stack.pop() {
        if let Some(ps) = parents.get(op)
            && reached.insert(op)
        {
            stack.extend(ps.iter());
        }
    }
    reached.len() == parents.len()
}
