//! A node's side of the protocol (docs/protocol.md, "Node").
//!
//! [`NodeCore`] holds the node's volatile protocol state and implements the policy. Its
//! persistent state lives in the [`LocalRepo`]: the jj repository in production, a model of
//! it in tests. Neither performs I/O on the network: [`NodeCore::step`] returns requests to
//! send, and [`NodeCore::handle`] consumes replies.

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
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

    /// The content of `ops`, for `Push`.
    fn ops_attachment(&self, ops: &[Self::Op]) -> Result<Self::Attachment, Self::Error>;

    /// The objects `ops` require, for `Push`, omitting what the hub has because it holds
    /// `closure(base)`.
    fn objects_attachment(
        &self,
        ops: &[Self::Op],
        base: &Self::Op,
    ) -> Result<Self::Attachment, Self::Error>;

    /// What to tell the hub in `Fetch` about the objects this node has beyond
    /// `closure(accepted_base)`, which the hub leaves out anyway.
    fn fetch_haves(&self) -> Result<Self::Attachment, Self::Error>;

    /// What to tell the hub in `GetObjects` for `ops` about the objects this node has
    /// beyond `closure(accepted_base)`.
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

    /// The operations among `ops` whose objects are not all present, locally or staged.
    /// One question for many operations, since a real repository answers it by running
    /// `git`.
    fn objects_missing(&self, ops: &[Self::Op]) -> Result<Vec<Self::Op>, Self::Error>;

    /// Realizes a staged operation whose parents are local and whose objects are available.
    fn realize(&mut self, op: &Self::Op) -> Result<(), Self::Error>;

    /// Makes a local operation an op head (`heads := max(heads ∪ {op})`).
    fn advance(&mut self, op: &Self::Op) -> Result<(), Self::Error>;

    /// A local operation the hub has accepted, reachable from the op heads, used as the
    /// base of `Fetch` so a node is not sent history it already has. The root operation is
    /// always valid.
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
    /// Took in a `Fetched` reply: adopted its `(seq, head)` if it was newer, and staged its
    /// operations and their objects if they were all in `anc*(known.head)`.
    Fetched {
        learned: Option<(u64, O)>,
        staged: Vec<O>,
    },
    /// Staged the objects of an `Objects` reply.
    StagedObjects(Vec<O>),
    /// Ignored: stale, or about another head, or not all reachable from the head it names.
    Ignored,
}

pub struct NodeCore<O> {
    root: O,
    known: (u64, O),
    /// Staged operations to realize, in order: each one's parents are local or earlier,
    /// and its objects are available. Planned by one walk, rather than one per step, for
    /// `known.head`, and dropped with it.
    plan: VecDeque<O>,
}

/// What [`NodeCore::survey`] found below `known.head`.
struct Survey<O> {
    /// The staged operations that can be realized, parents first.
    plan: VecDeque<O>,
    /// Whether some operation is not staged yet.
    missing_ops: bool,
    /// The staged operations whose objects are not all here.
    missing_objects: Vec<O>,
}

impl<O: Clone + Ord + Hash + Debug> NodeCore<O> {
    /// A node that has just started: it knows only the root operation.
    pub fn new(root: O) -> Self {
        Self {
            known: (0, root.clone()),
            root,
            plan: VecDeque::new(),
        }
    }

    pub fn known(&self) -> &(u64, O) {
        &self.known
    }

    /// What a node sends when it connects, and on every poll: a `Fetch` of the hub's head,
    /// with whatever is new since this node's accepted base.
    pub fn poll<R>(&self, repo: &R) -> Result<Request<O, R::Attachment>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        Ok(Request::Fetch {
            base: repo.accepted_base()?,
            haves: repo.fetch_haves()?,
        })
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
            if self.plan.is_empty() {
                let survey = Self::survey(repo, &known)?;
                if survey.plan.is_empty() {
                    return self.fetch(repo, survey);
                }
                self.plan = survey.plan;
            }
            let op = self.plan.pop_front().expect("planned above");
            repo.realize(&op)?;
            return Ok(Step::Realized(op));
        }
        self.plan.clear();
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
        // `known ∈ anc*(head)`: push, uploading what the hub lacks with it.
        let ops = repo.ops_between(head, &known)?;
        Ok(Step::Send(vec![Request::Push {
            ops_attachment: repo.ops_attachment(&ops)?,
            objects: repo.objects_attachment(&ops, &known)?,
            ops,
            expected: known,
            new: head.clone(),
        }]))
    }

    /// Walks `anc*(known)` down to the local operations, once: which staged operations can
    /// be realized now, in an order that puts parents first, and what the rest lack.
    fn survey<R>(repo: &R, known: &O) -> Result<Survey<O>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        let mut missing_ops = false;
        let mut local = HashSet::new();
        let mut parents_of = HashMap::new();
        // Staged operations, each after its parents.
        let mut order = vec![];
        let mut seen = HashSet::new();
        // (operation, whether its parents have been pushed)
        let mut stack = vec![(known.clone(), false)];
        while let Some((op, expanded)) = stack.pop() {
            if expanded {
                order.push(op);
                continue;
            }
            if !seen.insert(op.clone()) {
                continue;
            }
            if repo.is_local(&op)? {
                local.insert(op);
                continue;
            }
            match repo.staged_parents(&op)? {
                None => missing_ops = true,
                Some(parents) => {
                    stack.push((op.clone(), true));
                    stack.extend(parents.iter().map(|parent| (parent.clone(), false)));
                    parents_of.insert(op, parents);
                }
            }
        }
        let without_objects: HashSet<O> = if order.is_empty() {
            HashSet::new()
        } else {
            repo.objects_missing(&order)?.into_iter().collect()
        };
        let mut plan = VecDeque::new();
        let mut planned = HashSet::new();
        for op in order {
            let parents_ready = parents_of[&op]
                .iter()
                .all(|parent| local.contains(parent) || planned.contains(parent));
            if parents_ready && !without_objects.contains(&op) {
                planned.insert(op.clone());
                plan.push_back(op);
            }
        }
        let mut missing_objects: Vec<O> = without_objects.into_iter().collect();
        missing_objects.sort();
        Ok(Survey {
            plan,
            missing_ops,
            missing_objects,
        })
    }

    /// Requests whatever `closure(known.head)` still lacks, as a survey found: operations
    /// come with their objects from `Fetch`, which asks about the hub's head, the newest
    /// `known.head`; `GetObjects` asks only for objects of operations already staged.
    fn fetch<R>(&self, repo: &R, survey: Survey<O>) -> Result<Step<O, R::Attachment>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        let Survey {
            missing_ops,
            missing_objects,
            ..
        } = survey;
        let mut requests = vec![];
        if missing_ops {
            requests.push(self.poll(repo)?);
        }
        if !missing_objects.is_empty() {
            requests.push(Request::GetObjects {
                haves: repo.objects_request(&missing_objects)?,
                base: repo.accepted_base()?,
                for_ops: missing_objects,
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
                if seq > self.known.0 {
                    self.learn(seq, head.clone());
                    Ok(Handled::Learned { kind, seq, head })
                } else {
                    Ok(Handled::Ignored)
                }
            }
            Reply::Fetched {
                seq,
                head,
                ops,
                ops_attachment,
                objects,
            } => {
                let learned = (seq > self.known.0).then(|| {
                    self.learn(seq, head.clone());
                    (seq, head.clone())
                });
                // Stage only operations in `anc*(known.head)`: the guard Locality, and so
                // MergeOwnership, depend on (docs/protocol.md, "Fetch").
                if ops.is_empty() || head != self.known.1 || !all_reach(&head, &ops) {
                    return Ok(match learned {
                        Some((seq, head)) => Handled::Learned {
                            kind: HeadKind::Head,
                            seq,
                            head,
                        },
                        None => Handled::Ignored,
                    });
                }
                repo.stage_ops(&ops, &ops_attachment)?;
                let staged: Vec<O> = ops.into_iter().map(|entry| entry.id).collect();
                repo.stage_objects(&staged, &objects)?;
                Ok(Handled::Fetched { learned, staged })
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

    /// Whether `reply`, to this node's own request, says that the hub has gone back: to a
    /// head older than the one this node knows, or to another with the same sequence
    /// number. A hub that keeps what it accepts never does, since it answers a request only
    /// after everything this node learned before sending it, but one that lost heads, as a
    /// power cut can make it, does. Taking such a reply for a stale one would leave the
    /// node deaf to the hub's announcements, and pushing what the hub rejects, again and
    /// again, so [`Self::handle_reply`] restarts first. A notification can be stale, and
    /// never counts.
    pub fn hub_went_back<A>(&self, reply: &Reply<O, A>) -> bool {
        let (seq, head) = match reply {
            Reply::Head {
                kind: HeadKind::Notify,
                ..
            }
            | Reply::Objects { .. } => return false,
            Reply::Head { seq, head, .. } | Reply::Fetched { seq, head, .. } => (*seq, head),
        };
        seq < self.known.0 || (seq == self.known.0 && *head != self.known.1)
    }

    /// Adopts `(seq, head)`. A plan made for the head known before may realize operations
    /// that aren't in `anc*(head)`, if the hub went back, so it goes.
    fn learn(&mut self, seq: u64, head: O) {
        self.known = (seq, head);
        self.plan.clear();
    }

    /// Takes a reply to this node's own request, as [`Self::handle`] does, having first
    /// [`restart`](Self::restart)ed if it says the hub went back ([`Self::hub_went_back`]).
    pub fn handle_reply<R>(
        &mut self,
        repo: &mut R,
        reply: Reply<O, R::Attachment>,
    ) -> Result<Handled<O>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        if self.hub_went_back(&reply) {
            self.restart();
        }
        self.handle(repo, reply)
    }

    /// Forgets everything volatile, as a restart does.
    pub fn restart(&mut self) {
        *self = Self::new(self.root.clone());
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

#[cfg(test)]
mod tests {
    use super::*;

    fn head(kind: HeadKind, seq: u64, head: u32) -> Reply<u32, ()> {
        Reply::Head { kind, seq, head }
    }

    #[test]
    fn a_reply_older_than_what_the_node_knows_says_the_hub_went_back() {
        let mut core = NodeCore::new(0);
        core.known = (4, 40);
        for kind in [
            HeadKind::Head,
            HeadKind::Accepted,
            HeadKind::Rejected,
            HeadKind::Incomplete,
        ] {
            assert!(core.hub_went_back(&head(kind, 3, 30)), "{kind:?}");
            assert!(core.hub_went_back(&head(kind, 4, 41)), "{kind:?}");
            assert!(!core.hub_went_back(&head(kind, 4, 40)), "{kind:?}");
            assert!(!core.hub_went_back(&head(kind, 5, 50)), "{kind:?}");
        }
        let fetched = |seq, head| Reply::Fetched {
            seq,
            head,
            ops: vec![],
            ops_attachment: (),
            objects: (),
        };
        assert!(core.hub_went_back(&fetched(0, 0)));
        assert!(!core.hub_went_back(&fetched(4, 40)));
        // A notification can be stale, and an `Objects` reply names no head.
        assert!(!core.hub_went_back(&head(HeadKind::Notify, 3, 30)));
        assert!(!core.hub_went_back(&Reply::<u32, ()>::Objects {
            for_ops: vec![],
            attachment: (),
        }));
    }
}
