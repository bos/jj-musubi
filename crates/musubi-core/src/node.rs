//! A node's side of the protocol (docs/internals/protocol.md, "Node" and "Supersedes").
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
use crate::message::RecordState;
use crate::message::Records;
use crate::message::Reply;
use crate::message::Request;

/// A node's persistent state, in canonical terms.
pub trait LocalRepo {
    type Op: Clone + Ord + Hash + Debug;
    type Attachment;
    type Error;

    /// This node's machine key, which names it to the hub.
    fn machine(&self) -> String;

    /// The canonical forms of the local op heads (canonicalizing any new local operations).
    fn heads(&mut self) -> Result<Vec<Self::Op>, Self::Error>;

    /// Reads the heads and names pending drops against the known hub history, after
    /// noticing any local abandonment. This renames bookkeeping, not local history.
    /// A backend whose ids are immutable identities needs no separate name reconciliation.
    fn heads_for(&mut self, _known: &Self::Op) -> Result<Vec<Self::Op>, Self::Error> {
        self.heads()
    }

    /// Whether `op` is present locally, as an original or a realization; or, if this node
    /// dropped it, whether all its history has in place of it is.
    fn is_local(&self, op: &Self::Op) -> Result<bool, Self::Error>;

    /// Whether `ancestor ∈ anc*(op)`, for local `op`; or, if this node dropped `ancestor`,
    /// whether all its history has in place of it is.
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

    /// Stores the canonical bodies and parent closure of whole records without staging
    /// them as ancestors of the current head. A backend whose ids already describe its
    /// immutable operations needs no separate metadata storage.
    fn store_record_ops(
        &mut self,
        _records: &[Vec<Self::Op>],
        _attachment: &Self::Attachment,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

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

    /// Realizes a staged operation whose parents are local and whose objects are available;
    /// or, if this node dropped it, nothing: what it has in place of it is local already.
    fn realize(&mut self, op: &Self::Op) -> Result<(), Self::Error>;

    /// Makes a local operation an op head (`heads := max(heads ∪ {op})`), or, if this node
    /// dropped it, what its history has in place of it: `heads := max(heads ∪ images(op))`,
    /// the operations below it that survive the drop. A real repository may also merge that
    /// head set, as `merge_heads` would: model this as advance followed by an environment
    /// merge, not as a sync step that creates a canonical operation.
    /// Advancing while records are prepared takes them and replaces any heads they drop
    /// with their surviving images, even if `op` was already below an old head.
    fn advance(&mut self, op: &Self::Op) -> Result<(), Self::Error>;

    /// A local operation the hub has accepted, reachable from the op heads, used as the
    /// base of `Fetch` so a node is not sent history it already has. The root operation is
    /// always valid.
    fn accepted_base(&self) -> Result<Self::Op, Self::Error>;

    fn set_accepted_base(&mut self, op: &Self::Op) -> Result<(), Self::Error>;

    /// The hub's records this node took last.
    fn applied_records(&self) -> Result<Records<Self::Op>, Self::Error>;

    /// Whether received records still need reconciliation. A backend may retain them before
    /// realizing their history, so it can recover them even when the hub announces the same
    /// records this node already applied.
    fn has_record_receipts(&self) -> Result<bool, Self::Error> {
        Ok(false)
    }

    /// The state of [`Self::applied_records`].
    fn records(&self) -> Result<RecordState, Self::Error>;

    /// The state of `records`: their count, and their digest, which this node computes as the
    /// hub does.
    fn records_state(&self, records: &Records<Self::Op>) -> Result<RecordState, Self::Error>;

    /// What this node dropped that the records it took don't drop: what it has yet to
    /// publish, sorted. Empty if nothing.
    fn pending(&self) -> Result<Vec<Self::Op>, Self::Error>;

    /// Gets ready to take `records`, the hub's: names what this node has as the hub does,
    /// beside what it has, without changing its op heads, so that it can realize and advance
    /// to the hub's head first. Returns whether they drop one of the op heads.
    fn prepare_records(&mut self, records: &Records<Self::Op>) -> Result<bool, Self::Error>;

    /// Takes the hub's records, none of which drops an op head: drops what they drop, and
    /// names what this node has as the hub does. What else this node dropped stays pending.
    /// Their base is this node's, or none, or this node is [fresh](Self::fresh).
    fn adopt(&mut self, records: &Records<Self::Op>) -> Result<(), Self::Error>;

    /// Whether this node has nothing of the hive's: it joined on the root, has taken no
    /// records, and has neither pushed nor realized anything since. Only such a node may take
    /// the hub's records from those the hub pruned, knowing only their count and digest: it
    /// holds no operation they drop.
    fn fresh(&self) -> Result<bool, Self::Error>;

    /// This node is about to push to the hub, or to realize one of the hub's operations: from
    /// now on it is no longer [fresh](Self::fresh).
    fn share(&mut self) -> Result<(), Self::Error>;

    /// The records whose count and digest are `prefix`, as this node took them, if it ever
    /// held them: the first of those it holds now, or of records it took before an older
    /// announcement gave it fewer, or others. Having held them, it dropped what they drop, so
    /// it may take the hub's records from those the hub pruned (docs/internals/design.md,
    /// "What an abandon costs the hub"). Their base is this node's, or none.
    fn held(&self, prefix: &RecordState) -> Result<Option<Records<Self::Op>>, Self::Error>;

    /// The error that says this node lacks records the hub pruned, so that it can never take
    /// the hub's, nor sync again.
    fn lacks_pruned(&self) -> Self::Error;

    /// Whether this node dropped `op`, an operation the hub named.
    fn is_dropped(&self, op: &Self::Op) -> Result<bool, Self::Error>;

    /// This node is about to push `head`.
    fn pushing(&mut self, _head: &Self::Op) -> Result<(), Self::Error> {
        Ok(())
    }

    /// This node learned that the hub's head is `head`, from a reply to its own request: if
    /// that is what it pushed last, the hub took it, though the base may not have moved to
    /// it yet, so that a `jj op abandon` of it must be noticed as one of the base would be.
    fn learned(&mut self, _head: &Self::Op) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Writes the fix-up on the single op head, before a supersede, and returns it
    /// (docs/internals/design.md, "The fix-up"); or `None` if the head already descends
    /// from the one for what this node has yet to publish. With `publish_from`, if that
    /// restoring work is cached and the current head still equals the given known head,
    /// writes a neutral child so the pending drops have a distinct head to publish. That
    /// child preserves current state rather than replaying the cached restoring work.
    /// It declines the child only when the head it would write on is not the one
    /// [`heads_for`](Self::heads_for) returned, and stays so: a backend that declined at the
    /// head it returned would have [`NodeCore::step`] poll for ever.
    fn write_fixup(
        &mut self,
        publish_from: Option<&Self::Op>,
    ) -> Result<Option<Self::Op>, Self::Error>;
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
    /// Took the hub's records.
    Adopted,
    /// Wrote the fix-up, if it hadn't, and pushes it, or the head, with what this node
    /// dropped.
    Superseded {
        fixup: Option<O>,
        push: Request<O, A>,
    },
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
    /// The hub refused a push: this node's records aren't the hub's.
    Refused,
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
    /// The hub's records as of the newest head this node heard of, or as a refusal said.
    hub_records: Option<RecordState>,
    /// The hub's records, all of them, where they aren't this node's: to take once none of
    /// them drops an op head.
    announced: Option<Records<O>>,
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
            hub_records: None,
            announced: None,
        }
    }

    pub fn known(&self) -> &(u64, O) {
        &self.known
    }

    /// The operations left in the current realization plan, in order.
    pub fn planned(&self) -> impl ExactSizeIterator<Item = &O> {
        self.plan.iter()
    }

    /// What a node sends when it connects, and on every poll: a `Fetch` of the hub's head,
    /// with whatever is new since this node's accepted base.
    pub fn poll<R>(&self, repo: &R) -> Result<Request<O, R::Attachment>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        Ok(Request::Fetch {
            machine: repo.machine(),
            base: repo.accepted_base()?,
            haves: repo.fetch_haves()?,
            records: repo.records()?,
        })
    }

    /// Takes the next policy step (docs/internals/protocol.md, "Policy" and "Supersedes").
    pub fn step<R>(&mut self, repo: &mut R) -> Result<Step<O, R::Attachment>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        let heads = repo.heads_for(&self.known.1)?;
        // Take the hub's records first. Where they drop a head, advancing finishes taking
        // them even if the hub's head is already below that old, dropped head.
        let mut records_drop_head = false;
        if let Some(records) = self.announced.take()
            && (records != repo.applied_records()? || repo.has_record_receipts()?)
        {
            if !repo.prepare_records(&records)? {
                repo.adopt(&records)?;
                return Ok(Step::Adopted);
            }
            records_drop_head = true;
            self.announced = Some(records);
        }
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
            repo.share()?;
            repo.realize(&op)?;
            return Ok(Step::Realized(op));
        }
        self.plan.clear();
        let mut descends = false;
        for head in &heads {
            descends |= repo.is_ancestor(&known, head)?;
        }
        if records_drop_head || !descends {
            // Never to a head this node dropped, but to what its history has in place of it,
            // which the hub accepted too: the drop is then this node's to publish, beside its
            // own work, rather than waiting for another machine to move the hub past it.
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
        let records = repo.records()?;
        let dropped = repo.pending()?;
        let differ = match &self.hub_records {
            Some(hub) => *hub != records,
            // A supersede writes the fix-up first, so it waits to know the hub's records, as
            // after a restart: the hub may have taken this node's drops already.
            None => !dropped.is_empty(),
        };
        if differ {
            // The hub refuses what this node would push, its ids not being the hub's, until
            // this node takes the hub's records, which a fetch brings.
            return Ok(if self.announced.is_some() {
                Step::Idle
            } else {
                Step::Send(vec![self.poll(repo)?])
            });
        }
        // Not two or more heads, and op heads are never empty.
        let head = heads[0].clone();
        if dropped.is_empty() {
            if head == known {
                return Ok(Step::Idle);
            }
            // `known ∈ anc*(head)`: push, uploading what the hub lacks with it.
            return Ok(Step::Send(vec![self.push(repo, &head, records, vec![])?]));
        }
        // A supersede: the fix-up, pushed with what this node dropped.
        let fixup = repo.write_fixup((head == known).then_some(&known))?;
        let new = fixup.clone().unwrap_or(head);
        if new == known {
            // The fix-up written was the known head itself, which marks it written, so the
            // next write is a neutral tip (`write_known` in formal/Musubi/NodeSettle.lean). Or
            // the backend declined the tip, the head it writes on not being what `heads_for`
            // read: a command landed in between, or the backend merged in a head it hid. That
            // head stays, unless it is abandoned, which the next step advances past, so the
            // next step does not decline at it. A decline repeats only while commands keep
            // landing between those two reads, never on its own.
            // Refresh, rather than report idle while these drops still need publishing.
            return Ok(Step::Send(vec![self.poll(repo)?]));
        }
        let push = self.push(repo, &new, records, dropped)?;
        Ok(Step::Superseded { fixup, push })
    }

    /// A `Push` of `head`, which descends from `known.head`, uploading what the hub lacks.
    fn push<R>(
        &self,
        repo: &mut R,
        head: &O,
        records: RecordState,
        dropped: Vec<O>,
    ) -> Result<Request<O, R::Attachment>, R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        // Once the hub has pruned the record that dropped it, nothing but this keeps it from
        // taking back what this node pushes (docs/internals/design.md, "What an abandon costs
        // the hub"): a bug here must be loud.
        assert!(
            !repo.is_dropped(head)?,
            "pushing {head:?}, which this node dropped"
        );
        repo.share()?;
        repo.pushing(head)?;
        let known = self.known.1.clone();
        let ops = repo.ops_between(head, &known)?;
        Ok(Request::Push {
            machine: repo.machine(),
            ops_attachment: repo.ops_attachment(&ops)?,
            objects: repo.objects_attachment(&ops, &known)?,
            ops,
            expected: known,
            new: head.clone(),
            records,
            dropped,
        })
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
            Reply::Head {
                kind,
                seq,
                head,
                records,
            } => {
                if seq > self.known.0 {
                    // First, so that a failure leaves the reply to be taken again.
                    repo.learned(&head)?;
                    self.learn(seq, head.clone());
                    self.note_records(repo, kind, records)?;
                    Ok(Handled::Learned { kind, seq, head })
                } else {
                    if seq == self.known.0 && head == self.known.1 {
                        self.note_records(repo, kind, records)?;
                    }
                    Ok(Handled::Ignored)
                }
            }
            Reply::Fetched {
                seq,
                head,
                ops,
                ops_attachment,
                objects,
                records,
                records_from,
                new_records,
                pruned,
            } => {
                if seq > self.known.0 {
                    repo.learned(&head)?;
                }
                let learned = (seq > self.known.0).then(|| {
                    self.learn(seq, head.clone());
                    (seq, head.clone())
                });
                if seq == self.known.0 && head == self.known.1 {
                    if !new_records.is_empty() {
                        repo.store_record_ops(&new_records, &ops_attachment)?;
                    }
                    self.note_announced(repo, records, records_from, new_records, pruned)?;
                }
                // Stage only operations in `anc*(known.head)`: the guard Locality, and so
                // MergeOwnership, depend on (docs/internals/protocol.md, "Fetch").
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
            Reply::Refused { records } => {
                self.hub_records = Some(records);
                Ok(Handled::Refused)
            }
        }
    }

    /// Takes in the hub's records as of the head this node knows, from a reply of `kind`.
    /// Where the hub accepted this node's own push, taking its pending drops as the next
    /// record, this node takes that record too. Not from a notification: another node may have
    /// dropped the same, and this node takes the hub's records as the hub announces them, in
    /// a reply to its own request, which a notification isn't.
    fn note_records<R>(
        &mut self,
        repo: &R,
        kind: HeadKind,
        records: RecordState,
    ) -> Result<(), R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        if kind == HeadKind::Accepted && records != repo.records()? {
            let dropped = repo.pending()?;
            if !dropped.is_empty() {
                let mut all = repo.applied_records()?;
                all.records.push(dropped);
                if records == repo.records_state(&all)? {
                    self.announced = Some(all);
                }
            }
        }
        self.hub_records = Some(records);
        Ok(())
    }

    /// Takes in the hub's records from a `Fetched` reply about the head this node knows:
    /// `new_records`, from the `from`th on, and `pruned`, the count and digest of the first
    /// ones, which the hub no longer has. Fails if this node never held those, unless it is
    /// fresh, and then starts from them.
    fn note_announced<R>(
        &mut self,
        repo: &R,
        records: RecordState,
        from: u64,
        new_records: Vec<Vec<O>>,
        pruned: RecordState,
    ) -> Result<(), R::Error>
    where
        R: LocalRepo<Op = O>,
    {
        let mine = repo.applied_records()?;
        // This node's first `count` records, if it knows them: not those it knows only by
        // their count and digest, nor more than it has.
        let first = |count: u64| {
            let kept = count.checked_sub(mine.base.count)?;
            let kept = usize::try_from(kept).ok()?;
            (kept <= mine.records.len()).then(|| Records {
                base: mine.base.clone(),
                records: mine.records[..kept].to_vec(),
            })
        };
        let mut all = match first(from) {
            Some(mut all) => {
                all.records.extend(new_records.iter().cloned());
                Some(all)
            }
            None => None,
        };
        if let Some(candidate) = &all
            && repo.records_state(candidate)? != records
        {
            all = None;
        }
        let Some(all) = all else {
            // The hub's records from those it pruned, which this node took, or held before an
            // older announcement, after a restart or from a hub made again, gave it fewer: the
            // hub prunes only records every node said it took, so it dropped what they drop
            // (`Exec.sexec_announced_held`). That includes none, whose records a node with
            // records it knows only by their count and digest takes whole where a hub that
            // went back or was made again has pruned nothing. A fresh node, which has nothing
            // of the hive's, starts from them as the hub keeps them.
            let held = repo.held(&pruned)?;
            if from == pruned.count {
                let base = match &held {
                    Some(held) => Some(held.clone()),
                    None => repo.fresh()?.then(|| Records {
                        base: pruned.clone(),
                        records: vec![],
                    }),
                };
                if let Some(mut base) = base {
                    base.records.extend(new_records);
                    if repo.records_state(&base)? == records {
                        self.announced = Some(base);
                        self.hub_records = Some(records);
                        return Ok(());
                    }
                }
            }
            if held.is_some() {
                // Records this node can't complete from those it holds now, as they answer a
                // request sent before it took others: the reply to its next request starts
                // from those the hub pruned.
                return Ok(());
            }
            return Err(repo.lacks_pruned());
        };
        self.announced = (all != mine || repo.has_record_receipts()?).then_some(all);
        self.hub_records = Some(records);
        Ok(())
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
            | Reply::Objects { .. }
            | Reply::Refused { .. } => return false,
            Reply::Head { seq, head, .. } | Reply::Fetched { seq, head, .. } => (*seq, head),
        };
        seq < self.known.0 || (seq == self.known.0 && *head != self.known.1)
    }

    /// Adopts `(seq, head)`. A plan made for the head known before may realize operations
    /// that aren't in `anc*(head)`, if the hub went back, so it goes, and so do the records
    /// known as of it.
    fn learn(&mut self, seq: u64, head: O) {
        self.known = (seq, head);
        self.plan.clear();
        self.hub_records = None;
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
/// check that keeps operations the hub has not accepted out of `staged`
/// (docs/internals/protocol.md, "Fetch").
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

    const NO_RECORDS: RecordState = RecordState {
        count: 0,
        digest: vec![],
    };

    fn head(kind: HeadKind, seq: u64, head: u32) -> Reply<u32, ()> {
        Reply::Head {
            kind,
            seq,
            head,
            records: NO_RECORDS,
        }
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
            records: NO_RECORDS,
            records_from: 0,
            new_records: vec![],
            pruned: NO_RECORDS,
        };
        assert!(core.hub_went_back(&fetched(0, 0)));
        assert!(!core.hub_went_back(&fetched(4, 40)));
        // A notification can be stale, and an `Objects` reply or a refusal names no head.
        assert!(!core.hub_went_back(&head(HeadKind::Notify, 3, 30)));
        assert!(!core.hub_went_back(&Reply::<u32, ()>::Objects {
            for_ops: vec![],
            attachment: (),
        }));
        assert!(!core.hub_went_back(&Reply::<u32, ()>::Refused {
            records: NO_RECORDS
        }));
    }
}
