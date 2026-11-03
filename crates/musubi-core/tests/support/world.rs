//! A hub and nodes running the real core over a network the test controls completely, with
//! every step translated into Lean model actions (docs/internals/conformance.md).

use std::collections::BTreeSet;

use musubi_core::hub;
use musubi_core::hub::CasOutcome;
use musubi_core::message::HeadKind;
use musubi_core::message::OpEntry;
use musubi_core::message::RecordState;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::Handled;
use musubi_core::node::NodeCore;
use musubi_core::node::Step;
use serde_json::Value;
use serde_json::json;

use super::model::Advanced;
use super::model::FakeHub;
use super::model::FakeRepo;
use super::model::Obj;
use super::model::Op;
use super::model::ROOT;
use super::model::SharedUniv;
use super::model::Univ;
use super::model::flat;
use super::oracle::Measure;
use super::oracle::Oracle;
use super::storage::{Fallible, Faults, SharedFaults, StorageError, Timing};

mod storage_failures;

type Req = Request<Op, Vec<Obj>>;
type Rep = Reply<Op, Vec<Obj>>;

#[derive(Clone, Debug)]
enum Payload {
    /// A request, and for a `Push`, the records its node had taken and what it had dropped
    /// when it sent it: what the model's supersede carries (`sendSup`).
    Request(usize, Req, Option<Sup>),
    Reply(usize, Rep),
}

/// The records a node had taken, and everything it had dropped.
type Sup = (Vec<Vec<Op>>, Vec<Op>);

/// A message in flight: what the Rust side actually sent, and its Lean model form, which is
/// several messages for a `Fetched` reply.
#[derive(Clone, Debug)]
struct InFlight {
    model: Vec<Value>,
    payload: Payload,
    delivered: bool,
}

pub struct World {
    univ: SharedUniv,
    hub: Fallible<FakeHub>,
    /// `hist[i]`: the head accepted at sequence number `i`.
    hist: Vec<Op>,
    repos: Vec<Fallible<FakeRepo>>,
    cores: Vec<NodeCore<Op>>,
    /// Every message ever sent. Any can be delivered again, so this is the model's `net`.
    net: Vec<InFlight>,
    oracle: Option<Oracle>,
    /// Reused by the next case after a storage prefix leaves the oracle's abstraction.
    retired_oracle: Option<Oracle>,
    oracle_state: Value,
    faults: SharedFaults,
    pub trace: Vec<Value>,
    /// The operations each node last staged from a `Fetched` reply.
    last_staged: Vec<Option<Vec<Op>>>,
    /// Whether the hub has gone back: MergeOwnership no longer holds (docs/internals/protocol.md,
    /// "Network and failures").
    went_back: bool,
    /// The heads the hub accepted and then lost, going back, with their sequence numbers:
    /// the properties that rest on its history only growing hold of its history together
    /// with them.
    lost: Vec<(u64, Op)>,
    /// Whether each node has taken a false reply ([`Self::false_reply`]): the properties that
    /// rest on the hub's honesty, Locality and KnownIsHubHistory among them, no longer hold
    /// of it.
    misled: Vec<bool>,
    /// The operations false replies and a lying hub's replies have carried, which a node
    /// misled may have, though the hub never accepted them.
    offered: BTreeSet<Op>,
    /// Whether any node has dropped anything: the measure of `Liveness.lean`, which knows
    /// nothing of supersedes, falls only before.
    dropped_any: bool,
    /// The sequence numbers of the heads the hub accepted through what survives of the head
    /// it had, not as its descendant in the original history (`imageAccept`).
    contracted_accepts: BTreeSet<u64>,
    /// Whether any step left the original-history model: such an acceptance, an advance to
    /// what survives of a dropped head, or one as prepared records name the history.
    contracted: bool,
    /// Whether the hub was remade where going back would have left it at a head it lacks.
    pub remade_for_rollback: bool,
}

/// What of a node `World::quiesce` watches across an exchange.
struct NodeView {
    lops: BTreeSet<Op>,
    heads: BTreeSet<Op>,
    known: (u64, Op),
    dropped: BTreeSet<Op>,
    applied: Vec<Vec<Op>>,
    crash_pending: bool,
}

fn kind_name(kind: HeadKind) -> &'static str {
    match kind {
        HeadKind::Head => "head",
        HeadKind::Accepted => "accepted",
        HeadKind::Rejected => "rejected",
        HeadKind::Incomplete => "incomplete",
        HeadKind::Notify => "notify",
    }
}

fn sorted(items: impl IntoIterator<Item = u64>) -> Vec<u64> {
    items
        .into_iter()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

impl World {
    pub fn new(nodes: usize, oracle: Option<Oracle>) -> Self {
        let univ = SharedUniv::new(std::cell::RefCell::new(Univ::new()));
        let faults = SharedFaults::new(std::cell::RefCell::new(Faults::default()));
        let mut world = Self {
            hub: Fallible::new(FakeHub::new(univ.clone()), faults.clone()),
            hist: vec![ROOT],
            repos: (0..nodes)
                .map(|n| Fallible::new(FakeRepo::new(univ.clone(), n), faults.clone()))
                .collect(),
            cores: (0..nodes).map(|_| NodeCore::new(ROOT)).collect(),
            net: vec![],
            univ,
            oracle,
            retired_oracle: None,
            oracle_state: Value::Null,
            faults,
            trace: vec![],
            last_staged: vec![None; nodes],
            went_back: false,
            lost: vec![],
            misled: vec![false; nodes],
            offered: BTreeSet::new(),
            dropped_any: false,
            contracted_accepts: BTreeSet::new(),
            contracted: false,
            remade_for_rollback: false,
        };
        if let Some(oracle) = &mut world.oracle {
            world.oracle_state = oracle.reset(nodes);
        }
        world
    }

    pub fn nodes(&self) -> usize {
        self.repos.len()
    }

    pub fn local_ops(&self, node: usize) -> Vec<Op> {
        self.repos[node].lops.iter().copied().collect()
    }

    /// The local operations `node` can name in a push: those no record it took drops, which
    /// the root is always among.
    pub fn nameable_ops(&self, node: usize) -> Vec<Op> {
        let repo = &self.repos[node];
        let taken: BTreeSet<Op> = flat(&repo.applied).into_iter().collect();
        repo.lops.difference(&taken).copied().collect()
    }

    pub fn net_len(&self) -> usize {
        self.net.len()
    }

    /// Indices of messages never delivered.
    pub fn undelivered(&self) -> Vec<usize> {
        (0..self.net.len())
            .filter(|&i| !self.net[i].delivered)
            .collect()
    }

    /// The kinds of the head replies sent to `node`, oldest first.
    pub fn head_replies(&self, node: usize) -> Vec<HeadKind> {
        self.net
            .iter()
            .filter_map(|message| match &message.payload {
                Payload::Reply(to, Reply::Head { kind, .. }) if *to == node => Some(*kind),
                _ => None,
            })
            .collect()
    }

    /// Records a model action and, with an oracle, checks it is a legal step leading to the
    /// state the Rust side is in.
    fn act(&mut self, action: Value) {
        self.act_all(vec![action]);
    }

    /// Records model actions that one Rust event performs together, such as taking in a
    /// `Fetched` reply, and checks that they lead to the state the Rust side is in.
    fn act_all(&mut self, actions: Vec<Value>) {
        self.trace.extend(actions.iter().cloned());
        // Without an oracle there is nothing to check against, and building the state took
        // most of the time of the tests that run without one.
        let Some(mut oracle) = self.oracle.take() else {
            return;
        };
        let expected = self.state_json();
        let mut state = std::mem::take(&mut self.oracle_state);
        for action in &actions {
            state = oracle.step(action).unwrap_or_else(|error| {
                panic!(
                    "the Lean model rejects {action}: {error}\ntrace: {:#?}",
                    self.trace
                )
            });
        }
        let (got, want) = (canonical_state(&state), canonical_state(&expected));
        assert_eq!(
            got, want,
            "state differs from the Lean model after {actions:?}"
        );
        self.oracle_state = state;
        self.oracle = Some(oracle);
    }

    fn send(&mut self, model: Vec<Value>, payload: Payload) {
        self.net.push(InFlight {
            model,
            payload,
            delivered: false,
        });
    }

    // Environment.

    pub fn user_op(&mut self, node: usize, parent: Op, objs: usize) {
        let (_, objs) = self.repos[node].user_op(parent, objs);
        self.act(json!({"kind": "userOp", "node": node, "parent": parent, "objs": objs}));
    }

    /// The operations `jj op abandon` on `node` may drop.
    pub fn abandonable(&self, node: usize) -> Vec<Op> {
        self.repos[node].abandonable()
    }

    /// `jj op abandon` on `node` drops `ops`.
    pub fn op_abandon(&mut self, node: usize, ops: Vec<Op>) {
        self.repos[node].abandon(&ops);
        self.dropped_any |= !ops.is_empty();
        self.act(json!({"kind": "abandon", "node": node, "ops": sorted(ops)}));
    }

    // Node side.

    /// The poll timer: send a `Fetch`.
    pub fn poll(&mut self, node: usize) {
        let before = self.storage_begin();
        match self.cores[node].poll(&self.repos[node]) {
            Ok(request) => self.send_request(node, request),
            Err(error) => self.storage_failed(Some(node), before, error, vec![]),
        }
    }

    /// One policy step. Returns whether anything happened.
    pub fn node_step(&mut self, node: usize, merge_objs: usize) -> bool {
        let before = self.storage_begin();
        let burst_before = self.oracle.as_ref().map(|_| {
            (
                self.cores[node].known().1,
                self.repos[node].applied.clone(),
                self.repos[node].dropped.clone(),
                self.burst_state(node),
            )
        });
        self.repos[node].merge_objs = merge_objs;
        let heads_before: Vec<Op> = self.repos[node].heads.iter().copied().collect();
        let step = match self.cores[node].step(&mut self.repos[node]) {
            Ok(step) => step,
            Err(error) => {
                self.storage_failed(Some(node), before, error, vec![]);
                return false;
            }
        };
        let burst_kind = match &step {
            Step::Merged => Some(("merge", None)),
            Step::Realized(op) => Some(("realize", Some(*op))),
            Step::Advanced(_)
                if !matches!(self.repos[node].last_advance, Some(Advanced::Prepared(_))) =>
            {
                Some(("advance", None))
            }
            _ => None,
        };
        match step {
            Step::Idle => return false,
            Step::Merged => {
                let (op, parents, objs) = self.repos[node].last_merge.take().unwrap();
                assert_eq!(parents, heads_before);
                self.check_merge_ownership(node, op, &parents);
                self.act(json!({"kind": "merge", "node": node, "parents": parents, "objs": objs}));
            }
            Step::Realized(op) => self.act(json!({"kind": "realize", "node": node, "opId": op})),
            Step::Advanced(_) => {
                let advanced = self.repos[node].last_advance.take().expect("advanced");
                self.contracted |= advanced != Advanced::Plain;
                self.act(advanced.action(node));
            }
            Step::Send(requests) => {
                for request in requests {
                    self.check_upload(node, &request);
                    self.send_request(node, request);
                }
            }
            Step::Adopted => {
                let records = records_json(&self.repos[node].applied);
                self.act(json!({"kind": "adopt", "node": node, "records": records}));
            }
            Step::Superseded { fixup, push } => {
                if let Some(fixup) = fixup {
                    let (op, parent) = self.repos[node].last_fixup.take().unwrap();
                    assert_eq!(op, fixup);
                    self.act(json!({"kind": "userOp", "node": node, "parent": parent, "objs": []}));
                }
                self.check_upload(node, &push);
                self.send_request(node, push);
            }
        }
        if let (Some((known, applied, dropped, before)), Some((kind, op))) =
            (burst_before, burst_kind)
            && self.repos[node].applied == applied
            && self.repos[node].dropped == dropped
        {
            let after = self.burst_state(node);
            let reply = self.oracle.as_mut().unwrap().call(&json!({
                "op": "localBurst", "node": node, "known": known,
                "kind": kind, "opId": op, "before": before, "after": after,
            }));
            assert_eq!(reply["ok"], true, "local burst query failed: {reply}");
            assert_eq!(reply["matches"], true, "local burst fields differ: {reply}");
        }
        true
    }

    fn burst_state(&self, node: usize) -> Value {
        json!({
            "local": sorted(self.repos[node].lops.iter().copied()),
            "heads": sorted(self.repos[node].heads.iter().copied()),
            "plan": self.cores[node].planned().copied().collect::<Vec<_>>(),
        })
    }

    fn send_request(&mut self, node: usize, request: Req) {
        let univ = self.univ.clone();
        let univ = univ.borrow();
        let repo = &self.repos[node];
        let sup = (
            repo.applied.clone(),
            repo.dropped.iter().copied().collect::<Vec<_>>(),
        );
        let (actions, model, sup) = match &request {
            Request::Fetch { base, haves, .. } => {
                let haves = sorted(haves.iter().copied());
                (
                    vec![json!({"kind": "fetchAll", "node": node, "base": base, "haves": haves})],
                    vec![json!({"msg": "fetch", "node": node, "base": base, "haves": haves})],
                    None,
                )
            }
            Request::GetObjects { for_ops, haves, .. } => {
                // What the hub sends back: the objects, less the haves.
                let objs = sorted(
                    univ.objs_of(for_ops.iter().copied())
                        .into_iter()
                        .filter(|o| !haves.contains(o)),
                );
                (
                    vec![json!({"kind": "fetchObjs", "node": node, "objs": objs})],
                    vec![json!({"msg": "getObjs", "node": node, "objs": objs})],
                    None,
                )
            }
            Request::Push {
                ops,
                objects,
                expected,
                new,
                records,
                dropped,
                ..
            } => {
                // Keep the one actual packet tied to its send-time source, rather than
                // reconstructing an unrelated supersede that merely names the same head.
                assert_eq!(univ.records_of(records), Some(sup.0.as_slice()));
                let applied = flat(&sup.0);
                let pending: BTreeSet<_> = dropped.iter().copied().collect();
                assert_eq!(
                    repo.dropped,
                    applied.union(&pending).copied().collect::<BTreeSet<_>>()
                );
                assert!(applied.is_disjoint(&pending));
                let (ops, objs) = (sorted(ops.iter().copied()), sorted(objects.iter().copied()));
                (
                    vec![
                        json!({"kind": "pushAll", "node": node, "ops": ops, "objs": objs,
                            "expected": expected, "new": new}),
                        json!({"kind": "sendSup", "node": node, "new": new}),
                    ],
                    vec![
                        json!({"msg": "push", "node": node, "ops": ops, "objs": objs,
                            "expected": expected, "new": new}),
                        sup_json(node, &sup, *new),
                    ],
                    Some(sup),
                )
            }
        };
        drop(univ);
        self.send(model, Payload::Request(node, request, sup));
        self.act_all(actions);
    }

    /// A policy `Push` uses its actual send-time snapshot and uploads exactly the model's
    /// `upOps` and `upObjs`. The separate rogue-push rule deliberately bypasses policy.
    fn check_upload(&mut self, node: usize, request: &Req) {
        let Request::Push {
            ops,
            objects,
            expected,
            new,
            records,
            dropped,
            ..
        } = request
        else {
            return;
        };
        assert_eq!(*expected, self.cores[node].known().1);
        assert_eq!(self.repos[node].heads, BTreeSet::from([*new]));
        let Some(oracle) = &mut self.oracle else {
            return;
        };
        let applied = self.univ.borrow().records_of(records).unwrap().to_vec();
        let reply = oracle.call(&json!({
            "op": "pushSnapshot", "node": node,
            "ops": sorted(ops.iter().copied()), "objs": sorted(objects.iter().copied()),
            "expected": expected, "new": new, "knownSeq": self.cores[node].known().0,
            "applied": records_json(&applied), "pending": dropped,
        }));
        assert_eq!(reply["ok"], true, "push snapshot failed: {reply}");
        assert_eq!(
            reply["matches"], true,
            "packet differs from its source: {reply}"
        );
        assert_eq!(
            reply["allDropped"],
            json!(sorted(self.repos[node].dropped.iter().copied()))
        );
        let (up_ops, up_objs) = oracle.upload(node, *new);
        assert_eq!(
            (sorted(ops.iter().copied()), sorted(objects.iter().copied())),
            (up_ops, up_objs),
            "node {node}'s push of {new} does not upload upOps and upObjs\ntrace: {:#?}",
            self.trace
        );
    }

    /// A push the policy would never make: `Cas(expected, new)` for any local `new`, without
    /// uploading anything. The model allows it, so the hub must defend itself. `new` is no
    /// operation a record the node took drops: a node never names one, which the hub can't
    /// refuse once it has pruned the record.
    pub fn rogue_push(&mut self, node: usize, expected: Op, new: Op) {
        use musubi_core::node::LocalRepo as _;
        let repo = &self.repos[node];
        let request = Request::Push {
            machine: repo.machine(),
            ops: vec![],
            ops_attachment: vec![],
            objects: vec![],
            expected,
            new,
            records: repo.records().unwrap(),
            dropped: repo.pending().unwrap(),
        };
        self.send_request(node, request);
    }

    /// How often `node`'s core has read a staged operation, and asked about objects.
    pub fn repo_work(&self, node: usize) -> (usize, usize) {
        let repo = &self.repos[node];
        (repo.staged_reads.get(), repo.object_checks.get())
    }

    /// The operations `node` last staged from a `Fetched` reply.
    pub fn last_staged(&self, node: usize) -> Option<&[Op]> {
        self.last_staged[node].as_deref()
    }

    pub fn accepted_heads(&self) -> Vec<Op> {
        self.hist.clone()
    }

    // Network.

    /// Delivers message `index` of everything ever sent, to the hub or to a node.
    pub fn deliver(&mut self, index: usize) {
        self.net[index].delivered = true;
        let message = self.net[index].clone();
        self.deliver_payload(message.payload);
    }

    /// A `Fetch`, whose reply comes straight back, as the answer to it.
    pub fn poll_now(&mut self, node: usize) {
        let sent_before = self.net.len();
        self.poll(node);
        self.round_trip(sent_before);
    }

    /// One policy step whose requests reach the hub at once, and whose replies come
    /// straight back: a fast round trip, interleaved with whatever else is going on.
    pub fn exchange(&mut self, node: usize, merge_objs: usize) {
        let sent_before = self.net.len();
        if !self.node_step(node, merge_objs) {
            return;
        }
        self.round_trip(sent_before);
    }

    /// [`Self::exchange`], with the measures checked across it, as `quiesce` checks them.
    pub fn exchange_checked(&mut self, node: usize, merge_objs: usize) {
        let mut measure = self.measure();
        let before = self.node_view(node);
        self.exchange(node, merge_objs);
        self.check_measure(node, before, &mut measure);
    }

    /// [`Self::poll_now`], with the measures checked across it, as `quiesce` checks them.
    pub fn poll_now_checked(&mut self, node: usize) {
        let mut measure = self.measure();
        let before = self.node_view(node);
        self.poll_now(node);
        self.check_measure(node, before, &mut measure);
    }

    /// Delivers each request sent since `sent_before` to the hub, and its reply straight back.
    fn round_trip(&mut self, sent_before: usize) {
        let mut i = sent_before;
        while i < self.net.len() {
            if matches!(self.net[i].payload, Payload::Request(..)) {
                let replies_from = self.net.len();
                self.deliver(i);
                if replies_from < self.net.len() {
                    // Straight back, as an answer to the request, not any old reply.
                    self.net[replies_from].delivered = true;
                    if let Payload::Reply(node, reply) = self.net[replies_from].payload.clone() {
                        self.node_handle(node, reply, true);
                    }
                }
            }
            i += 1;
        }
    }

    fn deliver_payload(&mut self, payload: Payload) {
        match payload {
            Payload::Request(node, request, sup) => self.hub_handle(node, request, sup),
            Payload::Reply(node, reply) => self.node_handle(node, reply, false),
        }
    }

    fn hub_handle(&mut self, node: usize, request: Req, sup: Option<Sup>) {
        let before = self.storage_begin();
        let actions = match &request {
            Request::Fetch { base, haves, .. } => vec![
                json!({"kind": "hubFetch", "node": node, "base": base,
                    "haves": sorted(haves.iter().copied())}),
                json!({"kind": "sendD", "node": node}),
            ],
            Request::GetObjects { for_ops, haves, .. } => {
                let objs = sorted(
                    self.univ
                        .borrow()
                        .objs_of(for_ops.iter().copied())
                        .into_iter()
                        .filter(|o| !haves.contains(o)),
                );
                vec![json!({"kind": "hubGetObjs", "node": node, "objs": objs})]
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
                let push = hub::Push {
                    machine,
                    ops,
                    ops_attachment,
                    objects,
                    expected,
                    new,
                    records,
                    dropped,
                };
                let (outcome, handled) = match push.answer(&mut self.hub) {
                    Ok(result) => result,
                    Err(error) => {
                        self.storage_failed(Some(node), before, error, vec![]);
                        return;
                    }
                };
                let (applied, all_dropped) = sup.expect("a push carries a supersede");
                let action = |kind: &str| {
                    json!({"kind": kind, "node": node,
                        "ops": sorted(ops.iter().copied()), "objs": sorted(objects.iter().copied()),
                        "expected": expected, "new": new})
                };
                let with_sup = |kind: &str| {
                    let mut action = action(kind);
                    action["applied"] = records_json(&applied);
                    action["dropped"] = json!(sorted(all_dropped.iter().copied()));
                    action
                };
                let actions = match outcome {
                    CasOutcome::Idempotent => vec![action("hubPushIdem")],
                    CasOutcome::Accepted => vec![
                        with_sup("hubSupAccept"),
                        json!({"kind": "sendD", "node": node}),
                    ],
                    CasOutcome::Rejected => vec![with_sup("hubPushReject")],
                    CasOutcome::Incomplete => vec![action("hubPushIncomplete")],
                    CasOutcome::Refused => vec![with_sup("hubPushRefuse")],
                };
                let announced = outcome == CasOutcome::Accepted;
                let contracted = announced && !self.univ.borrow().is_ancestor(*expected, *new);
                self.reply_and_act(node, handled.reply, actions, handled.publish, announced);
                if contracted {
                    self.contracted_accepts.insert(self.hub.seq);
                    self.contracted = true;
                }
                return;
            }
        };
        let handled = match hub::handle(&mut self.hub, request) {
            Ok(handled) => handled,
            Err(error) => {
                self.storage_failed(Some(node), before, error, vec![]);
                return;
            }
        };
        self.reply_and_act(node, handled.reply, actions, handled.publish, false);
    }

    /// Sends `reply`, and the notifications of a head the hub `publish`es, with the model
    /// `actions` the hub took. A `Fetched` reply carries the hub's records, and so does the
    /// reply to a push it accepted, if `announced`: from the records state it carries, and
    /// the records the node had, the node knows them all.
    fn reply_and_act(
        &mut self,
        node: usize,
        reply: Rep,
        actions: Vec<Value>,
        publish: Option<(u64, Op, RecordState)>,
        announced: bool,
    ) {
        // A storage error must never be reported as a successful publication. Check the
        // actual adapter, even when a prior partial import retired this case's oracle.
        match &reply {
            Reply::Head { seq, head, .. } | Reply::Fetched { seq, head, .. } => {
                assert_eq!(
                    (*seq, *head),
                    (self.hub.seq, self.hub.head),
                    "hub reply differs from storage"
                );
            }
            _ => {}
        }
        if let Some((seq, head, _)) = &publish {
            assert_eq!(
                (*seq, *head),
                (self.hub.seq, self.hub.head),
                "hub publication differs from storage"
            );
            assert!(
                self.hub.closed(*head),
                "hub published a head without its required data"
            );
        }
        let records =
            json!({"msg": "dropped", "node": node, "records": records_json(&self.hub.records)});
        let model = match &reply {
            Reply::Head {
                kind, seq, head, ..
            } => {
                let mut model = vec![
                    json!({"msg": "head", "node": node, "headKind": kind_name(*kind), "seq": seq, "head": head}),
                ];
                if announced {
                    model.push(records);
                }
                model
            }
            Reply::Fetched {
                seq,
                head,
                ops,
                objects,
                ..
            } => vec![
                json!({"msg": "head", "node": node, "headKind": "head", "seq": seq, "head": head}),
                json!({"msg": "ops", "node": node, "ops": sorted(ops.iter().map(|e| e.id))}),
                json!({"msg": "objs", "node": node, "objs": sorted(objects.iter().copied())}),
                records,
            ],
            Reply::Objects { attachment, .. } => {
                vec![
                    json!({"msg": "objs", "node": node, "objs": sorted(attachment.iter().copied())}),
                ]
            }
            Reply::Refused { .. } => vec![],
        };
        self.send(model, Payload::Reply(node, reply));
        if let Some((seq, head, records)) = publish {
            assert_eq!(seq as usize, self.hist.len());
            self.hist.push(head);
            for target in 0..self.nodes() {
                let reply = Reply::Head {
                    kind: HeadKind::Notify,
                    seq,
                    head,
                    records: records.clone(),
                };
                let model = json!({"msg": "head", "node": target, "headKind": "notify", "seq": seq, "head": head});
                self.send(vec![model], Payload::Reply(target, reply));
            }
        }
        self.act_all(actions);
    }

    /// Has `node` take `reply`: `own` if it answers the request the node just sent, which
    /// the node takes as saying where the hub is now (`NodeCore::handle_reply`).
    fn node_handle(&mut self, node: usize, reply: Rep, own: bool) {
        let before = self.storage_begin();
        let known_before = *self.cores[node].known();
        let incoming = match &reply {
            Reply::Head { seq, head, .. } | Reply::Fetched { seq, head, .. } => Some((*seq, *head)),
            Reply::Objects { .. } | Reply::Refused { .. } => None,
        };
        let restarted = own && self.cores[node].hub_went_back(&reply);
        let head_kind = match &reply {
            Reply::Head { kind, .. } => *kind,
            _ => HeadKind::Head,
        };
        let objects = match &reply {
            Reply::Objects { attachment, .. } => sorted(attachment.iter().copied()),
            Reply::Fetched { objects, .. } => sorted(objects.iter().copied()),
            Reply::Head { .. } | Reply::Refused { .. } => vec![],
        };
        let mut actions = vec![];
        let handled = if own {
            if self.cores[node].hub_went_back(&reply) {
                actions.push(json!({"kind": "loseKnown", "node": node}));
            }
            self.cores[node].handle_reply(&mut self.repos[node], reply)
        } else {
            self.cores[node].handle(&mut self.repos[node], reply)
        };
        let handled = match handled {
            Ok(handled) => handled,
            Err(error) => {
                let (seq, head) = *self.cores[node].known();
                if (seq, head) != known_before && seq > 0 {
                    actions.push(json!({"kind": "learn", "node": node,
                        "headKind": kind_name(head_kind), "seq": seq, "head": head}));
                }
                self.storage_failed(Some(node), before, error, actions);
                return;
            }
        };
        if let (Some(oracle), Some(incoming)) = (&mut self.oracle, incoming) {
            let expected = oracle.call(&json!({
                "op": "headControl", "root": ROOT,
                "known": known_before, "incoming": incoming,
                "own": own, "notify": head_kind == HeadKind::Notify,
            }));
            assert_eq!(expected["ok"], true, "head control failed: {expected}");
            assert_eq!(expected["restart"], json!(restarted));
            assert_eq!(expected["known"], json!(self.cores[node].known()));
        }
        match handled {
            Handled::Learned { kind, seq, head } => {
                actions.push(json!({"kind": "learn", "node": node, "headKind": kind_name(kind), "seq": seq, "head": head}));
                self.act_all(actions);
            }
            Handled::Fetched { learned, staged } => {
                if let Some((seq, head)) = learned {
                    actions.push(json!({"kind": "learn", "node": node, "headKind": "head", "seq": seq, "head": head}));
                }
                actions.push(
                    json!({"kind": "recvOps", "node": node, "ops": sorted(staged.iter().copied())}),
                );
                let crashed = std::mem::take(&mut self.repos[node].crash_before_objects);
                if crashed {
                    self.act_all(actions);
                    self.crash_node(node);
                } else {
                    actions.push(json!({"kind": "recvObjs", "node": node, "objs": objects}));
                    self.act_all(actions);
                }
                self.last_staged[node] = Some(staged);
            }
            Handled::StagedObjects(_) => {
                actions.push(json!({"kind": "recvObjs", "node": node, "objs": objects}));
                self.act_all(actions);
            }
            Handled::Ignored | Handled::Refused => {
                if !actions.is_empty() {
                    self.act_all(actions);
                }
            }
        }
    }

    // Failures.

    /// Delivers to `node` every head notification it has not had.
    pub fn deliver_notifications(&mut self, node: usize) {
        for index in self.undelivered() {
            if matches!(
                &self.net[index].payload,
                Payload::Reply(to, Reply::Head { kind: HeadKind::Notify, .. }) if *to == node
            ) {
                self.deliver(index);
            }
        }
    }

    /// Makes `node` crash the next time it takes in a `Fetched` reply, after staging the
    /// operations and before staging their objects.
    pub fn crash_before_objects(&mut self, node: usize) {
        self.repos[node].crash_before_objects = true;
    }

    pub fn crash_node(&mut self, node: usize) {
        self.cores[node].restart();
        self.act(json!({"kind": "loseKnown", "node": node}));
    }

    /// The hub goes back to the head it accepted at `seq`, as a power cut can make it lose
    /// the later ones (`hubRegress`). Going back to where it is changes nothing, and the
    /// properties that need a hub that never went back still hold.
    pub fn hub_goes_back(&mut self, seq: u64) {
        // A head it accepted through what survives of the one before need not reach that one,
        // whose objects it may have forgotten since: going back there leaves no hub that
        // works. This harness explicitly chooses a maintainer's remake recovery; it does
        // not claim that native startup detects every missing historical object.
        if !self.hub.closed(self.hist[seq as usize]) {
            self.trace
                .push(json!({"marker": "rollback to an incomplete head: remake"}));
            self.remade_for_rollback = true;
            self.remake();
            return;
        }
        let lost: Vec<Op> = self.hist.drain(seq as usize + 1..).collect();
        self.went_back |= !lost.is_empty();
        self.contracted_accepts.retain(|&accepted| accepted <= seq);
        self.lost.extend((seq + 1..).zip(lost));
        self.hub.head = self.hist[seq as usize];
        self.hub.seq = seq;
        self.hub.record_hist.truncate(seq as usize + 1);
        self.hub.records = self.hub.record_hist[seq as usize].clone();
        self.hub.pruned_hist.truncate(seq as usize + 1);
        self.hub.pruned = self.hub.pruned_hist[seq as usize];
        // A hub goes back by restarting.
        self.hub.restart();
        self.act(json!({"kind": "hubRegress", "seq": seq}));
    }

    pub fn hub_head(&self) -> Op {
        self.hub.head
    }

    pub fn dropped(&self, node: usize) -> &BTreeSet<Op> {
        &self.repos[node].dropped
    }

    /// The hub's records `node` took last.
    pub fn applied(&self, node: usize) -> &[Vec<Op>] {
        &self.repos[node].applied
    }

    pub fn heads(&self, node: usize) -> &BTreeSet<Op> {
        &self.repos[node].heads
    }

    /// The hub's answer to a push of `new`, which needs nothing uploaded, from `expected`,
    /// with `records`, taken straight from the hub, outside the network and the model.
    pub fn answer_push(
        &mut self,
        expected: Op,
        new: Op,
        records: &[Vec<Op>],
        dropped: &[Op],
    ) -> CasOutcome {
        let records = self.univ.borrow_mut().record_state(records);
        let push = hub::Push {
            machine: "outside",
            ops: &[],
            ops_attachment: &vec![],
            objects: &vec![],
            expected: &expected,
            new: &new,
            records: &records,
            dropped,
        };
        push.answer(&mut self.hub).unwrap().0
    }

    pub fn hub_records(&self) -> &[Vec<Op>] {
        &self.hub.records
    }

    pub fn hub_seq(&self) -> u64 {
        self.hub.seq
    }

    pub fn crash_hub(&mut self) {
        self.hub.restart();
        self.act(json!({"kind": "crashHub"}));
    }

    /// The hub prunes its records, if every node has said it took them all (`prune`).
    pub fn prune(&mut self) {
        let before = self.storage_begin();
        let nodes: Vec<String> = (0..self.nodes()).map(|n| n.to_string()).collect();
        match hub::prune(&mut self.hub, nodes) {
            Ok(Some(count)) => self.act(json!({"kind": "prune", "count": count})),
            Ok(None) => {}
            // Server upkeep logs the error and keeps the adapter; the request succeeds.
            Err(error) => self.storage_failed(None, before, error, vec![]),
        }
    }

    /// How many of its records the hub has pruned.
    pub fn hub_pruned(&self) -> usize {
        self.hub.pruned
    }

    pub fn take_oracle(&mut self) -> Option<Oracle> {
        self.oracle.take().or_else(|| self.retired_oracle.take())
    }

    pub fn has_oracle(&self) -> bool {
        self.oracle.is_some()
    }

    /// A hub that garbage-collects what neither its head nor its history needs, including
    /// uploads it acknowledged but never accepted, as the model allows (`hubForget`): every
    /// operation outside the closures of the heads in its history, and every object outside
    /// its head's. A real hub replays every head it logged on opening its store, which needs
    /// their operations, not their objects.
    pub fn hub_forget(&mut self) {
        // Where the heads in its history are each above the one before in the original
        // history, as before any acceptance through what survives, the operations any of them
        // reaches are those its head reaches.
        let univ = self.univ.borrow();
        let mut keep = BTreeSet::new();
        for &head in &self.hist {
            keep.extend(univ.ancestors(head));
        }
        let objs = univ.objs_of(univ.ancestors(self.hub.head));
        self.hub.ops.retain(|op| keep.contains(op));
        self.hub.objs.retain(|obj| objs.contains(obj));
        drop(univ);
        let (ops, objs) = (
            sorted(self.hub.ops.iter().copied()),
            sorted(self.hub.objs.iter().copied()),
        );
        self.act(json!({"kind": "hubForget", "ops": ops, "objs": objs}));
    }

    /// The hive is made again, empty, as `HubDir::remake` makes one whose store is corrupt:
    /// the hub goes back to the root, then forgets everything else (`remake_reachable`).
    pub fn remake(&mut self) {
        self.hub_goes_back(0);
        self.hub_forget();
    }

    /// A lying hub: a `Fetched` reply about `head` carrying `op`, which the hub never
    /// accepted, delivered straight to the node. Either `op` is not reachable from `head`, or
    /// `head` is not the head the node knows (it is `op`, say). The node must ignore it
    /// (docs/internals/protocol.md, "Fetch"): staging operations the hub never accepted is how
    /// Locality would break. Unless a false reply told it of a head that reaches `op`.
    pub fn rogue_ops_reply(&mut self, node: usize, head: Op, op: Op) {
        use musubi_core::node::LocalRepo as _;
        let parents = self.univ.borrow().parents[op as usize].clone();
        let repo = &self.repos[node];
        // Not newer than what the node knows, or it would believe the head too.
        let reply = Reply::Fetched {
            seq: self.cores[node].known().0,
            head,
            ops: vec![OpEntry { id: op, parents }],
            ops_attachment: vec![],
            objects: vec![],
            records: repo.records().unwrap(),
            records_from: repo.applied.len() as u64,
            new_records: vec![],
            pruned: self.hub.univ.borrow_mut().record_state(&[]),
        };
        self.offered.insert(op);
        let handled = self.cores[node]
            .handle(&mut self.repos[node], reply)
            .unwrap();
        assert!(
            self.misled[node] || handled == Handled::Ignored,
            "node {node} accepted a lying hub's reply: {handled:?}"
        );
    }

    /// The records `node` has taken, how many, and the state of none, which it starts with,
    /// for a buggy hub's replies to agree with it on.
    pub fn node_records(&self, node: usize) -> (RecordState, u64, RecordState) {
        use musubi_core::node::LocalRepo as _;
        let repo = &self.repos[node];
        let none = self.univ.borrow_mut().record_state(&[]);
        (repo.records().unwrap(), repo.applied.len() as u64, none)
    }

    /// What the hub stores, accepted or not, for a buggy hub's replies to be made of.
    pub fn hub_stored(&self) -> (Vec<Op>, Vec<Obj>) {
        (
            self.hub.ops.iter().copied().collect(),
            self.hub.objs.iter().copied().collect(),
        )
    }

    pub fn parents(&self, op: Op) -> Vec<Op> {
        self.univ.borrow().parents[op as usize].clone()
    }

    /// The objects operation `op` made.
    pub fn objects(&self, op: Op) -> Vec<Obj> {
        self.univ.borrow().objs[op as usize].clone()
    }

    /// Whether the hub stores operation `op` and every operation and object it reaches.
    pub fn hub_closed(&self, op: Op) -> bool {
        self.hub.closed(op)
    }

    /// Whether the hub stores object `obj`.
    pub fn hub_has_object(&self, obj: Obj) -> bool {
        self.hub.objs.contains(&obj)
    }

    pub fn known(&self, node: usize) -> (u64, Op) {
        *self.cores[node].known()
    }

    /// A buggy hub: `node` takes `reply`, which the hub never sent, as an answer to its own
    /// request if `own`, or else as one that arrived late. The model has no such hub, so
    /// there is no oracle to check against.
    pub fn false_reply(&mut self, node: usize, reply: Rep, own: bool) {
        assert!(self.oracle.is_none(), "the Lean model has no hub that lies");
        self.misled[node] = true;
        match &reply {
            Reply::Head { head, .. } => {
                self.offered.insert(*head);
            }
            Reply::Fetched { head, ops, .. } => {
                self.offered.insert(*head);
                self.offered.extend(ops.iter().map(|entry| entry.id));
            }
            Reply::Objects { for_ops, .. } => self.offered.extend(for_ops.iter().copied()),
            Reply::Refused { .. } => {}
        }
        self.trace.push(
            json!({"kind": "falseReply", "node": node, "own": own, "reply": format!("{reply:?}")}),
        );
        self.node_handle(node, reply, own);
    }

    /// The operations the hub has accepted, before going back or since: below any head it
    /// accepted, not only its head, which an acceptance through what survives of the head
    /// before it need not descend from.
    fn ever_accepted(&self, univ: &Univ) -> BTreeSet<Op> {
        let mut accepted = BTreeSet::new();
        for &head in self
            .hist
            .iter()
            .chain(self.lost.iter().map(|(_, head)| head))
        {
            accepted.extend(univ.ancestors(head));
        }
        accepted
    }

    /// The operations the hub has never accepted: candidates for a lying hub to offer.
    pub fn unaccepted_ops(&self) -> Vec<Op> {
        let univ = self.univ.borrow();
        let accepted = self.ever_accepted(&univ);
        (1..univ.next())
            .filter(|op| !accepted.contains(op))
            .collect()
    }

    pub fn known_head(&self, node: usize) -> Op {
        self.cores[node].known().1
    }

    // Properties (docs/internals/protocol.md, "Properties").

    fn check_merge_ownership(&self, node: usize, merge: Op, parents: &[Op]) {
        if self.went_back || self.misled[node] {
            return;
        }
        let univ = self.univ.borrow();
        let accepted = univ.ancestors(self.hub.head);
        assert!(
            parents
                .iter()
                .any(|p| univ.creator[*p as usize] == Some(node) && !accepted.contains(p)),
            "MergeOwnership: merge {merge} on node {node} has no unaccepted parent of its own: {parents:?}"
        );
    }

    pub fn check_invariants(&self) {
        let univ = self.univ.borrow();
        assert!(self.hub.closed(self.hub.head), "HubClosed");
        let accepted = self.ever_accepted(&univ);
        for (n, repo) in self.repos.iter().enumerate() {
            // A node misled has only what the hub offered it, accepted or not.
            let offered = |x: &Op| self.misled[n] && self.offered.contains(x);
            for &x in &repo.lops {
                assert!(
                    univ.creator[x as usize] == Some(n) || accepted.contains(&x) || offered(&x),
                    "Locality: node {n} has {x}, neither its own nor accepted"
                );
                assert!(
                    univ.parents[x as usize]
                        .iter()
                        .all(|p| repo.lops.contains(p)),
                    "NodeClosed: parents"
                );
                assert!(
                    univ.objs[x as usize].iter().all(|o| repo.lobj.contains(o)),
                    "NodeClosed: objects"
                );
            }
            assert!(
                !repo.heads.is_empty() && repo.heads.is_subset(&repo.lops),
                "NodeClosed: heads"
            );
            for op in repo.sops.keys() {
                assert!(
                    accepted.contains(op) || offered(op),
                    "node {n} staged {op}, which the hub never accepted"
                );
            }
            assert_eq!(
                univ.maximal(&repo.heads),
                repo.heads,
                "heads form an antichain"
            );
            let (seq, head) = *self.cores[n].known();
            assert!(
                self.misled[n]
                    || self.hist.get(seq as usize) == Some(&head)
                    || self.lost.contains(&(seq, head)),
                "KnownIsHubHistory on node {n}"
            );
        }
        // Each head the hub accepted descends from the one before, or, where it accepted it
        // through what survives of that one, is above all of it, once everything the hub had
        // dropped then and the push dropped is (`imageAccept`'s `acceptDrops`).
        for (seq, pair) in (1..).zip(self.hist.windows(2)) {
            if self.contracted_accepts.contains(&seq) {
                let drops = flat(&self.hub.record_hist[seq as usize]);
                assert!(
                    univ.below(&drops, pair[0], pair[1]),
                    "HubMonotone, contracted"
                );
            } else {
                assert!(univ.is_ancestor(pair[0], pair[1]), "HubMonotone");
            }
        }
        // `SInv`: no head is in its holder's dropped set, and the root in none.
        let hub_dropped = self.hub.dropped();
        assert!(
            !hub_dropped.contains(&self.hub.head),
            "the hub's head is dropped"
        );
        assert!(!hub_dropped.contains(&ROOT), "the hub dropped the root");
        for (n, repo) in self.repos.iter().enumerate() {
            assert!(
                repo.heads.iter().all(|head| !repo.dropped.contains(head)),
                "node {n} has a head it dropped"
            );
            assert!(!repo.dropped.contains(&ROOT), "node {n} dropped the root");
            assert!(
                flat(&repo.applied).is_subset(&repo.dropped),
                "node {n} took records it doesn't drop"
            );
        }
    }

    pub fn converged(&self) -> bool {
        self.repos.iter().zip(&self.cores).all(|(repo, core)| {
            repo.heads == BTreeSet::from([self.hub.head])
                && *core.known() == (self.hub.seq, self.hub.head)
                && repo.applied == self.hub.records
                && repo.dropped == self.hub.dropped()
        })
    }

    /// Stops environment actions, makes the network reliable, and runs every node's policy
    /// until nothing changes. Panics if that takes too long: livelock.
    ///
    /// With an oracle, it checks the policy against the liveness proofs as it goes
    /// (docs/internals/conformance.md, "Liveness"): each exchange that changes a node's
    /// operations, heads, `known`, dropped set or applied records makes the refined measure
    /// fall, and one that doesn't leaves it where it was or lower. The older measures are
    /// checked only before drops, and `measure` only before the hub has gone back too.
    pub fn quiesce(&mut self) {
        self.trace.push(json!({"marker": "quiesce"}));
        let mut measure = self.measure();
        for _ in 0..30 {
            let mut changed = false;
            for node in 0..self.nodes() {
                // Each turn starts with a `Fetch`, whose reply makes the node's `known` a head
                // in the hub's current history, as `PStepR.realize` requires before the node
                // realizes anything: after the hub goes back, `NodeCore::step` would
                // otherwise realize below a head the hub has lost.
                let before = self.node_view(node);
                let sent_before = self.net.len();
                self.poll(node);
                self.round_trip(sent_before);
                self.check_measure(node, before, &mut measure);
                for _ in 0..200 {
                    let before = self.node_view(node);
                    let trace_before = self.trace.len();
                    self.exchange(node, 0);
                    if self.trace.len() == trace_before {
                        break;
                    }
                    self.check_measure(node, before, &mut measure);
                    changed = true;
                }
            }
            if !changed && self.converged() {
                // A cross-check of the oracle's `convergedE`: the states already agree.
                if let Some(measure) = self.measure() {
                    assert!(
                        measure.converged,
                        "converged, but not in the Lean model\ntrace: {:#?}",
                        self.trace
                    );
                }
                let univ = self.univ.borrow();
                let accepted = univ.ancestors(self.hub.head);
                // Through what survives, every operation the hub hasn't dropped; and in the
                // original history, where no step left it, every one.
                let dropped = self.hub.dropped();
                assert!(
                    (0..univ.next()).all(|x| accepted.contains(&x) || dropped.contains(&x)),
                    "converged, but not every operation that survives was accepted"
                );
                assert!(
                    self.contracted || (0..univ.next()).all(|x| accepted.contains(&x)),
                    "converged, but not every operation was accepted"
                );
                return;
            }
        }
        panic!("did not converge after quiescing\ntrace: {:#?}", self.trace);
    }

    /// The oracle's measures of the current state, with an oracle.
    pub fn measure(&mut self) -> Option<Measure> {
        let measure = self.oracle.as_mut().map(Oracle::measure);
        if let Some(measure) = &measure {
            let record_lag = self
                .repos
                .iter()
                .filter(|repo| repo.applied != self.hub.records)
                .count() as u64;
            assert_eq!(
                measure.smeasure[8], record_lag,
                "record lag differs from Lean"
            );
            assert_eq!(
                measure.converged,
                self.converged(),
                "convergence differs from Lean"
            );
        }
        measure
    }

    /// The parts of a node the measures read, which an exchange that changes the node
    /// changes. Only with an oracle: nothing else checks them.
    fn node_view(&self, node: usize) -> Option<NodeView> {
        let repo = &self.repos[node];
        self.has_oracle().then(|| NodeView {
            lops: repo.lops.clone(),
            heads: repo.heads.clone(),
            known: *self.cores[node].known(),
            dropped: repo.dropped.clone(),
            applied: repo.applied.clone(),
            crash_pending: repo.crash_before_objects,
        })
    }

    /// After one of `node`'s exchanges in `quiesce`: the measure falls if the exchange
    /// changed the node, and does not rise if it didn't. Only the record-aware measure must
    /// fall for an exchange that changes applied records alone. The older measures apply
    /// only before drops, and `measure` only before the hub has gone back too.
    fn check_measure(
        &mut self,
        node: usize,
        before: Option<NodeView>,
        measure: &mut Option<Measure>,
    ) {
        let (Some(before), Some(after), Some(new)) = (before, self.node_view(node), self.measure())
        else {
            return;
        };
        // A crash the test armed before quiescing is no policy step: start afresh from it.
        let crashed = before.crash_pending && !after.crash_pending;
        let old = measure.replace(new.clone()).unwrap();
        if crashed {
            return;
        }
        let changed = (&before.lops, &before.heads, before.known, &before.dropped)
            != (&after.lops, &after.heads, after.known, &after.dropped);
        let records_changed = before.applied != after.applied;
        let fell = |old: &Vec<u64>, new: &Vec<u64>| {
            if changed { new < old } else { new <= old }
        };
        let what = if changed { "fall" } else { "stay or fall" };
        assert!(
            self.went_back || self.dropped_any || fell(&old.measure, &new.measure),
            "node {node}'s exchange did not make the measure {what}: {:?} to {:?}\ntrace: {:#?}",
            old.measure,
            new.measure,
            self.trace
        );
        assert!(
            self.dropped_any || fell(&old.rmeasure, &new.rmeasure),
            "node {node}'s exchange did not make rmeasure {what}: {:?} to {:?}\ntrace: {:#?}",
            old.rmeasure,
            new.rmeasure,
            self.trace
        );
        let what = if changed || records_changed {
            "fall"
        } else {
            "stay or fall"
        };
        assert!(
            if changed || records_changed {
                new.smeasure < old.smeasure
            } else {
                new.smeasure <= old.smeasure
            },
            "node {node}'s exchange did not make the record measure {what}: {:?} to {:?}\ntrace: {:#?}",
            old.smeasure,
            new.smeasure,
            self.trace
        );
    }

    /// The Rust side's state in the oracle's JSON form.
    fn state_json(&self) -> Value {
        let univ = self.univ.borrow();
        let ops: Vec<Value> = (1..univ.next())
            .map(|id| json!({"id": id, "parents": univ.parents[id as usize], "objs": univ.objs[id as usize]}))
            .collect();
        let nodes: Vec<Value> = self
            .repos
            .iter()
            .zip(&self.cores)
            .map(|(repo, core)| {
                let (seq, head) = core.known();
                json!({
                    "lops": repo.lops, "lobj": repo.lobj, "heads": repo.heads,
                    "known": [seq, head], "sops": repo.sops.keys().collect::<Vec<_>>(), "sobj": repo.sobj,
                    "dropped": repo.dropped, "applied": records_json(&repo.applied),
                })
            })
            .collect();
        let net: BTreeSet<String> = self
            .net
            .iter()
            .flat_map(|m| m.model.iter().map(Value::to_string))
            .collect();
        json!({
            "next": univ.next(),
            "ops": ops,
            "hub": {"ops": self.hub.ops, "objs": self.hub.objs, "head": self.hub.head, "seq": self.hub.seq,
                "records": records_json(&self.hub.records), "pruned": self.hub.pruned},
            "nodes": nodes,
            "net": net.into_iter().map(|m| serde_json::from_str::<Value>(&m).unwrap()).collect::<Vec<_>>(),
        })
    }
}

/// Records as the model's JSON has them: in order, each sorted.
fn records_json(records: &[Vec<Op>]) -> Value {
    json!(
        records
            .iter()
            .map(|record| sorted(record.iter().copied()))
            .collect::<Vec<_>>()
    )
}

/// The model's supersede message: the records a node had taken, and what it had dropped.
/// A supersede message, riding on a push to `new`.
fn sup_json(node: usize, (applied, dropped): &Sup, new: Op) -> Value {
    json!({"msg": "supersede", "node": node, "applied": records_json(applied),
        "dropped": sorted(dropped.iter().copied()), "new": new})
}

/// Normalizes a state for comparison: sets become sorted arrays and `net` a sorted,
/// deduplicated list. Pairs (`known`) and node order are kept.
fn canonical_state(state: &Value) -> Value {
    fn set(value: &Value) -> Value {
        let mut numbers: Vec<u64> = value
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_u64)
            .collect();
        numbers.sort_unstable();
        numbers.dedup();
        json!(numbers)
    }
    fn with_sets(value: &Value, fields: &[&str]) -> Value {
        let mut value = value.clone();
        for field in fields {
            if let Some(entry) = value.get(*field) {
                let normalized = set(entry);
                value[*field] = normalized;
            }
        }
        value
    }
    let mut ops: Vec<Value> = state["ops"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|op| with_sets(op, &["parents", "objs"]))
        .collect();
    ops.sort_by_key(|op| op["id"].as_u64());
    let nodes: Vec<Value> = state["nodes"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|node| with_sets(node, &["lops", "lobj", "heads", "sops", "sobj", "dropped"]))
        .collect();
    let mut net: Vec<Value> = state["net"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|msg| with_sets(msg, &["ops", "objs", "dropped"]))
        .collect();
    net.sort_by_cached_key(Value::to_string);
    net.dedup();
    json!({
        "next": state["next"],
        "ops": ops,
        "hub": with_sets(&state["hub"], &["ops", "objs"]),
        "nodes": nodes,
        "net": net,
    })
}
