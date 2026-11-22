//! A hub and nodes running the real core over a network the test controls completely, with
//! every step translated into Lean model actions (docs/internals/conformance.md).

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use musubi_core::hub;
use musubi_core::hub::CasOutcome;
use musubi_core::message::Head;
use musubi_core::message::HeadKind;
use musubi_core::message::OpEntry;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::Handled;
use musubi_core::node::NodeCore;
use musubi_core::node::Step;
use serde_json::Value;
use serde_json::json;

use super::model::FakeHub;
use super::model::FakeRepo;
use super::model::Obj;
use super::model::Op;
use super::model::ROOT;
use super::model::SharedUniv;
use super::model::Univ;
use super::oracle::Measure;
use super::oracle::Oracle;
use super::storage::{Fallible, Faults, SharedFaults, StorageError, Timing};

mod properties;
mod storage_failures;

type Req = Request<Op, Vec<Obj>>;
type Rep = Reply<Op, Vec<Obj>>;

#[derive(Clone, Debug)]
enum Payload {
    Request(usize, Req),
    Reply(usize, Rep),
}

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
}

/// What of a node `World::quiesce` watches across an exchange.
struct NodeView {
    lops: BTreeSet<Op>,
    heads: BTreeSet<Op>,
    known: (u64, Op),
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

/// One line for a recorded model action or harness marker: its kind, then its other fields as
/// `name=value`. A case records hundreds of actions, which `{:#?}` spread over thousands of
/// lines.
fn compact_action(action: &Value) -> String {
    let Some(fields) = action.as_object() else {
        return action.to_string();
    };
    let plain = |value: &Value| {
        value
            .as_str()
            .map_or_else(|| value.to_string(), str::to_string)
    };
    let mut line: Vec<String> = ["kind", "marker"]
        .iter()
        .filter_map(|name| fields.get(*name).map(plain))
        .collect();
    line.extend(
        fields
            .iter()
            .filter(|(name, _)| *name != "kind" && *name != "marker")
            .map(|(name, value)| format!("{name}={}", plain(value))),
    );
    line.join(" ")
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
        };
        if let Some(oracle) = &mut world.oracle {
            world.oracle_state = oracle.reset(nodes);
        }
        world
    }

    pub fn nodes(&self) -> usize {
        self.repos.len()
    }

    /// The trace so far, one line per model action or harness marker, for a failure.
    pub fn compact_trace(&self) -> String {
        let lines: Vec<String> = self.trace.iter().map(compact_action).collect();
        lines.join("\n")
    }

    pub fn local_ops(&self, node: usize) -> Vec<Op> {
        self.repos[node].lops.iter().copied().collect()
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
                    "the Lean model rejects {action}: {error}\ntrace:\n{}",
                    self.compact_trace()
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
        self.repos[node].merge_objs = merge_objs;
        let heads_before: Vec<Op> = self.repos[node].heads.iter().copied().collect();
        let step = match self.cores[node].step(&mut self.repos[node]) {
            Ok(step) => step,
            Err(error) => {
                self.storage_failed(Some(node), before, error, vec![]);
                return false;
            }
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
            Step::Advanced(_) => self.act(json!({"kind": "advance", "node": node})),
            Step::Send(requests) => {
                for request in requests {
                    self.check_upload(node, &request);
                    self.send_request(node, request);
                }
            }
        }
        true
    }

    fn send_request(&mut self, node: usize, request: Req) {
        let univ = self.univ.clone();
        let univ = univ.borrow();
        let (action, model) = match &request {
            Request::Fetch { base, haves, .. } => {
                let haves = sorted(haves.iter().copied());
                (
                    json!({"kind": "fetchAll", "node": node, "base": base, "haves": haves}),
                    json!({"msg": "fetch", "node": node, "base": base, "haves": haves}),
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
                    json!({"kind": "fetchObjs", "node": node, "objs": objs}),
                    json!({"msg": "getObjs", "node": node, "objs": objs}),
                )
            }
            Request::Push {
                ops,
                objects,
                expected,
                new,
                ..
            } => {
                let (ops, objs) = (sorted(ops.iter().copied()), sorted(objects.iter().copied()));
                (
                    json!({"kind": "pushAll", "node": node, "ops": ops, "objs": objs,
                        "expected": expected, "new": new}),
                    json!({"msg": "push", "node": node, "ops": ops, "objs": objs,
                        "expected": expected, "new": new}),
                )
            }
        };
        drop(univ);
        self.send(vec![model], Payload::Request(node, request));
        self.act(action);
    }

    /// A policy `Push` uploads exactly the model's `upOps` and `upObjs`. The separate
    /// rogue-push rule deliberately bypasses policy.
    fn check_upload(&mut self, node: usize, request: &Req) {
        let Request::Push {
            ops,
            objects,
            expected,
            new,
            ..
        } = request
        else {
            return;
        };
        assert_eq!(*expected, self.cores[node].known().head);
        assert_eq!(self.repos[node].heads, BTreeSet::from([*new]));
        let Some(oracle) = &mut self.oracle else {
            return;
        };
        let (up_ops, up_objs) = oracle.upload(node, *new);
        assert_eq!(
            (sorted(ops.iter().copied()), sorted(objects.iter().copied())),
            (up_ops, up_objs),
            "node {node}'s push of {new} does not upload upOps and upObjs\ntrace:\n{}",
            self.compact_trace()
        );
    }

    /// A push the policy would never make: `Cas(expected, new)` for any local `new`, without
    /// uploading anything. The model allows it, so the hub must defend itself.
    pub fn rogue_push(&mut self, node: usize, expected: Op, new: Op) {
        let request = Request::Push {
            ops: vec![],
            ops_attachment: vec![],
            objects: vec![],
            expected,
            new,
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
            Payload::Request(node, request) => self.hub_handle(node, request),
            Payload::Reply(node, reply) => self.node_handle(node, reply, false),
        }
    }

    fn hub_handle(&mut self, node: usize, request: Req) {
        let before = self.storage_begin();
        let action = match &request {
            Request::Fetch { base, haves, .. } => json!({"kind": "hubFetch", "node": node,
                "base": base, "haves": sorted(haves.iter().copied())}),
            Request::GetObjects { for_ops, haves, .. } => {
                let objs = sorted(
                    self.univ
                        .borrow()
                        .objs_of(for_ops.iter().copied())
                        .into_iter()
                        .filter(|o| !haves.contains(o)),
                );
                json!({"kind": "hubGetObjs", "node": node, "objs": objs})
            }
            Request::Push {
                ops,
                ops_attachment,
                objects,
                expected,
                new,
            } => {
                let push = hub::Push {
                    ops,
                    ops_attachment,
                    objects,
                    expected,
                    new,
                };
                let (outcome, handled) = match push.answer(&mut self.hub) {
                    Ok(result) => result,
                    Err(error) => {
                        self.storage_failed(Some(node), before, error, vec![]);
                        return;
                    }
                };
                let kind = match outcome {
                    CasOutcome::Idempotent => "hubPushIdem",
                    CasOutcome::Accepted => "hubPushAccept",
                    CasOutcome::Rejected => "hubPushReject",
                    CasOutcome::Incomplete => "hubPushIncomplete",
                };
                let action = json!({"kind": kind, "node": node,
                    "ops": sorted(ops.iter().copied()), "objs": sorted(objects.iter().copied()),
                    "expected": expected, "new": new});
                self.reply_and_act(node, handled.reply, action, handled.publish);
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
        self.reply_and_act(node, handled.reply, action, handled.publish);
    }

    /// Sends `reply`, and the notifications of a head the hub `publish`es, with the model
    /// `action` the hub took.
    fn reply_and_act(&mut self, node: usize, reply: Rep, action: Value, publish: Option<Head<Op>>) {
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
        if let Some(Head { seq, head }) = &publish {
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
        let model = match &reply {
            Reply::Head { kind, seq, head } => vec![
                json!({"msg": "head", "node": node, "headKind": kind_name(*kind), "seq": seq, "head": head}),
            ],
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
            ],
            Reply::Objects { attachment, .. } => {
                vec![
                    json!({"msg": "objs", "node": node, "objs": sorted(attachment.iter().copied())}),
                ]
            }
        };
        self.send(model, Payload::Reply(node, reply));
        if let Some(Head { seq, head }) = publish {
            assert_eq!(seq as usize, self.hist.len());
            self.hist.push(head);
            for target in 0..self.nodes() {
                let reply = Reply::Head {
                    kind: HeadKind::Notify,
                    seq,
                    head,
                };
                let model = json!({"msg": "head", "node": target, "headKind": "notify", "seq": seq, "head": head});
                self.send(vec![model], Payload::Reply(target, reply));
            }
        }
        self.act(action);
    }

    /// Has `node` take `reply`: `own` if it answers the request the node just sent, which
    /// the node takes as saying where the hub is now (`NodeCore::handle_reply`).
    fn node_handle(&mut self, node: usize, reply: Rep, own: bool) {
        let before = self.storage_begin();
        let known_before = self.known(node);
        let head_kind = match &reply {
            Reply::Head { kind, .. } => *kind,
            _ => HeadKind::Head,
        };
        let objects = match &reply {
            Reply::Objects { attachment, .. } => sorted(attachment.iter().copied()),
            Reply::Fetched { objects, .. } => sorted(objects.iter().copied()),
            Reply::Head { .. } => vec![],
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
                let (seq, head) = self.known(node);
                if (seq, head) != known_before && seq > 0 {
                    actions.push(json!({"kind": "learn", "node": node,
                        "headKind": kind_name(head_kind), "seq": seq, "head": head}));
                }
                self.storage_failed(Some(node), before, error, actions);
                return;
            }
        };
        match handled {
            Handled::Learned { kind, seq, head } => {
                actions.push(json!({"kind": "learn", "node": node, "headKind": kind_name(kind), "seq": seq, "head": head}));
                self.act_all(actions);
            }
            Handled::Fetched { learned, staged } => {
                if let Some(Head { seq, head }) = learned {
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
            Handled::Ignored => {
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
        self.repos[node].restart();
        self.cores[node].restart();
        self.act(json!({"kind": "loseKnown", "node": node}));
    }

    /// The hub goes back to the head it accepted at `seq`, as a power cut can make it lose
    /// the later ones (`hubRegress`). Going back to where it is changes nothing, and the
    /// properties that need a hub that never went back still hold.
    pub fn hub_goes_back(&mut self, seq: u64) {
        let lost: Vec<Op> = self.hist.drain(seq as usize + 1..).collect();
        self.went_back |= !lost.is_empty();
        self.lost.extend((seq + 1..).zip(lost));
        self.hub.head = self.hist[seq as usize];
        self.hub.seq = seq;
        self.act(json!({"kind": "hubRegress", "seq": seq}));
    }

    pub fn hub_head(&self) -> Op {
        self.hub.head
    }

    pub fn heads(&self, node: usize) -> &BTreeSet<Op> {
        &self.repos[node].heads
    }

    pub fn hub_seq(&self) -> u64 {
        self.hub.seq
    }

    pub fn crash_hub(&mut self) {
        self.act(json!({"kind": "crashHub"}));
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
        let parents = self.univ.borrow().parents[op as usize].clone();
        // Not newer than what the node knows, or it would believe the head too.
        let reply = Reply::Fetched {
            seq: self.cores[node].known().seq,
            head,
            ops: vec![OpEntry { id: op, parents }],
            ops_attachment: vec![],
            objects: vec![],
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
        let Head { seq, head } = *self.cores[node].known();
        (seq, head)
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
        }
        self.trace.push(
            json!({"kind": "falseReply", "node": node, "own": own, "reply": format!("{reply:?}")}),
        );
        self.node_handle(node, reply, own);
    }

    /// The operations the hub has accepted, before going back or since: below any head it
    /// accepted, not only its head, which may have lost heads since.
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
        self.cores[node].known().head
    }

    /// Stops environment actions, makes the network reliable, and runs every node's policy
    /// until nothing changes. Panics if that takes too long: livelock.
    ///
    /// With an oracle, it checks the policy against the liveness proofs as it goes
    /// (docs/internals/conformance.md, "Liveness"): each exchange that changes a node's
    /// operations, heads or `known` makes `rmeasure` fall, and one that doesn't leaves it where
    /// it was or lower; `measure` is checked only before the hub has gone back.
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
                        "converged, but not in the Lean model\ntrace:\n{}",
                        self.compact_trace()
                    );
                }
                let univ = self.univ.borrow();
                let accepted = univ.ancestors(self.hub.head);
                assert!(
                    (0..univ.next()).all(|x| accepted.contains(&x)),
                    "converged, but not every operation was accepted"
                );
                return;
            }
        }
        panic!(
            "did not converge after quiescing\ntrace:\n{}",
            self.compact_trace()
        );
    }

    /// The oracle's measures of the current state, with an oracle.
    pub fn measure(&mut self) -> Option<Measure> {
        let measure = self.oracle.as_mut().map(Oracle::measure);
        if let Some(measure) = &measure {
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
            known: self.known(node),
            crash_pending: repo.crash_before_objects,
        })
    }

    /// After one of `node`'s exchanges in `quiesce`: the measures fall if the exchange
    /// changed the node, and do not rise if it didn't; `measure` only before the hub has
    /// gone back.
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
        let changed =
            (&before.lops, &before.heads, before.known) != (&after.lops, &after.heads, after.known);
        let fell = |old: &Vec<u64>, new: &Vec<u64>| {
            if changed { new < old } else { new <= old }
        };
        let what = if changed { "fall" } else { "stay or fall" };
        assert!(
            self.went_back || fell(&old.measure, &new.measure),
            "node {node}'s exchange did not make the measure {what}: {:?} to {:?}\ntrace:\n{}",
            old.measure,
            new.measure,
            self.compact_trace()
        );
        assert!(
            fell(&old.rmeasure, &new.rmeasure),
            "node {node}'s exchange did not make rmeasure {what}: {:?} to {:?}\ntrace:\n{}",
            old.rmeasure,
            new.rmeasure,
            self.compact_trace()
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
                let Head { seq, head } = *core.known();
                json!({
                    "lops": repo.lops, "lobj": repo.lobj, "heads": repo.heads,
                    "known": [seq, head], "sops": repo.sops.keys().collect::<Vec<_>>(), "sobj": repo.sobj,
                })
            })
            .collect();
        // Compact JSON remains the ordering/deduplication key. Protocol numbers are integer
        // IDs and counts, so each key identifies its original Value without reparsing it.
        let net: BTreeMap<String, &Value> = self
            .net
            .iter()
            .flat_map(|message| &message.model)
            .map(|message| (message.to_string(), message))
            .collect();
        Value::Object(
            [
                ("next".to_owned(), univ.next().into()),
                ("ops".to_owned(), Value::Array(ops)),
                ("hub".to_owned(), json!({
                    "ops": self.hub.ops, "objs": self.hub.objs, "head": self.hub.head, "seq": self.hub.seq,
                })),
                ("nodes".to_owned(), Value::Array(nodes)),
                ("net".to_owned(), Value::Array(net.into_values().cloned().collect())),
            ]
            .into_iter()
            .collect(),
        )
    }
}

/// Normalizes a state for comparison: sets become sorted arrays and `net` a sorted,
/// deduplicated list. Pairs (`known`) and node order are kept. Only the fields of
/// `Exec.lean`'s state are compared.
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
    /// `value` with only `kept` of its fields, those in `sets` normalized as sets.
    fn project(value: &Value, kept: &[&str], sets: &[&str]) -> Value {
        Value::Object(
            kept.iter()
                .filter_map(|&field| {
                    let entry = value.get(field)?;
                    let entry = if sets.contains(&field) {
                        set(entry)
                    } else {
                        entry.clone()
                    };
                    Some((field.to_owned(), entry))
                })
                .collect(),
        )
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
        .map(|node| {
            let sets = ["lops", "lobj", "heads", "sops", "sobj"];
            let kept = ["lops", "lobj", "heads", "known", "sops", "sobj"];
            project(node, &kept, &sets)
        })
        .collect();
    let mut net: Vec<Value> = state["net"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|msg| with_sets(msg, &["ops", "objs"]))
        .collect();
    net.sort_by_cached_key(Value::to_string);
    net.dedup();
    Value::Object(
        [
            ("next".to_owned(), state["next"].clone()),
            ("ops".to_owned(), Value::Array(ops)),
            (
                "hub".to_owned(),
                project(
                    &state["hub"],
                    &["ops", "objs", "head", "seq"],
                    &["ops", "objs"],
                ),
            ),
            ("nodes".to_owned(), Value::Array(nodes)),
            ("net".to_owned(), Value::Array(net)),
        ]
        .into_iter()
        .collect(),
    )
}
