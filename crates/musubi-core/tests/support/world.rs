//! A hub and nodes running the real core over a network the test controls completely, with
//! every step translated into Lean model actions (docs/conformance.md).

use std::collections::BTreeSet;

use musubi_core::hub;
use musubi_core::hub::CasOutcome;
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
use super::oracle::Oracle;

type Req = Request<Op, Vec<Obj>>;
type Rep = Reply<Op, Vec<Obj>>;

#[derive(Clone, Debug)]
enum Payload {
    Request(usize, Req),
    Reply(usize, Rep),
}

/// A message in flight: its Lean model form, and what the Rust side actually sent.
#[derive(Clone, Debug)]
struct InFlight {
    model: Value,
    payload: Payload,
    delivered: bool,
}

pub struct World {
    univ: SharedUniv,
    hub: FakeHub,
    /// `hist[i]`: the head accepted at sequence number `i`.
    hist: Vec<Op>,
    repos: Vec<FakeRepo>,
    cores: Vec<NodeCore<Op>>,
    /// Every message ever sent. Any can be delivered again, so this is the model's `net`.
    net: Vec<InFlight>,
    oracle: Option<Oracle>,
    pub trace: Vec<Value>,
    /// The operations each node last asked for with `GetOpsSince`.
    last_fetch: Vec<Option<Vec<Op>>>,
}

fn kind_name(kind: HeadKind) -> &'static str {
    match kind {
        HeadKind::Head => "head",
        HeadKind::Accepted => "accepted",
        HeadKind::Rejected => "rejected",
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
        let mut world = Self {
            hub: FakeHub::new(univ.clone()),
            hist: vec![ROOT],
            repos: (0..nodes).map(|n| FakeRepo::new(univ.clone(), n)).collect(),
            cores: (0..nodes).map(|_| NodeCore::new(ROOT)).collect(),
            net: vec![],
            univ,
            oracle,
            trace: vec![],
            last_fetch: vec![None; nodes],
        };
        if let Some(oracle) = &mut world.oracle {
            oracle.reset(nodes);
        }
        world
    }

    pub fn nodes(&self) -> usize {
        self.repos.len()
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

    /// Records a model action and, with an oracle, checks it is a legal step leading to the
    /// state the Rust side is in.
    fn act(&mut self, action: Value) {
        self.trace.push(action.clone());
        let expected = self.state_json();
        if let Some(oracle) = &mut self.oracle {
            let state = oracle.step(&action).unwrap_or_else(|error| {
                panic!(
                    "the Lean model rejects {action}: {error}\ntrace: {:#?}",
                    self.trace
                )
            });
            let (got, want) = (canonical_state(&state), canonical_state(&expected));
            assert_eq!(
                got, want,
                "state differs from the Lean model after {action}"
            );
        }
    }

    fn send(&mut self, model: Value, payload: Payload) {
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

    /// The poll timer: send `GetHead`.
    pub fn poll(&mut self, node: usize) {
        self.send(
            json!({"msg": "getHead", "node": node}),
            Payload::Request(node, Request::GetHead),
        );
        self.act(json!({"kind": "getHead", "node": node}));
    }

    /// One policy step. Returns whether anything happened.
    pub fn node_step(&mut self, node: usize, merge_objs: usize) -> bool {
        self.repos[node].merge_objs = merge_objs;
        let heads_before: Vec<Op> = self.repos[node].heads.iter().copied().collect();
        let step = self.cores[node].step(&mut self.repos[node]).unwrap();
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
            Request::GetHead => (
                json!({"kind": "getHead", "node": node}),
                json!({"msg": "getHead", "node": node}),
            ),
            Request::GetOpsSince { head, base } => {
                let ops = univ.between(*head, *base);
                self.last_fetch[node] = Some(ops.clone());
                (
                    json!({"kind": "fetchOps", "node": node, "ops": ops}),
                    json!({"msg": "getOps", "node": node, "ops": ops}),
                )
            }
            Request::GetObjects { for_ops, .. } => {
                let objs = sorted(univ.objs_of(for_ops.iter().copied()));
                (
                    json!({"kind": "fetchObjs", "node": node, "objs": objs}),
                    json!({"msg": "getObjs", "node": node, "objs": objs}),
                )
            }
            Request::PutOps { ops, .. } => {
                let ops = sorted(ops.iter().copied());
                (
                    json!({"kind": "uploadOps", "node": node, "ops": ops}),
                    json!({"msg": "putOps", "node": node, "ops": ops}),
                )
            }
            Request::PutObjects { attachment, .. } => {
                let objs = sorted(attachment.iter().copied());
                (
                    json!({"kind": "uploadObjs", "node": node, "objs": objs}),
                    json!({"msg": "putObjs", "node": node, "objs": objs}),
                )
            }
            Request::Cas { expected, new } => (
                json!({"kind": "push", "node": node, "expected": expected, "new": new}),
                json!({"msg": "cas", "node": node, "expected": expected, "new": new}),
            ),
        };
        drop(univ);
        self.send(model, Payload::Request(node, request));
        self.act(action);
    }

    /// A push the policy would never make: `Cas(expected, new)` for any local `new`, without
    /// uploading anything. The model allows it, so the hub must defend itself.
    pub fn rogue_push(&mut self, node: usize, expected: Op, new: Op) {
        self.send_request(node, Request::Cas { expected, new });
    }

    /// How often `node`'s core has read a staged operation, and asked about objects.
    pub fn repo_work(&self, node: usize) -> (usize, usize) {
        let repo = &self.repos[node];
        (repo.staged_reads.get(), repo.object_checks.get())
    }

    /// The operations `node` last asked for with `GetOpsSince`.
    pub fn last_fetch(&self, node: usize) -> Option<&[Op]> {
        self.last_fetch[node].as_deref()
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

    /// One policy step whose requests reach the hub at once, and whose replies come
    /// straight back: a fast round trip, interleaved with whatever else is going on.
    pub fn exchange(&mut self, node: usize, merge_objs: usize) {
        let sent_before = self.net.len();
        if !self.node_step(node, merge_objs) {
            return;
        }
        let mut i = sent_before;
        while i < self.net.len() {
            if matches!(self.net[i].payload, Payload::Request(..)) {
                let replies_from = self.net.len();
                self.deliver(i);
                if replies_from < self.net.len() {
                    self.deliver(replies_from);
                }
            }
            i += 1;
        }
    }

    fn deliver_payload(&mut self, payload: Payload) {
        match payload {
            Payload::Request(node, request) => self.hub_handle(node, request),
            Payload::Reply(node, reply) => self.node_handle(node, reply),
        }
    }

    fn hub_handle(&mut self, node: usize, request: Req) {
        let univ = self.univ.clone();
        let action = {
            let univ = univ.borrow();
            match &request {
                Request::GetHead => json!({"kind": "hubGetHead", "node": node}),
                Request::PutOps { ops, .. } => {
                    json!({"kind": "hubPutOps", "node": node, "ops": sorted(ops.iter().copied())})
                }
                Request::PutObjects { attachment, .. } => {
                    json!({"kind": "hubPutObjs", "node": node, "objs": sorted(attachment.iter().copied())})
                }
                Request::GetOpsSince { head, base } => {
                    json!({"kind": "hubGetOps", "node": node, "ops": univ.between(*head, *base)})
                }
                Request::GetObjects { for_ops, .. } => {
                    let objs = sorted(univ.objs_of(for_ops.iter().copied()));
                    json!({"kind": "hubGetObjs", "node": node, "objs": objs})
                }
                Request::Cas { .. } => Value::Null,
            }
        };
        let handled = if let Request::Cas { expected, new } = &request {
            let (outcome, handled) = hub::cas(&mut self.hub, expected, new).unwrap();
            let kind = match outcome {
                CasOutcome::Idempotent => "casIdem",
                CasOutcome::Accepted => "casAccept",
                CasOutcome::Rejected => "casReject",
            };
            self.reply_and_act(
                node,
                handled.reply,
                json!({"kind": kind, "node": node, "expected": expected, "new": new}),
                handled.publish,
            );
            return;
        } else {
            hub::handle(&mut self.hub, request).unwrap()
        };
        self.reply_and_act(node, handled.reply, action, handled.publish);
    }

    fn reply_and_act(
        &mut self,
        node: usize,
        reply: Rep,
        action: Value,
        publish: Option<(u64, Op)>,
    ) {
        let model = match &reply {
            Reply::Head { kind, seq, head } => {
                json!({"msg": "head", "node": node, "headKind": kind_name(*kind), "seq": seq, "head": head})
            }
            Reply::Stored => json!({"msg": "stored", "node": node}),
            Reply::Ops { ops, .. } => {
                json!({"msg": "ops", "node": node, "ops": sorted(ops.iter().map(|e| e.id))})
            }
            Reply::Objects { attachment, .. } => {
                json!({"msg": "objs", "node": node, "objs": sorted(attachment.iter().copied())})
            }
        };
        self.send(model, Payload::Reply(node, reply));
        if let Some((seq, head)) = publish {
            assert_eq!(seq as usize, self.hist.len());
            self.hist.push(head);
            for target in 0..self.nodes() {
                let reply = Reply::Head {
                    kind: HeadKind::Notify,
                    seq,
                    head,
                };
                let model = json!({"msg": "head", "node": target, "headKind": "notify", "seq": seq, "head": head});
                self.send(model, Payload::Reply(target, reply));
            }
        }
        self.act(action);
    }

    fn node_handle(&mut self, node: usize, reply: Rep) {
        let objects = match &reply {
            Reply::Objects { attachment, .. } => sorted(attachment.iter().copied()),
            _ => vec![],
        };
        match self.cores[node].handle(&mut self.repos[node], reply).unwrap() {
            Handled::Learned { kind, seq, head } => self.act(
                json!({"kind": "learn", "node": node, "headKind": kind_name(kind), "seq": seq, "head": head}),
            ),
            Handled::StagedOps(ops) => {
                self.act(json!({"kind": "recvOps", "node": node, "ops": sorted(ops)}));
            }
            Handled::StagedObjects(_) => {
                self.act(json!({"kind": "recvObjs", "node": node, "objs": objects}));
            }
            Handled::Acknowledged | Handled::Ignored => {}
        }
    }

    // Failures.

    pub fn crash_node(&mut self, node: usize) {
        self.cores[node].restart(ROOT);
        self.act(json!({"kind": "loseKnown", "node": node}));
    }

    pub fn crash_hub(&mut self) {
        self.act(json!({"kind": "crashHub"}));
    }

    pub fn has_oracle(&self) -> bool {
        self.oracle.is_some()
    }

    /// A hub that garbage-collects everything outside `closure(head)`, including uploads it
    /// acknowledged but never accepted. The model allows this (`hubForget`); it is not in
    /// the oracle's vocabulary, so only runs without an oracle use it.
    pub fn hub_forget(&mut self) {
        assert!(self.oracle.is_none(), "hubForget is not an oracle action");
        let univ = self.univ.borrow();
        let keep = univ.ancestors(self.hub.head);
        let objs = univ.objs_of(keep.iter().copied());
        self.hub.ops.retain(|op| keep.contains(op));
        self.hub.objs.retain(|obj| objs.contains(obj));
        drop(univ);
        self.trace.push(json!({"kind": "hubForget"}));
    }

    /// A lying hub: an `Ops` reply about `head` carrying `op`, which is not reachable from
    /// `head`, delivered straight to the node. The node must ignore it (docs/protocol.md,
    /// "Fetch"): staging operations the hub never accepted is how Locality would break.
    pub fn rogue_ops_reply(&mut self, node: usize, head: Op, op: Op) {
        let parents = self.univ.borrow().parents[op as usize].clone();
        let reply = Reply::Ops {
            head,
            ops: vec![OpEntry { id: op, parents }],
            attachment: vec![],
        };
        let handled = self.cores[node]
            .handle(&mut self.repos[node], reply)
            .unwrap();
        assert_eq!(
            handled,
            Handled::Ignored,
            "node {node} accepted a lying hub's reply"
        );
    }

    /// The operations the hub has not accepted: candidates for a lying hub to offer.
    pub fn unaccepted_ops(&self) -> Vec<Op> {
        let univ = self.univ.borrow();
        let accepted = univ.ancestors(self.hub.head);
        (1..univ.next())
            .filter(|op| !accepted.contains(op))
            .collect()
    }

    pub fn known_head(&self, node: usize) -> Op {
        self.cores[node].known().1
    }

    // Properties (docs/protocol.md, "Properties").

    fn check_merge_ownership(&self, node: usize, merge: Op, parents: &[Op]) {
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
        let accepted = univ.ancestors(self.hub.head);
        for (n, repo) in self.repos.iter().enumerate() {
            for &x in &repo.lops {
                assert!(
                    univ.creator[x as usize] == Some(n) || accepted.contains(&x),
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
                    accepted.contains(op),
                    "node {n} staged {op}, which the hub never accepted"
                );
            }
            assert_eq!(
                univ.maximal(&repo.heads),
                repo.heads,
                "heads form an antichain"
            );
            let (seq, head) = *self.cores[n].known();
            assert_eq!(
                self.hist.get(seq as usize),
                Some(&head),
                "KnownIsHubHistory on node {n}"
            );
        }
        for pair in self.hist.windows(2) {
            assert!(univ.is_ancestor(pair[0], pair[1]), "HubMonotone");
        }
    }

    pub fn converged(&self) -> bool {
        self.repos.iter().zip(&self.cores).all(|(repo, core)| {
            repo.heads == BTreeSet::from([self.hub.head])
                && *core.known() == (self.hub.seq, self.hub.head)
        })
    }

    /// Stops environment actions, makes the network reliable, and runs every node's policy
    /// until nothing changes. Panics if that takes too long: livelock.
    pub fn quiesce(&mut self) {
        self.trace.push(json!({"marker": "quiesce"}));
        for _ in 0..30 {
            let mut changed = false;
            for node in 0..self.nodes() {
                self.poll(node);
                self.deliver_latest();
                self.deliver_latest();
                for _ in 0..200 {
                    let before = self.trace.len();
                    self.exchange(node, 0);
                    if self.trace.len() == before {
                        break;
                    }
                    changed = true;
                }
            }
            if !changed && self.converged() {
                let univ = self.univ.borrow();
                let accepted = univ.ancestors(self.hub.head);
                assert!(
                    (0..univ.next()).all(|x| accepted.contains(&x)),
                    "converged, but not every operation was accepted"
                );
                return;
            }
        }
        panic!("did not converge after quiescing\ntrace: {:#?}", self.trace);
    }

    fn deliver_latest(&mut self) {
        self.deliver(self.net.len() - 1);
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
                })
            })
            .collect();
        let net: BTreeSet<String> = self.net.iter().map(|m| m.model.to_string()).collect();
        json!({
            "next": univ.next(),
            "ops": ops,
            "hub": {"ops": self.hub.ops, "objs": self.hub.objs, "head": self.hub.head, "seq": self.hub.seq},
            "nodes": nodes,
            "net": net.into_iter().map(|m| serde_json::from_str::<Value>(&m).unwrap()).collect::<Vec<_>>(),
        })
    }
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
        .map(|node| with_sets(node, &["lops", "lobj", "heads", "sops", "sobj"]))
        .collect();
    let mut net: Vec<Value> = state["net"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|msg| with_sets(msg, &["ops", "objs"]))
        .collect();
    net.sort_by_key(Value::to_string);
    net.dedup();
    json!({
        "next": state["next"],
        "ops": ops,
        "hub": with_sets(&state["hub"], &["ops", "objs"]),
        "nodes": nodes,
        "net": net,
    })
}
