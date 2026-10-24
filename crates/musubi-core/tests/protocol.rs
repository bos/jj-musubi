//! Hegel stateful tests of the protocol core: a hub and several nodes, a network the test
//! controls completely, environment actions, and crashes (docs/internals/testing.md).
//!
//! `protocol_invariants` checks the model's safety properties directly on the Rust state.
//! `conformance` additionally runs the Lean model in lockstep and requires every step to be
//! a legal model step leading to the same state (docs/internals/conformance.md).

#![allow(clippy::unwrap_used)]

mod support;

use std::cell::Cell;
use std::cell::RefCell;
use std::rc::Rc;

use hegel::TestCase;
use hegel::generators as gs;
use musubi_core::message::HeadKind;
use serde_json::Value;
use serde_json::json;
use support::oracle::Oracle;
use support::world::World;

struct Machine {
    world: Rc<RefCell<World>>,
    crashes: usize,
}

fn pick(tc: &TestCase, len: usize) -> usize {
    tc.draw(gs::integers::<usize>().max_value(len - 1))
}

#[hegel::state_machine]
impl Machine {
    #[rule(weight = 3)]
    fn user_op(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        let local = world.local_ops(node);
        // Usually a head, sometimes an older operation (a long-running jj command).
        let parent = local[pick(&tc, local.len())];
        let objs = tc.draw(gs::integers::<usize>().max_value(2));
        world.user_op(node, parent, objs);
    }

    #[rule(weight = 4)]
    fn node_step(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        let merge_objs = tc.draw(gs::integers::<usize>().max_value(1));
        world.node_step(node, merge_objs);
    }

    #[rule]
    fn poll(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        world.poll(node);
    }

    #[rule(weight = 4)]
    fn exchange(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        let merge_objs = tc.draw(gs::integers::<usize>().max_value(1));
        world.exchange(node, merge_objs);
    }

    #[rule(weight = 6)]
    fn deliver(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let undelivered = world.undelivered();
        tc.assume(world.net_len() > 0);
        // Usually something not yet delivered, in any order; sometimes any message ever
        // sent, so deliveries also repeat.
        let index = if !undelivered.is_empty() && tc.draw(gs::integers::<u8>().max_value(4)) > 0 {
            undelivered[pick(&tc, undelivered.len())]
        } else {
            pick(&tc, world.net_len())
        };
        world.deliver(index);
    }

    #[rule]
    fn rogue_push(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        let accepted = world.accepted_heads();
        let expected = accepted[pick(&tc, accepted.len())];
        let local = world.local_ops(node);
        let new = local[pick(&tc, local.len())];
        world.rogue_push(node, expected, new);
    }

    #[rule]
    fn lying_hub(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let candidates = world.unaccepted_ops();
        tc.assume(!candidates.is_empty());
        let node = pick(&tc, world.nodes());
        let op = candidates[pick(&tc, candidates.len())];
        // About the head the node knows, so only the reachability check stands between the
        // node and the lie; about another head; or about the operation itself, so that it
        // reaches itself and only the check that the reply is about the known head stands.
        let head = match tc.draw(gs::integers::<u8>().max_value(2)) {
            0 => world.known_head(node),
            1 => op + 1,
            _ => op,
        };
        world.rogue_ops_reply(node, head, op);
    }

    #[rule]
    fn hub_forgets(&mut self, tc: TestCase) {
        tc.assume(self.crashes < 3);
        self.crashes += 1;
        self.world.borrow_mut().hub_forget();
    }

    #[rule]
    fn remake(&mut self, tc: TestCase) {
        tc.assume(self.crashes < 3);
        self.crashes += 1;
        self.world.borrow_mut().remake();
    }

    #[rule]
    fn hub_goes_back(&mut self, tc: TestCase) {
        tc.assume(self.crashes < 3);
        let mut world = self.world.borrow_mut();
        let seq = world.hub_seq();
        tc.assume(seq > 0);
        self.crashes += 1;
        let back = tc.draw(gs::integers::<u64>().max_value(seq - 1));
        world.hub_goes_back(back);
    }

    #[rule]
    fn crash_node(&mut self, tc: TestCase) {
        tc.assume(self.crashes < 3);
        self.crashes += 1;
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        world.crash_node(node);
    }

    #[rule]
    fn crash_mid_fetch(&mut self, tc: TestCase) {
        tc.assume(self.crashes < 3);
        self.crashes += 1;
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        world.crash_before_objects(node);
    }

    #[rule]
    fn crash_hub(&mut self, tc: TestCase) {
        tc.assume(self.crashes < 3);
        self.crashes += 1;
        self.world.borrow_mut().crash_hub();
    }

    #[invariant(always_run)]
    fn safety(&mut self, _: TestCase) {
        self.world.borrow().check_invariants();
    }
}

/// Runs a case, returning its oracle, if it has one, for the next case once this one passes.
fn run(tc: TestCase, oracle: Option<Oracle>) -> Option<Oracle> {
    let nodes = tc.draw(gs::integers::<usize>().min_value(2).max_value(3));
    let world = Rc::new(RefCell::new(World::new(nodes, oracle)));
    hegel::stateful::machine(Machine {
        world: world.clone(),
        crashes: 0,
    })
    .run(tc);
    let mut world = world.borrow_mut();
    world.quiesce();
    world.check_invariants();
    if let Some(path) = std::env::var_os("MUSUBI_TRACE_STATS") {
        // Appends one line of action kinds per case, for checking what the search reaches.
        let kinds: Vec<&str> = world
            .trace
            .iter()
            .filter_map(|a| a["kind"].as_str().or_else(|| a["marker"].as_str()))
            .collect();
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap();
        std::io::Write::write_all(&mut file, format!("{}\n", kinds.join(" ")).as_bytes()).unwrap();
    }
    world.take_oracle()
}

#[hegel::test(test_cases = 300)]
fn protocol_invariants(tc: TestCase) {
    run(tc, None);
}

#[hegel::test(test_cases = conformance_cases())]
fn conformance(tc: TestCase) {
    // One oracle for each case after one that passed, reset by `World::new`: starting one
    // took longer than most cases. One whose case failed goes, in whatever state it was.
    thread_local!(static ORACLE: Cell<Option<Oracle>> = const { Cell::new(None) });
    let oracle = ORACLE.take().unwrap_or_else(Oracle::spawn);
    ORACLE.set(run(tc, Some(oracle)));
}

/// How many cases the conformance test makes: 150 on CI, where it runs as a job of its own,
/// and 50 elsewhere, where it would otherwise take most of `just test`'s time.
/// `MUSUBI_CONFORMANCE_CASES` sets it, as `just mutants` does.
fn conformance_cases() -> u64 {
    if let Some(cases) = std::env::var("MUSUBI_CONFORMANCE_CASES")
        .ok()
        .and_then(|cases| cases.parse().ok())
    {
        return cases;
    }
    if std::env::var_os("CI").is_some() {
        150
    } else {
        50
    }
}

/// A hub may drop uploads it stored but never accepted (the model's `hubForget`), such as
/// those of a push it rejected. The node must upload them again with its next push.
#[test]
fn push_after_forgotten_upload_reuploads() {
    let mut world = World::new(2, None);
    world.user_op(0, 0, 1);
    world.user_op(1, 0, 1);
    // Node 1's push wins; node 0's, stored but rejected, is then forgotten.
    world.exchange(1, 0);
    world.exchange(0, 0);
    world.hub_forget();
    world.quiesce();
    world.check_invariants();
}

/// A push from the hub's head whose closure the hub still lacks is `Incomplete`, not
/// `Rejected`: a node takes `Rejected` for a lost race, and would fetch and push the same
/// again forever, though it can't send what it lacks.
#[test]
fn an_unclosable_push_is_incomplete() {
    let mut world = World::new(1, None);
    world.user_op(0, 0, 1);
    let op = *world.local_ops(0).last().unwrap();
    world.rogue_push(0, 0, op);
    for index in world.undelivered() {
        world.deliver(index);
    }
    assert_eq!(world.head_replies(0), [HeadKind::Incomplete]);
}

/// A node fetches only operations it lacks: once the hub accepts its own push, it fetches
/// from there, and a restart, which forgets `known`, does not set it back.
#[test]
fn fetch_after_own_push_asks_only_for_newer_operations() {
    for restart in [false, true] {
        let mut world = World::new(2, None);
        world.user_op(0, 0, 1);
        world.quiesce();
        world.user_op(1, 1, 1);
        world.exchange(1, 0);
        if restart {
            world.crash_node(0);
            world.exchange(0, 0);
        }
        world.quiesce();
        assert_eq!(world.last_staged(0), Some(&[2][..]), "restart: {restart}");
    }
}

/// Catching up on a long history costs time linear in its length: each staged operation is
/// read a bounded number of times, and objects are checked in a few batches, not once per
/// operation per step.
#[test]
fn catching_up_is_linear() {
    let length = 200;
    let mut world = World::new(2, None);
    let mut head = 0;
    for _ in 0..length {
        world.user_op(1, head, 1);
        head = *world.local_ops(1).last().unwrap();
    }
    world.quiesce();
    let (reads, checks) = world.repo_work(0);
    assert!(reads <= 4 * length, "{reads} reads of staged operations");
    assert!(checks <= 4, "{checks} object checks");
}

/// A node that crashed after staging operations but before staging their objects asks for
/// the objects, and does not realize the operations without them.
#[test]
fn objects_lost_in_a_crash_are_fetched_again() {
    let mut world = World::new(2, None);
    world.user_op(0, 0, 2);
    world.quiesce();
    world.user_op(0, 1, 2);
    world.exchange(0, 0);
    // Node 1 fetches, staging the operation but not its objects, and restarts.
    world.crash_before_objects(1);
    world.poll(1);
    let sent = world.net_len();
    world.deliver(sent - 1);
    world.deliver(sent);
    // It learns the head from a notification, not from fetching again.
    world.deliver_notifications(1);
    for _ in 0..5 {
        world.exchange(1, 0);
    }
    assert!(
        world
            .trace
            .iter()
            .any(|action| action["kind"] == "fetchObjs"),
        "no GetObjects: {:#?}",
        world.trace
    );
    world.quiesce();
    world.check_invariants();
}

/// Sends `node`'s `Fetch`, has the hub answer it, and the node take the answer, as a reply
/// to no request of its own: the node has restarted already. Returns the request's index.
fn fetch(world: &mut World, node: usize) -> usize {
    world.poll(node);
    let request = world.net_len() - 1;
    world.deliver(request);
    world.deliver(request + 1);
    request
}

/// `RegressScenario.trace` (formal/Musubi/RegressScenario.lean), through the core and the
/// oracle: once the hub has gone back, two nodes merge the same heads (`duplicateMerge`).
/// Then every node converges, `rmeasure` falling as it does. The trace restarts A and B
/// before they fetch, so here they crash, rather than restart on the hub's reply
/// (`NodeCore::handle_reply`), which would record `loseKnown` after the `Fetch`.
/// Named for CI's conformance job, which has the oracle.
#[test]
fn regress_scenario_conformance() {
    let mut world = World::new(3, Some(Oracle::spawn()));
    world.user_op(0, 0, 0);
    world.user_op(2, 0, 0);
    // A pushes 1; B fetches it.
    world.exchange(0, 0);
    let b_fetch = fetch(&mut world, 1);
    world.node_step(1, 0);
    world.node_step(1, 0);
    // The hub goes back; C pushes 2, and doesn't hear back.
    world.hub_goes_back(0);
    world.node_step(2, 0);
    world.deliver(world.net_len() - 1);
    // A catches up and merges.
    world.crash_node(0);
    fetch(&mut world, 0);
    for _ in 0..3 {
        world.node_step(0, 0);
    }
    // So does B, its first `Fetch` delivered again.
    world.crash_node(1);
    world.deliver(b_fetch);
    world.deliver(world.net_len() - 1);
    for _ in 0..3 {
        world.node_step(1, 0);
    }
    let fetch_all = |node: usize| json!({"kind": "fetchAll", "node": node, "base": 0, "haves": []});
    let hub_fetch = |node: usize| json!({"kind": "hubFetch", "node": node, "base": 0, "haves": []});
    let push = |kind: &str, node: usize, op: u64| json!({"kind": kind, "node": node, "ops": [op], "objs": [], "expected": 0, "new": op});
    let learn = |node: usize, kind: &str, head: u64| json!({"kind": "learn", "node": node, "headKind": kind, "seq": 1, "head": head});
    let (recv_ops, recv_objs, realize, advance, merge, lose_known) = (
        |node: usize, op: u64| json!({"kind": "recvOps", "node": node, "ops": [op]}),
        |node: usize| json!({"kind": "recvObjs", "node": node, "objs": []}),
        |node: usize, op: u64| json!({"kind": "realize", "node": node, "opId": op}),
        |node: usize| json!({"kind": "advance", "node": node}),
        |node: usize| json!({"kind": "merge", "node": node, "parents": [1, 2], "objs": []}),
        |node: usize| json!({"kind": "loseKnown", "node": node}),
    );
    let user_op = |node: usize| json!({"kind": "userOp", "node": node, "parent": 0, "objs": []});
    let trace: Vec<Value> = vec![
        user_op(0),
        user_op(2),
        push("pushAll", 0, 1),
        push("hubPushAccept", 0, 1),
        learn(0, "accepted", 1),
        fetch_all(1),
        hub_fetch(1),
        learn(1, "head", 1),
        recv_ops(1, 1),
        recv_objs(1),
        realize(1, 1),
        advance(1),
        json!({"kind": "hubRegress", "seq": 0}),
        push("pushAll", 2, 2),
        push("hubPushAccept", 2, 2),
        lose_known(0),
        fetch_all(0),
        hub_fetch(0),
        learn(0, "head", 2),
        recv_ops(0, 2),
        recv_objs(0),
        realize(0, 2),
        advance(0),
        merge(0),
        lose_known(1),
        hub_fetch(1),
        learn(1, "head", 2),
        recv_ops(1, 2),
        recv_objs(1),
        realize(1, 2),
        advance(1),
        merge(1),
    ];
    assert_eq!(world.trace, trace);
    // The merges are operations 3 and 4.
    assert!(world.local_ops(0).contains(&3) && world.local_ops(1).contains(&4));
    world.quiesce();
    world.check_invariants();
}

/// A hive made again, empty (`HubDir::remake`), is filled again by its machines: each takes
/// the hub's reply as saying it went back, and pushes everything it has.
#[test]
fn remade_hive_conformance() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(0, 0, 1);
    world.quiesce();
    world.user_op(1, 1, 1);
    world.exchange(1, 0);
    world.user_op(0, 1, 1);
    world.remake();
    let before = world.trace.len();
    world.quiesce();
    world.check_invariants();
    // Nothing crashed: each restart is the core's, on a reply.
    for node in 0..2 {
        assert!(
            world.trace[before..].contains(&json!({"kind": "loseKnown", "node": node})),
            "node {node} did not take the hub's reply as saying it went back"
        );
    }
}
