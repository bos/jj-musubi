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
use std::convert::Infallible;
use std::rc::Rc;

use hegel::TestCase;
use hegel::generators as gs;
use musubi_core::hub::CasOutcome;
use musubi_core::hub::HubStorage;
use musubi_core::hub::Push;
use musubi_core::message::HeadKind;
use musubi_core::message::OpEntry;
use musubi_core::message::RecordState;
use musubi_core::message::Reply;
use serde_json::Value;
use serde_json::json;
use support::oracle::Oracle;
use support::storage::Timing;
use support::world::World;

struct Machine {
    world: Rc<RefCell<World>>,
    crashes: usize,
    /// Whether nodes may take false replies ([`Machine::false_reply`]).
    false_replies: bool,
    storage_failures: bool,
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

    /// `jj op abandon` of some of the operations below a node's heads.
    #[rule(weight = 2)]
    fn op_abandon(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        let candidates = world.abandonable(node);
        tc.assume(!candidates.is_empty());
        let ops: Vec<u64> = candidates
            .into_iter()
            .filter(|_| tc.draw(gs::booleans()))
            .collect();
        tc.assume(!ops.is_empty());
        world.op_abandon(node, ops);
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
        let nameable = world.nameable_ops(node);
        let new = nameable[pick(&tc, nameable.len())];
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

    /// A buggy hub: any reply made of what it stores, about any head, with any sequence
    /// number near the node's or the hub's, or the largest, to a request of the node's or
    /// out of the blue. Only in `nodes_recover_from_false_replies`, since the safety
    /// properties, and the Lean model, rest on the hub's honesty.
    #[rule]
    fn false_reply(&mut self, tc: TestCase) {
        tc.assume(self.false_replies);
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        let (ops, objs) = world.hub_stored();
        // The node's own records, so that the reply is judged on its operations alone.
        let (records, records_from, pruned) = world.node_records(node);
        let some = |items: &[u64]| -> Vec<u64> {
            if items.is_empty() {
                return vec![];
            }
            (0..tc.draw(gs::integers::<usize>().max_value(3)))
                .map(|_| items[pick(&tc, items.len())])
                .collect()
        };
        let head = ops[pick(&tc, ops.len())];
        let near = tc.draw(gs::sampled_from(vec![world.known(node).0, world.hub_seq()]));
        let seq = match tc.draw(gs::integers::<u8>().max_value(3)) {
            0 => near.saturating_sub(1),
            1 => near,
            2 => near.saturating_add(1),
            _ => u64::MAX,
        };
        let reply = match tc.draw(gs::integers::<u8>().max_value(2)) {
            0 => Reply::Head {
                kind: tc.draw(gs::sampled_from(vec![
                    HeadKind::Head,
                    HeadKind::Accepted,
                    HeadKind::Rejected,
                    HeadKind::Incomplete,
                    HeadKind::Notify,
                ])),
                seq,
                head,
                records,
            },
            1 => Reply::Fetched {
                seq,
                head,
                // Usually a chain down from the head, as a node stages only operations that
                // all reach the head; sometimes any.
                ops: if tc.draw(gs::booleans()) {
                    chain(&tc, &world, head, &ops)
                } else {
                    some(&ops)
                }
                .into_iter()
                .map(|id| OpEntry {
                    id,
                    parents: world.parents(id),
                })
                .collect(),
                ops_attachment: vec![],
                objects: some(&objs),
                records,
                records_from,
                new_records: vec![],
                pruned,
            },
            _ => Reply::Objects {
                for_ops: some(&ops),
                attachment: some(&objs),
            },
        };
        let own = tc.draw(gs::booleans());
        world.false_reply(node, reply, own);
    }

    /// The hub prunes its records, once every node has said it took them all: sometimes
    /// once the hive has converged, every node having fetched last, telling the hub it took
    /// them, so that what follows meets a hub that has pruned.
    #[rule]
    fn prune(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        if tc.draw(gs::booleans()) {
            world.quiesce();
        }
        world.prune();
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

    /// An error in a policy step, poll, request or reply, counted from actual storage
    /// calls. Timing and countdown are Hegel draws, so both shrink and replay with the
    /// surrounding protocol sequence.
    #[rule(weight = 3)]
    fn storage_failure(&mut self, tc: TestCase) {
        tc.assume(self.storage_failures);
        let mut world = self.world.borrow_mut();
        let node = pick(&tc, world.nodes());
        let timing = tc.draw(gs::sampled_from(vec![
            Timing::Before,
            Timing::After,
            Timing::Prefix,
        ]));
        let at = tc.draw(gs::integers::<usize>().min_value(1).max_value(24));
        world.arm_storage(at, timing);
        match tc.draw(gs::integers::<u8>().max_value(3)) {
            0 => world.poll_now(node),
            1 => world.exchange(node, 1),
            2 => world.prune(),
            _ => {
                let pending = world.undelivered();
                if !pending.is_empty() {
                    world.deliver(pending[pick(&tc, pending.len())]);
                }
            }
        }
        world.stop_storage();
    }

    #[invariant(always_run)]
    fn safety(&mut self, _: TestCase) {
        self.world.borrow().check_invariants();
    }
}

/// `head` and a few of its stored ancestors, each a parent of one before it: operations that
/// all reach `head`.
fn chain(tc: &TestCase, world: &World, head: u64, stored: &[u64]) -> Vec<u64> {
    let mut chain = vec![head];
    for _ in 0..tc.draw(gs::integers::<usize>().max_value(3)) {
        let below = chain[pick(tc, chain.len())];
        let parents: Vec<u64> = world
            .parents(below)
            .into_iter()
            .filter(|parent| stored.contains(parent) && !chain.contains(parent))
            .collect();
        if !parents.is_empty() {
            chain.push(parents[pick(tc, parents.len())]);
        }
    }
    chain
}

/// Runs a case, returning its oracle, if it has one, for the next case once this one passes.
fn run(
    tc: TestCase,
    oracle: Option<Oracle>,
    false_replies: bool,
    storage_failures: bool,
) -> Option<Oracle> {
    run_from(tc, oracle, false_replies, storage_failures, |_, _| 0)
}

/// [`run`], from where `prefix` takes the hive first, which returns how many crashes it used.
fn run_from(
    tc: TestCase,
    oracle: Option<Oracle>,
    false_replies: bool,
    storage_failures: bool,
    prefix: impl FnOnce(&TestCase, &mut World) -> usize,
) -> Option<Oracle> {
    let nodes = tc.draw(gs::integers::<usize>().min_value(2).max_value(3));
    let world = Rc::new(RefCell::new(World::new(nodes, oracle)));
    let crashes = prefix(&tc, &mut world.borrow_mut());
    hegel::stateful::machine(Machine {
        world: world.clone(),
        crashes,
        false_replies,
        storage_failures,
    })
    .run(tc);
    let mut world = world.borrow_mut();
    world.quiesce();
    world.check_invariants();
    // Every node has said, fetching last, that it took every record: the hub prunes them, and
    // the hive still converges.
    world.prune();
    assert_eq!(world.hub_pruned(), world.hub_records().len());
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
    run(tc, None, false, false);
}

/// Nodes that take false replies, as a buggy hub might send, made of what it stores, stay
/// sound: a node realizes nothing without its parents and objects, its heads are local
/// operations, an antichain, and it has only its own operations and those the hub accepted
/// or offered it. A node never misled keeps every property. And once the hub is honest
/// again, the hive converges, every operation accepted. The Lean model, which has no such
/// hub, isn't consulted.
#[hegel::test(test_cases = 300)]
fn nodes_recover_from_false_replies(tc: TestCase) {
    run(tc, None, true, false);
}

#[hegel::test(test_cases = conformance_cases())]
fn conformance(tc: TestCase) {
    // One oracle for each case after one that passed, reset by `World::new`: starting one
    // took longer than most cases. One whose case failed goes, in whatever state it was.
    thread_local!(static ORACLE: Cell<Option<Oracle>> = const { Cell::new(None) });
    let oracle = ORACLE.take().unwrap_or_else(Oracle::spawn);
    ORACLE.set(run(tc, Some(oracle), false, false));
}

/// A head the hub accepted through what survives of the one before need not reach it. Once
/// the hub has forgotten objects only that one reached, going back there would leave a hub
/// without what its head needs. The environment explicitly chooses a remake, and every
/// node's work reaches the new one; native detection of the damaged interval is not modeled.
#[test]
fn going_back_past_an_acceptance_through_survivors_remakes_the_hub() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    for parent in 0..3 {
        world.user_op(0, parent, 1);
        world.exchange(0, 0);
    }
    world.op_abandon(0, vec![2]);
    while world.hub_records().is_empty() {
        world.exchange(0, 0);
    }
    fetch(&mut world, 1);
    world.exchange(1, 0);
    world.user_op(1, 0, 1);
    world.hub_goes_back(2);
    world.poll_now_checked(1);
    for _ in 0..16 {
        world.exchange_checked(1, 0);
    }
    // Node 1 published the drop, through what survives of 2, which its head doesn't reach.
    assert!(world.hub_seq() > 2);
    assert!(world.hub_records().iter().flatten().any(|&op| op == 2));
    world.hub_forget();
    let lost = world.objects(2);
    assert!(!lost.is_empty());
    assert!(lost.iter().all(|&obj| !world.hub_has_object(obj)));
    assert!(!world.hub_closed(2));
    world.hub_goes_back(2);
    assert!(world.remade_for_rollback);
    assert_eq!((world.hub_seq(), world.hub_head()), (0, 0));
    world.quiesce();
    world.check_invariants();
}

/// Generated sequences seldom reach a node that knows a head it dropped and lacks what
/// survives of it: one that took the hub's records before realizing that history, when the
/// hub then goes back to that head. Each case here starts there, generated, and goes on as
/// `conformance` does, so that advancing to what survives, the hub accepting a push through
/// it, and switching to prepared records are checked against the Lean model with the rest.
#[hegel::test(test_cases = conformance_cases())]
fn survivor_advance_conformance(tc: TestCase) {
    thread_local!(static ORACLE: Cell<Option<Oracle>> = const { Cell::new(None) });
    let oracle = ORACLE.take().unwrap_or_else(Oracle::spawn);
    ORACLE.set(run_from(tc, Some(oracle), false, false, dropped_known));
}

/// Node 0 makes a few operations, one on another, and drops some of those below its head;
/// node 1 takes the records without that history, perhaps with work of its own; the hub goes
/// back to one of the dropped operations; and node 1 hears of it and takes a few steps first.
/// One crash.
fn dropped_known(tc: &TestCase, world: &mut World) -> usize {
    let length = tc.draw(gs::integers::<u64>().min_value(3).max_value(5));
    for parent in 0..length {
        let objs = tc.draw(gs::integers::<usize>().max_value(1));
        world.user_op(0, parent, objs);
        world.exchange(0, 0);
    }
    let dropped: Vec<u64> = (1..length).filter(|_| tc.draw(gs::booleans())).collect();
    tc.assume(!dropped.is_empty());
    world.op_abandon(0, dropped.clone());
    while world.hub_records().is_empty() {
        world.exchange(0, 0);
    }
    fetch(world, 1);
    world.exchange(1, 0);
    for _ in 0..tc.draw(gs::integers::<usize>().max_value(2)) {
        let local = world.local_ops(1);
        let parent = local[pick(tc, local.len())];
        world.user_op(1, parent, 0);
    }
    world.hub_goes_back(dropped[pick(tc, dropped.len())]);
    // Node 1 hears of it first, and takes some steps, before anything else happens: each, as
    // `quiesce`'s, makes the measures fall.
    world.poll_now_checked(1);
    for _ in 0..tc.draw(gs::integers::<usize>().max_value(12)) {
        world.exchange_checked(1, 0);
    }
    1
}

/// Storage errors are observed before recovery, then the daemon's reopen/restart is
/// applied. The oracle checks representable prefixes; a partial merged upload or received
/// bundle explicitly retires it for that case. Rust safety, retention and convergence
/// checks continue through every fault and recovery.
#[hegel::test(test_cases = conformance_cases())]
fn storage_failures_preserve_operations(tc: TestCase) {
    thread_local!(static ORACLE: Cell<Option<Oracle>> = const { Cell::new(None) });
    let oracle = ORACLE.take().unwrap_or_else(Oracle::spawn);
    ORACLE.set(run(tc, Some(oracle), false, true));
}

#[path = "protocol/storage_boundaries.rs"]
mod storage_boundaries;

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

/// Acceptance makes progress before the acknowledgement, and an honest delayed fetch
/// still makes progress after another push moved the hub. These are the two split-exchange
/// boundaries of AsyncLiveness, not a claim that every asynchronous event lowers the rank.
#[test]
fn lost_acceptance_and_delayed_fetch_make_progress() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(0, 0, 1);
    let request = world.net_len();
    assert!(world.node_step(0, 0));
    let before = world.measure().unwrap();
    world.deliver(request);
    let accepted = world.measure().unwrap();
    assert_eq!(world.hub_head(), 1);
    assert_eq!(world.known(0), (0, 0)); // The acceptance reply is lost.
    assert!(accepted.rmeasure < before.rmeasure);

    let fetch = world.net_len();
    world.poll(1);
    let delayed = world.net_len();
    world.deliver(fetch); // The reply names head 1, but is not delivered yet.

    world.poll_now(0); // A retry learns the accepted push through a fresh fetch.
    world.user_op(0, 1, 1);
    world.exchange(0, 0);
    assert_eq!(world.hub_head(), 2);
    let before = world.measure().unwrap();
    world.deliver(delayed);
    let learned = world.measure().unwrap();
    assert_eq!(world.known(1), (1, 1));
    assert_eq!(world.hub_seq(), 2);
    assert!(learned.rmeasure < before.rmeasure);
    world.quiesce();
    world.check_invariants();
}

/// A peer can publish a surviving ancestor while dropping a later operation. A follower
/// still at that dropped head must take the records without waiting for another push.
#[test]
fn records_dropping_a_head_are_taken_when_the_hub_is_its_ancestor() {
    use std::collections::BTreeSet;

    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(0, 0, 0);
    world.quiesce();
    world.user_op(0, 1, 0);
    world.quiesce();
    assert_eq!(world.heads(1), &BTreeSet::from([2]));

    world.user_op(0, 2, 0);
    world.op_abandon(0, vec![2]);
    world.hub_goes_back(0);
    let request = world.net_len();
    world.rogue_push(0, 0, 1);
    world.deliver(request);
    assert_eq!(world.hub_head(), 1);
    assert_eq!(world.hub_records(), &[vec![2]]);

    world.poll_now(1);
    assert!(
        world.node_step(1, 0),
        "the dropped head must not block adoption"
    );
    assert_eq!(world.applied(1), &[vec![2]]);
    assert_eq!(world.heads(1), &BTreeSet::from([1]));
    assert!(!world.node_step(1, 0));
    world.check_invariants();
}

/// The trait endpoint recorded by the real-repository orphan-realization regression:
/// equal head and records, a cached restoring payload, and a pending collateral drop.
/// This is a local write-boundary test, not a full-state original-ancestry projection.
#[test]
fn cached_restoration_still_publishes_a_pending_drop_at_the_known_head() {
    use musubi_core::message::Request;
    use musubi_core::node::{NodeCore, Step};
    use support::model::{FakeRepo, ROOT, Univ};

    let univ = Rc::new(RefCell::new(Univ::new()));
    let mut repo = FakeRepo::new(univ.clone(), 0);
    let (dropped, _) = repo.user_op(ROOT, 0);
    let (head, _) = repo.user_op(ROOT, 0);
    repo.heads = [head].into();
    repo.abandon(&[dropped]);
    repo.fixup_cached = true;
    let records = univ.borrow_mut().record_state(&[]);
    let mut core = NodeCore::new(ROOT);
    let learn = |core: &mut NodeCore<u64>, repo: &mut FakeRepo| {
        core.handle_reply(
            repo,
            Reply::Head {
                kind: HeadKind::Head,
                seq: 1,
                head,
                records: records.clone(),
            },
        )
        .unwrap();
    };
    learn(&mut core, &mut repo);
    let answer = Oracle::spawn().call(&json!({"op": "retryPublication",
        "pending": [dropped], "written": true, "aligned": false, "headKnown": true}));
    assert_eq!(answer["restoring"], false);
    assert_eq!(answer["tip"], true);
    let Step::Superseded {
        fixup: Some(tip),
        push,
    } = core.step(&mut repo).unwrap()
    else {
        panic!("cached state must not strand the pending drop");
    };
    let Request::Push {
        new,
        expected,
        dropped: payload,
        ..
    } = push
    else {
        panic!("not a push");
    };
    assert_eq!((expected, new, payload), (head, tip, vec![dropped]));
    assert_ne!(tip, head);
    assert_eq!(univ.borrow().parents[tip as usize], [head]);
    // The first request is lost before delivery. Core restart keeps repository state.
    core.restart();
    learn(&mut core, &mut repo);
    let Step::Superseded { fixup: None, push } = core.step(&mut repo).unwrap() else {
        panic!("retry must reuse the existing tip");
    };
    let Request::Push { new, .. } = push else {
        panic!("not a push");
    };
    assert_eq!(new, tip);
}

/// A stale head must not change the records that gate a pending supersede. Only an
/// acceptance can supply the missing record without fetching its actual grouping.
/// This checks `handle`; `handle_reply` may restart first when its own call detects rollback.
#[test]
fn head_replies_update_records_only_for_the_known_pair() {
    use musubi_core::message::Request;
    use musubi_core::node::{Handled, NodeCore, Step};
    use support::model::{FakeRepo, ROOT, Univ};

    // Newer pairs are learned; an equal sequence about another head is an old history.
    for (seq, same_head, takes_records) in [
        (1, true, false),
        (1, false, false),
        (2, true, true),
        (2, false, false),
        (3, true, true),
        (3, false, true),
    ] {
        for kind in [HeadKind::Head, HeadKind::Notify, HeadKind::Accepted] {
            let univ = Rc::new(RefCell::new(Univ::new()));
            let mut repo = FakeRepo::new(univ.clone(), 0);
            let (dropped, _) = repo.user_op(ROOT, 0);
            let (head, _) = repo.user_op(dropped, 0);
            let empty = univ.borrow_mut().record_state(&[]);
            let next = univ.borrow_mut().record_state(&[vec![dropped]]);
            let mut core = NodeCore::new(ROOT);
            core.handle(
                &mut repo,
                Reply::Head {
                    kind: HeadKind::Head,
                    seq: 2,
                    head,
                    records: empty,
                },
            )
            .unwrap();
            repo.abandon(&[dropped]);
            let named = if same_head { head } else { ROOT };
            let handled = core
                .handle(
                    &mut repo,
                    Reply::Head {
                        kind,
                        seq,
                        head: named,
                        records: next,
                    },
                )
                .unwrap();
            if seq == 3 {
                assert_eq!(
                    handled,
                    Handled::Learned {
                        kind,
                        seq,
                        head: named
                    }
                );
                assert_eq!(core.known(), &(seq, named));
            } else {
                assert_eq!(handled, Handled::Ignored);
                assert_eq!(core.known(), &(2, head));
            }
            let step = core.step(&mut repo).unwrap();
            if !takes_records {
                // The old announcement must not block publication of the local drop.
                let Step::Superseded { push, .. } = step else {
                    panic!("old pair changed record bookkeeping: {seq}, {same_head}, {kind:?}");
                };
                assert!(matches!(push, Request::Push { dropped: d, .. } if d == [dropped]));
            } else if kind == HeadKind::Accepted {
                assert_eq!(step, Step::Adopted);
                assert_eq!(repo.applied, [vec![dropped]]);
            } else {
                let Step::Send(requests) = step else {
                    panic!("a notification cannot acknowledge our drop: {step:?}");
                };
                assert!(matches!(&requests[..], [Request::Fetch { .. }]));
                assert!(repo.applied.is_empty());
            }
        }
    }
}

/// A fetch marks a newly learned head accepted before changing knowledge. Old fetches
/// can still carry data, but must not mark another head accepted or replace current records.
/// This checks filtering in `handle`, before `handle_reply`'s separate rollback recovery.
#[test]
fn fetched_replies_mark_only_new_heads_and_take_only_current_records() {
    use musubi_core::node::{Handled, NodeCore, Step};
    use support::model::{FakeRepo, ROOT, Univ};
    use support::storage::{Fallible, Faults};

    for (seq, same_head, takes_records, learns) in [
        (1, true, false, false),
        (1, false, false, false),
        (2, true, true, false),
        (2, false, false, false),
        (3, true, true, true),
        (3, false, true, true),
    ] {
        let univ = Rc::new(RefCell::new(Univ::new()));
        let mut repo = FakeRepo::new(univ.clone(), 0);
        let (dropped, _) = repo.user_op(ROOT, 0);
        let (head, _) = repo.user_op(dropped, 0);
        let empty = univ.borrow_mut().record_state(&[]);
        let next = univ.borrow_mut().record_state(&[vec![dropped]]);
        let mut core = NodeCore::new(ROOT);
        core.handle(
            &mut repo,
            Reply::Head {
                kind: HeadKind::Head,
                seq: 2,
                head,
                records: empty.clone(),
            },
        )
        .unwrap();
        let faults = Rc::new(RefCell::new(Faults::default()));
        // Count storage effects without injecting a failure.
        faults.borrow_mut().arm(usize::MAX, Timing::Before);
        let mut repo = Fallible::new(repo, faults.clone());
        let named = if same_head { head } else { ROOT };
        let handled = core
            .handle(
                &mut repo,
                Reply::Fetched {
                    seq,
                    head: named,
                    ops: vec![],
                    ops_attachment: vec![],
                    objects: vec![],
                    records: next,
                    records_from: 0,
                    new_records: vec![vec![dropped]],
                    pruned: empty,
                },
            )
            .unwrap();
        let marks = faults
            .borrow()
            .calls
            .iter()
            .filter(|&&call| call == "node.learned")
            .count();
        assert_eq!(marks, usize::from(learns), "{seq}, {same_head}");
        if learns {
            assert_eq!(
                handled,
                Handled::Learned {
                    kind: HeadKind::Head,
                    seq,
                    head: named
                }
            );
            assert_eq!(core.known(), &(seq, named));
        } else {
            assert_eq!(handled, Handled::Ignored);
            assert_eq!(core.known(), &(2, head));
        }
        let step = core.step(&mut repo).unwrap();
        assert_eq!(
            step,
            if takes_records {
                Step::Adopted
            } else {
                Step::Idle
            },
            "{seq}, {same_head}"
        );
        assert_eq!(
            repo.applied,
            if takes_records {
                vec![vec![dropped]]
            } else {
                vec![]
            }
        );
    }
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
    let send_d = |node: usize| json!({"kind": "sendD", "node": node});
    let send_sup = |node: usize, new: u64| json!({"kind": "sendSup", "node": node, "new": new});
    let push = |kind: &str, node: usize, op: u64| json!({"kind": kind, "node": node, "ops": [op], "objs": [], "expected": 0, "new": op});
    let accept = |node: usize, op: u64| json!({"kind": "hubSupAccept", "node": node, "ops": [op], "objs": [], "expected": 0, "new": op, "applied": [], "dropped": []});
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
        send_sup(0, 1),
        accept(0, 1),
        send_d(0),
        learn(0, "accepted", 1),
        fetch_all(1),
        hub_fetch(1),
        send_d(1),
        learn(1, "head", 1),
        recv_ops(1, 1),
        recv_objs(1),
        realize(1, 1),
        advance(1),
        json!({"kind": "hubRegress", "seq": 0}),
        push("pushAll", 2, 2),
        send_sup(2, 2),
        accept(2, 2),
        send_d(2),
        lose_known(0),
        fetch_all(0),
        hub_fetch(0),
        send_d(0),
        learn(0, "head", 2),
        recv_ops(0, 2),
        recv_objs(0),
        realize(0, 2),
        advance(0),
        merge(0),
        lose_known(1),
        hub_fetch(1),
        send_d(1),
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

/// A node abandons operations the hub has, and publishes the abandon with a fix-up operation;
/// the other node takes the hub's record. Through the core and the oracle.
#[test]
fn supersede_conformance() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(0, 0, 1);
    world.user_op(0, 1, 1);
    world.quiesce();
    world.op_abandon(0, vec![1]);
    world.quiesce();
    world.check_invariants();
    assert_eq!(world.hub_records(), [vec![1]]);
    assert!(
        world
            .trace
            .iter()
            .any(|action| action["kind"] == "adopt" && action["node"] == 1),
        "node 1 did not take the record: {:#?}",
        world.trace
    );
}

/// Two nodes abandon operations concurrently: whichever supersede the hub takes first, the
/// other is pushed again after it, and the hub ends up with both records.
#[test]
fn concurrent_supersedes_conformance() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(0, 0, 0);
    world.user_op(0, 1, 0);
    world.user_op(0, 2, 0);
    world.quiesce();
    world.op_abandon(0, vec![1]);
    world.op_abandon(1, vec![2]);
    world.quiesce();
    world.check_invariants();
    assert_eq!(world.hub_records().len(), 2);
}

/// A remake lets a machine republish two drops as one record. Another machine still has
/// the same dropped union in two records: adoption changes only its ordered records.
#[test]
fn regrouped_records_conformance() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(0, 0, 0);
    world.user_op(0, 1, 0);
    world.user_op(0, 2, 0);
    world.quiesce();
    world.op_abandon(0, vec![1]);
    world.quiesce();
    world.op_abandon(0, vec![2]);
    world.quiesce();
    assert_eq!(world.hub_records(), [vec![1], vec![2]]);

    world.remake();
    // Only machine 0 talks to the remade hub, and republishes both drops at once.
    world.poll_now(0);
    for _ in 0..20 {
        world.exchange(0, 0);
        if world.hub_records() == [vec![1, 2]] {
            break;
        }
    }
    assert_eq!(world.hub_records(), [vec![1, 2]]);
    assert_eq!(world.dropped(1), world.dropped(0));
    world.poll_now(1);
    let before = world.measure().unwrap().smeasure;
    let drops = world.dropped(1).clone();
    let trace = world.trace.len();
    world.node_step(1, 0);
    assert_eq!(world.trace[trace]["kind"], "adopt");
    assert_eq!(world.dropped(1), &drops);
    let after = world.measure().unwrap().smeasure;
    assert_eq!(&before[..8], &after[..8]);
    assert_eq!(after[8] + 1, before[8]);
    world.quiesce();
    world.check_invariants();
}

/// A push whose node hasn't taken the hub's latest record is refused, even from the hub's
/// head: its ids aren't the hub's. The node never sends one knowingly, so the test answers
/// one itself.
#[test]
fn a_push_without_the_hubs_records_is_refused() {
    let mut world = World::new(1, None);
    world.user_op(0, 0, 0);
    world.user_op(0, 1, 0);
    world.quiesce();
    world.op_abandon(0, vec![1]);
    world.quiesce();
    assert_eq!(world.hub_records(), [vec![1]]);
    let head = world.hub_head();
    world.user_op(0, head, 0);
    let new = *world.local_ops(0).last().unwrap();
    assert_eq!(world.answer_push(head, new, &[], &[]), CasOutcome::Refused);
    assert_eq!(world.hub_head(), head);
}

/// A hub whose storage answers `Push::answer`'s checks as it is told. Its records are a
/// `RecordState`, compared whole by the hub. What an accept does to them is the backend's,
/// and not modelled here: `set_head` moves only the sequence and the head.
struct Scripted {
    seq: u64,
    head: u32,
    records: RecordState,
    dropped: bool,
    closed: bool,
    descends: bool,
}

fn record_state(count: u64, digest: u8) -> RecordState {
    RecordState {
        count,
        digest: vec![digest],
    }
}

impl HubStorage for Scripted {
    type Op = u32;
    type Attachment = ();
    type Error = Infallible;

    fn head(&self) -> (u64, u32) {
        (self.seq, self.head)
    }

    fn set_head(&mut self, seq: u64, head: &u32, _: &[u32]) -> Result<(), Infallible> {
        self.seq = seq;
        self.head = *head;
        Ok(())
    }

    fn records(&self) -> RecordState {
        self.records.clone()
    }

    fn pruned(&self) -> RecordState {
        record_state(0, 0)
    }

    fn records_since(&self, _: &RecordState) -> Result<(u64, Vec<Vec<u32>>), Infallible> {
        unreachable!("a push asks for no records")
    }

    fn is_dropped(&self, _: &u32, _: &[u32]) -> Result<bool, Infallible> {
        Ok(self.dropped)
    }

    fn report(&mut self, _: &str, _: &RecordState) {}

    fn reported(&self, _: &str) -> Option<RecordState> {
        None
    }

    fn prune(&mut self, _: u64) -> Result<(), Infallible> {
        unreachable!("a push prunes nothing")
    }

    fn store_ops(&mut self, _: &[u32], _: &()) -> Result<(), Infallible> {
        Ok(())
    }

    fn store_objects(&mut self, _: &[u32], _: &()) -> Result<(), Infallible> {
        Ok(())
    }

    fn ops_since(&self, _: &u32, _: &u32) -> Result<(Vec<OpEntry<u32>>, ()), Infallible> {
        unreachable!("a push sends no operations back")
    }

    fn objects_for(&self, _: &[u32], _: &u32, _: &()) -> Result<(), Infallible> {
        unreachable!("a push sends no objects back")
    }

    fn is_closed(&self, _: &u32, _: &[u32]) -> Result<bool, Infallible> {
        Ok(self.closed)
    }

    fn descends(&self, _: &u32, _: &u32, _: &[u32]) -> Result<bool, Infallible> {
        Ok(self.descends)
    }
}

/// `Push::answer` takes each of its paths as the Lean model's raw `rawPush` does, on raw ids,
/// for every answer its storage can give and for records the hub's, or another count or
/// digest of them: the outcome, and the hub's head and sequence after. Whether the records
/// match is the hub's whole comparison of them, never one of counts.
#[test]
fn raw_push_answers_as_the_model() {
    let mut oracle = Oracle::spawn();
    let hub = record_state(2, 0xaa);
    let offered = [
        hub.clone(),
        record_state(2, 0xbb),
        record_state(3, 0xaa),
        record_state(3, 0xbb),
    ];
    let mut seen = std::collections::BTreeSet::new();
    for records in &offered {
        for case in 0..64u8 {
            let bit = |n: u8| case & (1 << n) != 0;
            let mut storage = Scripted {
                seq: 5,
                head: 10,
                records: hub.clone(),
                dropped: bit(0),
                closed: bit(1),
                descends: bit(2),
            };
            let expected = if bit(3) { 10 } else { 9 };
            let new = if bit(4) { 10 } else { 11 };
            let dropped: &[u32] = if bit(5) { &[7] } else { &[] };
            let (outcome, _) = Push {
                machine: "n",
                ops: &[],
                ops_attachment: &(),
                objects: &(),
                expected: &expected,
                new: &new,
                records,
                dropped,
            }
            .answer(&mut storage)
            .unwrap();
            let reply = oracle.call(&json!({
                "op": "rawPush", "seq": 5, "head": 10,
                "expected": expected, "new": new, "dropped": dropped,
                "recordsMatch": *records == hub, "isDropped": bit(0),
                "isClosed": bit(1), "descends": bit(2),
            }));
            assert_eq!(reply["ok"], true, "{reply}");
            let name = format!("{outcome:?}");
            assert_eq!(reply["outcome"], name, "{records:?}, case {case}: {reply}");
            seen.insert(name);
            assert_eq!(
                (reply["seq"].as_u64(), reply["head"].as_u64()),
                (Some(storage.seq), Some(u64::from(storage.head))),
                "{records:?}, case {case}: {reply}"
            );
        }
    }
    assert_eq!(seen.len(), 5, "every outcome: {seen:?}");
}

/// The recovery choice reads a raw graph, locality, bodies and per-operation objects, not
/// original identities or object ids in place of operation ids. Compare those reads before
/// each actual core step, and check local steps and completed metadata calls by field effects.
#[test]
fn raw_recovery_choices_and_calls_match_the_model() {
    use musubi_core::hub;
    use musubi_core::node::{LocalRepo as _, NodeCore, Step};
    use support::model::{FakeHub, FakeRepo, Op, ROOT, SharedUniv, Univ};

    fn snapshot(repo: &FakeRepo, core: &NodeCore<Op>, raw: &[Op]) -> Value {
        let univ = repo.univ.borrow();
        let objects: Vec<Op> = raw
            .iter()
            .copied()
            .filter(|op| {
                // An absent body cannot establish that all of its objects are available.
                (repo.lops.contains(op) || repo.sops.contains_key(op))
                    && univ.objs[*op as usize]
                        .iter()
                        .all(|o| repo.lobj.contains(o) || repo.sobj.contains(o))
            })
            .collect();
        json!({
            "local": repo.lops, "heads": repo.heads,
            "plan": core.planned().copied().collect::<Vec<_>>(),
            "staged": repo.sops.keys().chain(repo.lops.iter()).copied().collect::<Vec<_>>(),
            "objects": objects,
        })
    }

    let mut oracle = Oracle::spawn();
    let mut seen = std::collections::BTreeSet::new();
    for prefix in 0..=2u64 {
        for head_case in 0..3 {
            for bits in 0..64u8 {
                let bit = |n: u8| bits & (1 << n) != 0;
                let univ = SharedUniv::new(RefCell::new(Univ::new()));
                for parent in 0..2 {
                    let mut u = univ.borrow_mut();
                    // Several objects per operation distinguish operation and object ids.
                    let objects = u.fresh_objs(3);
                    u.create(0, vec![parent], objects);
                }
                let mut repo = FakeRepo::new(univ.clone(), 1);
                for op in 1..=prefix {
                    repo.lops.insert(op);
                    repo.lobj
                        .extend(univ.borrow().objs[op as usize].iter().copied());
                }
                repo.heads = [prefix].into();
                if head_case > 0 {
                    repo.user_op(prefix, 0);
                }
                if head_case == 2 {
                    repo.user_op(ROOT, 0);
                }
                for op in 1..=2u64 {
                    if bit((op - 1) as u8) {
                        repo.sops.insert(op, vec![op - 1]);
                    }
                    if bit((op + 1) as u8) {
                        repo.sobj
                            .extend(univ.borrow().objs[op as usize].iter().copied());
                    }
                }
                if bit(4) {
                    if prefix == 0 || repo.heads.contains(&1) {
                        continue;
                    }
                    repo.abandon(&[1]);
                }
                let mut hub = FakeHub::new(univ.clone());
                hub.ops.extend([1, 2]);
                hub.objs = univ.borrow().objs_of([1, 2]);
                hub.set_head(1, &2, &[]).unwrap();
                let mut heard = hub.records();
                if bit(5) {
                    heard.digest.push(0xff);
                }
                let mut core = NodeCore::new(ROOT);
                // A Head, not Accepted, stores exactly this heard record state and announces
                // no records. There are no concurrent commands or receipts in these cases.
                core.handle_reply(
                    &mut repo,
                    Reply::Head {
                        kind: HeadKind::Head,
                        seq: 1,
                        head: 2,
                        records: heard.clone(),
                    },
                )
                .unwrap();
                let raw = [0, 1, 2];
                for _ in 0..3 {
                    let before = snapshot(&repo, &core, &raw);
                    let images: Vec<Op> =
                        univ.borrow().images(&repo.dropped, 2).into_iter().collect();
                    let pending = !repo.pending().unwrap().is_empty();
                    let known_local = repo.is_local(&2).unwrap();
                    let mut query = json!({
                        "op": "rawControl", "known": 2, "rawClosure": raw,
                        "images": images, "before": before,
                        "primitives": {
                            "announced": false, "dropHead": false,
                            "differ": heard != repo.records().unwrap(), "pending": pending,
                            "headIsKnown": repo.heads.len() == 1 && repo.heads.contains(&2),
                            // FakeRepo writes a fresh fix-up or uses a distinct head; no
                            // concurrent command can make it decline the marker here.
                            "newIsKnown": false,
                        },
                    });
                    let step = core.step(&mut repo).unwrap();
                    let mut stop = false;
                    let choice = match step {
                        Step::Idle => {
                            stop = true;
                            "idle"
                        }
                        Step::Merged => "merge",
                        Step::Realized(op) => {
                            query["opId"] = json!(op);
                            "realize"
                        }
                        Step::Advanced(_) => "advance",
                        Step::Superseded { .. } => {
                            stop = true;
                            "push"
                        }
                        Step::Send(requests) => {
                            stop = true;
                            if requests
                                .iter()
                                .any(|r| matches!(r, musubi_core::message::Request::Push { .. }))
                            {
                                "push"
                            } else {
                                let fetch = requests.iter().any(|r| {
                                    matches!(r, musubi_core::message::Request::Fetch { .. })
                                });
                                for request in requests {
                                    let reply = hub::handle(&mut hub, request).unwrap().reply;
                                    core.handle_reply(&mut repo, reply).unwrap();
                                }
                                if fetch && known_local {
                                    "poll"
                                } else if fetch {
                                    "fetch"
                                } else {
                                    "objects"
                                }
                            }
                        }
                        Step::Adopted => panic!("the setup announced no records"),
                    };
                    if ["merge", "realize", "advance", "fetch", "objects"].contains(&choice) {
                        query["kind"] = json!(choice);
                        query["after"] = snapshot(&repo, &core, &raw);
                    }
                    query["parents"] = json!(univ.borrow().parents);
                    let reply = oracle.call(&query);
                    assert_eq!(reply["ok"], true, "{reply}");
                    assert_eq!(
                        reply["choice"], choice,
                        "prefix {prefix}, heads {head_case}, bits {bits}: {query}: {reply}"
                    );
                    if query.get("kind").is_some() {
                        assert_eq!(reply["matches"], true, "{query}: {reply}");
                    }
                    seen.insert(choice);
                    if stop {
                        break;
                    }
                }
            }
        }
    }
    assert_eq!(
        seen,
        [
            "advance", "fetch", "idle", "merge", "objects", "poll", "push", "realize"
        ]
        .into()
    );
}

/// The hub prunes its records once every node has said it took them all, and not before: then
/// it no longer refuses a push by a pruned id, but still by its records. More abandons after
/// it are taken, and pruned too. Through the core and the oracle.
#[test]
fn prune_conformance() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(0, 0, 0);
    world.user_op(0, 1, 0);
    world.quiesce();
    world.op_abandon(0, vec![1]);
    // Node 0 publishes the abandon; node 1, which hasn't taken it, holds pruning back.
    while world.hub_records().is_empty() {
        world.exchange(0, 0);
    }
    world.poll_now(0);
    world.prune();
    assert_eq!(world.hub_pruned(), 0);
    world.quiesce();
    world.prune();
    assert_eq!(world.hub_pruned(), 1);
    let head = world.hub_head();
    // Not refused by its id, which the hub no longer knows, but by its records.
    assert_eq!(
        world.answer_push(head, 1, &[vec![1]], &[]),
        CasOutcome::Rejected
    );
    assert_eq!(world.answer_push(head, 1, &[], &[]), CasOutcome::Refused);
    world.user_op(1, head, 0);
    let new = *world.local_ops(1).last().unwrap();
    world.op_abandon(1, vec![head]);
    world.quiesce();
    world.check_invariants();
    assert_eq!(world.hub_records().len(), 2, "{:#?}", world.trace);
    world.prune();
    assert_eq!(world.hub_pruned(), 2);
    assert!(world.local_ops(0).contains(&new));
    world.quiesce();
    world.check_invariants();
}

/// Node 1 asks the hub for its records, and the reply is held up; meanwhile node 0 abandons an
/// operation, both nodes take the record, and the hub prunes it.
fn prune_after_held_reply(world: &mut World, remade: bool) -> Vec<usize> {
    world.user_op(0, 0, 0);
    world.user_op(0, 1, 0);
    world.quiesce();
    if remade {
        world.op_abandon(0, vec![1]);
        world.quiesce();
        // The hive is made again: node 0 publishes the abandon again, after the reply.
        world.remake();
    }
    let sent = world.net_len();
    world.poll(1);
    world.deliver(sent);
    let held: Vec<usize> = world
        .undelivered()
        .into_iter()
        .filter(|&index| index > sent)
        .collect();
    if !remade {
        world.op_abandon(0, vec![1]);
    }
    world.quiesce();
    world.prune();
    assert_eq!(world.hub_pruned(), 1);
    held
}

/// A node that restarts takes the reply held up since before the hub pruned its record, which
/// tells it of no records, as about the head it knows: it takes none. Having held the record
/// the hub pruned, it then takes the hub's records from there, though the hub knows that
/// record only by its count and digest. Without that, the node stops for good, as
/// lacking records the hub pruned. With the hive made again in between, the reply comes from
/// the hub made again, at its root, before the node took the records again: the node takes it
/// as after a restart, but the hub it prunes on went back and took them again. Through the core
/// and the oracle.
#[test]
fn a_node_takes_records_from_a_pruned_prefix_it_held() {
    for remade in [false, true] {
        let mut world = World::new(2, Some(Oracle::spawn()));
        let held = prune_after_held_reply(&mut world, remade);
        world.crash_node(1);
        for index in held {
            world.deliver(index);
        }
        world.node_step(1, 0);
        assert!(world.applied(1).is_empty(), "remade: {remade}");
        world.quiesce();
        world.check_invariants();
        assert_eq!(world.applied(1), [vec![1]], "remade: {remade}");
    }
}

/// A push with the hub's records is refused if its new head is one the hub dropped, or one
/// the push itself drops. A node never names an operation a record it took drops, so neither
/// conformance nor the model reaches the first; the hub checks it anyway, while it remembers
/// dropping the operation.
#[test]
fn a_push_to_a_dropped_head_is_refused() {
    let mut world = World::new(1, None);
    world.user_op(0, 0, 0);
    world.user_op(0, 1, 0);
    world.quiesce();
    world.op_abandon(0, vec![1]);
    world.quiesce();
    assert_eq!(world.hub_records(), [vec![1]]);
    let head = world.hub_head();
    let records = [vec![1]];
    assert_eq!(
        world.answer_push(head, 1, &records, &[]),
        CasOutcome::Refused
    );
    world.user_op(0, head, 0);
    let new = *world.local_ops(0).last().unwrap();
    assert_eq!(
        world.answer_push(head, new, &records, &[new]),
        CasOutcome::Refused
    );
    assert_eq!(world.hub_head(), head);
}

/// A node never advances to a head it dropped, but to what survives of it: here one it took
/// from the hub's records, which the hub then lost, going back to that head. It realizes what
/// survives, merges it with any work of its own, and publishes the drop itself, rather than
/// waiting for the node that dropped it, which here never syncs again before quiescing.
#[test]
fn a_node_advances_to_what_survives_of_a_head_it_dropped() {
    for own_work in [true, false] {
        let mut world = World::new(2, Some(Oracle::spawn()));
        for parent in 0..3 {
            world.user_op(0, parent, 0);
            world.exchange(0, 0);
        }
        // Node 0 drops 2, between 1 and its head 3, and publishes the drop.
        world.op_abandon(0, vec![2]);
        while world.hub_records().is_empty() {
            world.exchange(0, 0);
        }
        // Node 1 fetches the hub's head and records, and takes them: its only head is the root.
        fetch(&mut world, 1);
        world.exchange(1, 0);
        assert!(world.dropped(1).contains(&2));
        if own_work {
            world.user_op(1, 0, 0);
        }
        world.hub_goes_back(2);
        // Node 1 hears that the hub went back to 2, and goes on from 1, which survives it,
        // each step making the measures fall, as in `quiesce`.
        world.poll_now_checked(1);
        for _ in 0..16 {
            world.exchange_checked(1, 0);
        }
        assert!(!world.heads(1).contains(&2), "own work: {own_work}");
        assert_ne!(world.hub_head(), 2, "own work: {own_work}");
        assert!(
            world.hub_records().iter().flatten().any(|&op| op == 2),
            "own work: {own_work}"
        );
        world.check_invariants();
        world.quiesce();
        world.check_invariants();
    }
}
