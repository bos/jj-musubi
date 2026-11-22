//! Hegel stateful tests of the protocol core: a hub and several nodes, a network the test
//! controls completely, environment actions, and crashes (docs/internals/testing.md).
//!
//! `protocol_invariants` checks the model's safety properties directly on the Rust state.
//! `conformance` additionally runs the Lean model in lockstep and requires every step to be
//! a legal model step leading to the same state (docs/internals/conformance.md).

#![allow(clippy::unwrap_used)]

mod support;

use std::cell::RefCell;
use std::convert::Infallible;
use std::panic;
use std::panic::AssertUnwindSafe;
use std::rc::Rc;

use hegel::TestCase;
use hegel::generators as gs;
use musubi_core::hub::HubStorage;
use musubi_core::hub::Push;
use musubi_core::message::Head;
use musubi_core::message::HeadKind;
use musubi_core::message::OpEntry;
use musubi_core::message::Reply;
use serde_json::Value;
use serde_json::json;
use support::oracle::Oracle;
use support::storage::Timing;
use support::world::World;

/// Which additional actions a generated case admits. All three environments include local
/// work, arbitrary network delivery and crashes. False replies exceed the
/// Lean model's honest-hub assumptions; storage failures keep the oracle until a partial
/// effect leaves its abstraction.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Environment {
    Protocol,
    FalseReplies,
    StorageFailures,
}

struct Machine {
    world: Rc<RefCell<World>>,
    crashes: usize,
    environment: Environment,
}

/// How many crashes a case may have, the prefix's among them.
const CRASHES: usize = 3;

/// A crash, or a hub that loses what a crash can make it lose. The first is the one a
/// failure shrinks to.
#[derive(Clone, Copy, Debug)]
enum Crash {
    /// A node, keeping only its persistent state.
    Node,
    /// A node partway through taking in a fetch.
    NodeMidFetch,
    /// The hub, keeping only its persistent state.
    Hub,
    /// The hub goes back to an earlier head, as a power cut that loses the last heads it
    /// accepted would.
    HubGoesBack,
    /// The hub drops what lies outside `closure(head)`.
    HubForgets,
    /// The hive is made again, empty, as the hub does one whose store is corrupt.
    Remake,
}

/// Which head a lying hub's reply is about.
#[derive(Clone, Copy, Debug)]
enum LieAbout {
    /// The head the node knows, so only the reachability check stands between the node and
    /// the lie.
    KnownHead,
    /// Another head.
    AnotherHead,
    /// The operation itself, so that it reaches itself and only the check that the reply is
    /// about the known head stands.
    Itself,
}

/// Which kind of reply a buggy hub sends.
#[derive(Clone, Copy, Debug)]
enum FalseReply {
    Head,
    Fetched,
    Objects,
}

/// The sequence number a false reply carries: near the node's or the hub's, or the largest.
#[derive(Clone, Copy, Debug)]
enum Seq {
    At(SeqOf),
    Below(SeqOf),
    Above(SeqOf),
    Largest,
}

#[derive(Clone, Copy, Debug)]
enum SeqOf {
    Node,
    Hub,
}

impl Seq {
    /// `Largest` is listed twice so that a quarter of false replies carry `u64::MAX`, which no
    /// node's or hub's sequence number comes near.
    const ALL: [Self; 8] = [
        Self::At(SeqOf::Node),
        Self::At(SeqOf::Hub),
        Self::Below(SeqOf::Node),
        Self::Below(SeqOf::Hub),
        Self::Above(SeqOf::Node),
        Self::Above(SeqOf::Hub),
        Self::Largest,
        Self::Largest,
    ];

    fn value(self, world: &World, node: usize) -> u64 {
        let of = |of: SeqOf| match of {
            SeqOf::Node => world.known(node).0,
            SeqOf::Hub => world.hub_seq(),
        };
        match self {
            Self::At(near) => of(near),
            Self::Below(near) => of(near).saturating_sub(1),
            Self::Above(near) => of(near).saturating_add(1),
            Self::Largest => u64::MAX,
        }
    }
}

/// What a storage error interrupts.
#[derive(Clone, Copy, Debug)]
enum Interrupted {
    Poll,
    Exchange,
    Delivery,
}

/// A node of the hive.
fn node_ids(world: &World) -> impl gs::PrintableGenerator<usize> {
    gs::integers::<usize>().max_value(world.nodes() - 1)
}

#[hegel::state_machine]
impl Machine {
    #[rule(weight = 3)]
    fn user_op(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = tc.draw(node_ids(&world));
        // Usually a head, sometimes an older operation (a long-running jj command). Heads come
        // first, newest first, then the older operations, so that a failure shrinks to the
        // ordinary case: an operation on a head.
        let heads = world.heads(node);
        let older = world
            .local_ops(node)
            .into_iter()
            .filter(|op| !heads.contains(op));
        let candidates: Vec<_> = heads.iter().rev().copied().chain(older.rev()).collect();
        let parent = tc.draw(gs::sampled_from(candidates));
        let objs = tc.draw(gs::integers::<usize>().max_value(2));
        world.user_op(node, parent, objs);
    }

    #[rule(weight = 4)]
    fn node_step(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = tc.draw(node_ids(&world));
        let merge_objs = tc.draw(gs::integers::<usize>().max_value(1));
        world.node_step(node, merge_objs);
    }

    #[rule]
    fn poll(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = tc.draw(node_ids(&world));
        world.poll(node);
    }

    #[rule(weight = 4)]
    fn exchange(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = tc.draw(node_ids(&world));
        let merge_objs = tc.draw(gs::integers::<usize>().max_value(1));
        world.exchange(node, merge_objs);
    }

    /// Delivers a message, by its place among every message ever sent: usually one not yet
    /// delivered, in any order; sometimes any, so deliveries also repeat.
    #[rule(weight = 6)]
    fn deliver(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        tc.assume(world.net_len() > 0);
        let undelivered = world.undelivered();
        let p_again = if undelivered.is_empty() { 1.0 } else { 0.2 };
        let again = tc.draw(gs::weighted_booleans(p_again));
        let candidates = if again {
            (0..world.net_len()).collect()
        } else {
            undelivered
        };
        let message = tc.draw(gs::sampled_from(candidates));
        world.deliver(message);
    }

    #[rule]
    fn rogue_push(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let node = tc.draw(node_ids(&world));
        let expected = tc.draw(gs::sampled_from(world.accepted_heads()));
        let new = tc.draw(gs::sampled_from(world.local_ops(node)));
        world.rogue_push(node, expected, new);
    }

    #[rule]
    fn lying_hub(&mut self, tc: TestCase) {
        let mut world = self.world.borrow_mut();
        let candidates = world.unaccepted_ops();
        tc.assume(!candidates.is_empty());
        let node = tc.draw(node_ids(&world));
        let op = tc.draw(gs::sampled_from(candidates));
        let about = tc.draw(gs::sampled_from(vec![
            LieAbout::KnownHead,
            LieAbout::AnotherHead,
            LieAbout::Itself,
        ]));
        let head = match about {
            LieAbout::KnownHead => world.known_head(node),
            LieAbout::AnotherHead => op + 1,
            LieAbout::Itself => op,
        };
        world.rogue_ops_reply(node, head, op);
    }

    /// A buggy hub's reply ([`false_reply_to`]), to a request of the node's or out of the
    /// blue. Only in `nodes_recover_from_false_replies`, since the safety properties, and
    /// the Lean model, rest on the hub's honesty.
    #[rule]
    fn false_reply(&mut self, tc: TestCase) {
        tc.assume(self.environment == Environment::FalseReplies);
        let mut world = self.world.borrow_mut();
        let node = tc.draw(node_ids(&world));
        let reply = false_reply_to(&tc, &world, node);
        let own = tc.draw(gs::booleans());
        world.false_reply(node, reply, own);
    }

    /// Every crash, weighted as the six were when each was a rule of its own, so that the
    /// budget is checked in one place and a failure names the crash it took.
    #[rule(weight = 6)]
    fn crash(&mut self, tc: TestCase) {
        tc.assume(self.crashes < CRASHES);
        let mut world = self.world.borrow_mut();
        let mut crashes = vec![Crash::Node, Crash::NodeMidFetch, Crash::Hub];
        // Only a hub that has accepted something has an earlier head to go back to.
        if world.hub_seq() > 0 {
            crashes.push(Crash::HubGoesBack);
        }
        crashes.extend([Crash::HubForgets, Crash::Remake]);
        let crash = tc.draw(gs::sampled_from(crashes));
        self.crashes += 1;
        match crash {
            Crash::Node => {
                let node = tc.draw(node_ids(&world));
                world.crash_node(node);
            }
            Crash::NodeMidFetch => {
                let node = tc.draw(node_ids(&world));
                world.crash_before_objects(node);
            }
            Crash::Hub => world.crash_hub(),
            Crash::HubGoesBack => {
                let back = tc.draw(gs::integers::<u64>().max_value(world.hub_seq() - 1));
                world.hub_goes_back(back);
            }
            Crash::HubForgets => world.hub_forget(),
            Crash::Remake => world.remake(),
        }
    }

    /// An error in a policy step, poll, request or reply, counted from actual storage
    /// calls. Timing and countdown are Hegel draws, so both shrink and replay with the
    /// surrounding protocol sequence.
    #[rule(weight = 3)]
    fn storage_failure(&mut self, tc: TestCase) {
        tc.assume(self.environment == Environment::StorageFailures);
        let mut world = self.world.borrow_mut();
        let node = tc.draw(node_ids(&world));
        let timing = tc.draw(gs::sampled_from(vec![
            Timing::Before,
            Timing::After,
            Timing::Prefix,
        ]));
        let at = tc.draw(gs::integers::<usize>().min_value(1).max_value(24));
        let pending = world.undelivered();
        let mut actions = vec![Interrupted::Poll, Interrupted::Exchange];
        if !pending.is_empty() {
            actions.push(Interrupted::Delivery);
        }
        let interrupted = tc.draw(gs::sampled_from(actions));
        world.arm_storage(at, timing);
        match interrupted {
            Interrupted::Poll => world.poll_now(node),
            Interrupted::Exchange => world.exchange(node, 1),
            Interrupted::Delivery => {
                let message = tc.draw(gs::sampled_from(pending));
                world.deliver(message);
            }
        }
        world.stop_storage();
    }

    #[invariant(always_run)]
    fn safety(&mut self, tc: TestCase) {
        check_safety(&tc, &self.world.borrow());
    }
}

/// Checks the safety laws. A law that fails prints the world's trace, one model action per
/// line, before the failure, as the oracle's and `quiesce`'s failures carry it.
fn check_safety(tc: &TestCase, world: &World) {
    let checked = panic::catch_unwind(AssertUnwindSafe(|| world.check_invariants()));
    if let Err(failure) = checked {
        tc.note(&format!("trace:\n{}", world.compact_trace()));
        panic::resume_unwind(failure);
    }
}

/// A reply a buggy hub might send `node`: made of what it stores, about any head, with a
/// sequence number near the node's or the hub's, or the largest.
#[hegel::test_helper]
fn false_reply_to(tc: &TestCase, world: &World, node: usize) -> Reply<u64, Vec<u64>> {
    let (ops, objs) = world.hub_stored();
    let head = tc.draw(gs::sampled_from(ops.as_slice()));
    let sequence = tc.draw(gs::sampled_from(Seq::ALL.as_slice()));
    let seq = sequence.value(world, node);
    let reply = tc.draw(gs::sampled_from(vec![
        FalseReply::Head,
        FalseReply::Fetched,
        FalseReply::Objects,
    ]));
    match reply {
        FalseReply::Head => {
            let head_kind = tc.draw(gs::sampled_from(vec![
                HeadKind::Head,
                HeadKind::Accepted,
                HeadKind::Rejected,
                HeadKind::Incomplete,
                HeadKind::Notify,
            ]));
            Reply::Head {
                kind: head_kind,
                seq,
                head,
            }
        }
        FalseReply::Fetched => {
            // Half the time a chain down from the head, as a node stages only operations
            // that all reach the head; otherwise any.
            let any_ops = tc.draw(gs::booleans());
            let fetched = if any_ops {
                some_of(tc, "ops", &ops)
            } else {
                chain(tc, world, head, &ops)
            };
            Reply::Fetched {
                seq,
                head,
                ops: fetched
                    .into_iter()
                    .map(|id| OpEntry {
                        id,
                        parents: world.parents(id),
                    })
                    .collect(),
                ops_attachment: vec![],
                objects: some_of(tc, "objects", &objs),
            }
        }
        FalseReply::Objects => Reply::Objects {
            for_ops: some_of(tc, "for_ops", &ops),
            attachment: some_of(tc, "attachment", &objs),
        },
    }
}

/// Up to three of `items`, perhaps repeated, drawn as `name`.
fn some_of(tc: &TestCase, name: &str, items: &[u64]) -> Vec<u64> {
    if items.is_empty() {
        return vec![];
    }
    tc.draw_named(name, gs::vecs(gs::sampled_from(items)).max_size(3))
}

/// `head` and a few of its stored ancestors, each a parent of one before it: operations that
/// all reach `head`.
#[hegel::test_helper]
fn chain(tc: &TestCase, world: &World, head: u64, stored: &[u64]) -> Vec<u64> {
    let mut chain = vec![head];
    let steps = tc.draw(gs::integers::<usize>().max_value(3));
    for _ in 0..steps {
        let below = tc.draw(gs::sampled_from(chain.clone()));
        let parents: Vec<u64> = world
            .parents(below)
            .into_iter()
            .filter(|parent| stored.contains(parent) && !chain.contains(parent))
            .collect();
        if !parents.is_empty() {
            let parent = tc.draw(gs::sampled_from(parents));
            chain.push(parent);
        }
    }
    chain
}

/// Runs a case, returning its oracle, if it has one, for the next case once this one passes.
fn run(tc: TestCase, oracle: Option<Oracle>, environment: Environment) -> Option<Oracle> {
    run_from(tc, oracle, environment, |_, _| 0)
}

/// [`run`], from where `prefix` takes the hive first, which returns how many crashes it used.
fn run_from(
    tc: TestCase,
    oracle: Option<Oracle>,
    environment: Environment,
    prefix: impl FnOnce(&TestCase, &mut World) -> usize,
) -> Option<Oracle> {
    let nodes = tc.draw_named("nodes", gs::integers::<usize>().min_value(2).max_value(3));
    let world = Rc::new(RefCell::new(World::new(nodes, oracle)));
    let crashes = prefix(&tc, &mut world.borrow_mut());
    hegel::stateful::machine(Machine {
        world: world.clone(),
        crashes,
        environment,
    })
    .run(tc.clone());
    let mut world = world.borrow_mut();
    world.quiesce();
    check_safety(&tc, &world);
    // What the search reaches: with `HEGEL_STATISTICS=1`, Hegel reports the share of cases that
    // took each kind of action.
    for kind in world
        .trace
        .iter()
        .filter_map(|a| a["kind"].as_str().or_else(|| a["marker"].as_str()))
        .collect::<std::collections::BTreeSet<_>>()
    {
        tc.event(kind);
    }
    world.take_oracle()
}

#[hegel::test(test_cases = 300)]
fn protocol_invariants(tc: TestCase) {
    run(tc, None, Environment::Protocol);
}

/// Nodes that take false replies, as a buggy hub might send, made of what it stores, stay
/// sound: a node realizes nothing without its parents and objects, its heads are local
/// operations, an antichain, and it has only its own operations and those the hub accepted
/// or offered it. A node never misled keeps every property. And once the hub is honest
/// again, the hive converges, every operation accepted. The Lean model, which has no such
/// hub, isn't consulted.
#[hegel::test(test_cases = 300)]
fn nodes_recover_from_false_replies(tc: TestCase) {
    run(tc, None, Environment::FalseReplies);
}

// This and the other two conformance tests below make hegel.toml's default number of cases.
#[hegel::test]
fn conformance(tc: TestCase) {
    // `World::new` resets the oracle, and a case gives it back only if it passes.
    if let Some(oracle) = run(tc, Some(Oracle::kept()), Environment::Protocol) {
        oracle.keep();
    }
}

/// Storage errors are observed before recovery, then the daemon's reopen/restart is
/// applied. The oracle checks representable prefixes; a partial merged upload or received
/// bundle explicitly retires it for that case. Rust safety, retention and convergence
/// checks continue through every fault and recovery.
#[hegel::test]
fn storage_failures_preserve_operations(tc: TestCase) {
    if let Some(oracle) = run(tc, Some(Oracle::kept()), Environment::StorageFailures) {
        oracle.keep();
    }
}

#[path = "protocol/storage_boundaries.rs"]
mod storage_boundaries;

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

/// A fetch marks a newly learned head accepted before changing knowledge. Old fetches
/// can still carry data, but must not mark another head accepted.
/// This checks filtering in `handle`, before `handle_reply`'s separate rollback recovery.
#[test]
fn fetched_replies_mark_only_new_heads() {
    use musubi_core::node::{Handled, NodeCore};
    use support::model::{FakeRepo, ROOT, Univ};
    use support::storage::{Fallible, Faults};

    for (seq, same_head, learns) in [
        (1, true, false),
        (1, false, false),
        (2, true, false),
        (2, false, false),
        (3, true, true),
        (3, false, true),
    ] {
        let univ = Rc::new(RefCell::new(Univ::new()));
        let mut repo = FakeRepo::new(univ.clone(), 0);
        let (head, _) = repo.user_op(ROOT, 0);
        let mut core = NodeCore::new(ROOT);
        core.handle(
            &mut repo,
            Reply::Head {
                kind: HeadKind::Head,
                seq: 2,
                head,
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
            assert_eq!(core.known(), &Head { seq, head: named });
        } else {
            assert_eq!(handled, Handled::Ignored);
            assert_eq!(core.known(), &Head { seq: 2, head });
        }
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

/// A hub whose storage answers `Push::answer`'s checks as it is told.
struct Scripted {
    seq: u64,
    head: u32,
    closed: bool,
    descends: bool,
}

impl HubStorage for Scripted {
    type Op = u32;
    type Attachment = ();
    type Error = Infallible;

    fn head(&self) -> Head<u32> {
        Head {
            seq: self.seq,
            head: self.head,
        }
    }

    fn set_head(&mut self, seq: u64, head: &u32) -> Result<(), Infallible> {
        self.seq = seq;
        self.head = *head;
        Ok(())
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

    fn is_closed(&self, _: &u32) -> Result<bool, Infallible> {
        Ok(self.closed)
    }

    fn descends(&self, _: &u32, _: &u32) -> Result<bool, Infallible> {
        Ok(self.descends)
    }
}

/// `Push::answer` takes each of its paths as the Lean model's raw `rawPush` does, on raw ids,
/// for every answer its storage can give: the outcome, and the hub's head and sequence
/// after. The model's push may carry records and drops; this hub's never do.
#[test]
fn raw_push_answers_as_the_model() {
    let mut oracle = Oracle::spawn();
    let mut seen = std::collections::BTreeSet::new();
    for case in 0..16u8 {
        let bit = |n: u8| case & (1 << n) != 0;
        let mut storage = Scripted {
            seq: 5,
            head: 10,
            closed: bit(0),
            descends: bit(1),
        };
        let expected = if bit(2) { 10 } else { 9 };
        let new = if bit(3) { 10 } else { 11 };
        let (outcome, _) = Push {
            ops: &[],
            ops_attachment: &(),
            objects: &(),
            expected: &expected,
            new: &new,
        }
        .answer(&mut storage)
        .unwrap();
        let reply = oracle.call(&json!({
            "op": "rawPush", "seq": 5, "head": 10,
            "expected": expected, "new": new, "dropped": [],
            "recordsMatch": true, "isDropped": false,
            "isClosed": bit(0), "descends": bit(1),
        }));
        assert_eq!(reply["ok"], true, "{reply}");
        let name = format!("{outcome:?}");
        assert_eq!(reply["outcome"], name, "case {case}: {reply}");
        seen.insert(name);
        assert_eq!(
            (reply["seq"].as_u64(), reply["head"].as_u64()),
            (Some(storage.seq), Some(u64::from(storage.head))),
            "case {case}: {reply}"
        );
    }
    assert_eq!(seen.len(), 4, "every outcome: {seen:?}");
}

/// The recovery choice reads a raw graph, locality, bodies and per-operation objects, not
/// original identities or object ids in place of operation ids. Compare those reads before
/// each actual core step, and check local steps and completed metadata calls by field effects.
#[test]
fn raw_recovery_choices_and_calls_match_the_model() {
    use musubi_core::hub;
    use musubi_core::node::{LocalRepo as _, NodeCore, Step};
    use std::collections::BTreeSet;
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
    let mut seen = BTreeSet::new();
    for prefix in 0..=2u64 {
        for head_case in 0..3 {
            for bits in 0..16u8 {
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
                let mut hub = FakeHub::new(univ.clone());
                hub.ops.extend([1, 2]);
                hub.objs = univ.borrow().objs_of([1, 2]);
                hub.set_head(1, &2).unwrap();
                let mut core = NodeCore::new(ROOT);
                core.handle_reply(
                    &mut repo,
                    Reply::Head {
                        kind: HeadKind::Head,
                        seq: 1,
                        head: 2,
                    },
                )
                .unwrap();
                let raw = [0, 1, 2];
                for _ in 0..3 {
                    let before = snapshot(&repo, &core, &raw);
                    // Nothing is dropped: all that survives of the known head is itself.
                    let images: Vec<Op> = vec![2];
                    let known_local = repo.is_local(&2).unwrap();
                    let mut query = json!({
                        "op": "rawControl", "known": 2, "rawClosure": raw,
                        "images": images, "before": before,
                        "primitives": {
                            "announced": false, "dropHead": false,
                            "differ": false, "pending": false,
                            "headIsKnown": repo.heads == BTreeSet::from([2]),
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
        // A node whose known head is local fetches only for records, which no node has
        // now: the model's `poll` choice is never taken.
        [
            "advance", "fetch", "idle", "merge", "objects", "push", "realize"
        ]
        .into()
    );
}
