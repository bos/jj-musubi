//! Hegel stateful tests of the protocol core: a hub and several nodes, a network the test
//! controls completely, environment actions, and crashes (docs/testing.md).
//!
//! `protocol_invariants` checks the model's safety properties directly on the Rust state.
//! `conformance` additionally runs the Lean model in lockstep and requires every step to be
//! a legal model step leading to the same state (docs/conformance.md).

#![allow(clippy::unwrap_used)]

mod support;

use std::cell::RefCell;
use std::rc::Rc;

use hegel::TestCase;
use hegel::generators as gs;
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
        // Usually about the head the node asked for, so only the reachability check stands
        // between the node and the lie.
        let head = if tc.draw(gs::booleans()) {
            world.known_head(node)
        } else {
            op + 1
        };
        tc.assume(head != op);
        world.rogue_ops_reply(node, head, op);
    }

    #[rule]
    fn hub_forgets(&mut self, tc: TestCase) {
        tc.assume(self.crashes < 3);
        let mut world = self.world.borrow_mut();
        tc.assume(!world.has_oracle());
        self.crashes += 1;
        world.hub_forget();
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

fn run(tc: TestCase, oracle: Option<Oracle>) {
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
}

#[hegel::test(test_cases = 300)]
fn protocol_invariants(tc: TestCase) {
    run(tc, None);
}

#[hegel::test(test_cases = 150)]
fn conformance(tc: TestCase) {
    run(tc, Some(Oracle::spawn()));
}

/// A hub may drop uploads it acknowledged but never accepted (the model's `hubForget`). A
/// node whose push is then rejected must upload again rather than retry the push forever.
#[test]
fn push_after_forgotten_upload_reuploads() {
    let mut world = World::new(2, None);
    world.user_op(0, 0, 1);
    // Send the upload and deliver it with both acknowledgements, leaving the push unsent.
    world.node_step(0, 0);
    for index in world.undelivered() {
        world.deliver(index);
    }
    for index in world.undelivered() {
        world.deliver(index);
    }
    world.hub_forget();
    world.quiesce();
    world.check_invariants();
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
        // Node 1 uploads, then pushes.
        world.exchange(1, 0);
        world.exchange(1, 0);
        if restart {
            world.crash_node(0);
            world.exchange(0, 0);
        }
        world.quiesce();
        assert_eq!(world.last_fetch(0), Some(&[2][..]), "restart: {restart}");
    }
}
