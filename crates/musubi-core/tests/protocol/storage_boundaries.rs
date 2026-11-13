//! A fixed protocol schedule sweeps every nth call, to make boundary coverage independent
//! of random rule frequency. No real repository is made for a replay.

use super::*;
use std::collections::BTreeSet;

fn schedule(world: &mut World) {
    world.user_op(0, 0, 2);
    world.user_op(0, 1, 2);
    world.user_op(0, 2, 2);
    world.user_op(1, 0, 1);
    world.quiesce();
    world.op_abandon(0, vec![1]);
    world.quiesce();
    let head = world.hub_head();
    world.user_op(0, head, 2);
    world.exchange(0, 0);
    world.crash_before_objects(1);
    world.poll(1);
    // A failed poll may send nothing; pending notifications are still honest deliveries.
    for index in world.undelivered() {
        world.deliver(index);
    }
    for index in world.undelivered() {
        world.deliver(index);
    }
    world.deliver_notifications(1);
    for _ in 0..12 {
        world.exchange(1, 0);
    }
    world.quiesce();
    world.check_invariants();
}

/// A delayed reply can replace the records a node currently holds after the hub prunes.
/// Its next fetch must retrieve the prefix it held before; faults may interrupt each call.
fn held_schedule(world: &mut World) {
    world.user_op(0, 0, 2);
    world.user_op(0, 1, 2);
    world.quiesce();
    let sent = world.net_len();
    world.poll(1);
    if world.net_len() > sent {
        world.deliver(sent);
    }
    let held: Vec<_> = world
        .undelivered()
        .into_iter()
        .filter(|&index| index > sent)
        .collect();
    world.op_abandon(0, vec![1]);
    world.quiesce();
    world.prune();
    // The first prune can fail once; the production server retries upkeep on a later call.
    world.prune();
    world.crash_node(1);
    for index in held {
        world.deliver(index);
    }
    world.node_step(1, 0);
    world.quiesce();
    world.check_invariants();
}

#[test]
fn every_storage_boundary_recovers() {
    let mut coverage = BTreeSet::new();
    let mut counts = vec![];
    for schedule in [schedule, held_schedule] {
        for timing in [Timing::Before, Timing::After, Timing::Prefix] {
            let mut baseline = World::new(2, None);
            baseline.arm_storage(usize::MAX, timing);
            schedule(&mut baseline);
            let (calls, failed) = baseline.stop_storage();
            assert!(failed.is_none());
            counts.push(calls.len());
            for at in 1..=calls.len() {
                let mut world = World::new(2, None);
                world.arm_storage(at, timing);
                schedule(&mut world);
                let (_, failure) = world.stop_storage();
                let failure = failure.unwrap_or_else(|| panic!("{timing:?} call {at} not reached"));
                coverage.insert((failure.call, failure.timing));
            }
        }
    }
    let before = [
        "hub.records_since",
        "hub.is_dropped",
        "hub.store_ops",
        "hub.store_objects",
        "hub.ops_since",
        "hub.objects_for",
        "hub.is_closed",
        "hub.descends",
        "hub.set_head",
        "node.heads",
        "node.is_local",
        "node.is_ancestor",
        "node.merge_heads",
        "node.ops_between",
        "node.ops_attachment",
        "node.objects_attachment",
        "node.fetch_haves",
        "node.objects_request",
        "node.stage_ops",
        "node.stage_objects",
        "node.staged_parents",
        "node.objects_missing",
        "node.realize",
        "node.advance",
        "node.accepted_base",
        "node.set_accepted_base",
        "node.applied_records",
        "node.records",
        "node.pending",
        "node.records_state",
        "node.prepare_records",
        "node.adopt",
        "node.is_dropped",
        "node.write_fixup",
        "node.held",
        "node.share",
        "node.pushing",
        "node.learned",
        "hub.prune",
    ];
    let after = [
        "hub.store_ops",
        "hub.store_objects",
        "node.stage_ops",
        "node.stage_objects",
        "node.merge_heads",
        "node.advance",
        "node.set_accepted_base",
        "node.adopt",
        "node.write_fixup",
    ];
    let prefix = [
        "hub.store_ops",
        "hub.store_objects",
        "node.stage_ops",
        "node.stage_objects",
    ];
    let expected: BTreeSet<_> = before
        .into_iter()
        .map(|call| (call, Timing::Before))
        .chain(after.into_iter().map(|call| (call, Timing::After)))
        .chain(prefix.into_iter().map(|call| (call, Timing::Prefix)))
        .collect();
    assert_eq!(coverage, expected, "countdowns per timing: {counts:?}");
}

/// A repeated upload that adds nothing is a stutter, even when an import fails. Keep the
/// oracle for the error, restart and honest suffix rather than claiming an unsupported
/// transition merely because the attachment was nonempty.
#[test]
fn duplicate_upload_errors_stutter_in_the_model() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(0, 0, 1);
    world.user_op(0, 1, 1);
    // The first message is a push containing both operations and both objects.
    world.exchange(0, 0);
    for (at, timing) in [
        (3, Timing::Before),
        (1, Timing::After),
        (2, Timing::After),
        (1, Timing::Prefix),
        (2, Timing::Prefix),
    ] {
        world.arm_storage(at, timing);
        world.deliver(0);
        let (_, failure) = world.stop_storage();
        assert!(failure.is_some(), "{timing:?} call {at} not reached");
        assert!(
            world.has_oracle(),
            "unchanged duplicate upload retired the oracle"
        );
        world.check_invariants();
    }
    world.quiesce();
    world.check_invariants();
}

/// An error after staging operations restarts the process before its armed object loss.
/// The subsequent object-only reply belongs to a new receipt and must be retained.
#[test]
fn an_interrupted_fetch_does_not_discard_a_later_object_reply() {
    let mut world = World::new(2, Some(Oracle::spawn()));
    world.user_op(1, 0, 1);
    world.exchange(1, 0);
    world.crash_before_objects(0);
    world.poll(0);
    let request = world.net_len() - 1;
    world.deliver(request);
    let reply = world.net_len() - 1;
    world.arm_storage(1, Timing::After);
    world.deliver(reply);
    let (_, failure) = world.stop_storage();
    assert_eq!(failure.unwrap().call, "node.stage_ops");
    assert!(world.has_oracle());
    world.deliver_notifications(0);
    world.exchange(0, 0);
    assert!(world.has_oracle());
    world.quiesce();
    world.check_invariants();
}
