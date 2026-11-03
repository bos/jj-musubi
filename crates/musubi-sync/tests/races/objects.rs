//! An empty object reply must not keep a sync working from a hub that no longer exists.

use musubi_core::hub;
use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::LocalRepo as _;
use musubi_core::node::Step;
use musubi_jj::op_id::CanonicalOp;
use musubi_sync::Attachment;
use musubi_sync::OpId;

use crate::fixture::Fixture;

/// Delay notifications while using the real handler, as a request can overtake them.
fn poll(hive: &mut Fixture, node: usize) {
    let member = &hive.hive.members[node];
    let request = member.adapter.poll(&member.core).unwrap();
    let reply = hub::handle(&mut hive.hive.hub, request).unwrap().reply;
    let member = &mut hive.hive.members[node];
    member
        .core
        .handle_reply(&mut member.adapter, reply)
        .unwrap();
    member.adapter.before_sync().unwrap();
}

fn next_request(hive: &mut Fixture, node: usize) -> Request<OpId, Attachment> {
    let member = &mut hive.hive.members[node];
    let step = member.core.step(&mut member.adapter).unwrap();
    let Step::Send(mut requests) = step else {
        panic!("expected one request: {step:?}")
    };
    assert_eq!(requests.len(), 1);
    requests.pop().unwrap()
}

/// A remade hub may know neither an old requested operation nor its objects. Returning
/// success for its empty reply used to repeat GetObjects without fetching the new head.
#[test]
fn an_empty_object_reply_retries_from_the_remade_hub() {
    let mut hive = Fixture::recorded(
        &["alpha", "beta"],
        "staged-objects-before-rollback",
        |hive| {
            hive.commit(
                0,
                "common",
                "common base before the partially received operation",
            );
            hive.sync();
            let base_seq = hive.hive.hub.store().head().0;
            hive.commit(0, "alpha-only", "alpha work survives the remade hub");
            hive.hive.sync(0).unwrap();
            let member = &hive.hive.members[1];
            let request = member.adapter.poll(&member.core).unwrap();
            let Reply::Fetched {
                ops,
                ops_attachment,
                ..
            } = hub::handle(&mut hive.hive.hub, request).unwrap().reply
            else {
                unreachable!()
            };
            assert!(!ops.is_empty());
            // This is the real handler's prefix before stage_objects. A crash here retains
            // canonical bodies but has not imported their objects.
            hive.hive.members[1]
                .adapter
                .stage_ops(&ops, &ops_attachment)
                .unwrap();
            hive.reopen(1);
            hive.hive.hub_goes_back(base_seq).unwrap();
        },
    );
    let base = hive.hive.hub_head();
    let old = hive.hive.members[0].adapter.accepted_base().unwrap();
    let required: Vec<_> = hive
        .node(1)
        .required_commits(&[CanonicalOp(old.clone())])
        .unwrap()
        .into_iter()
        .collect();
    assert!(
        !hive
            .node(1)
            .object_store()
            .unwrap()
            .missing(&required)
            .unwrap()
            .is_empty()
    );

    // Beta starts against the rolled-back hub. Alpha republishes while beta's notice is
    // delayed, so beta's own stale push is rejected and teaches it the old head.
    poll(&mut hive, 1);
    assert_eq!(hive.hive.members[1].core.known().1, base);
    hive.commit(1, "beta-only", "beta work escapes the objects-only loop");
    poll(&mut hive, 0);
    let request = next_request(&mut hive, 0);
    assert!(matches!(&request, Request::Push { new, .. } if *new == old));
    let handled = hub::handle(&mut hive.hive.hub, request).unwrap();
    assert!(handled.publish.is_some());
    let member = &mut hive.hive.members[0];
    member
        .core
        .handle_reply(&mut member.adapter, handled.reply)
        .unwrap();
    let request = next_request(&mut hive, 1);
    assert!(matches!(&request, Request::Push { expected, .. } if *expected == base));
    let reply = hub::handle(&mut hive.hive.hub, request).unwrap().reply;
    assert!(matches!(&reply, Reply::Head { kind: HeadKind::Rejected, head, .. } if *head == old));
    let member = &mut hive.hive.members[1];
    member
        .core
        .handle_reply(&mut member.adapter, reply)
        .unwrap();

    let request = next_request(&mut hive, 1);
    assert!(matches!(&request, Request::GetObjects { for_ops, .. } if for_ops.contains(&old)));
    // Reconnection can complete between calls while a local step runs. No outstanding
    // request fails, and the daemon does not cancel a running sync on reconnect.
    hive.hive.remake_hub().unwrap();
    let reply = hub::handle(&mut hive.hive.hub, request).unwrap().reply;
    assert!(matches!(
        &reply,
        Reply::Objects {
            attachment: Attachment::None,
            ..
        }
    ));
    let member = &mut hive.hive.members[1];
    let err = member
        .core
        .handle_reply(&mut member.adapter, reply)
        .unwrap_err();
    assert_eq!(
        err.to_string(),
        "the hub did not supply the objects this machine needs"
    );
    assert_eq!(member.core.known().1, old);

    // The daemon's existing error recovery reopens before its next round. Beta finishes
    // that round without waiting for alpha to restore the old head or its missing objects.
    hive.reopen(1);
    hive.hive.sync(1).unwrap();
    assert_eq!(hive.hive.members[1].core.known().1, hive.hive.hub_head());
    assert!(
        !hive
            .node(1)
            .object_store()
            .unwrap()
            .missing(&required)
            .unwrap()
            .is_empty()
    );
    assert!(
        hive.visible(1)
            .iter()
            .any(|c| c.ends_with("beta work escapes the objects-only loop"))
    );
    assert!(
        hive.node(0)
            .object_store()
            .unwrap()
            .missing(&required)
            .unwrap()
            .is_empty()
    );
    hive.sync();
    hive.assert_converged();
    assert!(
        hive.visible(1)
            .iter()
            .any(|c| c.ends_with("alpha work survives the remade hub"))
    );
    // A genuinely empty transfer, or an already-satisfied request, still succeeds.
    let adapter = &mut hive.hive.members[1].adapter;
    adapter.stage_objects(&[], &Attachment::None).unwrap();
    adapter.stage_objects(&[old], &Attachment::None).unwrap();
}
