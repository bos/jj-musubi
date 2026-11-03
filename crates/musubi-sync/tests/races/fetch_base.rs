//! Transfers after a machine no longer holds objects of its saved fetch base.

use jj_lib::object_id::ObjectId as _;
use musubi_core::message::Request;
use musubi_core::node::LocalRepo as _;
use musubi_jj::op_id::CanonicalOp;
use musubi_sync::OpId;

use crate::fixture::Fixture;

/// A restore, abandon and real jj gc can remove the raw base's commits while its surviving
/// local image remains. Both the existing daemon's next round and a reopened daemon fetch
/// the objects again, polling before between-round head discovery as the real driver does.
#[test]
fn collected_objects_of_an_abandoned_fetch_base_are_fetched_again() {
    for reopen in [false, true] {
        let mut hive = Fixture::recorded(&["alpha", "beta"], "abandoned-fetch-base", |hive| {
            hive.commit(0, "common", "common view before the removable raw base");
            hive.sync();
            let parent = hive.hive.hub_head();
            let parent_beta = hive.node(1).local_of(&CanonicalOp(parent)).unwrap();
            hive.commit(1, "only-at-base", "payload absent from the restored view");
            hive.sync();
            let base = hive.hive.hub_head();
            let base_beta = hive.node(1).local_of(&CanonicalOp(base)).unwrap();
            hive.commit(0, "after-base", "alpha retains the soon-collected payload");
            hive.hive.sync(0).unwrap();
            hive.repo(1).jj(&[
                "--ignore-working-copy",
                "op",
                "restore",
                &parent_beta.0.hex(),
            ]);
            hive.repo(1).jj(&[
                "--ignore-working-copy",
                "op",
                "abandon",
                &format!("{}..{}", parent_beta.0.hex(), base_beta.0.hex()),
            ]);
        });
        let saved =
            std::fs::read_to_string(hive.repo(1).repo_path().join("musubi/accepted_base")).unwrap();
        let base = OpId::try_from_hex(saved.trim()).unwrap();
        // Prime the positive check before the user's gc removes anything.
        assert_eq!(hive.hive.members[1].adapter.accepted_base().unwrap(), base);
        let required: Vec<_> = hive
            .node(1)
            .required_commits(&[CanonicalOp(base)])
            .unwrap()
            .into_iter()
            .collect();
        assert!(!required.is_empty());
        assert!(
            hive.node(1)
                .object_store()
                .unwrap()
                .missing(&required)
                .unwrap()
                .is_empty()
        );
        hive.repo(1)
            .jj(&["--ignore-working-copy", "util", "gc", "--expire=now"]);
        assert!(
            !hive
                .node(1)
                .object_store()
                .unwrap()
                .missing(&required)
                .unwrap()
                .is_empty()
        );
        if reopen {
            hive.reopen(1);
        }
        let mut sent_base = None;
        // This is the driver's order: poll and import first, then before_sync. Both use
        // NodeAdapter::poll, so the live daemon cannot reuse its earlier positive check.
        hive.hive
            .sync_steps(1, 0, &mut |request, reply| {
                if let Request::Fetch { base, .. } = request {
                    sent_base = Some(base.clone());
                }
                reply
            })
            .unwrap();
        assert!(
            hive.node(1)
                .object_store()
                .unwrap()
                .missing(&required)
                .unwrap()
                .is_empty()
        );
        let root = hive.node(1).canonical_store().root_operation_id().0.clone();
        assert_eq!(sent_base, Some(root), "reopen: {reopen}");
        hive.sync();
        hive.assert_converged();
    }
}
