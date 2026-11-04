//! Narrow native laws at the protocol's `LocalRepo` boundary.

use musubi_core::node::LocalRepo as _;
use musubi_jj::node::NodeRepo;
use musubi_sync::node::NodeAdapter;
use musubi_testutil::TestEnv;

/// A base precedes work made after it, never the other way around. Test the real
/// adapter directly: a fake returning true for every ancestry query can still converge in
/// some end-to-end schedules, so convergence alone is not an ancestry oracle.
#[test]
fn ancestry_distinguishes_a_base_from_its_descendant() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    node.create_join_operation("musubi: alpha joins").unwrap();
    let mut adapter = NodeAdapter::new(node).unwrap();
    let heads = adapter.heads().unwrap();
    assert_eq!(heads.len(), 1);
    let base = heads[0].clone();
    repo.write_file("later", "work after the base");
    repo.jj(&["commit", "-m", "work after the base"]);
    let heads = adapter.heads().unwrap();
    assert_eq!(heads.len(), 1);
    let later = &heads[0];
    assert_ne!(later, &base);
    for (ancestor, descendant, expected) in [
        (&base, &base, true),
        (later, later, true),
        (&base, later, true),
        (later, &base, false),
    ] {
        assert_eq!(
            adapter.is_ancestor(ancestor, descendant).unwrap(),
            expected,
            "{ancestor:?} precedes {descendant:?}"
        );
    }
}

/// Abandoning the history through another copy's latest work must keep that copy present,
/// so the hub waits for it to take the drop record before pruning it.
#[test]
fn pruning_waits_for_a_copy_whose_work_was_abandoned() {
    use crate::fixture::Fixture;

    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "start", "start");
    hive.sync();
    hive.commit(0, "second", "second");
    let accepted = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    hive.sync();
    let alpha = hive.machine_key(0);
    let beta = hive.machine_key(1);
    hive.repo(0).jj(&["describe", "-m", "third"]);
    let fresh = hive.env.clock().now();
    hive.repo(0)
        .jj(&["op", "abandon", &format!("..{accepted}")]);
    for _ in 0..3 {
        hive.hive.sync(0).unwrap();
    }
    assert!(hive.hive.hub.store().presence().unwrap().is_present(&beta));
    assert_eq!(hive.hive.hub.store().pruned(), 0);
    let alpha_work = hive
        .node(0)
        .activity()
        .unwrap()
        .into_iter()
        .find(|copy| copy.key == alpha)
        .unwrap()
        .last_work;
    assert_eq!(
        alpha_work, fresh,
        "repair must retain the surviving unpublished work's time"
    );
    hive.hive.sync(1).unwrap();
    hive.sync();
    hive.assert_converged();
}
