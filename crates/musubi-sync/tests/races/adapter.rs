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
