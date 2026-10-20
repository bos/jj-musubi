//! Races found by the generated end-to-end search (tests/e2e_search), reduced to
//! deterministic regressions.

use crate::fixture::Fixture;

/// A node merges its own concurrent work with an operation from the hub, and jj's merge
/// moves a bookmark: here it rebases beta's `topic` commit onto alpha's rewrite of its
/// parent. The merge operation becomes alpha's op head, so alpha's `.git` must show the
/// moved branch, as for any other operation musubi publishes as an op head.
#[test]
fn bookmark_moved_by_a_node_merge_is_exported() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.sync();
    let base = hive.commit_id(1, "base");
    hive.repo(1).jj(&["new", &base]);
    hive.commit(1, "topic", "topic");
    hive.repo(1)
        .jj(&["bookmark", "create", "topic", "-r", "@-"]);
    hive.repo(0)
        .jj(&["describe", &base, "-m", "base, reworded"]);
    hive.hive.sync(1).unwrap();
    // alpha's describe is concurrent with beta's operations: alpha's node merges them.
    hive.hive.sync(0).unwrap();
    let topic = hive.bookmarks(0)["topic@"].clone();
    let git = hive.repo(0).git(&["rev-parse", "refs/heads/topic"]);
    assert_eq!(git.trim(), topic, "alpha's git branch lags its bookmark");
    hive.sync();
    hive.assert_converged();
}
