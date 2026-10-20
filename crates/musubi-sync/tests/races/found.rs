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

/// Two machines rebase concurrently so that their rebases form a loop: alpha moves X, and
/// Y on it, onto Z, while beta moves Z onto Y. jj 0.46 panics merging such operations
/// ("graph has cycle"), and again on every load, which would leave every `jj` command on
/// alpha panicking. So musubi doesn't apply beta's operation on alpha: alpha's sync fails
/// with a hint, jj keeps working there, and once alpha reverts its rebase, it catches up.
#[test]
fn rebases_that_form_a_loop_pause_instead_of_breaking_jj() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let alpha = hive.repo(0);
    alpha.jj(&["new", "root()", "-m", "X"]);
    alpha.jj(&["new", "-m", "Y"]);
    alpha.jj(&["new", "root()", "-m", "Z"]);
    alpha.jj(&["new", "root()"]);
    hive.sync();
    let (x, y, z) = (
        hive.commit_id(0, "X"),
        hive.commit_id(0, "Y"),
        hive.commit_id(0, "Z"),
    );
    hive.repo(0).jj(&["rebase", "-s", &x, "-o", &z]);
    let rebase = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    hive.repo(1).jj(&["rebase", "-s", &z, "-o", &y]);
    hive.hive.sync(1).unwrap();
    let err = hive.hive.sync(0).unwrap_err();
    assert!(
        format!("{err:#}").contains("jj cannot merge this machine's operations"),
        "{err:#}"
    );
    hive.repo(0).jj(&["status"]);
    hive.repo(0).jj(&["op", "revert", &rebase]);
    hive.sync();
    hive.assert_converged();
}
