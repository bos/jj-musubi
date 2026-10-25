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
/// alpha panicking. So musubi doesn't apply beta's operation on alpha: alpha's sync fails,
/// naming alpha's rebase as the operation to revert, and jj keeps working there. Here alpha
/// makes a second such loop with P, Q and R, and goes on working on top of both rebases, so
/// the advice must pick each rebase out of later operations, and the second only once the
/// first is reverted. Following it, alpha catches up.
#[test]
fn rebases_that_form_a_loop_pause_instead_of_breaking_jj() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let alpha = hive.repo(0);
    for [a, b, c] in [["X", "Y", "Z"], ["P", "Q", "R"]] {
        alpha.jj(&["new", "root()", "-m", a]);
        alpha.jj(&["new", "-m", b]);
        alpha.jj(&["new", "root()", "-m", c]);
    }
    alpha.jj(&["new", "root()"]);
    hive.sync();
    let [x, y, z, p, q, r] = ["X", "Y", "Z", "P", "Q", "R"].map(|m| hive.commit_id(0, m));
    let last_op = |hive: &Fixture| {
        hive.repo(0)
            .jj(&["op", "log", "--no-graph", "-n1", "-T", "id.short(12)"])
    };
    hive.repo(0).jj(&["rebase", "-s", &x, "-o", &z]);
    let first = last_op(&hive);
    // Between the rebases, an operation that carries the first, but can't be what loops.
    hive.repo(0).jj(&["new", "root()", "-m", "U"]);
    hive.repo(0).jj(&["rebase", "-s", &p, "-o", &r]);
    let second = last_op(&hive);
    // Later work, some of it on what the rebases rewrote.
    let moved_y = hive.commit_id(0, "Y");
    hive.repo(0).jj(&["new", &moved_y, "-m", "W"]);
    hive.repo(0)
        .jj(&["describe", &hive.commit_id(0, "X"), "-m", "X2"]);
    hive.repo(0).jj(&["new", "root()", "-m", "V"]);
    hive.repo(1).jj(&["rebase", "-s", &z, "-o", &y]);
    hive.repo(1).jj(&["rebase", "-s", &r, "-o", &q]);
    hive.hive.sync(1).unwrap();
    for (round, expected) in [first, second].into_iter().enumerate() {
        let err = format!("{:#}", hive.hive.sync(0).unwrap_err());
        let advice = format!("`jj op revert {expected}`");
        assert!(err.contains(&advice), "expected {advice}: {err}");
        assert_eq!(hive.node(0).unmergeable_searches(), round + 1);
        // A retry with nothing new reuses the search.
        let again = format!("{:#}", hive.hive.sync(0).unwrap_err());
        assert_eq!(again, err);
        assert_eq!(hive.node(0).unmergeable_searches(), round + 1);
        hive.repo(0).jj(&["op", "revert", &expected]);
    }
    hive.sync();
    hive.assert_converged();
    hive.commit_id(1, "W");
    // As troubleshooting.md says: X, described since the rebase, is left divergent.
    let divergent = hive.repo(1).jj(&[
        "log",
        "-r",
        "divergent()",
        "--no-graph",
        "-T",
        r#"description.first_line() ++ "\n""#,
    ]);
    assert!(divergent.lines().any(|line| line == "X2"), "{divergent}");
}

/// The loop goes through work of the stuck machine's that the hive doesn't have yet: beta
/// commits on Q, rebases P onto its new working copy, and alpha moves Q onto P. Only beta's
/// rebase and its commit together loop with alpha's, so the advice must still name the
/// rebase, and reverting it must let beta catch up. Beta described P first: reverting that
/// would untie the loop too, but leave P divergent.
#[test]
fn a_loop_through_unshared_work_names_the_rebase() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let alpha = hive.repo(0);
    alpha.jj(&["new", "root()", "-m", "P"]);
    alpha.jj(&["new", "root()", "-m", "Q"]);
    alpha.jj(&["new", "root()"]);
    hive.sync();
    let [p, q] = ["P", "Q"].map(|m| hive.commit_id(1, m));
    let beta = hive.repo(1);
    beta.jj(&["describe", &p, "-m", "P2"]);
    beta.jj(&["new", &q, "-m", "c3"]);
    beta.jj(&["new"]);
    beta.jj(&["rebase", "-r", &hive.commit_id(1, "P2"), "-o", "@"]);
    let rebase = beta.jj(&["op", "log", "--no-graph", "-n1", "-T", "id.short(12)"]);
    hive.repo(0).jj(&["rebase", "-s", &q, "-o", &p]);
    hive.hive.sync(0).unwrap();
    let err = format!("{:#}", hive.hive.sync(1).unwrap_err());
    let advice = format!("`jj op revert {rebase}`");
    assert!(err.contains(&advice), "expected {advice}: {err}");
    hive.repo(1).jj(&["op", "revert", &rebase]);
    hive.sync();
    hive.assert_converged();
    let divergent = hive
        .repo(1)
        .jj(&["log", "-r", "divergent()", "--no-graph", "-T", "commit_id"]);
    assert_eq!(divergent, "");
}
