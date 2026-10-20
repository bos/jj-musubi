//! Commits rewritten concurrently on different machines.

use std::collections::BTreeSet;

use crate::fixture::Fixture;

fn divergent_changes(hive: &Fixture, index: usize) -> BTreeSet<String> {
    let template = "change_id ++ \"\\n\"";
    let out = hive
        .repo(index)
        .jj(&["log", "--no-graph", "-r", "divergent()", "-T", template]);
    out.lines().map(str::to_owned).collect()
}

/// Both machines reword the same commit. That is a genuine divergence, and jj shows it as
/// a divergent change; every machine must show the same divergence, with the same commit
/// ids, and resolving it on one machine resolves it everywhere.
///
/// alpha's working-copy commit sits on top of the reworded commit, so both rewrites also
/// rebase it, and it diverges too. jj does exactly this with two workspaces on one machine.
#[test]
fn same_change_rewritten_on_two_machines() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "file", "original");
    hive.sync();
    let original = hive.commit_id(0, "original");
    let change = hive
        .repo(0)
        .jj(&["log", "--no-graph", "-r", &original, "-T", "change_id"]);
    hive.repo(0)
        .jj(&["describe", &original, "-m", "alpha's wording"]);
    hive.repo(1)
        .jj(&["describe", &original, "-m", "beta's wording"]);
    hive.sync();
    hive.assert_converged();
    assert!(
        divergent_changes(&hive, 0).contains(&change),
        "{:?}",
        divergent_changes(&hive, 0)
    );
    assert_eq!(divergent_changes(&hive, 0), divergent_changes(&hive, 1));

    let beta_version = hive.commit_id(0, "beta's wording");
    hive.repo(0).jj(&["abandon", &beta_version]);
    hive.sync();
    hive.assert_converged();
    for index in [0, 1] {
        assert!(
            !divergent_changes(&hive, index).contains(&change),
            "still divergent on {index}"
        );
    }
}

/// One machine abandons a commit while the other builds on it. jj's merge rebases the
/// orphan onto the abandoned commit's parent, exactly once, so there is no divergence.
#[test]
fn commit_abandoned_while_another_machine_builds_on_it() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.commit(0, "doomed", "doomed");
    hive.sync();
    let doomed = hive.commit_id(1, "doomed");
    hive.repo(0).jj(&["abandon", &doomed]);
    hive.repo(1).jj(&["new", &doomed]);
    hive.repo(1).write_file("child", "child");
    hive.repo(1).jj(&["commit", "-m", "child"]);
    hive.sync();
    hive.assert_converged();
    let child = hive.commit_id(0, "child");
    let parent = hive.repo(0).jj(&[
        "log",
        "--no-graph",
        "-r",
        &format!("{child}-"),
        "-T",
        "description.first_line()",
    ]);
    assert_eq!(parent, "base");
    let divergent = hive
        .repo(0)
        .jj(&["log", "--no-graph", "-r", "divergent()", "-T", "commit_id"]);
    assert_eq!(divergent, "");
}

/// Three machines all build on the same commit before syncing. Merges happen one at a
/// time through the hub, so the result has no divergence.
#[test]
fn three_machines_build_on_the_same_commit() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(0, "base", "base");
    hive.sync();
    let base = hive.commit_id(0, "base");
    for (index, name) in ["alpha", "beta", "gamma"].iter().enumerate() {
        hive.repo(index).jj(&["new", &base]);
        hive.commit(index, name, &format!("from {name}"));
    }
    hive.repo(0)
        .jj(&["describe", &base, "-m", "base, reworded by alpha"]);
    hive.sync();
    hive.assert_converged();
    let divergent = hive
        .repo(2)
        .jj(&["log", "--no-graph", "-r", "divergent()", "-T", "commit_id"]);
    assert_eq!(divergent, "");
}

/// Both machines squash different work into the same commit: a divergent change, the same
/// everywhere.
#[test]
fn both_machines_squash_into_the_same_commit() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "target");
    hive.sync();
    let target = hive.commit_id(0, "target");
    let change = hive
        .repo(0)
        .jj(&["log", "--no-graph", "-r", &target, "-T", "change_id"]);
    for (index, file) in [(0, "from-alpha"), (1, "from-beta")] {
        hive.repo(index).jj(&["new", &target]);
        hive.repo(index).write_file(file, file);
        hive.repo(index).jj(&["squash"]);
    }
    hive.sync();
    hive.assert_converged();
    assert!(divergent_changes(&hive, 0).contains(&change));
}

/// A conflicted commit made on one machine is conflicted on the other, and resolving it
/// on the other resolves it on the first. Exercises jj's conflict trees and headers in
/// object transfer.
#[test]
fn conflicts_replicate_and_resolve() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "f", "base");
    let base = hive.commit_id(0, "base");
    // Two children of `base` that change `f` differently (`commit` writes the message as
    // the file's contents).
    for message in ["left", "right"] {
        hive.repo(0).jj(&["new", &base]);
        hive.commit(0, "f", message);
    }
    let (left, right) = (hive.commit_id(0, "left"), hive.commit_id(0, "right"));
    hive.repo(0).jj(&["rebase", "-r", &right, "-d", &left]);
    hive.sync();
    let conflicted = |hive: &Fixture, index: usize| {
        hive.repo(index).jj(&[
            "log",
            "--no-graph",
            "-r",
            "conflicts()",
            "-T",
            "description.first_line() ++ \"\\n\"",
        ])
    };
    assert_eq!(conflicted(&hive, 1), "right\n");
    let rebased = hive.commit_id(1, "right");
    hive.repo(1).jj(&["new", &rebased]);
    hive.repo(1).write_file("f", "resolved");
    hive.repo(1).jj(&["squash"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(conflicted(&hive, 0), "");
    let resolved = hive.commit_id(0, "right");
    assert_eq!(
        hive.repo(0).jj(&["file", "show", "-r", &resolved, "f"]),
        "resolved"
    );
}
