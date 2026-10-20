//! Bookmarks and tags moved concurrently on different machines.

use crate::fixture::Fixture;

/// Both machines point `main` at different new commits before syncing. jj's answer for
/// concurrent operations is a conflicted bookmark, and every machine must show the same
/// conflict, keep its git branch where it was, and not have a later `jj` command quietly
/// resolve it. Resolving it on one machine resolves it everywhere.
#[test]
fn same_bookmark_moved_to_different_commits() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.repo(0).jj(&["bookmark", "create", "main", "-r", "@-"]);
    hive.sync();
    for (index, name) in [(0, "from alpha"), (1, "from beta")] {
        hive.repo(index).jj(&["new", "main"]);
        hive.commit(index, name, name);
        hive.repo(index)
            .jj(&["bookmark", "move", "main", "--to", "@-"]);
    }
    hive.sync();
    hive.assert_converged();
    for index in [0, 1] {
        let main = &hive.bookmarks(index)["main@"];
        assert!(main.starts_with("conflict:"), "main on {index} is {main}");
    }

    let chosen = hive.commit_id(0, "from alpha");
    hive.repo(0).jj(&["bookmark", "set", "main", "-r", &chosen]);
    hive.sync();
    hive.assert_converged();
    for index in [0, 1] {
        assert_eq!(hive.bookmarks(index)["main@"], chosen);
        assert_eq!(
            hive.repo(index)
                .git(&["rev-parse", "refs/heads/main"])
                .trim(),
            chosen
        );
    }
}

/// Creating the same bookmark at the same commit on both machines is not a conflict.
#[test]
fn same_bookmark_created_at_the_same_commit() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.sync();
    let base = hive.commit_id(0, "base");
    for index in [0, 1] {
        hive.repo(index)
            .jj(&["bookmark", "create", "topic", "-r", &base]);
    }
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.bookmarks(0)["topic@"], base);
}

/// One machine moves a bookmark while the other deletes it.
#[test]
fn bookmark_moved_on_one_machine_and_deleted_on_another() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.repo(0).jj(&["bookmark", "create", "main", "-r", "@-"]);
    hive.sync();
    hive.commit(0, "a", "moved");
    hive.repo(0).jj(&["bookmark", "move", "main", "--to", "@-"]);
    hive.repo(1).jj(&["bookmark", "delete", "main"]);
    hive.sync();
    hive.assert_converged();
}

/// One machine moves a branch with git, behind jj's back, while the other moves the same
/// bookmark with jj. The git move is imported by the first machine's next jj command, and
/// the result must converge rather than flip back and forth.
#[test]
fn git_branch_moved_behind_jj_while_another_machine_moves_it() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.repo(0).jj(&["bookmark", "create", "main", "-r", "@-"]);
    hive.commit(0, "other", "other");
    hive.sync();
    let other = hive.commit_id(1, "other");
    hive.repo(1).git(&["update-ref", "refs/heads/main", &other]);
    hive.commit(0, "a", "from alpha");
    hive.repo(0).jj(&["bookmark", "move", "main", "--to", "@-"]);
    hive.sync();
    hive.repo(1).jj(&["status"]);
    hive.sync();
    hive.assert_converged();
}

#[test]
fn same_tag_created_at_different_commits() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.sync();
    hive.commit(0, "a", "from alpha");
    hive.commit(1, "b", "from beta");
    hive.repo(0).jj(&["tag", "set", "v1", "-r", "@-"]);
    hive.repo(1).jj(&["tag", "set", "v1", "-r", "@-"]);
    hive.sync();
    hive.assert_converged();
    // Each machine's git keeps its own value of a conflicted tag, so compare jj's tags,
    // not the `@git` remote's.
    let template =
        r#"if(!remote, name ++ ":" ++ added_targets.map(|c| c.commit_id()).join(",") ++ "\n")"#;
    let tags = |index| hive.repo(index).jj(&["tag", "list", "-T", template]);
    assert_eq!(tags(0), tags(1));
    assert!(
        tags(0).contains(','),
        "v1 should be conflicted: {}",
        tags(0)
    );
}

/// Both machines delete the same bookmark.
#[test]
fn same_bookmark_deleted_on_both_machines() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.repo(0).jj(&["bookmark", "create", "main", "-r", "@-"]);
    hive.sync();
    for index in [0, 1] {
        hive.repo(index).jj(&["bookmark", "delete", "main"]);
    }
    hive.sync();
    hive.assert_converged();
    assert!(!hive.bookmarks(0).contains_key("main@"));
}
