//! Workspace names: keys of every machine's working-copy commit in the shared view.

use musubi_testutil::TestEnv;

use crate::fixture::Fixture;

#[test]
fn basic_replication_converges() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "from alpha");
    hive.sync();
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.assert_converged();
    let visible = hive.visible(0);
    assert!(
        visible.iter().any(|c| c.ends_with("from alpha"))
            && visible.iter().any(|c| c.ends_with("from beta"))
    );
    // Workspaces are per-machine: each machine lists only its own, while the other's
    // working-copy commit is replicated as an ordinary commit.
    let workspaces = hive
        .repo(0)
        .jj(&["workspace", "list", "-T", "name ++ \"\\n\""]);
    assert_eq!(workspaces, "alpha\n");
}

/// Every machine's first workspace is called `default`. Workspaces are per-machine, so
/// that is fine: each machine keeps its own `default@`, and the other machine's
/// working-copy commit is just a commit.
#[test]
fn machines_may_share_a_workspace_name() {
    let env = TestEnv::new();
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "default");
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.commit(0, "a", "from alpha");
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.assert_converged();
    for index in [0, 1] {
        let workspaces = hive
            .repo(index)
            .jj(&["workspace", "list", "-T", "name ++ \"\\n\""]);
        assert_eq!(workspaces, "default\n");
        let parent = hive.repo(index).jj(&[
            "log",
            "--no-graph",
            "-r",
            "@-",
            "-T",
            "description.first_line()",
        ]);
        assert_eq!(
            parent,
            ["from alpha", "from beta"][index],
            "{index}'s @ moved"
        );
    }
}

/// No machine has another machine's workspaces, so none can forget, edit, or otherwise
/// touch them.
#[test]
fn other_machines_workspaces_are_not_visible_as_workspaces() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.sync();
    // jj only warns about forgetting a workspace it does not have, and changes nothing.
    let forget = hive.repo(0).jj_output(&["workspace", "forget", "beta"]);
    assert!(String::from_utf8_lossy(&forget.stderr).contains("No such workspace: beta"));
    assert!(
        !hive
            .repo(0)
            .jj_output(&["log", "-r", "beta@"])
            .status
            .success()
    );
    hive.sync();
    let workspaces = hive
        .repo(1)
        .jj(&["workspace", "list", "-T", "name ++ \"\\n\""]);
    assert_eq!(workspaces, "beta\n");
}

/// Rebasing another machine's working-copy commit (by rewriting its parent) is the normal
/// case and must not be mistaken for a collision.
#[test]
fn rewriting_under_another_machines_working_copy_is_allowed() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.sync();
    let base = hive.commit_id(1, "base");
    hive.repo(1).jj(&["new", &base]);
    hive.repo(1).write_file("work", "in progress");
    hive.repo(1).jj(&["status"]);
    hive.sync();
    hive.repo(0)
        .jj(&["describe", &base, "-m", "base, reworded"]);
    hive.sync();
    // beta's working copy was rebased onto the reworded commit; with auto-update-stale its
    // next command updates the files, and its edit survives.
    hive.repo(1).jj(&["status"]);
    assert_eq!(
        std::fs::read_to_string(hive.repo(1).path().join("work")).unwrap(),
        "in progress"
    );
    let parent = hive.repo(1).jj(&[
        "log",
        "--no-graph",
        "-r",
        "@-",
        "-T",
        "description.first_line()",
    ]);
    assert_eq!(parent, "base, reworded");
    hive.sync();
    hive.assert_converged();
}

/// A machine edits files but runs no jj command, so the edit is not snapshotted, while
/// another machine rewrites the parent of its working copy. The edit must survive: jj
/// snapshots it at the old operation before updating, at worst leaving a divergent
/// working-copy change.
#[test]
fn unsnapshotted_edit_survives_a_remote_rebase() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    hive.sync();
    let base = hive.commit_id(1, "base");
    hive.repo(1).jj(&["new", &base]);
    hive.sync();
    hive.repo(1).write_file("unsaved", "not yet snapshotted");
    hive.repo(0)
        .jj(&["describe", &base, "-m", "base, reworded"]);
    hive.sync();
    hive.repo(1).jj(&["status"]);
    assert_eq!(
        std::fs::read_to_string(hive.repo(1).path().join("unsaved")).unwrap(),
        "not yet snapshotted"
    );
    let with_edit = hive.repo(1).jj(&[
        "log",
        "--no-graph",
        "-r",
        "all() & files(\"unsaved\")",
        "-T",
        "commit_id ++ \"\\n\"",
    ]);
    assert!(!with_edit.is_empty(), "the edit is in no commit");
    hive.sync();
    hive.assert_converged();
}

/// One machine abandons another machine's working-copy commit (it can: the commit is
/// replicated like any other). The other machine gives itself a fresh working-copy commit
/// on the abandoned one's parent, exactly as jj does when you abandon `@` locally.
#[test]
fn abandoning_another_machines_working_copy_commit() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "base", "base");
    hive.repo(1).write_file("work", "beta's work");
    hive.repo(1).jj(&["status"]);
    hive.sync();
    let beta_wc = hive
        .repo(1)
        .jj(&["log", "--no-graph", "-r", "@", "-T", "commit_id"]);
    hive.repo(0).jj(&["abandon", &beta_wc]);
    hive.sync();
    hive.repo(1).jj(&["status"]);
    let parent = hive.repo(1).jj(&[
        "log",
        "--no-graph",
        "-r",
        "@-",
        "-T",
        "description.first_line()",
    ]);
    assert_eq!(parent, "base");
    let wc = hive
        .repo(1)
        .jj(&["log", "--no-graph", "-r", "@", "-T", "commit_id"]);
    assert_ne!(wc, beta_wc);
    hive.sync();
    hive.assert_converged();
}

/// Adding and forgetting a secondary workspace is a local matter: other machines never
/// see the workspace, only the commits it creates.
#[test]
fn secondary_workspaces_stay_local() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let extra = hive.env.root().join("beta-extra");
    hive.repo(1).jj(&[
        "workspace",
        "add",
        "--name",
        "beta-extra",
        extra.to_str().unwrap(),
    ]);
    hive.sync();
    hive.repo(1).jj(&["workspace", "forget", "beta-extra"]);
    hive.sync();
    hive.assert_converged();
    let workspaces = hive
        .repo(0)
        .jj(&["workspace", "list", "-T", "name ++ \"\\n\""]);
    assert_eq!(workspaces, "alpha\n");
}

fn working_copy(hive: &Fixture, index: usize) -> String {
    hive.repo(index)
        .jj(&["log", "--no-graph", "-r", "@", "-T", "commit_id"])
}

/// Other machines' workspaces show as labels: beta's `default` is `default@beta` on alpha,
/// an untracked remote bookmark that follows beta's working copy around.
#[test]
fn other_machines_workspaces_are_labeled() {
    let env = TestEnv::new();
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "default");
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.bookmarks(0)["default@beta"], working_copy(&hive, 1));
    assert_eq!(hive.bookmarks(1)["default@alpha"], working_copy(&hive, 0));
    assert!(
        !hive.bookmarks(0).contains_key("default@alpha"),
        "no label for oneself"
    );
    // In a colocated repository the label is also a git remote-tracking ref.
    let git = hive
        .repo(0)
        .git(&["rev-parse", "refs/remotes/beta/default"]);
    assert_eq!(git.trim(), working_copy(&hive, 1));

    // The label follows beta's working copy.
    hive.commit(1, "c", "more from beta");
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.bookmarks(0)["default@beta"], working_copy(&hive, 1));

    // When alpha rewrites the commit under beta's working copy, beta follows the rewrite,
    // and alpha's label catches up with beta's next operation. (Alpha's own label lags
    // until then: jj does not move remote bookmarks when it rewrites, and a label-only
    // operation after every such rewrite would be noise.)
    let parent = hive.commit_id(0, "more from beta");
    hive.repo(0)
        .jj(&["describe", &parent, "-m", "reworded by alpha"]);
    hive.sync();
    hive.repo(1).write_file("d", "beta keeps working");
    hive.repo(1).jj(&["status"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.bookmarks(0)["default@beta"], working_copy(&hive, 1));
    let parent_on_beta = hive.repo(1).jj(&[
        "log",
        "--no-graph",
        "-r",
        "@-",
        "-T",
        "description.first_line()",
    ]);
    assert_eq!(parent_on_beta, "reworded by alpha");
}

/// Labels are alpha's own view of the hive: changing them changes nothing for anyone else,
/// and the next sync puts them back.
#[test]
fn labels_are_local() {
    let env = TestEnv::new();
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "default");
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.sync();
    let beta_wc = working_copy(&hive, 1);
    hive.repo(0)
        .jj(&["bookmark", "forget", "--include-remotes", "default"]);
    hive.sync();
    hive.repo(1).jj(&["status"]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.assert_converged();
    assert_ne!(working_copy(&hive, 1), beta_wc);
    assert_eq!(hive.bookmarks(0)["default@beta"], working_copy(&hive, 1));
    let workspaces = hive
        .repo(1)
        .jj(&["workspace", "list", "-T", "name ++ \"\\n\""]);
    assert_eq!(workspaces, "default\n");
}

/// A machine renames its workspace; the other machines' label for it follows.
#[test]
fn renamed_workspace_relabels() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.sync();
    assert!(hive.bookmarks(0).contains_key("beta@beta"));
    hive.repo(1).jj(&["workspace", "rename", "laptop"]);
    hive.sync();
    hive.assert_converged();
    let labels = hive.bookmarks(0);
    assert!(
        labels.contains_key("laptop@beta") && !labels.contains_key("beta@beta"),
        "{labels:?}"
    );
}

/// Three machines with the same hostname: musubi tells them apart by a random suffix, and
/// labels the two others on each machine `default@mac-xxxx` and `default@mac-yyyy`.
#[test]
fn machines_sharing_a_hostname_are_told_apart() {
    let env = TestEnv::new();
    let repos = ["one", "two", "three"].map(|dir| env.init_repo_with_hostname(dir, "mac"));
    let mut hive = Fixture::join(env, repos.into());
    hive.sync();
    hive.assert_converged();
    for index in 0..3 {
        let labels: Vec<String> = hive
            .bookmarks(index)
            .into_iter()
            .filter(|(name, _)| name.starts_with("default@mac-"))
            .map(|(_, target)| target)
            .collect();
        let mut others: Vec<String> = (0..3)
            .filter(|&i| i != index)
            .map(|i| working_copy(&hive, i))
            .collect();
        let mut labels = labels;
        labels.sort();
        others.sort();
        assert_eq!(labels, others, "labels on {index}");
    }
}

/// Labels are tracked remote bookmarks, and jj merges a tracked remote bookmark's changes
/// into the local bookmark of the same name. Editing labels (untracking, forgetting,
/// undoing that) and the labeled machine moving on must never create a local bookmark,
/// which would replicate to every machine.
#[test]
fn label_edits_never_become_local_bookmarks() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    for step in [
        &["bookmark", "untrack", "beta@beta"][..],
        &["bookmark", "forget", "--include-remotes", "beta"],
        &["undo"],
    ] {
        hive.repo(0).jj(step);
        hive.sync();
    }
    hive.repo(0).jj(&["bookmark", "untrack", "beta@beta"]);
    hive.commit(1, "c", "beta moves on");
    hive.sync();
    hive.repo(0).jj(&["status"]);
    hive.sync();
    hive.assert_converged();
    for index in [0, 1] {
        let locals = crate::fixture::local_bookmarks(&hive.bookmarks(index));
        assert!(locals.is_empty(), "local bookmarks on {index}: {locals:?}");
    }
}
