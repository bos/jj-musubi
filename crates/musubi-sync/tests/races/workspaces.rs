//! Workspaces are per-machine, and each machine shows the others' as workspaces named
//! after the machine (`beta/default`).

use musubi_testutil::TestEnv;

use crate::fixture::Fixture;

fn names(hive: &Fixture, index: usize) -> Vec<String> {
    hive.workspaces(index).into_keys().collect()
}

fn working_copy(hive: &Fixture, index: usize) -> String {
    hive.repo(index)
        .jj(&["log", "--no-graph", "-r", "@", "-T", "commit_id"])
}

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
    // Each machine has its own workspace, and shows the other's under the machine's name.
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
    assert_eq!(names(&hive, 1), ["alpha/alpha", "beta"]);
}

/// Every machine's first workspace is called `default`. Workspaces are per-machine, so
/// that is fine: each machine keeps its own `default@`, and shows the other's as
/// `alpha/default@` or `beta/default@`.
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
    assert_eq!(names(&hive, 0), ["beta/default", "default"]);
    assert_eq!(names(&hive, 1), ["alpha/default", "default"]);
    for index in [0, 1] {
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
    // The other machine's working copy is a revision like any workspace's.
    let beta_wc = hive.repo(0).jj(&[
        "log",
        "--no-graph",
        "-r",
        "beta/default@",
        "-T",
        "commit_id",
    ]);
    assert_eq!(beta_wc, working_copy(&hive, 1));
}

/// Another machine's workspaces are that machine's own: forgetting them here changes
/// nothing anywhere else, and the next sync shows them again, even when the other machine
/// has done nothing since.
#[test]
fn other_machines_workspaces_are_theirs() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.sync();
    let beta_wc = working_copy(&hive, 1);
    // jj abandons an empty working-copy commit when it forgets the workspace, but not
    // another machine's.
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    assert_eq!(names(&hive, 0), ["alpha"]);
    hive.sync();
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
    assert_eq!(names(&hive, 1), ["alpha/alpha", "beta"]);
    assert_eq!(working_copy(&hive, 1), beta_wc);
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.assert_converged();
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
}

/// Each machine's view of the others' working copies follows them, including when this
/// machine rewrites the commit under one: jj moves the other machine's workspace at once,
/// as it moves any workspace's, and the other machine follows.
#[test]
fn other_machines_working_copies_follow_rewrites() {
    let env = TestEnv::new();
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "default");
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.workspaces(0)["beta/default"], working_copy(&hive, 1));
    let parent = hive.commit_id(0, "from beta");
    hive.repo(0)
        .jj(&["describe", &parent, "-m", "reworded by alpha"]);
    let moved_here = hive.workspaces(0)["beta/default"].clone();
    hive.sync();
    hive.repo(1).jj(&["status"]);
    assert_eq!(working_copy(&hive, 1), moved_here);
    let parent_on_beta = hive.repo(1).jj(&[
        "log",
        "--no-graph",
        "-r",
        "@-",
        "-T",
        "description.first_line()",
    ]);
    assert_eq!(parent_on_beta, "reworded by alpha");
    hive.sync();
    hive.assert_converged();
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

/// A machine's other workspaces show on every machine, and go when it forgets them.
#[test]
fn secondary_workspaces_show_everywhere() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let extra = hive.env.root().join("beta-extra");
    hive.repo(1).jj(&[
        "workspace",
        "add",
        "--name",
        "extra",
        extra.to_str().unwrap(),
    ]);
    hive.sync();
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta", "beta/extra"]);
    hive.repo(1).jj(&["workspace", "forget", "extra"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
}

/// A machine renames its workspace; the other machines show the new name.
#[test]
fn renamed_workspace_shows_renamed() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.sync();
    hive.repo(1).jj(&["workspace", "rename", "laptop"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(names(&hive, 0), ["alpha", "beta/laptop"]);
}

/// Three machines with the same hostname: musubi tells them apart by a random suffix, and
/// shows the two others on each machine as `mac-xxxx/default` and `mac-yyyy/default`.
#[test]
fn machines_sharing_a_hostname_are_told_apart() {
    let env = TestEnv::new();
    let repos = ["one", "two", "three"].map(|dir| env.init_repo_with_hostname(dir, "mac"));
    let mut hive = Fixture::join(env, repos.into());
    hive.sync();
    hive.assert_converged();
    for index in 0..3 {
        let others: Vec<String> = names(&hive, index)
            .into_iter()
            .filter(|name| name.contains('/'))
            .collect();
        assert_eq!(others.len(), 2, "{others:?}");
        assert!(
            others
                .iter()
                .all(|name| name.starts_with("mac-") && name.ends_with("/default")),
            "{others:?}"
        );
    }
}

/// Other machines' working copies are never git refs, so nothing git does can drop them
/// and have jj abandon the work under them: not a workspace name git can't store as a
/// ref, not an import in a repository that isn't colocated, and not a git remote named
/// after a machine.
#[test]
fn git_never_sees_other_machines_working_copies() {
    let env = TestEnv::new();
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "my laptop");
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.commit(1, "b1", "beta's stack 1");
    hive.commit(1, "b2", "beta's stack 2");
    hive.sync();
    let refs = hive.repo(0).git(&["for-each-ref", "--format=%(refname)"]);
    assert!(!refs.contains("beta"), "{refs}");
    let bare = hive.env.root().join("remote.git");
    hive.repo(0)
        .git(&["init", "--bare", "--quiet", bare.to_str().unwrap()]);
    hive.repo(0)
        .jj(&["git", "remote", "add", "beta", bare.to_str().unwrap()]);
    hive.repo(0).jj(&["git", "fetch", "--remote", "beta"]);
    hive.repo(0).jj(&["git", "import"]);
    hive.repo(0).jj(&["status"]);
    hive.sync();
    hive.assert_converged();
    for index in [0, 1] {
        let visible = hive.visible(index);
        assert!(
            visible.iter().any(|c| c.ends_with("beta's stack 2")),
            "{index}: {visible:?}"
        );
    }
}
