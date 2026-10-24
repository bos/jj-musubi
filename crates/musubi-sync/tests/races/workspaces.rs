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
    // another machine's, there or in the operations that follow.
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    assert_eq!(names(&hive, 0), ["alpha"]);
    hive.commit(0, "a", "from alpha");
    hive.sync();
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
    assert_eq!(names(&hive, 1), ["alpha/alpha", "beta"]);
    assert_eq!(working_copy(&hive, 1), beta_wc);
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.assert_converged();
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
}

/// The same while the other machine builds on its working-copy commit: `jj workspace
/// forget` abandons the empty commit here, but the hive keeps it, so the merge with what
/// the other machine built leaves that where it was, with the working copy beneath it.
#[test]
fn forgetting_another_machines_workspace_moves_nothing_built_on_it() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "b", "from beta");
    hive.commit(0, "a", "from alpha");
    hive.sync();
    let beta_wc = working_copy(&hive, 1);
    let moved = hive.commit_id(1, "from alpha");
    hive.repo(1).jj(&["rebase", "-r", &moved, "-o", &beta_wc]);
    hive.hive.sync(1).unwrap();
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(working_copy(&hive, 1), beta_wc);
    for m in 0..2 {
        let parent = hive.repo(m).jj(&[
            "log",
            "--no-graph",
            "-r",
            "description(exact:'from alpha\n')-",
            "-T",
            "commit_id",
        ]);
        assert_eq!(parent, beta_wc, "on {}", hive.repo(m).machine());
    }
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
}

/// The same at a merge with a line of history from before the other machine's working copy
/// existed, which never had its commit, or from before that machine joined: the hive keeps
/// the commit, and the other machine its working copy.
#[test]
fn other_machines_workspaces_are_theirs_through_a_merge() {
    for before_join in [false, true] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        // Newest first, down to the root, above which alpha adds its workspace and names it:
        // from before alpha joined, so from before beta was known.
        let ops = hive
            .repo(0)
            .jj(&["op", "log", "--no-graph", "-T", "id ++ \"\\n\""]);
        let ops: Vec<&str> = ops.lines().collect();
        let old = if before_join {
            ops[ops.len() - 3]
        } else {
            ops[0]
        }
        .to_owned();
        hive.commit(1, "b", "from beta");
        hive.sync();
        let beta_wc = working_copy(&hive, 1);
        hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
        hive.repo(0)
            .jj(&["--at-op", &old, "bookmark", "create", "x", "-r", "@"]);
        hive.sync();
        hive.sync();
        assert_eq!(
            working_copy(&hive, 1),
            beta_wc,
            "before_join: {before_join}"
        );
        hive.assert_converged();
        assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
    }
}

/// A machine that forgot another machine's workspace no longer sees its empty working-copy
/// commit, so jj leaves that commit behind when this machine rewrites its parent. The hive
/// mustn't keep it, which would bring the old parent back as a divergent copy: the other
/// machine gets a fresh `@` instead, on the rewritten parent, where jj would have moved the
/// working copy had it seen it.
#[test]
fn forgotten_working_copies_dont_keep_rewritten_parents() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    let parent = hive.commit_id(0, "from beta");
    hive.repo(0)
        .jj(&["describe", &parent, "-m", "reworded by alpha"]);
    hive.sync();
    hive.sync();
    for m in 0..2 {
        let divergent = hive.repo(m).jj(&[
            "log",
            "--no-graph",
            "-r",
            "divergent()",
            "-T",
            "commit_id ++ \"\\n\"",
        ]);
        assert_eq!(divergent, "", "divergence on {}", hive.repo(m).machine());
    }
    hive.assert_converged();
    assert_eq!(names(&hive, 0), ["alpha", "beta/beta"]);
    assert_eq!(parent_description(&hive, 1), "reworded by alpha");
}

/// As above, but abandoning the parent: the other machine's fresh `@` goes on the abandoned
/// commit's parent, as jj puts a working copy whose parent it abandons.
#[test]
fn forgotten_working_copies_follow_an_abandon_to_the_parent() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "a", "base on beta");
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    let parent = hive.commit_id(0, "from beta");
    hive.repo(0).jj(&["abandon", &parent]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(parent_description(&hive, 1), "base on beta");
}

/// The same, when something below the parent is abandoned: jj rebases the parent onto
/// what's left, and the fresh `@` follows it.
#[test]
fn forgotten_working_copies_follow_a_parent_rebased_by_an_abandon() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "a", "base on beta");
    hive.commit(1, "b", "from beta");
    hive.sync();
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    let base = hive.commit_id(0, "base on beta");
    hive.repo(0).jj(&["abandon", &base]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(parent_description(&hive, 1), "from beta");
    // Not the old commit kept alive as a divergent copy: `commit_id` wants just one.
    assert_eq!(revision_id(&hive, 1, "@-"), hive.commit_id(1, "from beta"));
}

/// The same, when the parent's whole branch is rebased elsewhere: the fresh `@` follows it.
/// Since a rewrite keeps the change id, it follows the moved parent after `jj rebase -r` too,
/// as jj does when it merges concurrent operations, though a local `jj rebase -r` would have
/// left the working copy behind. The commits alone can't tell the two apart.
#[test]
fn forgotten_working_copies_follow_a_moved_parent() {
    // `-b` moves "base on beta" along with the parent; `-r` moves the parent alone.
    for (how, below) in [("-b", "base on beta"), ("-r", "elsewhere")] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        hive.commit(1, "a", "base on beta");
        hive.commit(1, "b", "from beta");
        hive.sync();
        hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
        hive.repo(0)
            .jj(&["new", "--no-edit", "root()", "-m", "elsewhere"]);
        let elsewhere = hive.commit_id(0, "elsewhere");
        let parent = hive.commit_id(0, "from beta");
        hive.repo(0).jj(&["rebase", how, &parent, "-o", &elsewhere]);
        hive.sync();
        hive.sync();
        hive.assert_converged();
        assert_eq!(parent_description(&hive, 1), "from beta", "rebase {how}");
        assert_eq!(
            revision_id(&hive, 1, "@-"),
            hive.commit_id(1, "from beta"),
            "rebase {how}"
        );
        assert_eq!(
            revision_id(&hive, 1, "@--"),
            hive.commit_id(1, below),
            "rebase {how}"
        );
    }
}

/// A machine forgets another machine's workspace, then, before it syncs, abandons that
/// machine's `@`, which has edits, so the forget left it. The abandon stands, as it would
/// had the workspace still been there, and the other machine gets a fresh `@` on the
/// parent. musubi keeps visible a forgotten `@` that the forget abandoned, not one that a
/// later operation did.
#[test]
fn forgotten_working_copies_can_be_abandoned() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "a", "base on beta");
    hive.repo(1).write_file("work", "beta's work");
    hive.repo(1).jj(&["status"]);
    hive.sync();
    let beta_wc = working_copy(&hive, 1);
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    hive.repo(0).jj(&["abandon", &beta_wc]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    for m in 0..2 {
        assert!(
            !hive.visible(m).iter().any(|c| c.starts_with(&beta_wc)),
            "abandoned @ visible on {}",
            hive.repo(m).machine()
        );
    }
    assert_ne!(revision_id(&hive, 1, "@"), beta_wc);
    assert_eq!(parent_description(&hive, 1), "base on beta");
}

/// As [`forgotten_working_copies_can_be_abandoned`], but with a commit built on the `@`,
/// so that it isn't a head.
#[test]
fn forgotten_working_copies_built_on_can_be_abandoned() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "a", "base on beta");
    hive.repo(1)
        .jj(&["new", "--no-edit", "-m", "built on beta's @"]);
    hive.sync();
    let beta_wc = working_copy(&hive, 1);
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    hive.repo(0).jj(&["abandon", &beta_wc]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    for m in 0..2 {
        let visible = hive.visible(m);
        assert!(
            !visible.iter().any(|c| c.starts_with(&beta_wc)),
            "abandoned @ visible on {}",
            hive.repo(m).machine()
        );
        assert!(
            visible.iter().any(|c| c.ends_with("built on beta's @")),
            "{visible:?}"
        );
    }
    assert_ne!(revision_id(&hive, 1, "@"), beta_wc);
    assert_eq!(parent_description(&hive, 1), "base on beta");
}

/// The commit id of `revision` on machine `m`.
fn revision_id(hive: &Fixture, m: usize, revision: &str) -> String {
    hive.repo(m).jj(&["status"]);
    hive.repo(m)
        .jj(&["log", "--no-graph", "-r", revision, "-T", "commit_id"])
}

/// The description of machine `m`'s `@-`.
fn parent_description(hive: &Fixture, m: usize) -> String {
    hive.repo(m).jj(&["status"]);
    hive.repo(m).jj(&[
        "log",
        "--no-graph",
        "-r",
        "@-",
        "-T",
        "description.first_line()",
    ])
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
