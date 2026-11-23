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

/// A command at an operation from before the forget points a bookmark at the forgotten
/// working copy. The forgetting machine's next command merges the two, before musubi sees
/// either, and jj, which there had the forget abandon the commit, moves the bookmark to its
/// parent, as on one machine. The hive takes that merge, though it keeps the commit, and the
/// other machine its working copy.
#[test]
fn a_bookmark_set_at_a_forgotten_working_copy_moves_to_its_parent() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    let beta_wc = working_copy(&hive, 1);
    let old = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-n", "1", "-T", "id"]);
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    hive.repo(0)
        .jj(&["--at-op", &old, "bookmark", "set", "x", "-r", &beta_wc]);
    hive.commit(0, "a", "from alpha");
    hive.sync();
    hive.assert_converged();
    let parent = hive.commit_id(1, "from beta");
    for m in 0..2 {
        let x = hive
            .repo(m)
            .jj(&["log", "--no-graph", "-r", "x", "-T", "commit_id"]);
        assert_eq!(x, parent, "on {}", hive.repo(m).machine());
    }
    assert_eq!(working_copy(&hive, 1), beta_wc);
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
    use musubi_core::node::{LocalRepo as _, Step};
    use musubi_jj::op_id::CanonicalOp;

    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "a", "base on beta");
    hive.repo(1).write_file("work", "beta's work");
    hive.repo(1).jj(&["status"]);
    hive.sync();
    let beta_wc = working_copy(&hive, 1);
    hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
    hive.repo(0).jj(&["abandon", &beta_wc]);
    hive.hive.sync(0).unwrap();
    let target = hive.hive.hub_head();
    hive.hive.fetch(1).unwrap();
    // Advancing to one head may also write working-copy cleanup. It is an automatic write
    // inside the busy call, not an idle-maintenance call or a merge of concurrent heads.
    let mut advanced = false;
    for _ in 0..24 {
        let member = &mut hive.hive.members[1];
        assert_eq!(member.core.known().head, target);
        let before = member.adapter.heads().unwrap();
        assert_eq!(before.len(), 1);
        match member.core.step(&mut member.adapter).unwrap() {
            Step::Realized(_) => {}
            Step::Advanced(_) => {
                assert!(member.adapter.is_ancestor(&before[0], &target).unwrap());
                let after = member.adapter.heads().unwrap();
                assert_eq!(after.len(), 1);
                assert_ne!(after[0], target);
                let cleanup = member
                    .adapter
                    .repo()
                    .canonical_store()
                    .read_operation(&CanonicalOp(after[0].clone()))
                    .unwrap();
                assert_eq!(cleanup.parents, vec![target.clone()]);
                assert!(cleanup.metadata.description.contains("new working copy"));
                advanced = true;
                break;
            }
            step => panic!("expected realization or advance, got {step:?}"),
        }
    }
    assert!(advanced, "the fetched head was never advanced to");
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

/// Machine `index`'s own workspace `name`, at `dir` under the hive's root.
fn add_workspace(hive: &Fixture, index: usize, name: &str, dir: &str) -> musubi_testutil::TestRepo {
    let path = hive.env.root().join(dir);
    hive.repo(index)
        .jj(&["workspace", "add", "--name", name, path.to_str().unwrap()]);
    hive.repo(index).another_copy(&path)
}

/// Checks that machine `index`'s sync is refused for its workspaces with a `/` in their names,
/// as `refusal` says.
fn assert_refused(hive: &mut Fixture, index: usize, refusal: &str) {
    let err = hive.hive.sync(index).unwrap_err();
    assert!(musubi_sync::node::slashed_workspaces(&err), "{err:#}");
    assert_eq!(format!("{err:#}"), refusal);
}

/// A copy doesn't sync while it has a workspace of its own with a `/` in its name, as
/// `feat/x`: other machines show each other's workspaces by names of that form. It publishes
/// nothing, and other copies sync on. Its directory being away, as on a disk not mounted,
/// changes nothing, and a workspace forgotten with `jj workspace forget`, which leaves jj's
/// record of its directory, no longer counts. Renamed without the `/`, the workspace shows
/// everywhere, where it is, and the copy syncs on.
#[test]
fn a_slash_in_a_workspace_name_stops_its_copy_syncing_until_renamed() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let feat = add_workspace(&hive, 0, "feat/x", "alpha-feat");
    feat.write_file("from-alpha", "alpha's feat/x");
    feat.jj(&["describe", "-m", "alpha's feat/x"]);
    let own = hive.workspaces(0)["feat/x"].clone();
    add_workspace(&hive, 0, "beta/z", "alpha-beta-z");
    let head = hive.hive.hub_head();
    assert_refused(
        &mut hive,
        0,
        "this repository can't sync while its workspaces beta/z and feat/x have a \"/\" in \
         their names",
    );
    assert_eq!(hive.hive.hub_head(), head);
    // Nor does it take `beta/z` for one of beta's that `jj undo` brought back, and drop it.
    assert!(hive.node(0).show_other_workspaces().is_err());
    assert!(names(&hive, 0).contains(&"beta/z".to_owned()));
    hive.commit(1, "b", "from beta");
    hive.hive.sync(1).unwrap();
    let shown = names(&hive, 1);
    assert!(!shown.iter().any(|name| name.contains("feat")), "{shown:?}");

    hive.repo(0).jj(&["workspace", "forget", "beta/z"]);
    let refusal = "this repository can't sync while its workspace feat/x has a \"/\" in its name";
    assert_refused(&mut hive, 0, refusal);
    let path = hive.env.root().join("alpha-feat");
    let away = hive.env.root().join("alpha-feat-away");
    std::fs::rename(&path, &away).unwrap();
    assert_refused(&mut hive, 0, refusal);
    std::fs::rename(&away, &path).unwrap();
    assert!(!hive.visible(0).iter().any(|c| c.ends_with("from beta")));

    feat.jj(&["workspace", "rename", "feat-x"]);
    hive.sync();
    hive.sync();
    assert_eq!(hive.workspaces(1).get("alpha/feat-x"), Some(&own));
    assert!(hive.visible(0).iter().any(|c| c.ends_with("from beta")));
    hive.assert_converged();
}

/// A workspace added as `beta/x` during a sync stops it at its next step: before it sends
/// the commands that added it, and, where it realizes beta's work adding its `x`, after the
/// realization was made, before it is published. Published beside it, beta's `x`, shown as
/// `beta/x` too, would be one workspace with alpha's to jj's merge, and alpha's directory would
/// snapshot into beta's working copy. Renamed, alpha's stays alpha's, and beta's is shown as
/// `beta/x`; neither working copy moves.
#[test]
fn a_workspace_with_a_slash_added_during_a_sync_stops_it() {
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;

    for realizing in [false, true] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        let beta_x = add_workspace(&hive, 1, "x", "beta-x");
        beta_x.write_file("from-beta", "beta's x");
        beta_x.jj(&["describe", "-m", "beta's x"]);
        let theirs = hive.workspaces(1)["x"].clone();
        if realizing {
            hive.hive.sync(1).unwrap();
        }
        hive.hive.fetch(0).unwrap();
        let member = &mut hive.hive.members[0];
        while !member.adapter.is_local(&member.core.known().head).unwrap() {
            let step = member.core.step(&mut member.adapter).unwrap();
            assert!(matches!(step, Step::Realized(_)), "{step:?}");
        }
        let alpha_x = add_workspace(&hive, 0, "beta/x", "alpha-beta-x");
        let own = hive.workspaces(0)["beta/x"].clone();
        let head = hive.hive.hub_head();
        let member = &mut hive.hive.members[0];
        let err = member.core.step(&mut member.adapter).unwrap_err();
        assert!(musubi_sync::node::slashed_workspaces(&err), "{err:#}");
        assert_eq!(hive.hive.hub_head(), head, "realizing: {realizing}");
        assert_eq!(hive.workspaces(0).get("beta/x"), Some(&own));

        alpha_x.jj(&["workspace", "rename", "alpha-x"]);
        hive.sync();
        hive.sync();
        beta_x.jj(&["status"]);
        let alpha = hive.workspaces(0);
        assert_eq!(alpha.get("alpha-x"), Some(&own), "{alpha:?}");
        assert_eq!(alpha.get("beta/x"), Some(&theirs), "{alpha:?}");
        let beta = hive.workspaces(1);
        assert_eq!(beta.get("x"), Some(&theirs), "{beta:?}");
        assert_eq!(beta.get("alpha/alpha-x"), Some(&own), "{beta:?}");
        hive.assert_converged();
    }
}

/// `jj workspace forget` of a workspace of alpha's own named `beta/x`, as on being refused,
/// leaves jj's record of its directory. Once alpha shows beta's workspace `x` by that name,
/// whether beta adds it after or alpha shows it again after forgetting it here, alpha takes
/// the record for a workspace of its own and refuses to sync. `jj workspace remove beta/x`,
/// which the hint offers beside renaming, keeps the old directory's files in a commit of
/// alpha's, deletes the directory and the record, and moves nothing of beta's; alpha syncs on.
#[test]
fn a_forgotten_workspace_with_a_slash_is_removed_to_sync_on() {
    for shown_before in [false, true] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        if shown_before {
            add_workspace(&hive, 1, "x", "beta-x");
            hive.sync();
            hive.repo(0).jj(&["workspace", "forget", "beta/x"]);
        }
        let old = add_workspace(&hive, 0, "beta/x", "alpha-beta-x");
        old.write_file("old", "alpha's old files");
        old.jj(&["status"]);
        let old_commit = hive.workspaces(0)["beta/x"].clone();
        // Not yet snapshotted when the workspace is forgotten.
        old.write_file("unsaved", "alpha's unsaved edit");
        hive.repo(0).jj(&["workspace", "forget", "beta/x"]);
        if !shown_before {
            hive.sync();
            add_workspace(&hive, 1, "x", "beta-x");
        }
        let theirs = hive.workspaces(1)["x"].clone();
        hive.hive.sync(1).unwrap();
        // The sync that shows beta's `x` puts it in alpha's view, then stops.
        let err = hive.hive.sync(0).unwrap_err();
        assert!(musubi_sync::node::slashed_workspaces(&err), "{err:#}");

        hive.repo(0).jj(&["workspace", "remove", "beta/x"]);
        hive.sync();
        hive.sync();
        assert_eq!(hive.workspaces(0).get("beta/x"), Some(&theirs));
        assert_eq!(hive.workspaces(1).get("x"), Some(&theirs));
        assert!(!hive.env.root().join("alpha-beta-x").exists());
        let kept = hive.visible(1);
        assert!(
            kept.iter().any(|line| line.starts_with(&old_commit)),
            "{kept:?}"
        );
        let snapshot = hive.repo(1).jj(&[
            "log",
            "--no-graph",
            "-r",
            "description(substring:\"SNAPSHOT OF REMOVED WORKSPACE\")",
            "-T",
            "parents.map(|p| p.commit_id()) ++ \"\\n\"",
        ]);
        assert_eq!(snapshot.trim(), old_commit, "shown before: {shown_before}");
        hive.assert_converged();
    }
}

/// alpha forgets a workspace of its own named `beta/x`, as it might on being refused, and syncs;
/// beta adds `x`, which alpha shows as `beta/x`. `jj op restore` of the operation before the
/// forget, as `jj undo` restores, or `jj op revert` of the forget brings alpha's `beta/x` back
/// over beta's in alpha's view: the name stands for beta's workspace only where the view
/// brought back has it at the commit the hive gave beta's there, and alpha's was at its own,
/// so beta's working copy doesn't move.
#[test]
fn going_back_to_a_workspace_named_like_another_machines_moves_nothing_of_that_one() {
    for how in ["restore", "revert"] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        let own = add_workspace(&hive, 0, "beta/x", "alpha-beta-x");
        own.write_file("from-alpha", "alpha's beta/x");
        own.jj(&["describe", "-m", "alpha's beta/x"]);
        let last_op = |hive: &Fixture| {
            hive.repo(0).jj(&[
                "--ignore-working-copy",
                "--no-integrate-operation",
                "op",
                "log",
                "--no-graph",
                "-n1",
                "-T",
                "id",
            ])
        };
        let before = last_op(&hive);
        hive.repo(0).jj(&["workspace", "forget", "beta/x"]);
        let forget = last_op(&hive);
        hive.sync();
        add_workspace(&hive, 1, "x", "beta-x");
        let theirs = hive.workspaces(1)["x"].clone();
        hive.hive.sync(1).unwrap();
        // alpha shows beta's `x` now, under the name its own had, whose record jj kept.
        let err = hive.hive.sync(0).unwrap_err();
        assert!(musubi_sync::node::slashed_workspaces(&err), "{err:#}");
        if how == "restore" {
            hive.repo(0).jj(&["op", "restore", before.trim()]);
        } else {
            hive.repo(0).jj(&["op", "revert", forget.trim()]);
        }
        own.jj(&["workspace", "rename", "mine"]);
        hive.sync();
        hive.sync();
        let beta = hive.workspaces(1);
        assert_eq!(beta.get("x"), Some(&theirs), "{how}: {beta:?}");
        let alpha = hive.workspaces(0);
        assert_eq!(alpha.get("beta/x"), Some(&theirs), "{how}: {alpha:?}");
        hive.assert_converged();
    }
}

/// alpha forgets beta's workspace `beta/x` here, adds one of its own by that name, and reverts
/// the forget (`jj op revert`), which brings beta's back beside alpha's in the view. Whichever
/// commit the name ends at, beta's working copy stays where it is.
#[test]
fn reverting_a_forget_of_another_machines_workspace_beside_ones_own_moves_nothing_of_it() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    add_workspace(&hive, 1, "x", "beta-x");
    hive.sync();
    let theirs = hive.workspaces(1)["x"].clone();
    hive.repo(0).jj(&["workspace", "forget", "beta/x"]);
    let forget = hive.repo(0).jj(&[
        "--ignore-working-copy",
        "--no-integrate-operation",
        "op",
        "log",
        "--no-graph",
        "-n1",
        "-T",
        "id",
    ]);
    let own = add_workspace(&hive, 0, "beta/x", "alpha-beta-x");
    own.write_file("from-alpha", "alpha's beta/x");
    own.jj(&["describe", "-m", "alpha's beta/x"]);
    let alphas = hive.workspaces(0)["beta/x"].clone();
    hive.repo(0).jj(&["op", "revert", forget.trim()]);
    // jj's merge keeps alpha's under the name.
    assert_eq!(hive.workspaces(0).get("beta/x"), Some(&alphas));
    let err = hive.hive.sync(0).unwrap_err();
    assert!(musubi_sync::node::slashed_workspaces(&err), "{err:#}");
    own.jj(&["workspace", "rename", "mine"]);
    hive.sync();
    hive.sync();
    assert_eq!(hive.workspaces(1).get("x"), Some(&theirs));
    assert_eq!(hive.workspaces(1).get("alpha/mine"), Some(&alphas));
    assert_eq!(hive.workspaces(0).get("beta/x"), Some(&theirs));
    hive.assert_converged();
}

/// alpha forgets beta's workspace `beta/beta` here and adds one of its own by that name, which
/// stops alpha syncing until it is renamed. Adding it alone, `jj workspace add` moves the new
/// workspace to its commit in a second operation that starts from a view with `beta/beta`,
/// and alpha may work in it before renaming it. Canonicalized only after the rename, none of
/// these takes the name for beta's workspace, which the hive shows at another commit: beta's
/// working copy stays where it is.
#[test]
fn a_workspace_named_like_one_forgotten_here_moves_nothing_of_that_one() {
    for work in [false, true] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        hive.sync();
        let theirs = hive.workspaces(1)["beta"].clone();
        hive.repo(0).jj(&["workspace", "forget", "beta/beta"]);
        let own = add_workspace(&hive, 0, "beta/beta", "alpha-beta");
        if work {
            own.write_file("from-alpha", "alpha's work");
            own.jj(&["describe", "-m", "alpha's beta/beta"]);
        }
        let alphas = hive.workspaces(0)["beta/beta"].clone();
        assert_refused(
            &mut hive,
            0,
            "this repository can't sync while its workspace beta/beta has a \"/\" in its name",
        );
        own.jj(&["workspace", "rename", "mine"]);
        hive.sync();
        hive.sync();
        let alpha = hive.workspaces(0);
        assert_eq!(alpha.get("mine"), Some(&alphas), "work: {work}: {alpha:?}");
        assert_eq!(
            alpha.get("beta/beta"),
            Some(&theirs),
            "work: {work}: {alpha:?}"
        );
        let beta = hive.workspaces(1);
        assert_eq!(beta.get("beta"), Some(&theirs), "work: {work}: {beta:?}");
        assert_eq!(
            beta.get("alpha/mine"),
            Some(&alphas),
            "work: {work}: {beta:?}"
        );
        hive.assert_converged();
    }
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

/// Two machines that share a hostname show each other as the hub lists them, by name and part
/// of the id, not by the plain name, which the other has too, and each names itself so for
/// `musubi status`.
#[test]
fn two_machines_sharing_a_hostname_show_each_other_qualified() {
    let env = TestEnv::new();
    let repos = ["one", "two"].map(|dir| env.init_repo_with_hostname(dir, "mac"));
    let mut hive = Fixture::join(env, repos.into());
    hive.sync();
    hive.assert_converged();
    for (index, other) in [(0, 1), (1, 0)] {
        let qualified = musubi_jj::workspaces::qualified_name(&hive.machine_key(other));
        let others: Vec<String> = names(&hive, index)
            .into_iter()
            .filter(|name| name.contains('/'))
            .collect();
        assert_eq!(others, vec![format!("{qualified}/default")]);
        let own = hive.machine_key(index);
        let own_name = musubi_jj::workspaces::qualified_name(&own);
        let activity = hive.node(index).activity().unwrap();
        let named: Vec<(&str, &str)> = activity
            .iter()
            .map(|copy| (copy.key.as_str(), copy.name.as_str()))
            .collect();
        assert!(
            named.contains(&(own.as_str(), own_name.as_str())),
            "{named:?}"
        );
    }
}

/// An operation that forgot the workspace it was made in is realized under the name that
/// workspace shows by, `beta/beta`, as every other operation is, though the view no longer
/// names it. Under the plain name, `beta`, `jj undo` in a workspace of alpha's of that name
/// would take beta's operation for its own.
#[test]
fn an_operation_that_forgot_its_workspace_keeps_its_name() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.repo(1).jj(&["workspace", "forget", "beta"]);
    hive.sync();
    hive.sync();
    let template = r#"description.first_line() ++ "\t" ++ workspace_name ++ "\n""#;
    let ops = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-T", template]);
    let forget = ops
        .lines()
        .find(|line| line.starts_with("forget workspace beta"))
        .unwrap_or_else(|| panic!("no forget in {ops:?}"));
    assert_eq!(forget, "forget workspace beta\tbeta/beta@");
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

/// alpha restores the operation from before a second machine named beta joined, runs `jj new`
/// on it, and abandons the restore, with no sync between, so alpha's node never sees the
/// restore. jj moves the command onto the restore's
/// parent, whose view has no `beta/beta`, while its own view has it; but the name has a `/`, so
/// it is never alpha's own, and stays the first beta's.
#[test]
fn abandoning_a_restore_of_an_old_alias_keeps_others_workspaces_theirs() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "from alpha");
    hive.commit(1, "b", "from beta");
    hive.sync();
    let alpha = hive.repo(0);
    let old = alpha.jj(&[
        "--ignore-working-copy",
        "--no-integrate-operation",
        "op",
        "log",
        "--no-graph",
        "-n1",
        "-T",
        "id",
    ]);
    let second = hive.env.init_repo_with_hostname("beta-two", "beta");
    hive.add(second);
    hive.sync();
    hive.sync();

    let alpha = hive.repo(0);
    alpha.jj(&["op", "restore", &old]);
    let restore = alpha.jj(&[
        "--ignore-working-copy",
        "--no-integrate-operation",
        "op",
        "log",
        "--no-graph",
        "-n1",
        "-T",
        "id",
    ]);
    alpha.jj(&["new", "-m", "on the old alias"]);
    alpha.jj(&["op", "abandon", &restore]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    for index in 0..3 {
        let shown = names(&hive, index);
        assert!(
            shown.iter().all(|name| !name.starts_with("alpha/beta")),
            "machine {index} shows {shown:?}"
        );
    }
}

/// As `abandoning_a_restore_of_an_old_alias_keeps_others_workspaces_theirs`, with the old name
/// that of a machine alpha has forgotten, rather than one shown under a longer name since:
///
/// 1. alpha and beta sync; alpha shows `beta/beta`, and `old` is its operation.
/// 2. alpha forgets beta (`musubi forget`), which removes `beta/beta` from its view.
/// 3. `jj op restore <old>` brings `beta/beta` back; `jj new`; `jj op abandon` of the restore.
///
/// jj moves the command onto the restore's parent, whose view lacks `beta/beta`, and alpha could
/// show beta, forgotten but still known, as `beta` again. But `beta/beta` has a `/`, so it is
/// never alpha's own, where once, judged on its new parent alone, the command made it, and beta
/// listed its own workspace as `alpha/beta/beta` (#167).
#[test]
fn abandoning_a_restore_of_a_forgotten_machines_workspace_keeps_it_theirs() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "from alpha");
    hive.commit(1, "b", "from beta");
    hive.sync();
    let last_op = |hive: &Fixture| {
        hive.repo(0).jj(&[
            "--ignore-working-copy",
            "--no-integrate-operation",
            "op",
            "log",
            "--no-graph",
            "-n1",
            "-T",
            "id",
        ])
    };
    let old = last_op(&hive);
    let beta = hive.machine_key(1);
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.sync();
    hive.sync();
    assert!(!names(&hive, 0).contains(&"beta/beta".to_owned()));

    hive.repo(0).jj(&["op", "restore", &old]);
    let restore = last_op(&hive);
    hive.repo(0).jj(&["new", "-m", "on the old name"]);
    hive.repo(0).jj(&["op", "abandon", &restore]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    for index in 0..2 {
        let shown = names(&hive, index);
        assert!(
            shown.iter().all(|name| !name.starts_with("alpha/beta")),
            "machine {index} shows {shown:?}"
        );
    }
}
