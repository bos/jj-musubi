//! Operation-log level races: undo, op abandon, offline machines, restarts.

use musubi_testutil::TestEnv;

use crate::fixture::Fixture;

/// Both machines' workspaces called `default`, as they are unless renamed.
fn default_workspaces() -> Fixture {
    let env = TestEnv::new();
    let alpha = env.init_repo_with_workspace("alpha", "default");
    let beta = env.init_repo_with_workspace("beta", "default");
    Fixture::join(env, vec![alpha, beta])
}

/// `jj undo` undoes the latest operation, whichever machine made it, but refuses one made
/// in another workspace unless asked explicitly. Another machine's operations count as
/// made in another workspace, `alpha/default`, even though both workspaces are named
/// `default`.
#[test]
fn undo_of_another_machines_operation() {
    let mut hive = default_workspaces();
    hive.commit(0, "a", "to be undone");
    hive.sync();
    let refused = hive.repo(1).jj_output(&["undo"]);
    assert!(!refused.status.success());
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(stderr.contains("alpha/default"), "{stderr}");
    hive.sync();
    hive.assert_converged();
    assert!(hive.visible(1).iter().any(|c| c.ends_with("to be undone")));

    hive.repo(1).jj(&["undo", "--allow-cross-workspace"]);
    hive.sync();
    hive.assert_converged();
    assert!(!hive.visible(0).iter().any(|c| c.ends_with("to be undone")));
}

/// A machine undoes and redoes its own latest operation as usual, and both replicate.
#[test]
fn undo_and_redo_of_own_operation() {
    let mut hive = default_workspaces();
    hive.commit(0, "a", "undone and redone");
    hive.sync();
    hive.repo(0).jj(&["undo"]);
    hive.sync();
    hive.assert_converged();
    assert!(
        !hive
            .visible(1)
            .iter()
            .any(|c| c.ends_with("undone and redone"))
    );
    hive.repo(0).jj(&["redo"]);
    hive.sync();
    hive.assert_converged();
    assert!(
        hive.visible(1)
            .iter()
            .any(|c| c.ends_with("undone and redone"))
    );
}

/// jj's undo stack names operations by id, in descriptions such as "undo: restore to
/// operation <id>", and reads the ids back. An undo made on another machine names that
/// machine's operations, so musubi translates the ids, and the undo stack continues here.
#[test]
fn undo_stack_continues_across_machines() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "undone on alpha");
    hive.repo(0).jj(&["undo"]);
    hive.sync();
    hive.repo(1).jj(&["new", "-m", "undone on beta"]);
    hive.repo(1).jj(&["undo"]);
    hive.sync();
    hive.assert_converged();
    for machine in [0, 1] {
        let visible = hive.visible(machine);
        assert!(
            !visible.iter().any(|c| c.contains("undone on")),
            "{visible:?}"
        );
    }
}

/// Undoing another machine's undo goes further back along its undo stack, which jj finds
/// by the id in the undo's description, and redoing returns to where the other machine's
/// undo left things. (Redo has to come first: once another machine's operation arrives,
/// jj finds nothing to redo.)
#[test]
fn undo_and_redo_of_another_machines_undo() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.repo(0).jj(&["undo"]);
    hive.sync();
    let after_alphas_undo = hive.visible(1);
    hive.repo(1).jj(&["undo", "--allow-cross-workspace"]);
    assert_ne!(hive.visible(1), after_alphas_undo);
    hive.repo(1).jj(&["redo"]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.visible(0), after_alphas_undo);
}

/// Restoring an older view on one machine restores every machine's working copy, as
/// `jj op restore` restores every workspace's on one machine: the other machine's working
/// copy goes back to where it was then, and its working copy is stale until its next
/// command updates the files (with auto-update-stale, as the tests set it).
#[test]
fn op_restore_restores_other_machines_working_copies() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "b1", "beta committed");
    hive.sync();
    let restore_to = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let then = hive.workspaces(0)["beta/beta"].clone();
    hive.repo(1).write_file("b2", "beta in progress");
    hive.repo(1).jj(&["describe", "-m", "beta in progress"]);
    hive.sync();
    hive.repo(0).jj(&["op", "restore", &restore_to]);
    hive.sync();
    hive.repo(1).jj(&["status"]);
    let now = hive
        .repo(1)
        .jj(&["log", "--no-graph", "-r", "@", "-T", "commit_id"]);
    assert_eq!(now, then);
    hive.sync();
    hive.assert_converged();
}

/// The operation log shows which machine made each operation.
#[test]
fn op_log_names_other_machines_workspaces() {
    let mut hive = default_workspaces();
    hive.commit(0, "a", "on alpha");
    hive.sync();
    let template = "workspace_name ++ \"\\n\"";
    let alpha = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-n", "1", "-T", template]);
    let beta = hive
        .repo(1)
        .jj(&["op", "log", "--no-graph", "-n", "1", "-T", template]);
    assert_eq!(
        (alpha.as_str(), beta.as_str()),
        ("default@\n", "alpha/default@\n")
    );
}

/// A machine that misses many updates while doing its own work catches up with one merge.
#[test]
fn long_offline_machine_catches_up() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for i in 0..10 {
        hive.commit(0, &format!("a{i}"), &format!("alpha {i}"));
        hive.hive.sync(0).unwrap();
    }
    for i in 0..5 {
        hive.commit(1, &format!("b{i}"), &format!("beta {i}"));
    }
    hive.sync();
    hive.assert_converged();
    assert_eq!(
        hive.visible(1)
            .iter()
            .filter(|c| c.contains(" alpha ") || c.contains(" beta "))
            .count(),
        15
    );
}

/// `jj op abandon` rewrites operations the hub already accepted. Until it can be
/// replicated, the node must stop rather than reintroduce or duplicate history.
#[test]
fn op_abandon_pauses_replication() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    hive.repo(0).jj(&["op", "abandon", "..@-"]);
    let err = hive.try_sync().unwrap_err();
    assert!(format!("{err:#}").contains("op abandon"), "{err:#}");
}

/// The same when this machine's latest operation is a realization of another machine's:
/// `jj op abandon` rewrites the realizations above what it abandons, and they still name
/// their canonical operations.
#[test]
fn op_abandon_under_a_realized_head_pauses_replication() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "alpha 1");
    hive.sync();
    hive.commit(1, "b", "beta 1");
    hive.sync();
    hive.repo(0).jj(&["op", "abandon", "..@-"]);
    let err = hive.try_sync().unwrap_err();
    assert!(format!("{err:#}").contains("op abandon"), "{err:#}");
}

/// Abandoning only history from before a machine joined rewrites the operations since
/// into ones that canonicalize as before, so replication carries on, even once garbage
/// collection has removed the original join point.
#[test]
fn op_abandon_of_pre_join_history_is_harmless() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    for i in 0..3 {
        alpha.write_file(&format!("pre{i}"), "x");
        alpha.jj(&["commit", "-m", &format!("before joining {i}")]);
    }
    let join_point = alpha.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let mut hive = Fixture::join(env, vec![alpha, beta]);
    hive.commit(0, "post", "alpha after joining");
    hive.sync();
    hive.commit(1, "bpost", "beta after joining");
    hive.sync();
    hive.repo(0)
        .jj(&["op", "abandon", &format!("..{join_point}-")]);
    hive.repo(0).jj(&["util", "gc", "--expire=now"]);
    hive.commit(1, "b2", "beta again");
    hive.commit(0, "a2", "alpha again");
    hive.sync();
    hive.assert_converged();
}

/// A long-running command based on an old operation (here forced with `--at-op`) creates a
/// concurrent operation on the same machine; jj merges it locally, and the merge
/// replicates like any other.
#[test]
fn concurrent_operation_on_one_machine() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "base", "base");
    let old_op = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    hive.commit(0, "later", "later");
    let base = hive.commit_id(0, "base");
    hive.repo(0).jj(&[
        "--at-op",
        &old_op,
        "bookmark",
        "create",
        "stale-view",
        "-r",
        &base,
    ]);
    hive.sync();
    hive.assert_converged();
    assert!(hive.bookmarks(1).contains_key("stale-view@"));
}

/// A node that restarts loses its protocol state and its translation cache; it must
/// recover both and converge without duplicating anything.
#[test]
fn restart_with_lost_cache() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "before restart");
    hive.sync();
    std::fs::remove_file(hive.repo(1).repo_path().join("musubi/translation")).unwrap();
    hive.hive.restart(1);
    hive.commit(0, "b", "after restart");
    hive.commit(1, "c", "beta after restart");
    hive.sync();
    hive.assert_converged();
}

/// The hub restarts between one machine's push and another's fetch; its store is durable.
#[test]
fn hub_restart_between_push_and_fetch() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "before the restart");
    hive.hive.sync(0).unwrap();
    hive.hive.restart_hub().unwrap();
    hive.sync();
    hive.assert_converged();
    assert!(
        hive.visible(1)
            .iter()
            .any(|c| c.ends_with("before the restart"))
    );
}

/// A repository joins with its whole operation history rather than a join operation;
/// the other machine's op log then includes that history.
#[test]
fn joining_with_full_history() {
    use musubi_hub::store::Backend;
    use musubi_jj::node::NodeRepo;
    use musubi_sync::hive::Hive;

    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    for i in 0..3 {
        alpha.write_file(&format!("f{i}"), "x");
        alpha.jj(&["commit", "-m", &format!("history {i}")]);
    }
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    hive.add(NodeRepo::open(&alpha.repo_path(), &alpha.settings()).unwrap())
        .unwrap();
    let mut beta_node = NodeRepo::open(&beta.repo_path(), &beta.settings()).unwrap();
    beta_node
        .create_join_operation("musubi: beta joins")
        .unwrap();
    hive.add(beta_node).unwrap();
    let mut fixture = Fixture {
        env,
        repos: vec![alpha, beta],
        hive,
    };
    fixture.sync();
    fixture.assert_converged();
    let ops = fixture.repo(1).jj(&[
        "op",
        "log",
        "--no-graph",
        "-T",
        "description.first_line() ++ \"\\n\"",
    ]);
    assert!(
        ops.contains("commit"),
        "alpha's history should be in beta's op log:\n{ops}"
    );
}

/// Two fresh, empty repositories make a hive.
#[test]
fn empty_repositories_make_a_hive() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.assert_converged();
    hive.commit(1, "first", "first commit in the hive");
    hive.sync();
    hive.assert_converged();
}

/// jj 0.46 bug: one machine abandons a commit directly on the root while another makes it a
/// parent of a merge commit. Reconciling them would rebase the merge onto the root, which
/// jj's git backend refuses, so every jj command on the merging machine would fail. musubi
/// doesn't apply the other machine's operation there: its sync error names the problem and
/// the recovery, and jj keeps working. When jj fixes this, this test fails.
#[test]
fn root_parent_merge_bug_is_explained() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for message in ["x", "y"] {
        hive.repo(0).jj(&["new", "root()"]);
        hive.commit(0, message, message);
    }
    hive.sync();
    let (x, y) = (hive.commit_id(0, "x"), hive.commit_id(0, "y"));
    hive.repo(0).jj(&["abandon", &x]);
    hive.repo(1).jj(&["new", &x, &y, "-m", "merge"]);
    let err = hive.try_sync().unwrap_err();
    let message = format!("{err:#}");
    assert!(
        message.contains("root commit as one of the parents") && message.contains("op revert"),
        "{message}"
    );
    for machine in [0, 1] {
        hive.repo(machine).jj(&["status"]);
    }
}
