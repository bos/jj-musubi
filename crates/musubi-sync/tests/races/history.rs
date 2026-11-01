//! Operation-log level races: undo, op abandon, offline machines, restarts.

use musubi_sync::node::history_lost;
use musubi_testutil::TestEnv;

use crate::fixture::Fixture;
use crate::fixture::add_node;

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

/// `jj op abandon` of operations the hub accepted replicates: the other machine drops them
/// too, the repository staying as it was, and the hive converges.
#[test]
fn op_abandon_replicates() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    hive.assert_converged();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", "..@-"]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
    }
    assert!(hive.visible(1).iter().any(|c| c.ends_with("second")));
    hive.commit(1, "c", "third");
    hive.sync();
    hive.assert_converged();
    assert!(hive.visible(0).iter().any(|c| c.ends_with("third")));
}

/// The same when this machine's latest operation is a realization of another machine's:
/// `jj op abandon` rewrites the realizations above what it abandons, and they still name
/// their canonical operations.
#[test]
fn op_abandon_under_a_realized_head_replicates() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "alpha 1");
    hive.sync();
    hive.commit(1, "b", "beta 1");
    hive.sync();
    hive.assert_converged();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", "..@-"]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
    }
    assert!(hive.visible(0).iter().any(|c| c.ends_with("beta 1")));
}

/// The same for this machine's own operation below its merge with another machine's work,
/// made concurrently: jj rewrites every operation above the abandoned one that isn't below it,
/// putting even the other machine's realized operations on its parent, and musubi puts them
/// back. Noticed only after the settings reconciled before the sync had read the op heads, the
/// abandon left those reading an operation jj had rewritten: a realization no longer on its
/// canonical operation's parents, and the sync stopped for good.
#[test]
fn op_abandon_below_a_merge_with_concurrent_work_replicates() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "alpha 1");
    hive.sync();
    hive.commit(0, "c", "alpha's concurrent work");
    hive.commit(1, "b1", "beta 1");
    let abandoned = op_log(hive.repo(1))[0].clone();
    assert!(abandoned.1.starts_with("commit "), "{abandoned:?}");
    hive.commit(1, "b2", "beta 2");
    hive.sync();
    // jj merged alpha's realized work with beta's, above the abandoned operation.
    assert!(
        op_log(hive.repo(1))
            .iter()
            .take_while(|(id, _)| *id != abandoned.0)
            .any(|(_, description)| description == "reconcile divergent operations")
    );
    hive.repo(1).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
        let visible = hive.visible(machine);
        for work in ["alpha 1", "alpha's concurrent work", "beta 1", "beta 2"] {
            assert!(
                visible.iter().any(|c| c.ends_with(work)),
                "{machine}: {work}"
            );
        }
    }
}

/// Each operation `repo`'s op log shows, newest first: its id and description.
fn op_log(repo: &musubi_testutil::TestRepo) -> Vec<(String, String)> {
    repo.jj(&[
        "op",
        "log",
        "--no-graph",
        "-T",
        "id ++ \" \" ++ description.first_line() ++ \"\\n\"",
    ])
    .lines()
    .map(|line| {
        let (id, description) = line.split_once(' ').unwrap_or((line, ""));
        (id.to_owned(), description.to_owned())
    })
    .collect()
}

/// The newest operation below `repo`'s head that made a commit, described by its id.
fn commit_op(repo: &musubi_testutil::TestRepo) -> (String, String) {
    op_log(repo)
        .into_iter()
        .skip(1)
        .find(|(_, description)| description.starts_with("commit "))
        .expect("an operation that made a commit")
}

/// Whether `repo`'s op log has an operation described as `description`.
fn has_operation(repo: &musubi_testutil::TestRepo, description: &str) -> bool {
    op_log(repo).iter().any(|(_, d)| d == description)
}

/// Two machines abandon different operations of the hive's at once: whichever supersede the
/// hub takes first, the other is published again after it, and every machine drops both.
#[test]
fn concurrent_op_abandons_on_two_machines() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for i in 0..4 {
        hive.commit(0, &format!("a{i}"), &format!("alpha {i}"));
    }
    hive.sync();
    hive.assert_converged();
    let (alpha, beta) = (op_log(hive.repo(0)), op_log(hive.repo(1)));
    let (first, second) = (alpha[2].clone(), beta[4].clone());
    assert!(first.1.starts_with("commit") && second.1.starts_with("commit"));
    assert_ne!(first.1, second.1);
    hive.repo(0).jj(&["op", "abandon", &first.0]);
    hive.repo(1).jj(&["op", "abandon", &second.0]);
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.hive.hub.store().records().len(), 2);
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &first.1),
            "{machine}: {first:?}"
        );
        assert!(
            !has_operation(hive.repo(machine), &second.1),
            "{machine}: {second:?}"
        );
    }
    assert!(hive.visible(1).iter().any(|c| c.ends_with("alpha 3")));
}

/// A `jj` command that loaded the repository before the abandon arrived writes on an
/// operation it rewrote: its work syncs, on the rewritten history, and the abandoned
/// operations don't come back.
#[test]
fn a_jj_command_in_flight_during_the_rewrite() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    let stale = op_log(hive.repo(1))[0].0.clone();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    hive.assert_converged();
    let second = hive.commit_id(1, "second");
    hive.repo(1).jj(&[
        "--at-op", &stale, "bookmark", "create", "late", "-r", &second,
    ]);
    hive.sync();
    hive.assert_converged();
    assert!(hive.bookmarks(0).contains_key("late@"));
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
    }
}

/// A `jj` command that writes on the operation another machine abandoned while this machine
/// takes the abandon, between the sync step that prepares to take it and the next, which
/// gives the command's operation a canonical form on the abandoned one. Taking the abandon
/// renames that operation too: its work syncs, on the rewritten history, and the abandoned
/// operation doesn't come back.
#[test]
fn a_jj_command_while_taking_an_abandon() {
    use musubi_core::node::Step;

    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.repo(0)
        .jj(&["bookmark", "create", "dropped", "-r", "@-"]);
    let dropped = op_log(hive.repo(0))[0].0.clone();
    hive.sync();
    hive.commit(0, "b", "second");
    hive.repo(0).jj(&["op", "abandon", &dropped]);
    hive.hive.sync(0).unwrap();

    // The step that prepares to take the abandon, which drops this machine's op head, and
    // realizes the first of the hub's operations after it.
    hive.hive.fetch(1).unwrap();
    let member = &mut hive.hive.members[1];
    let step = member.core.step(&mut member.adapter).unwrap();
    assert!(matches!(step, Step::Realized(_)), "{step:?}");
    hive.commit(1, "c", "on the abandoned operation");
    hive.hive.sync(1).unwrap();

    hive.sync();
    hive.assert_converged();
    let work = "on the abandoned operation";
    assert!(hive.visible(0).iter().any(|c| c.ends_with(work)));
    for machine in 0..2 {
        assert!(
            !op_log(hive.repo(machine))
                .iter()
                .any(|(_, d)| d.starts_with("create bookmark dropped")),
            "{machine}"
        );
    }
}

/// A machine offline while another abandons operations, which keeps working, takes the
/// abandon when it comes back: its work syncs on the rewritten history.
#[test]
fn an_offline_machine_comes_back_after_an_abandon() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    let abandoned = commit_op(hive.repo(0));
    hive.commit(2, "g", "offline work");
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    for _ in 0..2 {
        hive.hive.sync(0).unwrap();
        hive.hive.sync(1).unwrap();
    }
    hive.sync();
    hive.assert_converged();
    assert!(hive.visible(0).iter().any(|c| c.ends_with("offline work")));
    for machine in 0..3 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
    }
}

/// The hub restarts between taking a supersede and the other machine fetching it, and before
/// it: its records are on disk with its heads.
#[test]
fn hub_restarts_during_and_after_a_rewrite() {
    for after in [false, true] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        hive.commit(0, "a", "first");
        hive.commit(0, "b", "second");
        hive.sync();
        let abandoned = commit_op(hive.repo(0));
        hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
        if after {
            hive.hive.sync(0).unwrap();
        }
        hive.hive.restart_hub().unwrap();
        hive.sync();
        hive.assert_converged();
        assert_eq!(hive.hive.hub.store().records().len(), 1, "after: {after}");
        for machine in 0..2 {
            assert!(
                !has_operation(hive.repo(machine), &abandoned.1),
                "{machine}"
            );
        }
    }
}

/// The hub loses the supersede, going back to before it, or is made again empty, after the
/// other machine took it: the machines that have the record publish it again, and the hive
/// converges without the abandoned operations.
#[test]
fn hub_goes_back_or_is_remade_after_a_rewrite() {
    for remade in [false, true] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        hive.commit(0, "a", "first");
        hive.commit(0, "b", "second");
        hive.sync();
        let seq = hive.hive.hub.store().head().0;
        let abandoned = commit_op(hive.repo(0));
        hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
        hive.sync();
        hive.assert_converged();
        if remade {
            hive.hive.remake_hub().unwrap();
        } else {
            hive.hive.hub_goes_back(seq).unwrap();
        }
        hive.commit(1, "c", "after");
        hive.sync();
        hive.assert_converged();
        assert_eq!(hive.hive.hub.store().records().len(), 1, "remade: {remade}");
        for machine in 0..2 {
            assert!(
                !has_operation(hive.repo(machine), &abandoned.1),
                "{machine}"
            );
        }
        assert!(hive.visible(0).iter().any(|c| c.ends_with("after")));
    }
}

/// A machine abandons twice before it syncs: both abandons reach every machine.
#[test]
fn two_op_abandons_before_a_sync() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for i in 0..3 {
        hive.commit(0, &format!("a{i}"), &format!("alpha {i}"));
    }
    hive.sync();
    let first = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &first.0]);
    let second = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &second.0]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(!has_operation(hive.repo(machine), &first.1), "{machine}");
        assert!(!has_operation(hive.repo(machine), &second.1), "{machine}");
    }
}

/// `jj util gc` removes what an abandon left unreachable before musubi sees it: the abandon
/// still reaches the other machine.
#[test]
fn op_abandon_then_gc() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.repo(0).jj(&["util", "gc", "--expire=now"]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
    }
}

/// Where the operation a machine last fetched from is out of reach though jj rewrote
/// nothing, which no abandon explains, the machine stops syncing rather than tell the hive
/// to drop what it has.
#[test]
fn an_unexplained_lost_base_pauses_without_dropping() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.hive.sync(0).unwrap();
    // beta has alpha's operation, fetched but not applied.
    hive.hive.fetch(1).unwrap();
    let staged = hive.hive.hub_head();
    std::fs::write(
        hive.repo(1).repo_path().join("musubi/accepted_base"),
        jj_lib::object_id::ObjectId::hex(&staged),
    )
    .unwrap();
    hive.hive.restart(1);
    let err = hive.hive.sync(1).unwrap_err();
    assert!(history_lost(&err), "{err:#}");
    assert!(hive.hive.hub.store().records().is_empty());
}

/// The operation `repo`'s op log shows described as `description`: its id.
fn op_described(repo: &musubi_testutil::TestRepo, description: &str) -> String {
    op_log(repo)
        .into_iter()
        .find(|(_, d)| d == description)
        .unwrap_or_else(|| panic!("no operation described as {description:?}"))
        .0
}

/// The hub loses two records it took, going back, and then takes another machine's first:
/// the machines that took the lost ones publish them again, named as the hub's history now
/// names those operations, and every machine drops all three.
#[test]
fn records_published_again_after_the_hub_took_others() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    for i in 0..4 {
        hive.commit(0, &format!("a{i}"), &format!("alpha {i}"));
    }
    hive.sync();
    hive.assert_converged();
    let seq = hive.hive.hub.store().head().0;
    let commits: Vec<String> = op_log(hive.repo(0))
        .into_iter()
        .skip(1)
        .filter(|(_, d)| d.starts_with("commit "))
        .map(|(_, d)| d)
        .collect();
    let (first, second, theirs) = (&commits[1], &commits[0], &commits[2]);
    // alpha abandons two operations, one after the other, publishing each; beta takes both.
    for abandoned in [first, second] {
        let op = op_described(hive.repo(0), abandoned);
        hive.repo(0).jj(&["op", "abandon", &op]);
        for _ in 0..2 {
            hive.hive.sync(0).unwrap();
            hive.hive.sync(1).unwrap();
        }
    }
    assert_eq!(hive.hive.hub.store().records().len(), 2);
    // The hub loses both; gamma, which saw neither, abandons another and publishes first.
    hive.hive.hub_goes_back(seq).unwrap();
    let op = op_described(hive.repo(2), theirs);
    hive.repo(2).jj(&["op", "abandon", &op]);
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub.store().records().len(), 1);
    hive.sync();
    hive.assert_converged();
    for machine in 0..3 {
        for abandoned in [first, second, theirs] {
            assert!(
                !has_operation(hive.repo(machine), abandoned),
                "{machine}: {abandoned}"
            );
        }
    }
}

/// The same where a machine also abandoned an operation it made after the records the hub
/// lost, on history the other machine's record then drops: published again, it is named as
/// the hive will have it.
#[test]
fn a_later_operation_published_again_after_the_hub_took_others() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    for i in 0..4 {
        hive.commit(0, &format!("a{i}"), &format!("alpha {i}"));
    }
    hive.sync();
    let seq = hive.hive.hub.store().head().0;
    let commits: Vec<String> = op_log(hive.repo(0))
        .into_iter()
        .skip(1)
        .filter(|(_, d)| d.starts_with("commit "))
        .map(|(_, d)| d)
        .collect();
    // gamma's is above alpha's first, so alpha's record renamed it.
    let (first, theirs) = (&commits[2], &commits[0]);
    let op = op_described(hive.repo(0), first);
    hive.repo(0).jj(&["op", "abandon", &op]);
    for _ in 0..2 {
        hive.hive.sync(0).unwrap();
        hive.hive.sync(1).unwrap();
    }
    // alpha makes two more operations, which beta takes, then abandons the first of them.
    hive.commit(0, "a4", "alpha 4");
    hive.commit(0, "a5", "alpha 5");
    for _ in 0..2 {
        hive.hive.sync(0).unwrap();
        hive.hive.sync(1).unwrap();
    }
    let later = op_log(hive.repo(0))
        .into_iter()
        .skip(1)
        .find(|(_, d)| d.starts_with("commit "))
        .unwrap();
    hive.repo(0).jj(&["op", "abandon", &later.0]);
    hive.hive.hub_goes_back(seq).unwrap();
    let op = op_described(hive.repo(2), theirs);
    hive.repo(2).jj(&["op", "abandon", &op]);
    hive.hive.sync(2).unwrap();
    // beta, which kept the later operation, publishes before alpha.
    hive.hive.sync(1).unwrap();
    hive.sync();
    hive.assert_converged();
    for machine in 0..3 {
        for abandoned in [first, theirs, &later.1] {
            assert!(
                !has_operation(hive.repo(machine), abandoned),
                "{machine}: {abandoned}"
            );
        }
    }
}

/// The operation the working copy at `path` last recorded, read without updating it.
fn recorded_op(repo: &musubi_testutil::TestRepo, path: &std::path::Path) -> String {
    use jj_lib::workspace::WorkspaceLoaderFactory as _;
    let workspace = jj_lib::workspace::DefaultWorkspaceLoaderFactory
        .create(path)
        .unwrap()
        .load(
            &repo.settings(),
            &jj_lib::default_backend_factories::default_backend_factories(),
            &jj_lib::default_backend_factories::default_working_copy_factories(),
        )
        .unwrap();
    jj_lib::object_id::ObjectId::hex(workspace.working_copy().operation_id())
}

/// Every workspace's working copy, on every machine, records an operation still in its
/// history once an abandon has rewritten it, as jj's own `jj op abandon` leaves the
/// workspace it runs in: otherwise jj takes the working copy for a sibling of the history
/// the next time its commit changes.
#[test]
fn op_abandon_moves_every_workspace() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let second = hive.repo(0).path().with_file_name("alpha-second");
    hive.repo(0)
        .jj(&["workspace", "add", second.to_str().unwrap()]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    // Each working copy records an operation above the one alpha abandons.
    hive.repo(0).jj(&["-R", second.to_str().unwrap(), "status"]);
    hive.repo(1).jj(&["status"]);
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    let workspaces = [
        (0, hive.repo(0).path().to_owned()),
        (0, second),
        (1, hive.repo(1).path().to_owned()),
    ];
    for (machine, path) in workspaces {
        let repo = hive.repo(machine);
        let recorded = recorded_op(repo, &path);
        let ops = repo.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-T",
            "id ++ \"\\n\"",
        ]);
        assert!(
            ops.lines().any(|id| id == recorded),
            "{} records {recorded}, not in its history",
            path.display()
        );
    }
    hive.assert_converged();
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

/// The hub restarts between one machine's push and another's fetch; its store is on disk.
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
    use musubi_jj::node::NodeRepo;
    use musubi_jj::objects::Backend;
    use musubi_sync::hive::Hive;

    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    for i in 0..3 {
        alpha.write_file(&format!("f{i}"), "x");
        alpha.jj(&["commit", "-m", &format!("history {i}")]);
    }
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Git).unwrap();
    let alpha_node = NodeRepo::open(&alpha.repo_path(), &alpha.settings()).unwrap();
    add_node(&mut hive, &env, alpha_node);
    let mut beta_node = NodeRepo::open(&beta.repo_path(), &beta.settings()).unwrap();
    beta_node
        .create_join_operation("musubi: beta joins")
        .unwrap();
    add_node(&mut hive, &env, beta_node);
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
