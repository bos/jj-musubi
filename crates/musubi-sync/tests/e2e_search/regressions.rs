//! Scripted end-to-end tests: fixed sequences of actions on real repositories, each pinning a
//! case the generated search (`main.rs`) is unlikely to line up by itself, or the evidence its
//! checks rely on. They run in the default suite and need no seed, so a failure here is the
//! same on every run.

use crate::reference;
use crate::world;
use crate::world::Naming;
use crate::world::Setup;
use crate::world::World;

/// After a trim, the workspace names the hive shows match what native jj shows: a realized
/// merge whose authenticated parents and local base let jj witness a restored name. A
/// realization's marker neither certifies that name nor disqualifies its independently checked
/// replay (docs/internals/testing.md, "Generated end-to-end tests").
#[test]
fn e2e_workspace_names_after_trim_match_native_jj() {
    let mut world = World::new(Setup {
        nodes: 3,
        naming: Naming::SharedHostname,
        prejoin: true,
        secondary: false,
    });
    world.restart(2);
    world.trim_below_accepted_push(1);
    world.sync(0);
    world.trim_below_accepted_forget(0, 1);
    world.sync(2);
    world.rename_workspace(0, 0, "alpha");
    let view = world.observe(0);
    world.raw_jj(
        0,
        &[
            "--ignore-working-copy",
            "bookmark",
            "list",
            "-T",
            r#"if(!remote && present, name ++ "\n")"#,
        ],
    );
    let target = view
        .commits
        .iter()
        .find(|commit| commit.working_copies.iter().any(|name| name == "alpha"))
        .unwrap()
        .id
        .clone();
    world.jj(0, &["bookmark", "create", "topic", "-r", &target]);
    let view = world.observe(1);
    let prejoin = view
        .commits
        .iter()
        .find(|commit| commit.subject == "pre-join work on beta")
        .unwrap();
    let parent = view
        .commits
        .iter()
        .find(|commit| commit.subject.is_empty() && commit.parents == [prejoin.id.clone()])
        .unwrap()
        .id
        .clone();
    world.jj(1, &["new", &parent]);
    world.forget_copy(2, 0);
    let commit = world
        .observe(0)
        .commits
        .into_iter()
        .find(|commit| commit.subject == "pre-join work on beta")
        .unwrap()
        .id;
    let description = world.message(0);
    world.jj(0, &["describe", &commit, "-m", &description]);
    world.restart_hub();
    world.an_hour_passes();
    let foreign = world.foreign_workspace_names(0)[0].clone();
    world.jj(0, &["workspace", "forget", &foreign]);
    world.converge();
    assert!(world.logical_extras[0].contains("default"));
}

/// Exercise the trim rule's history bookkeeping and independent jj replay, including the
/// joins that ordinary generated single-operation abandonment leaves in place.
#[test]
fn e2e_trim_below_accepted_push() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.trim_below_accepted_push(0);
    world.converge();
}

/// The generated forget/trim rule retains the independent import and history checks.
#[test]
fn e2e_trim_below_accepted_forget() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.trim_below_accepted_forget(0, 1);
    world.converge();
}

/// `late_command_after_trim` at its simplest: the node only notices the trim before a `jj
/// new` lands on jj's op head from before it, as in
/// `a_late_command_after_a_trim_to_the_root_keeps_others_workspaces_theirs`. The checks must
/// still find each machine's workspaces its own.
#[test]
fn e2e_late_command_after_trim() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.commit(0, 0, 0);
    world.commit(1, 0, 1);
    world.sync(1);
    let op = world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    let message = world.message(0);
    world.jj_at_op(0, &op, &["new", "-m", &message]);
    world.converge();
}

#[test]
fn e2e_git_change_while_taking_a_trim() {
    for forward in [false, true] {
        let mut world = World::new(Setup {
            nodes: 2,
            naming: Naming::Own,
            prejoin: false,
            secondary: false,
        });
        world.commit(1, 0, 0);
        world.jj(1, &["bookmark", "create", "x", "-r", "@-"]);
        world.converge();
        world.trim_below_accepted_push(0);
        world.sync_realizing(1, 1);
        if forward {
            world.jj(1, &["bookmark", "set", "x", "-r", "@"]);
        } else {
            world.jj(1, &["bookmark", "delete", "x"]);
        }
        world.converge();
    }
}

/// A command above an abandoned merge keeps its own payload when its one parent
/// expands to two. The later, genuine reconciliation must still merge both commands.
#[test]
fn e2e_command_above_dropped_merge() {
    let mut world = World::new(Setup {
        nodes: 4,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    let kept = world.hold_dropped_merge(&[0]);
    world.sync(1);
    world.check_dropped_by(1, &kept);
    let target = |world: &World, m, suffix: &str| {
        world
            .view_at_head(m)
            .commits
            .into_iter()
            .find(|c| c.subject.ends_with(suffix))
            .unwrap()
            .id
    };
    let a = target(&world, 0, "on alpha");
    let b = target(&world, 2, "on gamma");
    world.jj(0, &["bookmark", "set", "both", "-r", &a]);
    world.jj(2, &["bookmark", "set", "both", "-r", &b]);
    world.converge();
    let out = world.raw_jj(0, &["--ignore-working-copy", "bookmark", "list", "both"]);
    assert!(
        out.contains("conflict"),
        "expected both commands' targets: {out}"
    );
    // Trimming to the root preserves the inherited conflict in the surviving command.
    world.trim_below_accepted_push(0);
    world.converge();
}

/// The reference needs operations written before the requested command, and a read that
/// snapshots too: either can be the command whose parent later expands through a drop.
#[test]
fn e2e_records_snapshots_from_commands_and_looking() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.edit(0, 0);
    world.jj(0, &["describe", "-m", "after snapshot"]);
    let store = world.fx.hive.members[0]
        .adapter
        .repo()
        .loader()
        .op_store()
        .clone();
    let read = |hex: &str| {
        let id = jj_lib::op_store::OperationId::try_from_hex(hex).unwrap();
        futures::executor::block_on(store.read_operation(&id)).unwrap()
    };
    let command = read(&world.latest_op_head(0));
    let snapshot = read(&jj_lib::object_id::ObjectId::hex(&command.parents[0]));
    assert_eq!(snapshot.metadata.description, "snapshot working copy");
    for op in [&snapshot, &command] {
        assert!(world.evidence.commands.contains_key(&world::merge_key(op)));
    }
    world.edit(0, 1);
    world.observe(0);
    let snapshot = read(&world.latest_op_head(0));
    assert_eq!(snapshot.metadata.description, "snapshot working copy");
    assert!(
        world
            .evidence
            .commands
            .contains_key(&world::merge_key(&snapshot))
    );
    world.converge();

    // The captured native payload bounds translation even when it itself diverges. Both
    // versions come from the real snapshot/describe interval above, with one change id.
    let source = &world.evidence.commands[&world::merge_key(&command)];
    let mut divergent = source.made.clone();
    divergent
        .head_ids
        .extend(source.base.head_ids.iter().cloned());
    let mut reference = reference::Reference::build(&world);
    assert!(
        reference
            .unexplained_command_changes(&source.base, &divergent, &divergent)
            .is_empty()
    );
    assert!(
        !reference
            .unexplained_command_changes(&source.base, &source.made, &divergent)
            .is_empty()
    );
    let later = futures::executor::block_on(store.read_view(&snapshot.view_id)).unwrap();
    let mut different = source.made.clone();
    different.head_ids.extend(later.head_ids);
    assert!(
        !reference
            .unexplained_command_changes(&source.base, &divergent, &different)
            .is_empty()
    );
}

/// jj's known duplicate-commit bug (docs/internals/races.md, "Known jj limitations"): `musubi
/// forget` writes an operation the working copy isn't recorded at, `jj op abandon` of an
/// earlier one leaves the working copy at its operation's old version, and a commit in the
/// dirty working copy snapshots there and fails merging that with the head. The world runs the
/// command again, as a user would, and the replay judges what both runs wrote as jj's work.
/// Without the rerun, the commit fails with jj's "Newly-created commit ... already exists";
/// once jj is fixed (https://github.com/jj-vcs/jj/pull/10712), the first run succeeds and this
/// fails, so that the rerun is removed.
#[test]
fn e2e_command_rerun_past_jj_duplicate_commit_bug() {
    let mut world = World::new(Setup {
        nodes: 3,
        naming: Naming::Own,
        prejoin: true,
        secondary: false,
    });
    world.jj(1, &["bookmark", "create", "x", "-r", "@-"]);
    let op = world.raw_jj(
        1,
        &[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n1",
            "-T",
            "id",
        ],
    );
    world.jj(1, &["new", "--no-edit", "@", "-m", "child"]);
    world.forget_copy(1, 2);
    world.op_abandon(1, &op);
    world.sync(0);
    world.sync(1);
    world.commit(1, 0, 0);
    assert!(
        world
            .trace
            .iter()
            .any(|line| line.contains(world::JJ_DUPLICATE_COMMIT_BUG)),
        "jj no longer hits its duplicate-commit bug here (jj-vcs/jj#10712): remove the rerun"
    );
    // The failed run left jj's snapshot beside musubi's forget, and the rerun merged them
    // before committing: the capture takes the snapshot and the commit as native commands.
    let store = world.fx.hive.members[1]
        .adapter
        .repo()
        .loader()
        .op_store()
        .clone();
    let read = |id: &jj_lib::op_store::OperationId| {
        futures::executor::block_on(store.read_operation(id)).unwrap()
    };
    let command =
        read(&jj_lib::op_store::OperationId::try_from_hex(world.latest_op_head(1)).unwrap());
    let [merge] = command.parents.as_slice() else {
        panic!("the commit has one parent");
    };
    let merge = read(merge);
    assert_eq!(merge.metadata.description, "reconcile divergent operations");
    let snapshot = merge
        .parents
        .iter()
        .map(read)
        .find(|op| op.metadata.description == "snapshot working copy")
        .expect("the failed run's snapshot");
    for op in [&snapshot, &command] {
        assert!(
            !op.metadata
                .attributes
                .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
        );
        assert!(world.evidence.commands.contains_key(&world::merge_key(op)));
    }
    world.converge();
}

/// A second workspace brings back history that the primary workspace abandoned. After
/// another abandon and a sync, both paths of the resulting merge must use the same local
/// realization of each shared operation, including after translation cache loss.
#[test]
fn e2e_reparenting_a_merge_keeps_one_realization_per_operation() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::SharedHostname,
        prejoin: false,
        secondary: true,
    });
    world.jj(1, &["bookmark", "create", "drop-me", "-r", "@-"]);
    let bookmark = world.op_heads(1).pop().unwrap();
    world.converge();
    world.op_abandon(1, &bookmark);
    world.commit(1, 1, 0);
    world.commit(0, 0, 0);
    world.sync(0);
    world.jj(1, &["describe", "-m", "drop after forgetting"]);
    let describe = world.op_heads(1).pop().unwrap();
    world.jj(1, &["git", "fetch"]);
    world.forget_copy(1, 0);
    world.op_abandon(1, &describe);
    world.sync(1);
    world.jj(1, &["new"]);
    world.sync(0);
    world.restart(0);
    world.converge();
}
