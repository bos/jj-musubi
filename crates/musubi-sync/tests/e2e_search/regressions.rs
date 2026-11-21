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

/// Reduced by hand from a failure the search found (#167), with `late_commands_after_trims`
/// and then `op_abandon`, with every fix for #167 so far in place. After a full trim, which
/// its node takes, alpha runs a late command on its trim's op head; beta renames its
/// workspace and syncs; alpha trims again and syncs, runs a late command on the first late
/// one, which brings it back, and abandons that first late operation. The hive then gives
/// alpha beta's renamed workspace as its own: alpha lists `beta/third` as its own, and beta
/// lists `alpha/beta/third`. Without the rename, the second trim or the abandon, it passed;
/// the search's stepped-back clock, merges and third machine weren't needed.
#[test]
fn e2e_abandoning_a_late_command_after_a_rename_keeps_others_workspaces_theirs() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    let first = world.trim_to_unpublished_root(0);
    world.sync(0);
    let message = world.message(0);
    world.late_command(0, &first, &["new", "-m", &message], false);
    let late = world.late_ops(0)[0].id.clone();
    world.rename_workspace(1, 0, "third");
    world.sync(1);
    world.trim_to_unpublished_root(0);
    world.sync(0);
    let message = world.message(0);
    world.late_command(0, &late, &["new", "-m", &message], false);
    world.op_abandon(0, &late);
    world.converge();
}

/// The commit of the workspace that machine `m` shows as `name` at its operation `op`.
fn working_copy_at(world: &World, m: usize, op: &str, name: &str) -> crate::view::Commit {
    world
        .view_at(m, op)
        .commits
        .into_iter()
        .find(|commit| commit.working_copies.iter().any(|shown| shown == name))
        .unwrap_or_else(|| panic!("no working copy {name} at {op}"))
}

/// Reduced from a failure of `late_commands_after_trims`. Each machine starts with work
/// bookmarked `main`, which conflicts once they join. Beta trims to the root; alpha takes the
/// trim, whose realization carries the record of `main` alpha's `.git` has (the sync captures
/// that native frontier), trims too, and, before its node handles that (it only notices the
/// trim), abandons its own first commit at the trim's op head. The
/// next command merges, and imports `main` from `.git`, as jj does where both heads changed
/// the record. The import check judges the realization's record by the native frontier
/// captured before alpha took the trim (`Log::ref_operation`): judged by its source parents,
/// which record nothing, it changed the record as no import or export does.
#[test]
fn e2e_late_command_after_taking_a_trim() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: true,
        secondary: true,
    });
    world.trim_to_unpublished_root(1);
    world.sync(1);
    let op = world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    let first = working_copy_at(&world, 0, &op, "second").parents[0].clone();
    world.late_command(0, &op, &["abandon", &first], false);
    world.merge_late_heads(0);
    for m in 0..2 {
        world.check_imports(m);
    }
    world.converge();
}

/// Reduced from a failure of `late_commands_after_trims`. After a full trim, alpha runs late
/// commands with its clock stepped back: one puts its working copy on beta's, and, after
/// another trim, one on the merge abandons beta's commit, which leaves alpha's working copy on
/// the root, so jj writes `.git`'s HEAD unborn. The next command merges, the late head first,
/// and its record of HEAD is the other head's, so it imports HEAD from `.git`, as jj does where
/// both heads wrote HEAD. The import check counts that late command as writing HEAD unborn.
#[test]
fn e2e_late_command_leaving_head_unborn() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    let op = world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    let beta = working_copy_at(&world, 0, &op, "beta/beta").id;
    world.late_command(0, &op, &["new", &beta], true);
    world.merge_late_heads(0);
    let merge = world.late_ops(0)[0].id.clone();
    world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    world.late_command(0, &merge, &["abandon", &beta], true);
    world.jj(0, &["status"]);
    for m in 0..2 {
        world.check_imports(m);
    }
    world.converge();
}

/// Reduced from a failure of `late_commands_after_trims`: a gap in the reference, not a bug in
/// musubi, which this pins until the reference can witness the case. Beta renames its secondary
/// workspace without syncing; alpha trims to the root and, before its node handles that,
/// describes beta's working-copy commit twice at the trim's op head, merging between. beta's
/// old name comes back at alpha's later rewrite, beside the new one, as jj's merge of views
/// gives it (checked by hand). The reference can't witness that name: after alpha's trim the
/// canonical views leave out the absent beta's working copies, two rewrites of one commit make
/// the bindings it follows ambiguous at a merge, and certifying them needs jj's replay of
/// alpha's native merges for an absent copy's working copies. Once it can, this fails: make it
/// a plain regression.
#[test]
#[should_panic(expected = "beta lists workspaces")]
fn e2e_late_rewrites_of_a_renamed_workspace() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: true,
    });
    world.rename_workspace(1, 1, "default");
    let op = world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    let second = working_copy_at(&world, 0, &op, "beta/second").id;
    for _ in 0..2 {
        if world.op_heads(0).len() > 1 {
            world.merge_late_heads(0);
        }
        let message = world.message(0);
        world.late_command(0, &op, &["describe", &second, "-m", &message], false);
    }
    world.converge();
}

/// Reduced from a failure of `late_commands_after_trims`. After a full trim, alpha's late
/// command puts its working copy on its secondary workspace's commit; after another trim, a
/// late command on the merge abandons that commit, leaving `.git`'s HEAD unborn, while beta
/// renames and forgets a workspace. The next `jj` command merges and finds HEAD unborn: its
/// "import git head" checks nothing out, and resets HEAD to the working copy's parent, writing
/// `.git` and recording that (`jj_resets_an_unborn_head_it_imports`). The import check takes
/// what that import took from `.git` as the unborn HEAD, not the record it wrote.
#[test]
fn e2e_late_command_then_import_of_an_unborn_head() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: true,
    });
    let op = world.trim_to_unpublished_root(0);
    world.sync_partial(0, 2, None);
    let second = working_copy_at(&world, 0, &op, "second").id;
    world.late_command(0, &op, &["new", &second], true);
    world.merge_late_heads(0);
    let merge = world.late_ops(0)[0].id.clone();
    world.rename_workspace(1, 1, "work");
    world.sync(1);
    world.sync(0);
    world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    world.late_command(0, &merge, &["abandon", &second], true);
    world.forget_workspace(1, 1);
    world.sync(1);
    world.trim_to_unpublished_root(0);
    for m in 0..2 {
        world.check_imports(m);
    }
    world.converge();
}

/// Found by `late_commands_after_trims` with the fixes for #167 then in place, reduced by hand.
/// Beta trims and runs two late commands on its trim's op head; alpha commits; beta trims again,
/// runs another on the first trim's op head, and a late `jj new` on a merge of its first ones.
/// Alpha then trims, and after another machine joins and works, trims again, runs a late `jj new`
/// on beta's working copy at its first trim's op head, a late describe of beta's first late
/// commit at its second, and abandons that describe. The hive then gave alpha beta's workspace,
/// `beta/default`, as its own, until a name was taken as another machine's only when jj's
/// description said the command added it. Each of the join, the late `jj new` and the abandon is
/// needed; the joining machine's name isn't.
#[test]
fn e2e_abandoning_a_late_describe_after_a_join_keeps_others_workspaces_theirs() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Default,
        prejoin: false,
        secondary: true,
    });
    let find = |world: &World, m: usize, op: &str, name: &str| working_copy_at(world, m, op, name);
    let merge = |world: &mut World, m: usize| {
        if world.op_heads(m).len() > 1 {
            world.merge_late_heads(m);
        }
    };
    let describe = |world: &mut World, m: usize, op: &str, commit: &str, back: bool| {
        let message = world.message(m);
        world.late_command(m, op, &["describe", commit, "-m", &message], back);
    };
    // Beta: two trims, with late commands.
    let first = world.trim_to_unpublished_root(1);
    world.sync_partial(1, 1, None);
    let late = find(&world, 1, &first, "default");
    world.late_command(
        1,
        &first,
        &[
            "bookmark",
            "set",
            "topic",
            "-r",
            &late.id,
            "--allow-backwards",
        ],
        false,
    );
    merge(&mut world, 1);
    describe(&mut world, 1, &first, &late.parents[0], true);
    merge(&mut world, 1);
    let merges: Vec<String> = world
        .late_ops(1)
        .into_iter()
        .filter(|op| op.merge)
        .map(|op| op.id)
        .collect();
    let file = world::FILES.iter().position(|f| *f == "dir/c.txt").unwrap();
    world.commit(0, 0, file);
    world.sync(0);
    world.trim_to_unpublished_root(1);
    world.sync(1);
    let second = find(&world, 1, &first, "alpha/second").id;
    describe(&mut world, 1, &first, &second, false);
    merge(&mut world, 1);
    let alpha = find(&world, 1, &merges[0], "alpha/default").id;
    world.late_command(1, &merges[0], &["new", &alpha], true);
    world.observe(0);
    // Alpha: a trim, another machine joins and works, and another trim, with late commands.
    let a1 = world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    world.join_existing_copy(2);
    world.sync(2);
    world.commit(2, 0, 0);
    world.sync(2);
    let a2 = world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    let beta = find(&world, 0, &a1, "beta/default").id;
    world.late_command(0, &a1, &["new", &beta], true);
    merge(&mut world, 0);
    describe(&mut world, 0, &a2, &late.id, false);
    merge(&mut world, 0);
    let described = world
        .late_ops(0)
        .into_iter()
        .find(|op| !op.merge)
        .unwrap()
        .id;
    world.op_abandon(0, &described);
    world.converge();
}

/// Found by `late_commands_after_trims` with every fix for #167 then on main, reduced by hand.
/// Alpha trims and, with its clock stepped back, describes beta's secondary working copy late;
/// gamma renames its workspace without syncing. Alpha trims again and restores late to that
/// describe, then, with the clock stepped back, describes its own working copy late; gamma syncs.
/// Alpha trims a third time, taking gamma's rename, restores late to its first restore and
/// abandons late its rewritten working copy, both with the clock stepped back, and then runs `jj
/// op abandon` of that second restore and of its second late describe. Before lysvtvvk, after the
/// syncs the hive gave alpha gamma's renamed workspace, `gamma/gamma`, as its own, and gamma's
/// own view had its old name back, so its working-copy state named a workspace its view lacked:
/// its next command failed with "Workspace `gamma` doesn't have a working-copy commit". Dropping
/// the rename, or either `jj op abandon`, made it pass. On one machine jj does the same when an
/// undo crosses another workspace's rename (races.md, "Known jj limitations"), which that row
/// says can't happen across machines.
#[test]
fn e2e_abandoning_late_restores_after_a_rename_keeps_a_machines_own_workspace() {
    let mut world = World::new(Setup {
        nodes: 3,
        naming: Naming::Default,
        prejoin: false,
        secondary: true,
    });
    let newest = |world: &World, merge: bool| {
        world
            .late_ops(0)
            .into_iter()
            .find(|op| op.merge == merge)
            .unwrap()
            .id
    };
    let merge = |world: &mut World| {
        if world.op_heads(0).len() > 1 {
            world.merge_late_heads(0);
        }
    };
    let describe = |world: &mut World, op: &str, commit: &str, back: bool| {
        let message = world.message(0);
        world.late_command(0, op, &["describe", commit, "-m", &message], back);
    };
    let first = world.trim_to_unpublished_root(0);
    world.sync_partial(0, 1, None);
    let second = working_copy_at(&world, 0, &first, "beta/second").id;
    describe(&mut world, &first, &second, true);
    let described = newest(&world, false);
    merge(&mut world);
    let merged = newest(&world, true);
    world.rename_workspace(2, 0, "gamma");
    world.trim_to_unpublished_root(0);
    world.sync(0);
    world.late_command(0, &merged, &["op", "restore", &described], false);
    let restored = newest(&world, false);
    merge(&mut world);
    let own = working_copy_at(&world, 0, &merged, "default");
    describe(&mut world, &merged, &own.id, true);
    let described_own = newest(&world, false);
    merge(&mut world);
    let merged_again = newest(&world, true);
    world.sync(2);
    world.trim_to_unpublished_root(0);
    world.sync_partial(0, 0, None);
    world.late_command(0, &merged_again, &["op", "restore", &restored], true);
    let restored_again = newest(&world, false);
    merge(&mut world);
    let last = newest(&world, true);
    let rewritten = world
        .view_at(0, &last)
        .commits
        .into_iter()
        .find(|c| c.change == own.change && c.id != own.id)
        .unwrap()
        .id;
    world.late_command(0, &last, &["abandon", &rewritten], true);
    merge(&mut world);
    world.op_abandon(0, &restored_again);
    world.op_abandon(0, &described_own);
    for _ in 0..2 {
        world.sync(0);
        world.sync(1);
    }
    world.sync_partial(1, 3, None);
    world.sync(2);
    let message = world.message(2);
    world.jj(2, &["new", "-m", &message]);
    world.converge();
}

/// Reduced from a failure of `late_commands_after_trims` (finding G): a gap in the import check,
/// which this pins until it closes. After a full trim, beta runs a late `jj new` on alpha's
/// working copy, and on that, with the clock stepped back, a late abandon of the same commit,
/// which leaves beta's working copy on the root and `.git`'s HEAD unborn; then `jj op abandon` of
/// that late abandon. Alpha commits and syncs. Beta trims again and, with the clock stepped back,
/// abandons late the parent of its working copy at that trim's op head, leaving HEAD unborn
/// again, then runs `jj op abandon` of that op head. The next import takes the unborn HEAD, as jj
/// does where both heads wrote it. But `jj op abandon` has reparented the late command that wrote
/// it onto the root, where its absent record looks unchanged, so the check counts no writer of it
/// on that side of the merge and blames the other. Judging ancestry by the parents it judges
/// records by (captured originals, jj's and musubi's rewrites of merges above an abandon,
/// `musubi.reconciled-from`) would close it. Once it does, this fails: make it a plain
/// regression.
#[test]
#[should_panic(expected = "taking HEAD absent for jj's record of it")]
fn e2e_abandons_below_a_late_unborn_head() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    let merge = |world: &mut World| {
        if world.op_heads(1).len() > 1 {
            world.merge_late_heads(1);
        }
    };
    let first = world.trim_to_unpublished_root(1);
    world.sync_partial(1, 2, None);
    let alpha = working_copy_at(&world, 1, &first, "alpha/alpha").id;
    world.late_command(1, &first, &["new", &alpha], false);
    let on_alpha = world.late_ops(1)[0].id.clone();
    merge(&mut world);
    world.late_command(1, &on_alpha, &["abandon", &alpha], true);
    let abandoned = world.late_ops(1)[0].id.clone();
    merge(&mut world);
    world.op_abandon(1, &abandoned);
    let file = world::FILES.iter().position(|f| *f == "dir/c.txt").unwrap();
    world.commit(0, 0, file);
    world.sync(0);
    let second = world.trim_to_unpublished_root(1);
    world.sync_partial(1, 2, None);
    let below = working_copy_at(&world, 1, &second, "beta").parents[0].clone();
    world.late_command(1, &second, &["abandon", &below], true);
    world.op_abandon(1, &second);
    for m in 0..2 {
        world.check_imports(m);
    }
    world.converge();
}
