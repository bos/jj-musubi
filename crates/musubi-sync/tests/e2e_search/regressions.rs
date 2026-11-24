//! Scripted end-to-end tests: fixed sequences of actions on real repositories, each pinning a
//! case the generated search (`main.rs`) is unlikely to line up by itself, or the evidence its
//! checks rely on. They run in the default suite and need no seed, so a failure here is the
//! same on every run.

use crate::reference;
use crate::world;
use crate::world::Naming;
use crate::world::Setup;
use crate::world::World;

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

/// jj's import of a branch git moved rewrites, by change id, the commits only its old target
/// reaches, and moves the bookmarks on them, which git didn't move
/// (`record_synthetic_predecessors` in jj-lib's `git.rs`). Git moves `topic` back to its
/// version from before a describe of its parent, so jj moves `feature` back too, and exports
/// it. The import check's own rules explain only `topic`; plain jj, importing the same move,
/// makes the rest (`World::plain_jj_import`). The search failed here at seed 161.
///
/// The controls are records musubi could get wrong: `.git` holding an older version of a
/// rebased commit, the same change with the same description on its parent's same change,
/// with no git move, alone and beside a move git made of another ref. Each fails the check.
#[test]
fn e2e_imports_follow_what_jj_makes_of_a_git_move() {
    let (mut world, a, old_topic) = describe_under_bookmarks();
    world.move_git_branch(0, "topic", &old_topic);
    world.jj(0, &["status"]);
    assert_eq!(
        head_rev(&world, "feature"),
        a,
        "jj takes the move of topic as a rewrite of a"
    );
    world.converge();
    // Without `feature`, only `topic`'s commit, rebased, differs from its older version.
    let (b, a) = (old_topic.id, head_rev(&world, "feature"));
    world.jj(0, &["bookmark", "delete", "feature"]);
    world.jj(0, &["describe", "-r", &a, "-m", "a, again"]);
    assert_ne!(head_rev(&world, "topic"), b, "the describe rebases topic");
    // Plain jj starts from `.git` matching the record, so it doesn't make these imports.
    world
        .fx
        .repo(0)
        .git(&["update-ref", "refs/heads/topic", &b]);
    expect_unexplained(world, "bookmark topic");

    let (mut world, _, old_topic) = describe_under_bookmarks();
    let topic = head_rev(&world, "topic");
    let view = world.view_at_head(0);
    let rebased = view.commits.iter().find(|c| c.id == topic).unwrap();
    world.move_git_branch(0, "feature", rebased);
    world
        .fx
        .repo(0)
        .git(&["update-ref", "refs/heads/topic", &old_topic.id]);
    expect_unexplained(world, "bookmark topic");
}

/// Two merges can rebase one commit alike, each for a user's command of its own, and that is
/// no repeat of one rebase. Beta rebases `child` onto `parent` and syncs; alpha, not yet having
/// that, abandons `parent`, and its node merges that with beta's rebase, which rebases `child`
/// onto `parent`'s parent. Beta abandons `parent` too, at the operation before its rebase, and
/// jj's merge of the two on beta rebases `child` there as well, before beta has alpha's merge.
/// Converging, the two rebased commits diverge, as jj's own merge of the two lines makes
/// them. The nightly Search workflow's run 45238982632 found it on shard 2, whose
/// `MUSUBI_SEARCH_SEED` is the run's id, with a squash in place of alpha's abandon. Without
/// `brought_apart`, the same-rebase-twice check fails it.
#[test]
fn e2e_merges_of_two_abandons_rebase_one_commit_alike() {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.jj(0, &["new", "root()", "-m", "base"]);
    world.jj(0, &["new", "-m", "parent"]);
    let (base, parent) = (head_rev(&world, "@-"), head_rev(&world, "@"));
    world.jj(0, &["new", &base, "-m", "child"]);
    let child = head_rev(&world, "@");
    world.jj(0, &["new", "root()"]);
    // Converging forgets which machine made `child`, so that beta's rebase alone rewrote it.
    world.converge();
    let before = world.latest_op_head(1);
    world.jj(1, &["rebase", "-s", &child, "-o", &parent]);
    world.sync(1);
    world.jj(0, &["abandon", &parent]);
    world.sync(0);
    world.jj_at_op(1, &before, &["abandon", &parent]);
    world.observe(1);
    world.converge();
    let children = world.raw_jj(
        0,
        &[
            "log",
            "--no-graph",
            "-r",
            "description(substring:\"child\")",
            "-T",
            "parents.map(|p| p.commit_id()) ++ \"\\n\"",
        ],
    );
    assert_eq!(
        children.lines().collect::<Vec<_>>(),
        [base.as_str(), base.as_str()],
        "two alike rebases of child onto base"
    );
}

/// Machine 0 with `feature` on a commit `a` and `topic` on its child, synced, and then `a`
/// described, which rewrites both: the world, `a`, and `topic`'s commit as it was before.
fn describe_under_bookmarks() -> (World, String, crate::view::Commit) {
    let mut world = World::new(Setup {
        nodes: 2,
        naming: Naming::Own,
        prejoin: false,
        secondary: false,
    });
    world.commit(0, 0, 0);
    world.commit(0, 0, 1);
    let (a, b) = (head_rev(&world, "@--"), head_rev(&world, "@-"));
    world.jj(0, &["bookmark", "create", "feature", "-r", &a]);
    world.jj(0, &["bookmark", "create", "topic", "-r", &b]);
    world.sync(0);
    let old_topic = world
        .view_at_head(0)
        .commits
        .into_iter()
        .find(|c| c.id == b)
        .unwrap();
    world.jj(0, &["describe", "-r", &a, "-m", "a, described"]);
    (world, a, old_topic)
}

fn head_rev(world: &World, rev: &str) -> String {
    world.raw_jj(0, &["log", "--no-graph", "-r", rev, "-T", "commit_id"])
}

/// Runs a command on machine 0, which imports, and converges, expecting the import check to
/// fail on `what`, with plain jj's import differing.
fn expect_unexplained(mut world: World, what: &str) {
    let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        world.jj(0, &["status"]);
        world.converge();
    }))
    .expect_err("an import the record of git's refs caused fails the check");
    let message = failed.downcast_ref::<String>().unwrap();
    assert!(message.contains(&format!("changed {what}")), "{message}");
    assert!(message.contains("plain jj"), "{message}");
}

/// jj's known limitation after `jj op abandon` (docs/internals/races.md, "Known jj
/// limitations"): a command that loaded the repository before the abandon writes on an
/// operation it removed, and jj's merge of that rebases a child again from the original into an
/// identical divergent copy, though the merge's inputs already hold the first rebase. Abandoning
/// the copy recovers. Once jj stops making the copy, this fails, so that the row goes.
#[test]
fn a_native_serial_merge_can_repeat_a_rebase_after_abandon() {
    let env = musubi_testutil::TestEnv::new();
    // No Git working tree or branch import: this is unrelated to the snapshot/import
    // divergence when Git points a branch at an unsnapshotted working copy (#41).
    let repo = env.init_non_colocated_repo("native");
    let op = || {
        repo.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n",
            "1",
            "-T",
            "id",
        ])
        .trim()
        .to_owned()
    };
    let commit = || {
        repo.jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            "@",
            "-T",
            "commit_id",
        ])
        .trim()
        .to_owned()
    };
    let children = || {
        repo.jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            "description(substring:\"child\")",
            "-T",
            "commit_id ++ \"\\n\"",
        ])
        .lines()
        .map(str::to_owned)
        .collect::<Vec<_>>()
    };
    repo.jj(&["describe", "-m", "parent"]);
    let parent = commit();
    let base = op();
    repo.jj(&["new", "-m", "child"]);
    let original = commit();
    let left = op();
    repo.jj(&[
        "--at-op",
        &base,
        "describe",
        &parent,
        "-m",
        "rewritten parent",
    ]);
    repo.jj(&["status"]);
    let first = commit();

    // The merge keeps its result after its child-creation parent disappears. A delayed
    // command still has the old operation: jj rebases the original child again.
    repo.jj(&["op", "abandon", &left]);
    repo.jj(&[
        "--at-op", &left, "bookmark", "create", "delayed", "-r", &original,
    ]);
    repo.jj(&["status"]);
    let visible = children();
    assert_eq!(
        visible.len(),
        2,
        "notice when jj no longer makes this divergence"
    );
    let second = visible.iter().find(|id| **id != first).unwrap().clone();
    let show = |id: &str| {
        repo.jj(&[
            "--ignore-working-copy",
            "log",
            "--no-graph",
            "-r",
            id,
            "-T",
            "change_id ++ parents.map(|p| p.commit_id()).join(\",\") ++ description",
        ])
    };
    assert_eq!(show(&first), show(&second), "an identical copy");
    let diff = repo.jj(&[
        "--ignore-working-copy",
        "diff",
        "--summary",
        "--from",
        &first,
        "--to",
        &second,
    ]);
    assert!(diff.is_empty(), "an identical copy: {diff}");

    repo.jj(&["abandon", &second]);
    assert_eq!(children(), [first]);
}
