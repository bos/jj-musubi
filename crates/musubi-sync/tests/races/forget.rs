//! Forgetting a copy (docs/internals/races.md, "Copies that go away"): a forget removes the
//! copy's work it saw, and only the copy's own work brings it back.

use std::collections::BTreeSet;

use futures::executor::block_on;
use jj_lib::commit::Commit;
use jj_lib::object_id::ObjectId as _;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::repo::Repo as _;

use crate::fixture::Fixture;

/// The descriptions of the visible commits on machine `index`.
fn descriptions(hive: &Fixture, index: usize) -> BTreeSet<String> {
    hive.visible(index)
        .into_iter()
        .filter_map(|line| line.splitn(3, ' ').nth(2).map(str::to_owned))
        .collect()
}

/// A forget hides the copy on every machine, abandoning its empty working-copy commit and
/// keeping its work. The copy keeps its own working copy, and nothing musubi does there
/// brings it back, however often it syncs, nor publishes a new empty commit for it to work
/// on: only its next work does.
#[test]
fn a_forgotten_copy_comes_back_with_its_next_work() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    let beta = hive.machine_key(1);
    let empty = hive.workspaces(1)["beta"].clone();
    let before = hive.visible(0).len();
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.sync();
    hive.sync();
    assert_eq!(
        hive.visible(2).len(),
        before - 1,
        "only the empty working copy goes"
    );
    assert!(!hive.shown_machines().contains(&beta));
    for index in [0, 2] {
        assert!(!hive.workspace_names(index).contains("beta/beta"));
        assert!(descriptions(&hive, index).contains("from beta"));
        assert!(!hive.visible(index).iter().any(|c| c.starts_with(&empty)));
    }
    assert!(hive.workspace_names(1).contains("beta"));

    hive.commit(1, "b2", "beta again");
    hive.sync();
    assert!(hive.shown_machines().contains(&beta));
    assert!(hive.workspace_names(0).contains("beta/beta"));
    hive.assert_converged();
}

/// A forgotten copy whose next work leaves its working copy alone, as creating a bookmark
/// does, shows again with a working copy every machine can see. The forget abandoned its
/// empty working-copy commit, so it gets a new one, as jj gives a workspace whose commit is
/// abandoned.
#[test]
fn a_forgotten_copy_back_by_other_work_gets_a_new_working_copy() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    let beta = hive.machine_key(1);
    let empty = hive.workspaces(1)["beta"].clone();
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.sync();
    assert!(!hive.shown_machines().contains(&beta));
    hive.repo(1).jj(&["bookmark", "create", "x", "-r", "@-"]);
    hive.sync();
    assert!(hive.shown_machines().contains(&beta));
    let wc = hive.workspaces(1)["beta"].clone();
    assert_ne!(wc, empty);
    for index in 0..2 {
        assert!(
            hive.visible(index).iter().any(|c| c.starts_with(&wc)),
            "beta's working copy is hidden on {index}"
        );
    }
    hive.assert_converged();
}

/// A forget removes only the work it saw: work the copy did meanwhile keeps it.
#[test]
fn work_a_forget_didnt_see_keeps_the_copy() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = hive.machine_key(1);
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.commit(1, "b", "beta meanwhile");
    hive.hive.sync(0).unwrap();
    hive.sync();
    assert!(hive.shown_machines().contains(&beta));
    assert!(hive.workspace_names(0).contains("beta/beta"));
    hive.assert_converged();
}

/// `musubi leave` forgets its own copy after all its work, and that sticks however the
/// forget is merged: here another machine pushed first, so the leaving copy merges. Its
/// working-copy commit, which has changes, stays as an ordinary commit, and it keeps its
/// working copy.
#[test]
fn leaving_sticks_through_a_merge() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = hive.machine_key(1);
    hive.repo(1).write_file("wip", "unfinished");
    hive.repo(1).jj(&["util", "snapshot"]);
    let wip = hive.workspaces(1)["beta"].clone();
    let removed = hive.node(1).forget_self().unwrap().unwrap();
    hive.commit(0, "a", "alpha meanwhile");
    hive.hive.sync(0).unwrap();
    hive.hive.sync(1).unwrap();
    hive.node(1).restore_workspaces(&removed).unwrap();
    hive.node(1).give_back_working_copies().unwrap();
    hive.hive.sync(0).unwrap();
    assert!(!hive.shown_machines().contains(&beta));
    assert!(!hive.workspace_names(0).contains("beta/beta"));
    assert!(hive.visible(0).iter().any(|c| c.starts_with(&wip)));
    assert_eq!(hive.workspaces(1)["beta"], wip);
    // Already gone, it has nothing more to forget.
    assert!(hive.node(1).forget_self().unwrap().is_none());
}

/// Two machines that forget the same copy at once agree, and a forget of a copy already
/// forgotten writes nothing.
#[test]
fn concurrent_forgets_agree() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let beta = hive.machine_key(1);
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    assert!(hive.node(2).forget_copy(&beta, "beta").unwrap());
    hive.sync();
    assert!(!hive.shown_machines().contains(&beta));
    assert!(!hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.assert_converged();
    assert!(!hive.shown_machines().contains(&beta));
}

/// Removing a copy's last workspace doesn't remove its membership or make it impossible
/// to name that copy for `musubi forget`.
#[test]
fn a_copy_without_workspaces_can_be_forgotten_by_name() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = hive.machine_key(1);
    hive.repo(1).jj(&["workspace", "forget", "beta"]);
    hive.sync();
    assert!(hive.node(0).present_copies().unwrap().1.is_present(&beta));
    assert!(!hive.workspace_names(0).contains("beta/beta"));
    let qualified = musubi_jj::workspaces::qualified_name("beta", &beta);
    for name in ["beta", qualified.as_str(), beta.as_str()] {
        assert_eq!(
            hive.node(0).machine_named(name).unwrap(),
            Some(beta.clone())
        );
    }
    let activity = hive.node(0).activity().unwrap();
    assert_eq!(
        activity.iter().find(|copy| copy.key == beta).unwrap().name,
        "beta"
    );
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.sync();
    assert!(!hive.node(0).present_copies().unwrap().1.is_present(&beta));
}

/// While the hive has forgotten a copy, no other machine sees its working-copy commit as a
/// working copy, so a rewrite of it there doesn't move the copy's workspace. The copy
/// follows it to the rewrite itself, as jj would have moved it.
#[test]
fn a_forgotten_working_copy_follows_its_rewrite() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = hive.machine_key(1);
    hive.repo(1).write_file("wip", "unfinished");
    hive.repo(1).jj(&["util", "snapshot"]);
    hive.sync();
    let wip = hive.workspaces(0)["beta/beta"].clone();
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.repo(0)
        .jj(&["describe", "-r", &wip, "-m", "described by alpha"]);
    hive.sync();
    let described = hive.commit_id(1, "described by alpha");
    assert_eq!(hive.workspaces(1)["beta"], described);
}

/// Machine `index`'s working-copy commit in its own workspace `name`, read in process: a `jj`
/// command would snapshot, which is work, or update a stale working copy.
fn own_working_copy(hive: &Fixture, index: usize, name: &str) -> (bool, Commit) {
    let repo = hive.load(index);
    let id = repo
        .view()
        .get_wc_commit_id(WorkspaceName::new(name))
        .unwrap();
    let commit = block_on(repo.store().get_commit_async(id)).unwrap();
    let index = repo.index();
    let visible = block_on(index.has_id(id)).unwrap()
        && repo
            .view()
            .heads()
            .iter()
            .any(|head| block_on(index.is_ancestor(id, head)).unwrap());
    (visible, commit)
}

/// While the hive has forgotten a copy, its working copy stays on the empty commit the forget
/// abandoned, which no other machine sees, so jj doesn't rebase it when another machine
/// rewrites its parent, here with `how`. The copy rebases it itself, still hidden, onto the
/// commits described `parents`, as jj would have rebased a workspace it saw. Left on the old
/// parent, the copy's next snapshot brought that back on every machine: beside its rewrite,
/// divergent, or abandoned no longer. The copy's working copy is on "alpha parent", and with
/// `merge` on "alpha base" too. Returns the hive, converged.
fn forgotten_copy_snapshots_after_its_parent_is(
    how: &[&str],
    merge: bool,
    parents: &[&str],
) -> Fixture {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "alpha base");
    if merge {
        hive.repo(0).jj(&["new", "root()"]);
    }
    hive.commit(0, "p", "alpha parent");
    if merge {
        let base = hive.commit_id(0, "alpha base");
        hive.repo(0).jj(&["new", &base, "@-"]);
    }
    hive.sync();
    let alpha = hive.machine_key(0);
    let (_, empty) = own_working_copy(&hive, 0, "alpha");
    assert!(hive.node(1).forget_copy(&alpha, "alpha").unwrap());
    hive.sync();
    let parent = hive.commit_id(1, "alpha parent");
    let mut args = how.to_vec();
    args.push(&parent);
    hive.repo(1).jj(&args);
    let before = hive.visible(1);
    hive.sync();
    assert!(
        !hive.shown_machines().contains(&alpha),
        "rebasing its working copy is no work of alpha's"
    );
    assert_eq!(hive.visible(1), before, "beta sees alpha's working copy");
    let (visible, rebased) = own_working_copy(&hive, 0, "alpha");
    assert!(!visible, "alpha's working copy is visible");
    assert_eq!(rebased.change_id(), empty.change_id());
    let expected: Vec<String> = parents.iter().map(|p| hive.commit_id(1, p)).collect();
    let actual: Vec<String> = rebased.parent_ids().iter().map(|id| id.hex()).collect();
    assert_eq!(
        actual, expected,
        "alpha's working copy is on the wrong parents"
    );

    hive.repo(0).write_file("new", "alpha edit");
    hive.repo(0).jj(&["status"]);
    let with_edit = hive.repo(0).jj(&[
        "log",
        "--no-graph",
        "-r",
        "all() & files(\"new\")",
        "-T",
        "commit_id ++ \"\\n\"",
    ]);
    assert!(!with_edit.is_empty(), "the edit is in no commit");
    hive.assert_converged();
    assert!(hive.shown_machines().contains(&alpha));
    assert!(
        !descriptions(&hive, 1).contains("alpha parent"),
        "the old parent is back"
    );
    assert_eq!(
        hive.repo(0).jj(&["file", "show", "-r", "@", "new"]),
        "alpha edit"
    );
    let template = "description.first_line() ++ \"\\n\"";
    let shown = hive
        .repo(0)
        .jj(&["log", "--no-graph", "-r", "@-", "-T", template]);
    let mut shown: Vec<&str> = shown.lines().collect();
    let mut parents = parents.to_vec();
    shown.sort_unstable();
    parents.sort_unstable();
    assert_eq!(shown, parents);
    hive
}

/// The forgotten copy's working copy, a merge, goes onto the rewrite of one parent, beside
/// the other.
#[test]
fn a_forgotten_working_copy_follows_a_rewrite_of_its_parent() {
    forgotten_copy_snapshots_after_its_parent_is(
        &["describe", "-m", "reworded"],
        true,
        &["alpha base", "reworded"],
    );
}

/// The forgotten copy's working copy goes onto the abandoned parent's parent, without the
/// abandoned change. That changes its files, so the working copy is stale, as any workspace
/// jj moves: jj, updating it, snapshots the edit at the operation it last recorded, into a
/// commit beside the empty working copy, and takes the edit off the disk until the copy's
/// next sync follows that commit and the next command updates the files again.
#[test]
fn a_forgotten_working_copy_follows_an_abandon_of_its_parent() {
    let hive = forgotten_copy_snapshots_after_its_parent_is(&["abandon"], false, &["alpha base"]);
    assert!(!hive.repo(0).path().join("p").exists());
}

/// A machine that rewrites another's working-copy commit and then forgets that copy, before
/// hearing of work the copy did meanwhile, merges the two without bringing the old commit
/// back beside its rewrite: the copy, present again by that work, follows the rewrite.
#[test]
fn a_rewrite_before_a_forget_sticks_through_a_merge() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = hive.machine_key(1);
    hive.repo(1).write_file("wip", "unfinished");
    hive.repo(1).jj(&["util", "snapshot"]);
    hive.sync();
    let wip = hive.workspaces(0)["beta/beta"].clone();
    hive.repo(1).jj(&["bookmark", "create", "b", "-r", "@-"]);
    hive.hive.sync(1).unwrap();
    hive.repo(0)
        .jj(&["describe", "-r", &wip, "-m", "described by alpha"]);
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.sync();
    hive.sync();
    let described = hive.commit_id(0, "described by alpha");
    for index in 0..2 {
        assert!(
            !hive.visible(index).iter().any(|c| c.starts_with(&wip)),
            "the commit alpha rewrote is back on {index}"
        );
    }
    assert_eq!(hive.workspaces(1)["beta"], described);
    hive.assert_converged();
}

/// A forgotten copy keeps its working copy when it realizes the forget together with the
/// operation before it, which it carries its workspaces on from. Found by the end-to-end
/// search, in a hive with nothing in it yet.
#[test]
fn a_forgotten_copy_keeps_its_working_copy_through_a_run() {
    let env = musubi_testutil::TestEnv::new();
    let repos = vec![env.init_repo("alpha"), env.init_repo("beta")];
    let mut hive = Fixture::join(env, repos);
    let alpha = hive.machine_key(0);
    hive.commit(1, "b", "from beta");
    assert!(hive.node(1).forget_copy(&alpha, "alpha").unwrap());
    hive.sync();
    assert!(!hive.shown_machines().contains(&alpha));
    assert!(hive.workspace_names(0).contains("alpha"));
    hive.assert_converged();
}

/// `jj undo` of a forget brings the forgotten copy's workspaces back into this machine's
/// view, but not into the hive: only the copy's own work brings it back. Nor does this
/// machine take them for its own, and it drops them from its view as it syncs.
#[test]
fn undoing_a_forget_brings_back_nothing() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let gamma = hive.machine_key(2);
    assert!(hive.node(0).forget_copy(&gamma, "gamma").unwrap());
    hive.repo(0).jj(&["undo"]);
    hive.sync();
    let shown = hive.shown_machines();
    assert!(!shown.contains(&gamma));
    assert_eq!(shown.len(), 2, "{shown:?}");
    for index in [0, 1] {
        assert!(!hive.workspace_names(index).contains("gamma/gamma"));
        assert!(
            !hive
                .workspace_names(index)
                .iter()
                .any(|name| name.contains("/gamma/"))
        );
    }
    hive.assert_converged();
}

/// A merge of a forget that saw a copy's latest work with work from before it keeps the
/// copy's workspaces as its latest work left them, whichever parent the merge lists first.
#[test]
fn a_forgotten_copy_keeps_its_latest_workspaces_through_a_merge() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let alpha = hive.machine_key(0);
    hive.commit(2, "g", "gamma, on alpha as it joined");
    let path = hive.env.root().join("alpha-feat");
    let path = path.to_str().unwrap().to_owned();
    hive.repo(0)
        .jj(&["workspace", "add", "--name", "feat", &path]);
    hive.hive.sync(0).unwrap();
    hive.hive.sync(1).unwrap();
    assert!(hive.node(1).forget_copy(&alpha, "alpha").unwrap());
    hive.hive.sync(1).unwrap();
    hive.hive.sync(2).unwrap();
    hive.hive.sync(0).unwrap();
    assert!(!hive.shown_machines().contains(&alpha));
    let names = hive.workspace_names(0);
    assert!(
        names.contains("alpha") && names.contains("feat"),
        "{names:?}"
    );
    hive.sync();
    assert_eq!(hive.workspace_names(0), names);
}

/// A copy that leaves keeps a visible working-copy commit to work on, though the forget
/// abandoned its empty one, and no next work of its will show it again: so does one the
/// hive had forgotten already, which has nothing more to forget.
#[test]
fn a_copy_that_leaves_gets_a_new_working_copy() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let empty = hive.workspaces(1)["beta"].clone();
    let removed = hive.node(1).forget_self().unwrap().unwrap();
    hive.hive.sync(1).unwrap();
    hive.node(1).restore_workspaces(&removed).unwrap();
    assert_eq!(hive.workspaces(1)["beta"], empty);
    assert!(!hive.visible(1).iter().any(|c| c.starts_with(&empty)));
    hive.node(1).give_back_working_copies().unwrap();
    let given = hive.workspaces(1)["beta"].clone();
    assert!(hive.visible(1).iter().any(|c| c.starts_with(&given)));

    let gamma = hive.machine_key(2);
    let empty = hive.workspaces(2)["gamma"].clone();
    assert!(hive.node(0).forget_copy(&gamma, "gamma").unwrap());
    hive.hive.sync(0).unwrap();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.workspaces(2)["gamma"], empty);
    assert!(hive.node(2).forget_self().unwrap().is_none());
    hive.node(2).give_back_working_copies().unwrap();
    let given = hive.workspaces(2)["gamma"].clone();
    assert_ne!(given, empty);
    assert!(hive.visible(2).iter().any(|c| c.starts_with(&given)));
}

/// A copy that left and joins again shows again at once: joining is its work.
#[test]
fn a_copy_that_left_shows_again_once_it_joins() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = hive.machine_key(1);
    let removed = hive.node(1).forget_self().unwrap().unwrap();
    hive.hive.sync(1).unwrap();
    hive.node(1).restore_workspaces(&removed).unwrap();
    hive.node(1).give_back_working_copies().unwrap();
    hive.hive.sync(0).unwrap();
    assert!(!hive.shown_machines().contains(&beta));
    hive.node(1)
        .create_join_operation("musubi: beta joins the hive")
        .unwrap();
    hive.sync();
    assert!(hive.shown_machines().contains(&beta));
    assert!(hive.workspace_names(0).contains("beta/beta"));
}
