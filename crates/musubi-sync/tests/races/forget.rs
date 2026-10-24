//! Forgetting a copy (docs/internals/races.md, "Copies that go away"): a forget removes the
//! copy's work it saw, and only the copy's own work brings it back.

use std::collections::BTreeSet;

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

/// A workspace of this machine's own whose name has a `/` is still its own, shown elsewhere
/// as `alpha/feat/x`: only names that another machine's could have are taken for one.
#[test]
fn own_workspaces_with_a_slash_are_own() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let path = hive.env.root().join("alpha-feat");
    let path = path.to_str().unwrap().to_owned();
    hive.repo(0)
        .jj(&["workspace", "add", "--name", "feat/x", &path]);
    hive.sync();
    hive.sync();
    assert!(hive.workspace_names(0).contains("feat/x"));
    assert!(hive.workspace_names(1).contains("alpha/feat/x"));
}

/// A workspace of this machine's own named like another machine's is its own all the same,
/// whether it was made after that machine joined or before: the other machine is shown by
/// its name and part of its id instead. Nor does the hive forgetting this machine change
/// that, or undoing a forget of the workspace.
#[test]
fn own_workspaces_named_like_another_machine_are_own() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for name in ["beta/x", "gamma/x"] {
        let path = hive
            .env
            .root()
            .join(format!("alpha-{}", name.replace('/', "-")));
        let path = path.to_str().unwrap().to_owned();
        hive.repo(0)
            .jj(&["workspace", "add", "--name", name, &path]);
    }
    hive.sync();
    let gamma = hive.env.init_repo("gamma");
    hive.add(gamma);
    hive.sync();
    hive.sync();
    let alpha = hive.workspace_names(0);
    assert!(
        alpha.contains("beta/x") && alpha.contains("gamma/x"),
        "{alpha:?}"
    );
    let beta = hive.machine_key(1);
    let gamma = hive.machine_key(2);
    for (key, workspace) in [(&beta, "beta"), (&gamma, "gamma")] {
        let [_, qualified] = musubi_jj::workspaces::display_forms(key);
        assert!(
            alpha.contains(&format!("{qualified}/{workspace}")),
            "{alpha:?}"
        );
    }
    let shared = |hive: &Fixture| {
        for index in [1, 2] {
            let names = hive.workspace_names(index);
            assert!(names.contains("alpha/beta/x"), "{names:?}");
            assert!(names.contains("alpha/gamma/x"), "{names:?}");
        }
    };
    shared(&hive);
    hive.assert_converged();
    // `musubi forget` takes the name a machine is shown by, the plain one `musubi list` gives
    // it, or its key.
    let [_, qualified] = musubi_jj::workspaces::display_forms(&beta);
    for name in [qualified.as_str(), "beta", beta.as_str()] {
        assert_eq!(
            hive.node(0).machine_named(name).unwrap(),
            Some(beta.clone())
        );
    }
    assert_eq!(hive.node(0).machine_named("alpha").unwrap(), None);

    let alpha_key = hive.machine_key(0);
    assert!(hive.node(1).forget_copy(&alpha_key, "alpha").unwrap());
    hive.sync();
    assert_eq!(hive.workspace_names(0), alpha);
    hive.commit(0, "a", "alpha again");
    hive.sync();
    assert_eq!(hive.workspace_names(0), alpha);
    shared(&hive);

    hive.repo(0).jj(&["workspace", "forget", "beta/x"]);
    hive.repo(0).jj(&["undo"]);
    hive.sync();
    hive.sync();
    let names = hive.workspace_names(0);
    assert!(names.contains("beta/x"), "{names:?}");
    shared(&hive);
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
