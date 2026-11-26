//! Machine names (docs/internals/design.md, "Machine names"): a copy renames itself by
//! recording `musubi.name` when `musubi.machine-name` changes, and every machine, and the hub,
//! names the copies present at an operation by their names there, the one present under a
//! name longest keeping it plain.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use musubi_jj::workspaces::qualified_name;
use musubi_testutil::TestEnv;

use crate::fixture::Fixture;

/// The names in machine `index`'s view of other machines' workspaces.
fn others(hive: &Fixture, index: usize) -> BTreeSet<String> {
    hive.workspace_names(index)
        .into_iter()
        .filter(|name| name.contains('/'))
        .collect()
}

/// Each machine shows every other present one's workspace `workspace` of `keys` as the hub
/// names that machine, and names itself so too: every machine and the hub agree.
fn assert_named_alike(hive: &mut Fixture, keys: &[(String, &str)]) {
    let hub = hive.hub_names();
    for (index, (own, _)) in keys.iter().enumerate() {
        let expected: BTreeSet<String> = keys
            .iter()
            .filter(|(key, _)| key != own && hub.contains_key(key))
            .map(|(key, workspace)| format!("{}/{workspace}", hub[key]))
            .collect();
        assert_eq!(
            others(hive, index),
            expected,
            "machine {index}, hub {hub:?}"
        );
        if let Some(label) = hub.get(own) {
            let activity = hive.node(index).activity().unwrap();
            let name = activity.iter().find(|copy| copy.key == *own).unwrap();
            assert_eq!(&name.name, label, "machine {index}");
        }
    }
}

/// `musubi.machine-name` set on one machine renames it on every other one and on the hub at
/// their next sync, and the copy names itself so. Unset again, it keeps the name it recorded:
/// it doesn't go back to the name its key embeds.
#[test]
fn a_rename_reaches_every_machine_and_the_hub() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let beta = hive.machine_key(1);
    hive.set_machine_name(1, "desk");
    hive.sync();
    for index in [0, 2] {
        let names = others(&hive, index);
        assert!(names.contains("desk/beta"), "{names:?}");
        assert!(
            !names.iter().any(|name| name.starts_with("beta")),
            "{names:?}"
        );
    }
    assert_eq!(hive.hub_names()[&beta], "desk");
    let activity = hive.node(1).activity().unwrap();
    assert_eq!(
        activity.iter().find(|c| c.key == beta).unwrap().name,
        "desk"
    );
    // As its daemon restarted with the setting gone.
    hive.reopen(1);
    hive.commit(1, "b", "after unsetting");
    hive.sync();
    assert!(others(&hive, 0).contains("desk/beta"));
    hive.assert_converged();
}

/// A machine offline across another's rename shows that one under its old name, and works on
/// its working copy there. Its work is read by the names it saw, and the renamed machine's
/// working copy takes it, shown under the new name once the offline machine syncs.
#[test]
fn a_copy_offline_across_a_rename_reads_its_names_as_they_were() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.set_machine_name(1, "desk");
    hive.hive.sync(1).unwrap();
    hive.hive.sync(0).unwrap();
    assert!(others(&hive, 0).contains("desk/beta"));
    assert!(others(&hive, 2).contains("beta/beta"));
    let commit = hive.workspaces(2)["beta/beta"].clone();
    hive.repo(2)
        .jj(&["describe", "-r", &commit, "-m", "described offline"]);
    hive.sync();
    hive.sync();
    let described = hive
        .repo(1)
        .jj(&["log", "--no-graph", "-r", "@", "-T", "description"]);
    assert_eq!(described, "described offline\n");
    let names = others(&hive, 2);
    assert!(names.contains("desk/beta"), "{names:?}");
    assert!(!names.contains("beta/beta"), "{names:?}");
    hive.assert_converged();
}

/// alpha renames itself `beta`, beta's name, which beta has had since it joined: beta keeps
/// the plain name on every machine and the hub, though its key comes after alpha's, and alpha
/// is told apart by part of its key, as it names itself too.
#[test]
fn a_copy_that_stays_keeps_its_name_when_another_renames_into_it() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let (alpha, beta) = (hive.machine_key(0), hive.machine_key(1));
    hive.set_machine_name(0, "beta");
    hive.sync();
    let qualified = qualified_name("beta", &alpha);
    assert_eq!(
        others(&hive, 1),
        BTreeSet::from([format!("{qualified}/alpha")])
    );
    assert_eq!(others(&hive, 0), BTreeSet::from(["beta/beta".to_owned()]));
    assert_eq!(
        hive.hub_names(),
        BTreeMap::from([
            (alpha.clone(), qualified),
            (beta.clone(), "beta".to_owned())
        ])
    );
    assert_named_alike(&mut hive, &[(alpha, "alpha"), (beta, "beta")]);
    hive.assert_converged();
}

/// alpha forgets beta, and gamma renames itself `beta`, which, with beta gone, it has to
/// itself: no machine remembers beta's name. beta, seeing the forget, works again, and comes
/// back under its name, which gamma keeps, though beta's key comes first: beta is told apart.
#[test]
fn a_copy_that_stays_keeps_its_name_when_a_forgotten_one_returns_with_it() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let (alpha, beta, gamma) = (
        hive.machine_key(0),
        hive.machine_key(1),
        hive.machine_key(2),
    );
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.hive.sync(0).unwrap();
    hive.set_machine_name(2, "beta");
    hive.hive.sync(2).unwrap();
    hive.hive.sync(1).unwrap();
    hive.hive.sync(0).unwrap();
    assert!(!hive.shown_machines().contains(&beta));
    assert_eq!(others(&hive, 0), BTreeSet::from(["beta/gamma".to_owned()]));
    hive.commit(1, "b", "beta returns");
    hive.sync();
    hive.sync();
    assert!(hive.shown_machines().contains(&beta));
    let qualified = qualified_name("beta", &beta);
    assert_eq!(
        others(&hive, 0),
        BTreeSet::from(["beta/gamma".to_owned(), format!("{qualified}/beta")])
    );
    assert_named_alike(
        &mut hive,
        &[(alpha, "alpha"), (beta, "beta"), (gamma, "gamma")],
    );
    hive.assert_converged();
}

/// alpha and beta rename themselves `x` at once, neither seeing the other's: every machine,
/// and the hub, gives the plain name to the same one, and tells the other apart alike.
#[test]
fn concurrent_claims_to_a_name_resolve_alike_everywhere() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let keys = [
        hive.machine_key(0),
        hive.machine_key(1),
        hive.machine_key(2),
    ];
    for index in [0, 1] {
        hive.set_machine_name(index, "x");
        assert!(hive.node(index).record_name().unwrap());
    }
    hive.sync();
    hive.sync();
    let hub = hive.hub_names();
    let plain: Vec<&String> = keys[..2].iter().filter(|key| hub[*key] == "x").collect();
    assert_eq!(plain.len(), 1, "{hub:?}");
    for key in &keys[..2] {
        assert!(
            hub[key] == "x" || hub[key] == qualified_name("x", key),
            "{hub:?}"
        );
    }
    let [alpha, beta, gamma] = keys;
    assert_named_alike(
        &mut hive,
        &[(alpha, "alpha"), (beta, "beta"), (gamma, "gamma")],
    );
    hive.assert_converged();
}

/// `jj op restore` back across a rename, and across a forget, reads the names in the view it
/// brings back as the hive named workspaces then. gamma, whose workspace was
/// `gamma/default` then, is forgotten since, and beta, `beta/default` then, has renamed itself
/// `gamma`: the restore takes beta's working copy back to where it was then, as across no
/// rename, and moves nothing of beta's to where gamma's was, nor brings gamma back.
#[test]
fn op_restore_reads_names_as_the_view_brought_back_had_them() {
    let env = TestEnv::new();
    let repos =
        ["alpha", "beta", "gamma"].map(|name| env.init_repo_with_workspace(name, "default"));
    let mut hive = Fixture::join(env, repos.into());
    let (beta, gamma) = (hive.machine_key(1), hive.machine_key(2));
    hive.commit(1, "b1", "beta committed");
    hive.sync();
    let restore_to = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    let then = hive.workspaces(0)["beta/default"].clone();
    assert!(hive.node(0).forget_copy(&gamma, "gamma").unwrap());
    hive.sync();
    hive.set_machine_name(1, "gamma");
    hive.repo(1).write_file("b2", "beta in progress");
    hive.repo(1).jj(&["describe", "-m", "beta in progress"]);
    hive.sync();
    assert_eq!(
        others(&hive, 0),
        BTreeSet::from(["gamma/default".to_owned()])
    );
    hive.repo(0).jj(&["op", "restore", restore_to.trim()]);
    hive.sync();
    hive.repo(1).jj(&["status"]);
    let now = hive
        .repo(1)
        .jj(&["log", "--no-graph", "-r", "@", "-T", "commit_id"]);
    assert_eq!(now, then);
    hive.sync();
    assert!(!hive.shown_machines().contains(&gamma));
    assert!(hive.shown_machines().contains(&beta));
    assert_eq!(
        hive.workspaces(0).get("gamma/default"),
        Some(&then),
        "{:?}",
        hive.workspaces(0)
    );
    assert_eq!(
        others(&hive, 0),
        BTreeSet::from(["gamma/default".to_owned()])
    );
    hive.assert_converged();
}

/// A machine the hive has forgotten, whose daemon goes on, doesn't come back because
/// `musubi.machine-name` changed, as for the machine's other repos: it records the name once
/// its own work brings it back.
#[test]
fn a_forgotten_copy_takes_a_rename_only_once_it_comes_back() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = hive.machine_key(1);
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.hive.sync(0).unwrap();
    hive.hive.sync(1).unwrap();
    hive.set_machine_name(1, "desk");
    hive.sync();
    assert!(!hive.shown_machines().contains(&beta));
    hive.commit(1, "b", "beta returns");
    hive.sync();
    hive.sync();
    assert!(hive.shown_machines().contains(&beta));
    assert_eq!(others(&hive, 0), BTreeSet::from(["desk/beta".to_owned()]));
    hive.assert_converged();
}

/// beta renames itself `x`, and gamma takes `beta`, while alpha runs a `jj` command at the
/// operation before it heard, whose view names beta's working copy `beta/default`. jj's merge
/// of the two puts gamma's commit under `beta/default`, which the two operations it merges
/// give different machines: it stands for neither, and no working copy moves.
#[test]
fn a_name_two_merged_operations_give_different_machines_moves_nothing() {
    let env = TestEnv::new();
    let repos =
        ["alpha", "beta", "gamma"].map(|name| env.init_repo_with_workspace(name, "default"));
    let mut hive = Fixture::join(env, repos.into());
    hive.sync();
    let before = hive.workspaces(0);
    let at = hive
        .repo(0)
        .jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    hive.set_machine_name(1, "x");
    hive.hive.sync(1).unwrap();
    hive.set_machine_name(2, "beta");
    hive.hive.sync(2).unwrap();
    hive.hive.sync(0).unwrap();
    assert_eq!(
        others(&hive, 0),
        BTreeSet::from(["beta/default".to_owned(), "x/default".to_owned()])
    );
    hive.repo(0).jj(&[
        "--at-op",
        at.trim(),
        "describe",
        "-m",
        "alpha at an older operation",
    ]);
    hive.sync();
    hive.sync();
    let after = hive.workspaces(0);
    assert_eq!(
        after.get("x/default"),
        before.get("beta/default"),
        "{after:?}"
    );
    assert_eq!(
        after.get("beta/default"),
        before.get("gamma/default"),
        "{after:?}"
    );
    hive.assert_converged();
}
