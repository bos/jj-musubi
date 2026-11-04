//! Operation-log level races: undo, op abandon, offline machines, restarts.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;

use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
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
    use musubi_jj::node::NodeRepo;
    use serde_json::json;

    use crate::oracle::Oracle;

    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    hive.assert_converged();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", "..@-"]);
    hive.node(0).settle().unwrap();
    assert!(hive.node(0).check_abandon().unwrap());
    let pending = hive.node(0).pending_drops().clone();
    assert!(!pending.is_empty());
    let mut oracle = Oracle::spawn();
    let mut model = json!({"op": "retryFixup", "action": "write",
        "pending": (0..pending.ops().len()).collect::<Vec<_>>(),
        "written": false, "aligned": false});
    // No push reaches the hub: a canceled/failed call must reuse the written fix-up.
    // Reopen as well, so the bound depends on the persisted marker, not an in-memory cache.
    let first = hive.node(0).write_fixup().unwrap();
    assert!(first.is_some());
    let heads = hive.node(0).local_heads().unwrap();
    for attempt in 0..3 {
        let actual = if attempt == 0 {
            first.clone()
        } else {
            if attempt == 2 {
                let repo = hive.repo(0);
                let reopened = NodeRepo::open(&repo.repo_path(), &repo.settings())
                    .unwrap()
                    .with_repo_config(Some(repo.repo_config_path()));
                *hive.node(0) = reopened;
            }
            hive.node(0).write_fixup().unwrap()
        };
        let reply = oracle.call(&model);
        assert_eq!(reply["ok"], true, "{reply}");
        assert_eq!(reply["emitted"], actual.is_some());
        model["written"] = reply["written"].clone();
        assert_eq!(hive.node(0).pending_drops(), &pending);
        assert_eq!(hive.node(0).local_heads().unwrap(), heads);
    }
    hive.sync();
    hive.assert_converged();
    assert!(hive.node(0).pending_drops().is_empty());
    model["action"] = json!("adopt");
    model["nextPending"] = json!([]);
    let repaired = oracle.call(&model);
    assert_eq!(repaired["ok"], true, "{repaired}");
    assert_eq!(repaired["credit"], 0);
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

#[test]
fn a_cached_fixup_publishes_pending_drops_even_when_its_head_is_known() {
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;

    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let base = hive.hive.hub.store().head().0;

    // Beta keeps a branch alpha never took, which the hub then loses.
    hive.commit(1, "q", "beta's later drop");
    let q = op_log(hive.repo(1)).swap_remove(0);
    hive.commit(1, "b", "beta keeps this");
    hive.hive.sync(1).unwrap();
    hive.hive.hub_goes_back(base).unwrap();

    // Alpha publishes a different drop, stopping before adopting its accepted record.
    hive.commit(0, "p", "alpha's drop");
    let p = op_log(hive.repo(0)).swap_remove(0);
    hive.commit(0, "a", "alpha keeps this");
    hive.hive.sync(0).unwrap();
    hive.repo(0).jj(&["op", "abandon", &p.0]);
    hive.hive.sync_steps(0, 1, &mut |_, reply| reply).unwrap();
    assert!(!hive.node(0).pending_drops().is_empty());
    hive.hive.sync(2).unwrap();

    // On a new hub history beta publishes Q. Alpha takes Q, then crashes before advancing
    // to beta's head. Its unpublished P keeps the old fix-up marked written.
    hive.hive.hub_goes_back(base).unwrap();
    hive.repo(1).jj(&["op", "abandon", &q.0]);
    hive.hive.sync(1).unwrap();
    hive.hive.sync_steps(0, 1, &mut |_, reply| reply).unwrap();
    assert!(!hive.node(0).pending_drops().is_empty());
    hive.reopen(0);

    // The hub loses Q; gamma restores only P, on top of alpha's old fix-up.
    hive.hive.hub_goes_back(base).unwrap();
    hive.hive.sync(2).unwrap();
    let mut accepted = 0;
    hive.hive
        .sync_through(0, &mut |request, reply| {
            if let Reply::Head {
                kind: HeadKind::Accepted,
                ..
            } = &reply
            {
                let Request::Push { dropped, .. } = request else {
                    panic!("not a push");
                };
                assert!(!dropped.is_empty());
                accepted += 1;
            }
            reply
        })
        .unwrap();
    assert_eq!(accepted, 1);
    let heads = hive.node(0).canonical_heads().unwrap();
    let known = hive.hive.members[0].core.known().clone();
    assert_eq!(
        hive.hive.members[0].adapter.records().unwrap(),
        hive.hive.hub.records()
    );
    assert!(hive.node(0).pending_drops().is_empty());
    assert_eq!(heads.len(), 1);
    assert_eq!(heads[0].0, known.1);
    let member = &mut hive.hive.members[0];
    assert!(matches!(
        member.core.step(&mut member.adapter).unwrap(),
        musubi_core::node::Step::Idle
    ));
    hive.sync();
    hive.assert_converged();
    assert!(hive.node(0).pending_drops().is_empty());
}

#[test]
fn a_push_can_drop_its_expected_head_and_reuse_a_cached_fixup() {
    use std::collections::BTreeSet;

    use jj_lib::op_store::OperationId;
    use musubi_jj::op_id::CanonicalOp;
    use serde_json::json;

    use crate::oracle::Oracle;

    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let base = hive.hive.hub.store().head().0;
    let beta_base = op_log(hive.repo(1)).swap_remove(0).0;
    hive.commit(1, "q", "beta's later drop");
    let q = op_log(hive.repo(1)).swap_remove(0);
    hive.hive.sync(1).unwrap();
    let old = hive.hive.hub_head();
    hive.hive.sync(2).unwrap(); // Gamma holds precisely the head beta will abandon.
    hive.commit(1, "b", "beta keeps this");
    hive.hive.sync(1).unwrap();
    hive.hive.hub_goes_back(base).unwrap();

    hive.commit(0, "p", "alpha's drop");
    let p = op_log(hive.repo(0)).swap_remove(0);
    hive.commit(0, "a", "alpha keeps this");
    hive.hive.sync(0).unwrap();
    hive.repo(0).jj(&["op", "abandon", &p.0]);
    hive.hive.sync_steps(0, 1, &mut |_, reply| reply).unwrap();
    let fixup = hive.hive.hub_head();

    hive.hive.hub_goes_back(base).unwrap();
    hive.repo(1)
        .jj(&["op", "abandon", &format!("{beta_base}..{}", q.0)]);
    hive.hive.sync(1).unwrap();
    hive.hive.sync_steps(0, 1, &mut |_, reply| reply).unwrap();
    hive.reopen(0);

    hive.hive.hub_goes_back(base).unwrap();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub_head(), old);
    // Follow immutable original-parent material, rather than the already contracted
    // parent list, to check that alpha's cached fix-up never descended from this head.
    let old_original = hive
        .node(2)
        .canonical_store()
        .original_id(&CanonicalOp(old.clone()))
        .unwrap();
    let store = hive.node(0).canonical_store();
    let mut stack = vec![CanonicalOp(fixup.clone())];
    let mut seen = BTreeSet::new();
    while let Some(op) = stack.pop() {
        if !seen.insert(op.clone()) || op == *store.root_operation_id() {
            continue;
        }
        assert_ne!(store.original_id(&op).unwrap(), old_original);
        let raw = store.read_operation(&op).unwrap();
        for parent in raw.metadata.attributes["musubi.original-parents"].split(' ') {
            stack.push(CanonicalOp(OperationId::try_from_hex(parent).unwrap()));
        }
    }
    // Give the oracle the immutable DAG from the real stores. Parent material names the
    // canonical forms current at birth, so translate those names to original identities
    // before numbering the DAG in parent order.
    let mut names = BTreeMap::new();
    let mut raw_parents = BTreeMap::new();
    for machine in 0..3 {
        let store = hive.node(machine).canonical_store();
        for op in store.operation_ids().unwrap() {
            names.insert(op.0.clone(), store.original_id(&op).unwrap());
        }
    }
    let mut stack = vec![CanonicalOp(old.clone()), CanonicalOp(fixup.clone())];
    let mut visited = BTreeSet::new();
    let root = hive.node(0).canonical_store().root_operation_id().clone();
    while let Some(op) = stack.pop() {
        if !visited.insert(op.clone()) {
            continue;
        }
        let (raw, original) = (0..3)
            .find_map(|machine| {
                hive.node(machine)
                    .canonical_store()
                    .read_operation_and_original(&op)
                    .ok()
            })
            .unwrap();
        let parents = if op == root {
            vec![]
        } else {
            raw.metadata.attributes["musubi.original-parents"]
                .split(' ')
                .map(|p| OperationId::try_from_hex(p).unwrap())
                .collect::<Vec<_>>()
        };
        stack.extend(parents.iter().cloned().map(CanonicalOp));
        names.insert(op.0, original.clone());
        if let Some(previous) = raw_parents.insert(original, parents.clone()) {
            assert_eq!(previous, parents);
        }
    }
    let graph: BTreeMap<_, Vec<_>> = raw_parents
        .into_iter()
        .map(|(op, parents)| {
            (
                op,
                parents
                    .into_iter()
                    .map(|parent| names[&parent].clone())
                    .collect(),
            )
        })
        .collect();
    fn number(
        op: &OperationId,
        graph: &BTreeMap<OperationId, Vec<OperationId>>,
        numbers: &mut BTreeMap<OperationId, usize>,
        parents: &mut Vec<Vec<usize>>,
    ) -> usize {
        if let Some(index) = numbers.get(op) {
            return *index;
        }
        let ps = graph[op]
            .iter()
            .map(|parent| number(parent, graph, numbers, parents))
            .collect();
        let index = parents.len();
        numbers.insert(op.clone(), index);
        parents.push(ps);
        index
    }
    let mut numbers = BTreeMap::new();
    let mut parents = vec![];
    for op in graph.keys() {
        number(op, &graph, &mut numbers, &mut parents);
    }
    let mut oracle = Oracle::spawn();
    assert_eq!(hive.hive.hub.store().record_count(), 0);
    let seq = hive.hive.hub.store().head().0;
    let mut accepted = 0;
    hive.hive
        .sync_through(0, &mut |request, reply| {
            if let Reply::Head {
                kind: HeadKind::Accepted,
                ..
            } = &reply
            {
                let Request::Push {
                    expected,
                    new,
                    dropped,
                    ..
                } = request
                else {
                    panic!("only a push can be accepted");
                };
                assert_eq!(expected, &old);
                assert_eq!(new, &fixup);
                assert!(!dropped.is_empty());
                // Drops outside both heads' immutable ancestry cannot affect this check.
                let answer = oracle.call(&json!({"op": "contractedAncestry",
                    "parents": parents, "expected": numbers[&names[expected]],
                    "head": numbers[&names[new]],
                    "dropped": dropped.iter().filter_map(|op| numbers.get(&names[op]))
                        .collect::<Vec<_>>()
                }));
                assert_eq!(answer["ok"], true, "{answer}");
                assert_eq!(answer["descends"], true, "{answer}");
                assert_eq!(answer["original"], false, "{answer}");
                accepted += 1;
            }
            reply
        })
        .unwrap();
    assert_eq!(accepted, 1);
    assert_eq!(hive.hive.hub.store().head().0, seq + 1);
    assert_eq!(hive.hive.hub_head(), fixup);
    hive.sync();
    hive.assert_converged();
}

#[test]
fn pending_drops_get_a_new_tip_when_the_hub_already_has_the_cached_fixup() {
    use crate::oracle::Oracle;
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;
    use musubi_jj::op_id::CanonicalOp;
    use serde_json::json;

    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "q", "shared base");
    hive.sync();
    let q_alpha = op_log(hive.repo(0))[0].0.clone();
    let (q_seq, q) = hive.hive.hub.store().head();
    let q = q.clone();
    let q_beta = hive.node(1).local_of(&CanonicalOp(q.clone())).unwrap();
    hive.commit(0, "x", "drop this work");
    let p_alpha = op_log(hive.repo(0))[0].0.clone();
    hive.hive.sync(0).unwrap();
    let p = hive.hive.hub_head();
    hive.hive.fetch(1).unwrap();
    for _ in 0..16 {
        let member = &mut hive.hive.members[1];
        if member.adapter.is_local(&p).unwrap() {
            break;
        }
        assert!(matches!(
            member.core.step(&mut member.adapter).unwrap(),
            Step::Realized(_)
        ));
    }
    hive.node(1).settle().unwrap();
    let p_beta = hive.node(1).local_of(&CanonicalOp(p.clone())).unwrap();
    hive.repo(1)
        .jj(&["--ignore-working-copy", "op", "integrate", &p_beta.0.hex()]);
    assert_eq!(hive.hive.members[1].adapter.accepted_base().unwrap(), q);
    assert_eq!(
        hive.node(1).canonical_heads().unwrap(),
        [CanonicalOp(p.clone())]
    );

    hive.commit(0, "y", "keep this work");
    hive.repo(0)
        .jj(&["op", "abandon", &format!("{q_alpha}..{p_alpha}")]);
    let mut first_accepted = false;
    hive.hive
        .sync_steps(0, 1, &mut |request, reply| {
            if let (Request::Push { dropped, .. }, Reply::Head { kind, .. }) = (request, &reply) {
                assert_eq!(*kind, HeadKind::Accepted);
                assert!(dropped.contains(&p));
                first_accepted = true;
            }
            reply
        })
        .unwrap();
    assert!(first_accepted);
    let f = hive.hive.hub_head();
    assert!(!hive.node(0).pending_drops().is_empty());
    let saved: serde_json::Value = serde_json::from_slice(
        &std::fs::read(hive.repo(0).repo_path().join("musubi/records.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(saved["fixup_written"], true);
    assert_eq!(hive.hive.members[0].adapter.records().unwrap().count, 0);

    // A power cut may lose the recent custody write while jj's later operation writes
    // survive. Keep this older recovery case reachable without bypassing the new receipt
    // rule: restore the actual record state from before receiving F.
    let before_receipt =
        std::fs::read(hive.repo(1).repo_path().join("musubi/records.json")).unwrap();
    hive.hive.fetch(1).unwrap();
    for _ in 0..16 {
        let member = &mut hive.hive.members[1];
        if member.adapter.is_local(&f).unwrap() {
            break;
        }
        assert!(matches!(
            member.core.step(&mut member.adapter).unwrap(),
            Step::Realized(_)
        ));
    }
    hive.node(1).settle().unwrap();
    let f_beta = hive.node(1).local_of(&CanonicalOp(f)).unwrap();
    assert_eq!(hive.hive.members[1].adapter.records().unwrap().count, 0);
    std::fs::write(
        hive.repo(1).repo_path().join("musubi/records.json"),
        before_receipt,
    )
    .unwrap();
    hive.reopen(1);
    hive.repo(1).jj(&[
        "--ignore-working-copy",
        "--at-op",
        &f_beta.0.hex(),
        "describe",
        "-m",
        "blind child of fix-up",
    ]);
    hive.repo(1).jj(&[
        "--ignore-working-copy",
        "--at-op",
        &p_beta.0.hex(),
        "describe",
        "-m",
        "child of the old head",
    ]);
    hive.repo(1).jj(&[
        "--ignore-working-copy",
        "op",
        "abandon",
        &format!("{}..{}", q_beta.0.hex(), p_beta.0.hex()),
    ]);
    assert!(!hive.node(1).check_abandon().unwrap());
    assert!(hive.node(1).pending_drops().is_empty());
    assert_eq!(hive.hive.members[1].adapter.records().unwrap().count, 0);

    hive.hive.hub_goes_back(q_seq).unwrap();
    let taken = hive
        .hive
        .sync_steps(1, 24, &mut |request, reply| {
            if let Request::Push { dropped, .. } = request {
                assert!(dropped.is_empty(), "blind sender: {dropped:?}");
            }
            reply
        })
        .unwrap();
    assert!(taken < 24);
    let stable = hive.hive.hub.store().head().0;
    assert_eq!(hive.hive.hub.store().record_count(), 0);
    let parent = hive.hive.hub_head();
    hive.hive.fetch(0).unwrap();
    let mut advanced = false;
    for _ in 0..16 {
        let member = &mut hive.hive.members[0];
        match member.core.step(&mut member.adapter).unwrap() {
            Step::Realized(_) => {}
            Step::Advanced(head) => {
                assert_eq!(head, parent);
                advanced = true;
                break;
            }
            step => panic!("before publication: {step:?}"),
        }
    }
    assert!(advanced);
    let mut oracle = Oracle::spawn();
    let mut model = json!({"op": "retryPublication", "pending":
        (0..hive.node(0).pending_drops().ops().len()).collect::<Vec<_>>(),
        "written": true, "aligned": false, "headKnown": true});
    let next = oracle.call(&model);
    assert_eq!(next["ok"], true, "{next}");
    assert_eq!(next["restoring"], false);
    assert_eq!(next["tip"], true);
    assert_eq!(next["headKnown"], false);
    model["headKnown"] = next["headKnown"].clone();
    let member = &mut hive.hive.members[0];
    let Step::Superseded {
        fixup: Some(tip),
        push,
    } = member.core.step(&mut member.adapter).unwrap()
    else {
        panic!("pending drops need a new publication head");
    };
    let Request::Push { new, dropped, .. } = &push else {
        panic!("not a push");
    };
    assert_eq!(new, &tip);
    assert!(dropped.contains(&p));
    // A lost request publishes nothing. Its retry, including after a restart, reuses the tip.
    drop(push);
    let store = hive.node(0).canonical_store();
    let original = store.read_operation(&CanonicalOp(parent.clone())).unwrap();
    let marked = store.read_operation(&CanonicalOp(tip.clone())).unwrap();
    assert_eq!(marked.parents, std::slice::from_ref(&parent));
    assert_eq!(marked.view_id, original.view_id);
    assert!(marked.metadata.workspace_name.is_none());
    assert_eq!(
        marked
            .metadata
            .attributes
            .get("musubi.fixup")
            .map(String::as_str),
        Some("1")
    );
    for key in [
        "musubi.work",
        "musubi.forget",
        "musubi.forget-after",
        "musubi.settings",
        "musubi.expected",
    ] {
        assert!(
            !marked.metadata.attributes.contains_key(key),
            "replayed {key}"
        );
    }
    for reopen in [false, true] {
        if reopen {
            hive.reopen(0);
            hive.hive.fetch(0).unwrap();
        }
        let member = &mut hive.hive.members[0];
        let Step::Superseded { fixup: None, push } = member.core.step(&mut member.adapter).unwrap()
        else {
            panic!("retry must reuse the publication tip");
        };
        let Request::Push { new, .. } = push else {
            panic!("not a push");
        };
        assert_eq!(new, tip);
        assert_eq!(
            hive.node(0).canonical_heads().unwrap(),
            [CanonicalOp(tip.clone())]
        );
        let next = oracle.call(&model);
        assert_eq!(next["restoring"], false);
        assert_eq!(next["tip"], false);
    }
    let mut accepted = false;
    hive.hive
        .sync_through(0, &mut |request, reply| {
            if let Reply::Head {
                kind: HeadKind::Accepted,
                ..
            } = &reply
            {
                let Request::Push { new, dropped, .. } = request else {
                    panic!("not a push");
                };
                assert_eq!(new, &tip);
                assert!(dropped.contains(&p));
                accepted = true;
            }
            reply
        })
        .unwrap();
    assert!(accepted);
    assert!(hive.node(0).pending_drops().is_empty());
    assert!(hive.hive.hub.is_dropped(&p, &[]).unwrap());
    for round in 0..3 {
        for node in 0..2 {
            let taken = hive
                .hive
                .sync_steps(node, 24, &mut |_, reply| reply)
                .unwrap();
            assert!(taken < 24, "round {round}, node {node}");
        }
        assert_eq!(hive.hive.hub.store().head().0, stable + 1, "round {round}");
        assert_eq!(hive.hive.hub.store().record_count(), 1);
        assert!(hive.node(0).pending_drops().is_empty());
        for node in 0..2 {
            assert!(
                hive.node(node)
                    .is_dropped(&musubi_jj::records::HubOp(CanonicalOp(p.clone())))
            );
        }
        let head = hive.hive.hub_head();
        let records = hive.hive.hub.records();
        for node in 0..2 {
            assert_eq!(hive.hive.members[node].adapter.records().unwrap(), records);
            assert_eq!(
                hive.node(node).canonical_heads().unwrap(),
                [CanonicalOp(head.clone())]
            );
            let member = &mut hive.hive.members[node];
            assert!(matches!(
                member.core.step(&mut member.adapter).unwrap(),
                Step::Idle
            ));
            assert!(
                !member.adapter.when_idle().unwrap(),
                "round {round}, node {node}: maintenance wrote"
            );
        }
    }
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

/// What survives of an operation that is the hub's head when another machine dropped it.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Survivors {
    /// The one operation below it.
    One,
    /// A merge's, one below the other: what is left of the branch dropped with it, and the
    /// other parent.
    Nested,
    /// A merge's two parents, neither below the other, as when two machines merged the same
    /// heads, after the hub went back, and the abandon dropped one merge to the other.
    Apart,
    /// As `Apart`, but each a fetch of origin's `main`, which origin force-pushed between
    /// them: merged, `main@origin` is a conflict.
    Fetches,
    /// As `Fetches`, but the second fetch beta's own, which it published with its work: one
    /// of what survives is beta's op head.
    FetchedHere,
    /// As `Apart`, but the second a rebase that makes a loop with one of beta's own, which jj
    /// can't merge.
    Looping,
}

impl Survivors {
    /// Whether what survives is two operations, neither below the other.
    fn apart(self) -> bool {
        !matches!(self, Self::One | Self::Nested)
    }
}

/// Alpha, gamma and delta colocated, and beta, the machine that waits, colocated only if
/// `colocated`.
fn four_machines(colocated: bool) -> Fixture {
    const NAMES: [&str; 4] = ["alpha", "beta", "gamma", "delta"];
    if colocated {
        return Fixture::new(&NAMES);
    }
    let env = TestEnv::new();
    let repos = NAMES
        .iter()
        .map(|&name| match name {
            "beta" => env.init_non_colocated_repo(name),
            _ => env.init_repo(name),
        })
        .collect();
    Fixture::join(env, repos)
}

/// `refs/remotes/origin/main` in machine `index`'s `.git`.
fn git_main_at_origin(hive: &Fixture, index: usize) -> String {
    hive.repo(index)
        .git(&["rev-parse", "refs/remotes/origin/main"])
        .trim()
        .to_owned()
}

/// `main@origin` as machine `index`'s latest operation records it, without the import of a
/// `jj` command: the commit, or `conflict`.
fn recorded_main_at_origin(hive: &Fixture, index: usize) -> String {
    let template = r#"if(remote == "origin", if(conflict, "conflict", normal_target.commit_id()))"#;
    hive.repo(index).jj(&[
        "--ignore-working-copy",
        "bookmark",
        "list",
        "--all-remotes",
        "main",
        "-T",
        template,
    ])
}

/// Commits `upstream n` to origin's `main` from `seed`: on what it has, or, `forced`, in
/// place of it.
fn push_origin(hive: &Fixture, seed: &Path, n: usize, forced: bool) {
    use crate::remotes::seed_git;

    let origin = hive.env.root().join("origin.git");
    let run = |args: &[&str]| seed_git(hive, seed, args);
    if forced {
        run(&["reset", "--quiet", "--hard", "HEAD~"]);
    }
    std::fs::write(seed.join("upstream"), format!("upstream {n}")).unwrap();
    run(&["commit", "--quiet", "-am", &format!("upstream {n}")]);
    run(&[
        "push",
        "--quiet",
        "--force",
        origin.to_str().unwrap(),
        "main",
    ]);
}

/// In `hive`, of [`four_machines`], alpha abandons an operation the hub accepted, which gamma
/// keeps as its op head, and publishes the abandon. Beta, which has work of its own the hub
/// hasn't, takes alpha's record and realizes the hub's head, but stops before advancing past
/// what the record drops. With `leave`, alpha, and any other machine that would move the hub
/// on, leaves the hive, as `musubi leave` does. Then the hub goes back, losing the record, the
/// abandon and the leaves, and gamma publishes the operation again. Returns the hive, the
/// operation, the machines that left, and how an operation the abandon drops is described.
fn dropped_head_held(
    mut hive: Fixture,
    survivors: Survivors,
    leave: bool,
) -> (Fixture, musubi_sync::OpId, Vec<usize>, String) {
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;
    use musubi_jj::op_id::CanonicalOp;

    // What every machine has first: origin, for fetches; X, Y on it, and Z, for rebases.
    let seed = matches!(survivors, Survivors::Fetches | Survivors::FetchedHere).then(|| {
        let seed = crate::remotes::create_origin(&hive);
        let origin = hive.env.root().join("origin.git");
        for repo in &hive.repos {
            repo.jj(&["git", "remote", "add", "origin", origin.to_str().unwrap()]);
        }
        seed
    });
    if survivors == Survivors::Looping {
        let alpha = hive.repo(0);
        alpha.jj(&["new", "root()", "-m", "X"]);
        alpha.jj(&["new", "-m", "Y"]);
        alpha.jj(&["new", "root()", "-m", "Z"]);
        alpha.jj(&["new", "root()"]);
    }
    if seed.is_some() || survivors == Survivors::Looping {
        hive.sync();
    }
    let base = hive.hive.hub.store().head().0;
    // Beta's own work on the base, not yet published.
    hive.commit(1, "w", "beta's work");
    match survivors {
        // A fetch, before origin moves: its `.git` holds what its head records.
        Survivors::Fetches => {
            hive.repo(1).jj(&["git", "fetch"]);
        }
        Survivors::Looping => {
            let (x, z) = (hive.commit_id(1, "X"), hive.commit_id(1, "Z"));
            hive.repo(1).jj(&["rebase", "-s", &x, "-o", &z]);
        }
        _ => {}
    }
    let bookmark = |hive: &mut Fixture, name: &str| {
        hive.repo(0).jj(&["bookmark", "create", name, "-r", "@-"]);
        hive.hive.sync(0).unwrap();
        (op_log(hive.repo(0))[0].0.clone(), hive.hive.hub_head())
    };
    // Steps `machine` until it advances, merging with its own head, but doesn't push.
    let advance_only = |hive: &mut Fixture, machine: usize| {
        hive.hive.fetch(machine).unwrap();
        let member = &mut hive.hive.members[machine];
        for _ in 0..16 {
            match member.core.step(&mut member.adapter).unwrap() {
                Step::Advanced(_) => return,
                Step::Realized(_) | Step::Send(_) => {}
                step => panic!("{step:?}"),
            }
        }
        panic!("machine {machine} didn't advance");
    };
    let (abandon, kept, gone, regress, also_leave) = match survivors {
        Survivors::One => {
            bookmark(&mut hive, "p");
            let (x, x_hub) = bookmark(&mut hive, "x");
            hive.hive.sync(2).unwrap();
            bookmark(&mut hive, "y");
            (x, x_hub, "create bookmark x".to_owned(), base, vec![])
        }
        Survivors::Nested => {
            hive.commit(2, "d", "gamma's work");
            let gammas = op_log(hive.repo(2))[0].1.clone();
            hive.commit(0, "a", "alpha's work");
            let alphas = op_log(hive.repo(0))[0].1.clone();
            hive.hive.sync(0).unwrap();
            // Gamma merges alpha's work with its own: the merge it keeps.
            hive.hive.sync(2).unwrap();
            let merge = hive.hive.hub_head();
            hive.hive.sync(0).unwrap();
            bookmark(&mut hive, "y");
            let below = op_described(hive.repo(0), &gammas);
            let at = op_described(hive.repo(0), "reconcile divergent operations");
            (format!("{below}..{at}"), merge, alphas, base, vec![])
        }
        Survivors::Apart | Survivors::Fetches | Survivors::FetchedHere | Survivors::Looping => {
            // Alpha's p, which delta takes; the hub goes back, and gamma's q comes instead.
            // Each on its machine's working-copy commit, which `.git` can have. Or each a
            // fetch, of commits neither below the other, q beta's for `FetchedHere`. Or q a
            // rebase, for `Looping`.
            match &seed {
                Some(seed) => {
                    push_origin(&hive, seed, 2, false);
                    hive.repo(0).jj(&["git", "fetch"]);
                }
                None => {
                    hive.repo(0).jj(&["bookmark", "create", "p", "-r", "@"]);
                }
            }
            hive.hive.sync(0).unwrap();
            hive.hive.sync(3).unwrap();
            hive.hive.hub_goes_back(base).unwrap();
            let q_by = if survivors == Survivors::FetchedHere {
                1
            } else {
                2
            };
            match &seed {
                Some(seed) => {
                    push_origin(&hive, seed, 3, true);
                    hive.repo(q_by).jj(&["git", "fetch"]);
                }
                None if survivors == Survivors::Looping => {
                    let (y, z) = (hive.commit_id(2, "Y"), hive.commit_id(2, "Z"));
                    hive.repo(2).jj(&["rebase", "-s", &z, "-o", &y]);
                }
                None => {
                    hive.repo(2).jj(&["bookmark", "create", "q", "-r", "@"]);
                }
            }
            hive.hive.sync(q_by).unwrap();
            let q = hive.hive.hub.store().head().0;
            // Delta and alpha each merge p and q; alpha's is accepted, which gamma keeps.
            advance_only(&mut hive, 3);
            hive.hive.sync(0).unwrap();
            let ours = hive.hive.hub_head();
            hive.hive.sync(2).unwrap();
            hive.hive.sync(3).unwrap();
            let both = hive.hive.hub_head();
            hive.hive.sync(0).unwrap();
            bookmark(&mut hive, "y");
            let node = hive.node(0);
            let parents = node
                .canonical_store()
                .parents(&CanonicalOp(both.clone()))
                .unwrap();
            assert_eq!(parents.len(), 2, "{parents:?}");
            let theirs = parents.into_iter().find(|op| op.0 != ours).unwrap();
            let local = |op: &CanonicalOp| {
                let local = node.local_of(op).unwrap();
                jj_lib::object_id::ObjectId::hex(&local.0)
            };
            // Only alpha's merge: delta's has both its parents.
            let range = format!("{}..{}", local(&theirs), local(&CanonicalOp(ours.clone())));
            (
                range,
                ours,
                "reconcile divergent operations".to_owned(),
                q,
                vec![3],
            )
        }
    };
    hive.repo(0).jj(&["op", "abandon", &abandon]);
    hive.hive.sync(0).unwrap();
    assert_eq!(hive.hive.hub.store().record_count(), 1, "{survivors:?}");
    let mut left = vec![];
    if leave {
        for machine in std::iter::once(0).chain(also_leave) {
            // As `musubi leave` does: forget this copy, sync, and, the hive having it gone,
            // put its workspaces back; then it stops.
            let removed = hive.node(machine).forget_self().unwrap().unwrap();
            hive.hive.sync(machine).unwrap();
            let key = hive.node(machine).machine().key().to_owned();
            let (_, presence) = hive.node(machine).present_copies().unwrap();
            assert!(!presence.is_present(&key), "{machine} still present");
            hive.node(machine).restore_workspaces(&removed).unwrap();
            left.push(machine);
        }
    }

    // Beta takes the record and realizes the hub's head; the next step would advance to it.
    hive.hive.fetch(1).unwrap();
    let member = &mut hive.hive.members[1];
    let mut adopted = false;
    let mut realized = false;
    for _ in 0..32 {
        let known = member.core.known().1.clone();
        if adopted && member.adapter.is_local(&known).unwrap() {
            realized = true;
            break;
        }
        match member.core.step(&mut member.adapter).unwrap() {
            Step::Adopted => adopted = true,
            Step::Realized(_) | Step::Send(_) => {}
            step => panic!("{survivors:?}: {step:?}"),
        }
    }
    assert!(adopted && realized, "{survivors:?}");
    hive.reopen(1);

    // The hub loses the record, the abandon and the leaves; gamma publishes it again.
    hive.hive.hub_goes_back(regress).unwrap();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub_head(), kept, "{survivors:?}");
    (hive, kept, left, gone)
}

/// Syncs `participants` in fair rounds, each sync followed by the work a daemon does when its
/// policy is idle, until a round changes nothing. Some participant makes an accepted push that
/// drops `kept`, which the hub then has dropped, before the others take the record: once every
/// machine has, the hub prunes it, forgetting the ids it dropped. Returns whether beta made it.
fn settle_participants(
    hive: &mut Fixture,
    participants: &[usize],
    kept: &musubi_sync::OpId,
) -> bool {
    use musubi_core::hub::HubStorage as _;

    let (mut dropped_by, mut checked) = (None, false);
    for _ in 0..6 {
        let before = hive.hive.hub.store().head().0;
        let mut quiet = true;
        for &n in participants {
            let taken = hive
                .hive
                .sync_steps(n, 60, &mut |request, reply| {
                    if let (
                        Request::Push { dropped, .. },
                        Reply::Head {
                            kind: HeadKind::Accepted,
                            ..
                        },
                    ) = (request, &reply)
                        && dropped.contains(kept)
                    {
                        dropped_by.get_or_insert(n);
                    }
                    reply
                })
                .unwrap();
            if dropped_by.is_some() && !checked {
                assert!(hive.hive.hub.is_dropped(kept, &[]).unwrap(), "{n}");
                checked = true;
            }
            let idle = hive.hive.members[n].adapter.when_idle().unwrap();
            assert!(taken < 60, "{n} keeps stepping");
            quiet &= taken == 0 && !idle;
        }
        if quiet && hive.hive.hub.store().head().0 == before {
            assert!(checked, "no accepted push dropped {kept:?}");
            return dropped_by == Some(1);
        }
    }
    panic!("the hive doesn't settle");
}

/// The hive, as `participants` have it, has dropped `kept`, the operation `gone` describes,
/// and has beta's work: every participant at the hub's head, with its records and nothing
/// pending. Beta merged what survives of `kept` with its own work in one operation, as jj
/// merges op heads: both survivors where neither is below the other, not one at a time; of
/// nested ones only the upper, not what its own work is on already.
fn assert_dropped_head_settled(
    hive: &mut Fixture,
    participants: &[usize],
    kept: &musubi_sync::OpId,
    gone: &str,
    survivors: Survivors,
) {
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_jj::op_id::CanonicalOp;
    use musubi_jj::records::HubOp;

    let hub = hive.hive.hub_head();
    // The hub may have pruned the record since (`settle_participants` checked it held it), so
    // every participant holds it, as the hub's count and digest say.
    let records = hive.hive.hub.records();
    assert!(records.count >= 1, "the drop is lost");
    for &n in participants {
        assert_eq!(
            hive.node(n).canonical_heads().unwrap(),
            [CanonicalOp(hub.clone())],
            "{n}"
        );
        assert!(hive.node(n).pending_drops().is_empty(), "{n}");
        assert_eq!(
            hive.hive.members[n].adapter.records().unwrap(),
            records,
            "{n}"
        );
        assert!(
            hive.node(n).is_dropped(&HubOp(CanonicalOp(kept.clone()))),
            "{n}"
        );
        assert!(
            hive.visible(n).iter().any(|c| c.ends_with("beta's work")),
            "{n} lacks beta's work"
        );
        // Apart's description is the merges' it keeps too.
        if !survivors.apart() {
            assert!(
                !history(hive.repo(n))
                    .iter()
                    .any(|(_, d)| d.starts_with(gone)),
                "{n} still has {gone}"
            );
        }
    }
    let merges = hive.repo(1).jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-T",
        "description.first_line() ++ \" \" ++ parents.len() ++ \"\\n\"",
    ]);
    let three = merges
        .lines()
        .any(|line| line == "reconcile divergent operations 3");
    let beside_own_work = matches!(survivors, Survivors::Apart | Survivors::Fetches);
    assert_eq!(three, beside_own_work, "{merges}");
    if matches!(survivors, Survivors::Fetches | Survivors::FetchedHere) {
        // Every `.git` holds the same side of the conflict, which the import of each `jj`
        // command above took alike.
        let sides: BTreeSet<String> = participants
            .iter()
            .map(|&n| {
                let side = git_main_at_origin(hive, n);
                assert_eq!(recorded_main_at_origin(hive, n), side, "{n}");
                side
            })
            .collect();
        assert_eq!(sides.len(), 1, "{sides:?}");
    }
}

/// The operations of `store` that `ops` stand for, and every one below them, numbered so
/// that parents come first, with their parents as each was made, by the immutable
/// `musubi.original-parents` each version keeps, and each version taken for its original.
/// Returns the originals in that order, and each one's parents' numbers.
fn original_history(
    store: &musubi_jj::canonical::CanonicalStore,
    ops: &[musubi_jj::op_id::CanonicalOp],
) -> (Vec<jj_lib::op_store::OperationId>, Vec<Vec<usize>>) {
    use jj_lib::op_store::OperationId;
    use musubi_jj::op_id::CanonicalOp;

    let root = store.root_operation_id().clone();
    let parents_of = |op: &CanonicalOp| -> Vec<CanonicalOp> {
        if *op == root {
            return vec![];
        }
        let read = store.read_operation(op).unwrap();
        read.metadata.attributes["musubi.original-parents"]
            .split(' ')
            .map(|hex| CanonicalOp(OperationId::try_from_hex(hex).unwrap()))
            .collect()
    };
    let original = |op: &CanonicalOp| -> OperationId {
        if *op == root {
            root.0.clone()
        } else {
            store.original_id(op).unwrap()
        }
    };
    let mut order: Vec<OperationId> = vec![];
    let mut parents: Vec<Vec<usize>> = vec![];
    let mut stack: Vec<(CanonicalOp, bool)> = ops.iter().map(|op| (op.clone(), false)).collect();
    let mut seen = std::collections::HashSet::new();
    while let Some((op, expanded)) = stack.pop() {
        let id = original(&op);
        if expanded {
            if !order.contains(&id) {
                let numbered = parents_of(&op)
                    .iter()
                    .map(|parent| {
                        let parent = original(parent);
                        order.iter().position(|o| *o == parent).unwrap()
                    })
                    .collect();
                order.push(id);
                parents.push(numbered);
            }
            continue;
        }
        if !seen.insert(op.clone()) {
            continue;
        }
        stack.push((op.clone(), true));
        stack.extend(parents_of(&op).into_iter().map(|parent| (parent, false)));
    }
    (order, parents)
}

/// The finite local-work model reads the raw hub closure and the node's raw images as
/// different vertices, including when a pending drop rewrites the known operation.
#[test]
fn local_burst_conforms_across_a_pending_namespace() {
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;
    use musubi_jj::canonical::CanonicalStore;
    use musubi_jj::op_id::CanonicalOp;
    use musubi_jj::records::HubOp;
    use serde_json::json;

    use crate::oracle::Oracle;

    fn check_reads(hive: &mut Fixture, oracle: &mut Oracle) {
        use musubi_core::hub;
        use musubi_core::message::RecordState;
        use musubi_sync::{Attachment, OpId};

        type HubSnapshot = (u64, OpId, RecordState);
        fn hub_snapshot(hive: &Fixture) -> HubSnapshot {
            let (seq, head) = hive.hive.hub.store().head();
            (seq, head.clone(), hive.hive.hub.records())
        }
        let member = &hive.hive.members[1];
        let requests = [
            member.adapter.poll(&member.core).unwrap(),
            Request::GetObjects {
                for_ops: vec![hive.hive.hub_head()],
                base: member.adapter.root().clone(),
                haves: Attachment::None,
            },
        ];
        for request in requests {
            let call = match &request {
                Request::Fetch { .. } => "fetch",
                Request::GetObjects { .. } => "objects",
                Request::Push { .. } => unreachable!(),
            };
            let before = hub_snapshot(hive);
            // Observe the read handler itself; pruning and node callbacks are other events.
            let handled = hub::handle(&mut hive.hive.hub, request).unwrap();
            assert!(handled.publish.is_none(), "a read must not publish a head");
            let after = hub_snapshot(hive);
            let (kind, reply_snap, reply_records) = match &handled.reply {
                Reply::Fetched {
                    seq, head, records, ..
                } => ("fetched", Some((*seq, head.clone(), records.clone())), None),
                Reply::Objects { .. } => ("objects", None, None),
                Reply::Head {
                    seq, head, records, ..
                } => ("head", Some((*seq, head.clone(), records.clone())), None),
                Reply::Refused { records } => ("refused", None, Some(records.clone())),
            };
            let mut heads = vec![before.1.clone(), after.1.clone()];
            let mut records = vec![before.2.clone(), after.2.clone()];
            if let Some(snap) = &reply_snap {
                heads.push(snap.1.clone());
                records.push(snap.2.clone());
            }
            if let Some(state) = &reply_records {
                records.push(state.clone());
            }
            // Intern full identities by equality: a changed digest with the same count gets
            // another label, as does a changed raw head. No bits of either are truncated.
            let record_id = |state: &RecordState| records.iter().position(|s| s == state).unwrap();
            let encode = |s: &HubSnapshot| {
                json!({
                    "seq": s.0, "head": heads.iter().position(|h| h == &s.1).unwrap(),
                    "recs": record_id(&s.2),
                })
            };
            let observed = json!({
                "op": "hubRead", "call": call,
                "before": encode(&before), "after": encode(&after), "kind": kind,
                "replySnap": reply_snap.as_ref().map(encode),
                "replyRecs": reply_records.as_ref().map(record_id),
            });
            let checked = oracle.call(&observed);
            assert_eq!(checked["ok"], true, "{observed}: {checked}");
            assert_eq!(checked["matches"], true, "{observed}: {checked}");
        }
    }

    struct Snapshot {
        local: Vec<CanonicalOp>,
        heads: Vec<CanonicalOp>,
        plan: Vec<CanonicalOp>,
        images: Vec<CanonicalOp>,
    }
    fn snapshot(hive: &Fixture, raw: &[CanonicalOp]) -> Snapshot {
        let member = &hive.hive.members[1];
        let known = member.core.known().1.clone();
        let repo = member.adapter.repo();
        let heads = repo
            .local_heads()
            .unwrap()
            .iter()
            .map(|op| repo.canonical_of(op).expect("the core mapped its head"))
            .collect();
        Snapshot {
            local: raw
                .iter()
                .filter(|op| member.adapter.is_local(&op.0).unwrap())
                .cloned()
                .collect(),
            heads,
            plan: member.core.planned().cloned().map(CanonicalOp).collect(),
            images: member
                .adapter
                .repo()
                .to_node(&HubOp(CanonicalOp(known)))
                .unwrap()
                .into_iter()
                .map(|op| op.0)
                .collect(),
        }
    }
    fn graph(stores: [&CanonicalStore; 2], tops: Vec<CanonicalOp>) -> Vec<CanonicalOp> {
        let mut order = vec![];
        let mut seen = std::collections::HashSet::new();
        let mut stack: Vec<_> = tops.into_iter().map(|op| (op, false)).collect();
        while let Some((op, expanded)) = stack.pop() {
            if expanded {
                order.push(op);
            } else if seen.insert(op.clone()) {
                let store = stores.iter().find(|s| s.has_operation(&op)).unwrap();
                stack.push((op.clone(), true));
                stack.extend(store.parents(&op).unwrap().into_iter().map(|p| (p, false)));
            }
        }
        order
    }

    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "ancestor beta will drop");
    hive.sync();
    let a = hive.hive.hub_head();
    let a_beta = hive.node(1).local_of(&CanonicalOp(a)).unwrap();
    hive.commit(0, "b", "descendant beta has not received");
    hive.hive.sync(0).unwrap();
    let known = hive.hive.hub_head();
    hive.commit(1, "own", "beta's unpublished work above the ancestor");
    hive.repo(1).jj(&["op", "abandon", &a_beta.0.hex()]);
    hive.hive.fetch(1).unwrap();
    hive.hive.members[1].adapter.before_sync().unwrap();
    hive.hive.members[1].adapter.heads_for(&known).unwrap();
    let raw = hive
        .hive
        .hub
        .store()
        .canonical()
        .ancestors_until(&[CanonicalOp(known.clone())], |_| false)
        .unwrap();
    let mut oracle = Oracle::spawn();
    check_reads(&mut hive, &mut oracle);
    let mut realized = false;
    let mut advanced = false;
    let mut pushed = false;
    for _ in 0..24 {
        let before = snapshot(&hive, &raw);
        assert!(!before.images.contains(&CanonicalOp(known.clone())));
        let step = {
            let member = &mut hive.hive.members[1];
            member.core.step(&mut member.adapter).unwrap()
        };
        let (kind, op) = match step {
            Step::Realized(op) => {
                realized = true;
                ("realize", Some(CanonicalOp(op)))
            }
            Step::Merged => ("merge", None),
            Step::Advanced(_) => {
                advanced = true;
                ("advance", None)
            }
            Step::Superseded { push, .. } => {
                let Request::Push {
                    expected,
                    new,
                    records,
                    dropped,
                    ..
                } = &push
                else {
                    unreachable!("a supersede carries a push");
                };
                assert_eq!(expected, hive.hive.hub.store().head().1);
                assert_eq!(*records, hive.hive.hub.records());
                let count = hive.hive.hub.store().record_count();
                let effective: BTreeSet<_> = dropped
                    .iter()
                    .filter(|p| !hive.hive.hub.store().is_superseded(p))
                    .cloned()
                    .collect();
                // This packet names unpublished originals in the current hub namespace:
                // none is merely an obsolete rewritten alias that contraction ignores.
                let node = &hive.hive.members[1].adapter;
                let applied = node.applied_records().unwrap();
                assert_eq!(
                    applied.base.count, 0,
                    "this fixture has its whole record list"
                );
                let canonical = node.repo().canonical_store();
                let recorded: std::collections::HashSet<_> = applied
                    .records
                    .iter()
                    .flatten()
                    .map(|p| canonical.original_id(&CanonicalOp(p.clone())).unwrap())
                    .collect();
                let mut all_dropped = recorded.clone();
                for p in dropped {
                    let original = canonical.original_id(&CanonicalOp(p.clone())).unwrap();
                    assert!(!recorded.contains(&original));
                    assert!(effective.contains(p) || recorded.contains(&original));
                    all_dropped.insert(original);
                }
                assert!(!effective.is_empty());
                // Check the actual post-write head sent by this call, including its root,
                // rather than only the parents used to construct the fix-up.
                let sent = CanonicalOp(new.clone());
                let closure = canonical
                    .record_operations(std::slice::from_ref(&sent))
                    .unwrap();
                assert!(closure.contains(&sent));
                for op in closure {
                    assert!(!all_dropped.contains(&canonical.original_id(&op).unwrap()));
                }
                let handled = hive.hive.handle(push).unwrap();
                assert!(handled.publish.is_some());
                assert_eq!(hive.hive.hub.store().record_count(), count + 1);
                let appended: BTreeSet<_> = hive
                    .hive
                    .hub
                    .store()
                    .records()
                    .last()
                    .unwrap()
                    .ops()
                    .iter()
                    .map(|p| p.0.0.clone())
                    .collect();
                assert_eq!(appended, effective);
                let member = &mut hive.hive.members[1];
                member
                    .core
                    .handle_reply(&mut member.adapter, handled.reply)
                    .unwrap();
                pushed = true;
                break;
            }
            other => panic!("unexpected step in the complete-metadata burst: {other:?}"),
        };
        let after = snapshot(&hive, &raw);
        assert_eq!(before.images, after.images);
        let stores = [
            hive.hive.members[1].adapter.repo().canonical_store(),
            hive.hive.hub.store().canonical(),
        ];
        let mut tops = raw.clone();
        for state in [&before, &after] {
            tops.extend(
                state
                    .heads
                    .iter()
                    .chain(&state.plan)
                    .chain(&state.images)
                    .cloned(),
            );
        }
        let order = graph(stores, tops);
        let number = |op: &CanonicalOp| order.iter().position(|id| id == op).unwrap();
        let numbers = |ops: &[CanonicalOp]| ops.iter().map(number).collect::<Vec<_>>();
        let encode = |s: &Snapshot| {
            json!({
                "local": numbers(&s.local), "heads": numbers(&s.heads), "plan": numbers(&s.plan),
            })
        };
        let parents: Vec<Vec<usize>> = order
            .iter()
            .map(|op| {
                let store = stores.iter().find(|s| s.has_operation(op)).unwrap();
                store.parents(op).unwrap().iter().map(number).collect()
            })
            .collect();
        let reply = oracle.call(&json!({
            "op": "rawBurst", "parents": parents, "rawClosure": numbers(&raw),
            "images": numbers(&before.images), "kind": kind, "opId": op.as_ref().map(number),
            "before": encode(&before), "after": encode(&after),
        }));
        assert_eq!(reply["ok"], true, "{reply}");
        assert_eq!(reply["matches"], true, "{kind}: {reply}");
    }
    assert!(realized && advanced && pushed);
    check_reads(&mut hive, &mut oracle);
    hive.sync();
    hive.assert_converged();
}

/// An interrupted replacement by a Git-exported copy leaves two physical heads with one
/// canonical id. jj merges those aliases into a new child; canonical-set deduplication would
/// hide that write. The fine suffix must start after physical normalization completes.
#[test]
fn interrupted_git_export_can_leave_aliased_operation_heads() {
    use futures::executor::block_on;
    use jj_lib::object_id::ObjectId as _;
    use jj_lib::op_store::OperationId;
    use musubi_core::node::{LocalRepo as _, Step};
    use musubi_jj::op_id::LocalOp;
    use std::io::{BufRead as _, BufReader, Write as _};
    use std::process::Stdio;

    let mut fixture = Fixture::new(&["alpha"]);
    let commit = fixture
        .repo(0)
        .jj(&["log", "--no-graph", "-r", "@", "-T", "commit_id"]);
    let base = fixture.node(0).local_heads().unwrap()[0].clone();
    // Use a real prepared git transaction, so jj's export of p encounters a held ref lock.
    // Its operation is still published; this supported export failure leaves recorded git
    // state behind the bookmark. Abort before native merge retries the export.
    let mut git = fixture
        .repo(0)
        .program(Path::new("git"))
        .args(["update-ref", "--stdin"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = git.stdin.take().unwrap();
    let mut output = BufReader::new(git.stdout.take().unwrap());
    writeln!(
        input,
        "start\ncreate refs/heads/p {}\nprepare",
        commit.trim()
    )
    .unwrap();
    input.flush().unwrap();
    for expected in ["start: ok", "prepare: ok"] {
        let mut line = String::new();
        output.read_line(&mut line).unwrap();
        assert_eq!(line.trim(), expected);
    }
    fixture.repo(0).jj(&[
        "--ignore-working-copy",
        "bookmark",
        "create",
        "p",
        "-r",
        "@",
    ]);
    writeln!(input, "abort").unwrap();
    input.flush().unwrap();
    drop(input);
    let mut response = String::new();
    output.read_line(&mut response).unwrap();
    assert_eq!(response.trim(), "abort: ok");
    assert!(git.wait().unwrap().success());
    fixture.repo(0).jj(&[
        "--ignore-working-copy",
        "--at-op",
        &base.0.hex(),
        "bookmark",
        "create",
        "q",
        "-r",
        "@",
    ]);
    let repo_path = fixture.repo(0).repo_path();
    let operation_ids = || -> BTreeSet<OperationId> {
        std::fs::read_dir(repo_path.join("op_store/operations"))
            .unwrap()
            .map(|entry| entry.unwrap().file_name().into_string().unwrap())
            .filter_map(|name| OperationId::try_from_hex(&name))
            .collect()
    };
    let member = &mut fixture.hive.members[0];
    let initial_heads = member.adapter.heads().unwrap();
    assert_eq!(initial_heads.len(), 2);
    let before = operation_ids();
    let first = member.core.step(&mut member.adapter).unwrap();
    assert!(matches!(first, Step::Merged));
    let repo = member.adapter.repo_mut();
    let exported = repo.local_heads().unwrap();
    assert_eq!(exported.len(), 1);
    let exported = exported[0].clone();
    let ebody = block_on(repo.loader().op_store().read_operation(&exported.0)).unwrap();
    let canonical = repo.canonical_heads().unwrap();
    assert_eq!(canonical.len(), 1);
    let canonical = canonical[0].clone();
    let mut originals = vec![];
    for id in operation_ids().difference(&before) {
        if *id == exported.0 {
            continue;
        }
        let body = block_on(repo.loader().op_store().read_operation(id)).unwrap();
        if body.parents == ebody.parents
            && body.metadata == ebody.metadata
            && body.commit_predecessors == ebody.commit_predecessors
            && body.view_id != ebody.view_id
        {
            let local = LocalOp(id.clone());
            assert_eq!(repo.canonicalize(&local).unwrap(), canonical);
            originals.push(local);
        }
    }
    assert_eq!(
        originals.len(),
        1,
        "native merge must have produced an actual export replacement"
    );
    let original = originals.pop().unwrap();
    assert_ne!(original, exported);
    // Recreate only the lost removal: the actual old and new shipping bodies are untouched.
    block_on(
        repo.loader()
            .op_heads_store()
            .update_op_heads(&[], &original.0),
    )
    .unwrap();
    let known = member.core.known().1.clone();
    let heads = member.adapter.heads_for(&known).unwrap();
    assert_eq!(heads, vec![canonical.0.clone(), canonical.0.clone()]);
    let second = member.core.step(&mut member.adapter).unwrap();
    assert!(matches!(second, Step::Merged));
    let after = member.adapter.repo_mut().canonical_heads().unwrap();
    assert_eq!(after.len(), 1);
    assert_ne!(after[0], canonical);
    let parents = member
        .adapter
        .repo()
        .canonical_store()
        .parents(&after[0])
        .unwrap();
    assert_eq!(parents, vec![canonical]);
}

/// Identical ordinary merges on different copies are one canonical operation. The structural
/// write projection must allow the second copy to reuse the raw vertex the first wrote.
#[test]
fn independent_merges_can_reuse_a_canonical_operation() {
    use crate::oracle::Oracle;
    use jj_lib::config::{ConfigLayer, ConfigSource};
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::{LocalRepo as _, Step};
    use musubi_jj::node::NodeRepo;
    use musubi_jj::objects::Backend;
    use musubi_jj::op_id::CanonicalOp;
    use musubi_sync::hive::Hive;
    use musubi_sync::node::SystemClock;
    use musubi_testutil::TestEnv;

    let env = TestEnv::new();
    let repos: Vec<_> = ["alpha", "beta", "gamma", "delta"]
        .into_iter()
        .map(|name| env.init_simple_repo(name))
        .collect();
    let mut hive = Hive::new(&env.root().join("hub"), Backend::Simple).unwrap();
    hive.pruning = false;
    for repo in &repos {
        let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
        node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
            .unwrap();
        add_node(&mut hive, &env, node);
    }
    hive.sync_all().unwrap();
    let (sseq, s) = hive.hub.store().head();
    let (sseq, s) = (sseq, s.clone());

    // Gamma keeps the old physical S while the other copies hold P.
    repos[0].jj(&[
        "--ignore-working-copy",
        "bookmark",
        "create",
        "p",
        "-r",
        "root()",
    ]);
    hive.sync(0).unwrap();
    hive.sync(1).unwrap();
    hive.sync(3).unwrap();
    hive.sync(0).unwrap();
    let p = hive.hub_head();
    for n in [0, 1, 3] {
        assert_eq!(hive.members[n].adapter.heads().unwrap(), vec![p.clone()]);
        assert!(hive.members[n].adapter.pending().unwrap().is_empty());
    }
    assert_eq!(hive.members[2].adapter.heads().unwrap(), vec![s.clone()]);

    hive.hub_goes_back(sseq).unwrap();
    repos[2].jj(&[
        "--ignore-working-copy",
        "bookmark",
        "create",
        "q",
        "-r",
        "root()",
    ]);
    hive.sync(2).unwrap();
    let q = hive.hub_head();
    let qseq = hive.hub.store().head().0;
    let store = hive.hub.store().canonical();
    assert!(
        !store
            .is_ancestor_of(&CanonicalOp(p.clone()), &CanonicalOp(q.clone()))
            .unwrap()
    );
    assert!(
        !store
            .is_ancestor_of(&CanonicalOp(q.clone()), &CanonicalOp(p.clone()))
            .unwrap()
    );
    assert_eq!(hive.hub.records().count, 0);

    fn closure(
        store: &musubi_jj::canonical::CanonicalStore,
        roots: &[CanonicalOp],
    ) -> Vec<CanonicalOp> {
        let mut order = vec![];
        let mut seen = std::collections::HashSet::new();
        let mut stack: Vec<_> = roots.iter().cloned().map(|op| (op, false)).collect();
        while let Some((op, expanded)) = stack.pop() {
            if expanded {
                order.push(op);
            } else if seen.insert(op.clone()) {
                stack.push((op.clone(), true));
                stack.extend(store.parents(&op).unwrap().into_iter().map(|p| (p, false)));
            }
        }
        order
    }
    let mut oracle = Oracle::spawn();
    let mut global = vec![];
    let mut merged = vec![];
    for n in [0, 1, 3] {
        // Supported jj metadata settings, held fixed through the shipping initial Fetch and
        // ordinary advance. The system clock's tick deliberately leaves settings alone.
        let mut config = repos[n].settings().config().clone();
        config.remove_layers(ConfigSource::CommandArg);
        config.add_layer(
            ConfigLayer::parse(
                ConfigSource::CommandArg,
                r#"
operation.hostname = "the-same-host"
operation.username = "the-same-user"
debug.operation-timestamp = "2020-01-01T00:00:00Z"
debug.commit-timestamp = "2020-01-01T00:00:00Z"
"#,
            )
            .unwrap(),
        );
        let settings = repos[n].settings().with_new_config(config).unwrap();
        let node = NodeRepo::open(&repos[n].repo_path(), &settings).unwrap();
        let member = &mut hive.members[n];
        member.adapter = musubi_sync::node::NodeAdapter::new(node).unwrap();
        member.adapter.set_clock(Box::new(SystemClock));
        member.core.restart();
        hive.fetch(n).unwrap();
        if n == 3 {
            // Alpha publishes M. Delta realizes it detached, then the hub goes back to Q:
            // delta's physical head is still P, but its labels and local store already hold M.
            let member = &mut hive.members[0];
            let Step::Send(mut requests) = member.core.step(&mut member.adapter).unwrap() else {
                panic!("alpha must publish its merge")
            };
            assert_eq!(requests.len(), 1);
            let handled = hive.handle(requests.pop().unwrap()).unwrap();
            assert!(handled.publish.is_some());
            let member = &mut hive.members[0];
            member
                .core
                .handle_reply(&mut member.adapter, handled.reply)
                .unwrap();
            hive.fetch(n).unwrap();
            let m: &CanonicalOp = &merged[0];
            for _ in 0..32 {
                let member = &mut hive.members[n];
                if member.adapter.is_local(&m.0).unwrap() {
                    break;
                }
                assert!(matches!(
                    member.core.step(&mut member.adapter).unwrap(),
                    Step::Realized(_)
                ));
            }
            let member = &mut hive.members[n];
            assert!(member.adapter.is_local(&m.0).unwrap());
            assert_eq!(member.adapter.heads().unwrap(), vec![p.clone()]);
            hive.hub_goes_back(qseq).unwrap();
            hive.fetch(n).unwrap();
        }
        // Structural labels expose the two heads' ancestry; they make no claim about which
        // operations have been realized. Raw ids are shared across both observed writes.
        let roots = if n == 3 {
            vec![merged[0].clone()]
        } else {
            vec![CanonicalOp(p.clone()), CanonicalOp(q.clone())]
        };
        let old = closure(hive.members[n].adapter.repo().canonical_store(), &roots);
        if global.is_empty() {
            global = old.clone();
        }
        let global_before = global.clone();
        let mut did_advance = false;
        for _ in 0..32 {
            let member = &mut hive.members[n];
            match member.core.step(&mut member.adapter).unwrap() {
                Step::Realized(_) | Step::Adopted => {}
                Step::Advanced(_) => {
                    did_advance = true;
                    break;
                }
                other => panic!("unexpected step before ordinary advance: {other:?}"),
            }
        }
        assert!(did_advance);
        let member = &mut hive.members[n];
        let heads = member.adapter.repo_mut().canonical_heads().unwrap();
        assert_eq!(heads.len(), 1);
        let m = heads[0].clone();
        let body = member
            .adapter
            .repo()
            .canonical_store()
            .read_operation(&m)
            .unwrap();
        let mut parents = body.parents.clone();
        parents.sort();
        let mut expected = vec![p.clone(), q.clone()];
        expected.sort();
        assert_eq!(parents, expected);
        assert_eq!(old.contains(&m), n == 3);
        let mut new_labels = old.clone();
        if !new_labels.contains(&m) {
            new_labels.push(m.clone());
        }
        if !global.contains(&m) {
            global.push(m.clone());
        }
        assert_eq!(global.len() - global_before.len(), usize::from(n == 0));
        let store = member.adapter.repo().canonical_store();
        let encode = |raw: &[CanonicalOp], labels: &[CanonicalOp]| {
            let number =
                |ids: &[CanonicalOp], op: &CanonicalOp| ids.iter().position(|id| id == op).unwrap();
            let parents = |ids: &[CanonicalOp]| {
                ids.iter()
                    .map(|op| {
                        store
                            .parents(op)
                            .unwrap()
                            .iter()
                            .map(|p| number(ids, p))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            };
            serde_json::json!({
                "rawParents": parents(raw), "parents": parents(labels),
                "embedding": labels.iter().map(|op| number(raw, op)).collect::<Vec<_>>(),
            })
        };
        let query = serde_json::json!({
            "op": "nodeGrow", "before": encode(&global_before, &old),
            "after": encode(&global, &new_labels),
        });
        let checked = oracle.call(&query);
        assert_eq!(checked["ok"], true, "{query}: {checked}");
        assert_eq!(checked["matches"], true, "{query}: {checked}");
        assert_eq!(hive.hub_head(), q, "each checked write starts from Q");
        merged.push(m);
    }
    assert_eq!(
        merged[0], merged[1],
        "same bytes must reuse the global canonical id"
    );
    assert_eq!(merged[0], merged[2], "delta reuses its existing label too");

    // Publication adds the child head before removing its parents. Retain P beside M as
    // interrupted removal can leave it; the next merge only prunes that redundant head.
    let member = &mut hive.members[3];
    member.adapter.repo_mut().settle().unwrap();
    let repo = member.adapter.repo();
    let local_p = repo.local_of(&CanonicalOp(p.clone())).unwrap();
    futures::executor::block_on(
        repo.loader()
            .op_heads_store()
            .update_op_heads(&[], &local_p.0),
    )
    .unwrap();
    let bodies_before: BTreeSet<_> = repo
        .canonical_store()
        .operation_ids()
        .unwrap()
        .into_iter()
        .collect();
    let mut heads_before = member.adapter.heads_for(&q).unwrap();
    heads_before.sort();
    let mut expected = vec![p, merged[0].0.clone()];
    expected.sort();
    assert_eq!(heads_before, expected);
    let raw = closure(
        member.adapter.repo().canonical_store(),
        &[CanonicalOp(q.clone())],
    );
    let number = |op: &CanonicalOp| global.iter().position(|id| id == op).unwrap();
    let parents: Vec<Vec<usize>> = global
        .iter()
        .map(|op| {
            member
                .adapter
                .repo()
                .canonical_store()
                .parents(op)
                .unwrap()
                .iter()
                .map(number)
                .collect()
        })
        .collect();
    let snapshot = |member: &musubi_sync::hive::Member, heads: &[musubi_sync::OpId]| {
        serde_json::json!({
            "local": raw.iter().filter(|op| member.adapter.is_local(&op.0).unwrap())
                .map(number).collect::<Vec<_>>(),
            "heads": heads.iter().cloned().map(CanonicalOp).map(|op| number(&op)).collect::<Vec<_>>(),
            "plan": member.core.planned().cloned().map(CanonicalOp)
                .map(|op| number(&op)).collect::<Vec<_>>(),
        })
    };
    let before = snapshot(member, &heads_before);
    assert!(matches!(
        member.core.step(&mut member.adapter).unwrap(),
        Step::Merged
    ));
    let heads_after = member.adapter.heads_for(&q).unwrap();
    assert_eq!(heads_after, vec![merged[0].0.clone()]);
    let after = snapshot(member, &heads_after);
    let bodies_after: BTreeSet<_> = member
        .adapter
        .repo()
        .canonical_store()
        .operation_ids()
        .unwrap()
        .into_iter()
        .collect();
    assert_eq!(
        bodies_before, bodies_after,
        "pruning writes no canonical body"
    );
    let query = serde_json::json!({
        "op": "rawBurst", "kind": "merge", "opId": null, "parents": parents,
        "rawClosure": raw.iter().map(number).collect::<Vec<_>>(),
        "images": [number(&CanonicalOp(q.clone()))], "before": before, "after": after,
    });
    let checked = oracle.call(&query);
    assert_eq!(checked["ok"], true, "{query}: {checked}");
    assert_eq!(checked["matches"], true, "{query}: {checked}");
    assert_eq!(hive.hub_head(), q);
}

/// Preparing an incoming record writes rewrites beside the old heads. A core merge still
/// has those raw heads as parents, until the later advance takes the record. This is the
/// merge law used by the raw entry argument before current records have been applied.
#[test]
fn prepared_records_preserve_raw_merge_parents() {
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::node::{LocalRepo as _, Step};
    use musubi_jj::op_id::CanonicalOp;
    use musubi_jj::records::HubOp;

    let mut hive = Fixture::new(&["alpha", "beta"]);
    let before_a = op_log(hive.repo(1))[0].0.clone();
    hive.commit(0, "a", "head the next record drops");
    hive.sync();
    let a = hive.hive.hub_head();
    let a_alpha = hive.node(0).local_of(&CanonicalOp(a.clone())).unwrap();
    hive.hive.members[1].adapter.before_sync().unwrap();
    hive.commit(0, "b", "surviving descendant");
    hive.repo(0).jj(&["op", "abandon", &a_alpha.0.hex()]);
    hive.hive.sync(0).unwrap();
    // Receive through the actual handlers, before any between-round upkeep can merge the
    // two heads this old-operation command is about to create.
    let request = {
        let member = &hive.hive.members[1];
        member.core.poll(&member.adapter).unwrap()
    };
    let reply = hive.hive.handle(request).unwrap().reply;
    {
        let member = &mut hive.hive.members[1];
        member
            .core
            .handle_reply(&mut member.adapter, reply)
            .unwrap();
    }
    hive.repo(1).jj(&[
        "--ignore-working-copy",
        "--at-op",
        &before_a,
        "describe",
        "-m",
        "private branch beside the dropped head",
    ]);
    let known = hive.hive.hub_head();
    let member = &mut hive.hive.members[1];
    let old = member.adapter.heads_for(&known).unwrap();
    assert!(old.len() >= 2);
    assert!(old.contains(&a));
    let images = member
        .adapter
        .repo()
        .to_node(&HubOp(CanonicalOp(known.clone())))
        .unwrap();
    assert!(matches!(
        member.core.step(&mut member.adapter).unwrap(),
        Step::Merged
    ));
    assert_eq!(member.adapter.records().unwrap().count, 0);
    assert!(member.adapter.repo().has_record_custody());
    // Canonicalize the merge as the next normal head read does. This does not invoke the
    // adapter's pending-name reconciliation or advance/take the prepared records.
    let local = member.adapter.repo().local_heads().unwrap();
    assert_eq!(local.len(), 1);
    let merged = member.adapter.repo_mut().canonicalize(&local[0]).unwrap();
    let store = member.adapter.repo().canonical_store();
    for parent in old {
        assert!(store.is_ancestor_of(&CanonicalOp(parent), &merged).unwrap());
    }
    assert_eq!(
        member
            .adapter
            .repo()
            .to_node(&HubOp(CanonicalOp(known)))
            .unwrap(),
        images
    );
    hive.sync();
    hive.assert_converged();
}

/// The local helper contract for what a machine waiting on a dropped hub head would do,
/// which the policy doesn't take yet (it still waits there): advancing to what survives of
/// the operation, as the Lean model's `survivorAdvance` works it out over the original
/// history, merged with this machine's own work in the one operation jj would make of them
/// all, leaves its work in its history and none of what it dropped; and then the policy
/// publishes the drop itself, and the hive settles, without the machine that abandoned the
/// operation, which left. In a colocated repository musubi makes that merge and exports it,
/// a conflicted remote bookmark included, at the side every machine's `.git` holds; in one
/// that isn't, it publishes what survives apart, and jj merges them all at once. This is not
/// the driver's own step: that awaits the model's.
#[test]
fn advancing_to_what_survives_of_a_dropped_head() {
    use musubi_core::node::LocalRepo as _;
    use musubi_jj::op_id::CanonicalOp;
    use musubi_jj::op_id::LocalOp;
    use musubi_jj::records::HubOp;
    use serde_json::json;

    use crate::oracle::Oracle;

    let mut oracle = Oracle::spawn();
    for (survivors, colocated) in [
        (Survivors::One, true),
        (Survivors::Nested, true),
        (Survivors::Apart, true),
        (Survivors::Apart, false),
        (Survivors::Fetches, true),
        (Survivors::FetchedHere, true),
    ] {
        let case = format!("{survivors:?}, colocated: {colocated}");
        let (mut hive, kept, left, gone) =
            dropped_head_held(four_machines(colocated), survivors, true);
        assert_eq!(hive.repo(1).path().join(".git").exists(), colocated);
        let participants: Vec<usize> = (0..hive.hive.members.len())
            .filter(|n| !left.contains(n))
            .collect();
        // At the dropped head, having taken the hub's records, before the step that advances.
        hive.hive.fetch(1).unwrap();
        let member = &mut hive.hive.members[1];
        let step = member.core.step(&mut member.adapter).unwrap();
        assert!(
            matches!(step, musubi_core::node::Step::Adopted),
            "{case}: {step:?}"
        );
        assert_eq!(hive.hive.members[1].core.known().1, kept, "{case}");
        let kept_hub = HubOp(CanonicalOp(kept.clone()));
        assert!(hive.node(1).is_dropped(&kept_hub), "{case}");

        // Before any jj command: the op heads, what stands for them, and the model's answer.
        let (before, heads, dropped, order, frontier, merge, several) = {
            let node = hive.node(1);
            let before = node.local_heads().unwrap();
            let heads: Vec<CanonicalOp> = before
                .iter()
                .map(|h| node.canonical_of(h).unwrap())
                .collect();
            let store = node.canonical_store();
            let dropped: Vec<CanonicalOp> = node
                .pending_drops()
                .ops()
                .iter()
                .chain(node.applied_records().iter().flat_map(|r| r.ops()))
                // The model drops the original, not the surviving parents its current name
                // may already expand to after taking the record.
                .map(|op| op.0.clone())
                .filter(|op| store.has_operation(op))
                .collect();
            let known = CanonicalOp(kept.clone());
            let mut tops = heads.clone();
            tops.push(known.clone());
            tops.extend(dropped.iter().cloned());
            let (order, parents) = original_history(store, &tops);
            let number = |op: &CanonicalOp| {
                let id = store_original(node, op);
                order.iter().position(|o| *o == id).unwrap()
            };
            let reply = oracle.call(&json!({
                "op": "survivorAdvance",
                "parents": parents,
                "dropped": dropped.iter().map(number).collect::<Vec<_>>(),
                "heads": heads.iter().map(number).collect::<Vec<_>>(),
                "known": number(&known),
            }));
            assert_eq!(reply["ok"], true, "{case}: {reply}");
            let numbers = |key: &str| -> BTreeSet<usize> {
                reply[key]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|n| usize::try_from(n.as_u64().unwrap()).unwrap())
                    .collect()
            };
            let images: BTreeSet<usize> = node
                .to_node(&kept_hub)
                .unwrap()
                .iter()
                .map(|n| number(&n.0))
                .collect();
            assert_eq!(
                images,
                numbers("images"),
                "{case}: what survives of the head"
            );
            let merge = reply["merge"].as_bool().unwrap();
            let several = images.len() > 1;
            (
                before,
                heads,
                dropped,
                order,
                numbers("heads"),
                merge,
                several,
            )
        };

        // What beta's own fetch left in its `.git`.
        let fetched = matches!(survivors, Survivors::Fetches | Survivors::FetchedHere)
            .then(|| git_main_at_origin(&hive, 1));

        // The production helper, at that boundary.
        hive.hive.members[1].adapter.advance(&kept).unwrap();

        let node = hive.node(1);
        let number = |op: &CanonicalOp| {
            let id = store_original(node, op);
            order.iter().position(|o| *o == id)
        };
        let after = node.local_heads().unwrap();
        assert_eq!(after.len(), 1, "{case}: {after:?}");
        let head = &after[0];
        let read = |local: &LocalOp| {
            futures::executor::block_on(node.loader().op_store().read_operation(&local.0)).unwrap()
        };
        let reached: BTreeSet<usize> = if merge {
            // A new operation, merging exactly that frontier.
            assert!(!before.contains(head), "{case}");
            let parents = read(head).parents;
            assert_eq!(
                parents.len(),
                frontier.len(),
                "{case}: duplicate merge parents"
            );
            parents
                .iter()
                .map(|p| number(&node.canonical_of(&LocalOp(p.clone())).unwrap()).unwrap())
                .collect()
        } else {
            std::iter::once(number(&node.canonical_of(head).unwrap()).unwrap()).collect()
        };
        assert_eq!(reached, frontier, "{case}: the merge's parents");
        // Its own work stays below it, and nothing it dropped is.
        let mut stack = vec![head.clone()];
        let mut seen = std::collections::HashSet::new();
        let mut below = BTreeSet::new();
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone()) {
                continue;
            }
            if let Some(c) = node.canonical_of(&local) {
                below.insert(store_original(node, &c));
            }
            stack.extend(read(&local).parents.into_iter().map(LocalOp));
        }
        for h in &heads {
            assert!(
                below.contains(&store_original(node, h)),
                "{case}: own work lost"
            );
        }
        for d in &dropped {
            assert!(
                !below.contains(&store_original(node, d)),
                "{case}: dropped is back"
            );
        }
        if !colocated && merge {
            // Published apart, the realizations themselves, which jj then merged at once.
            let read_head = read(head);
            assert_eq!(
                read_head.metadata.description, "reconcile divergent operations",
                "{case}"
            );
            for parent in &read_head.parents {
                let parent = LocalOp(parent.clone());
                let canonical = node.canonical_of(&parent).unwrap();
                assert_eq!(node.local_of(&canonical), Some(parent), "{case}");
            }
        }
        if survivors == Survivors::Apart && colocated {
            // `.git` has the merge as exported: both survivors' bookmarks.
            let refs = hive.repo(1).git(&["show-ref"]);
            for name in ["refs/heads/p", "refs/heads/q"] {
                assert!(refs.contains(name), "{case}: {refs}");
            }
        }
        if let Some(fetched) = fetched {
            // The merge's conflicted `main@origin` exported as every machine's: the side
            // gamma's `.git` has, where it keeps the operation, before any `jj` command here
            // imports it. For `Fetches`, in place of beta's own fetch, which is no side; for
            // `FetchedHere`, beta's fetch is one.
            assert_eq!(recorded_main_at_origin(&hive, 1), "conflict", "{case}");
            let side = git_main_at_origin(&hive, 1);
            assert_eq!(side, git_main_at_origin(&hive, 2), "{case}");
            if survivors == Survivors::Fetches {
                assert_ne!(side, fetched, "{case}");
            }
        }
        if several {
            // Again, with the op heads at or above all that survives: nothing to do.
            let now = hive.node(1).local_heads().unwrap();
            hive.hive.members[1].adapter.advance(&kept).unwrap();
            assert_eq!(hive.node(1).local_heads().unwrap(), now, "{case}");
        }

        // Then the policy publishes the drop, and the hive settles.
        let published = settle_participants(&mut hive, &participants, &kept);
        assert!(published, "{case}: beta never published the drop");
        assert_dropped_head_settled(&mut hive, &participants, &kept, &gone, survivors);
    }
}

/// Where what survives of a dropped head is several operations, and jj can't merge them with
/// this machine's own work, here a rebase of beta's that makes a loop with one of them, the
/// advance publishes nothing, and refuses as for any operation jj can't merge. It lists this
/// machine's operations the hive doesn't have, rather than searching for the one to revert:
/// that search goes by a single realization, and could name an operation that has nothing to
/// do with the loop.
#[test]
fn advancing_to_what_survives_refuses_what_jj_cannot_merge() {
    use musubi_core::node::LocalRepo as _;

    let (mut hive, kept, _, _) = dropped_head_held(four_machines(true), Survivors::Looping, true);
    // At the dropped head, having taken the hub's records, before the step that advances.
    hive.hive.fetch(1).unwrap();
    let member = &mut hive.hive.members[1];
    let step = member.core.step(&mut member.adapter).unwrap();
    assert!(matches!(step, musubi_core::node::Step::Adopted), "{step:?}");
    let before = hive.node(1).local_heads().unwrap();
    let err = hive.hive.members[1].adapter.advance(&kept).unwrap_err();
    let err = format!("{err:#}");
    assert!(err.contains("newest first: "), "{err}");
    assert!(err.contains(" (rebase "), "{err}");
    assert_eq!(hive.node(1).unmergeable_searches(), 0);
    assert_eq!(hive.node(1).local_heads().unwrap(), before);
}

/// The hub going back to an operation this machine dropped, whose history it lacks, makes the
/// core plan realizing that history, the dropped operations in it too: one of those, a merge
/// with two operations that survive below it, can come up once its parents are local, before
/// the rest of the plan has made the hub's head local. Realizing it writes nothing, and fails
/// not, though nothing names it alone: what this machine has in its place is local already.
#[test]
fn realizing_an_operation_this_machine_dropped_writes_nothing() {
    use musubi_core::node::LocalRepo as _;
    use musubi_jj::op_id::CanonicalOp;
    use musubi_jj::records::HubOp;

    let (mut hive, kept, _, _) = dropped_head_held(four_machines(true), Survivors::Apart, true);
    // At the dropped head, having taken the hub's records, before the step that advances.
    hive.hive.fetch(1).unwrap();
    let member = &mut hive.hive.members[1];
    let step = member.core.step(&mut member.adapter).unwrap();
    assert!(matches!(step, musubi_core::node::Step::Adopted), "{step:?}");
    let kept_hub = HubOp(CanonicalOp(kept.clone()));
    assert!(hive.node(1).is_dropped(&kept_hub));
    assert_eq!(hive.node(1).to_node(&kept_hub).unwrap().len(), 2);
    let member = &mut hive.hive.members[1];
    assert!(member.adapter.is_local(&kept).unwrap());
    let before = hive.node(1).local_heads().unwrap();
    let ops = history(hive.repo(1)).len();
    hive.hive.members[1].adapter.realize(&kept).unwrap();
    assert_eq!(hive.node(1).local_heads().unwrap(), before);
    assert_eq!(history(hive.repo(1)).len(), ops);
}

/// A machine that took another's record, but stopped before advancing past what it drops,
/// holds that drop pending again once the hub loses the record. Where the hub's head is then
/// the dropped operation itself, published again by a third machine that kept it, the
/// machine advances to what survives of it, merged with its own work in the one operation
/// jj would make of them all, and publishes the drop itself, rather than waiting for the
/// machine that abandoned it, which may have left the hive (it had, before the hub lost both)
/// and never comes back. Before, it waited: the hive never had its work or the drop again.
#[test]
fn a_dropped_head_published_again_is_dropped_by_who_took_it() {
    let cases = [
        (Survivors::One, true),
        (Survivors::One, false),
        (Survivors::Nested, true),
        (Survivors::Apart, true),
    ];
    for (survivors, leave) in cases {
        let (mut hive, kept, left, gone) = dropped_head_held(four_machines(true), survivors, leave);
        let participants: Vec<usize> = (0..hive.hive.members.len())
            .filter(|n| !left.contains(n))
            .collect();
        let published = settle_participants(&mut hive, &participants, &kept);
        // Beta publishes the drop itself unless alpha, still in the hive, did first.
        if leave {
            assert!(published, "{survivors:?}: beta never published the drop");
        }
        assert_dropped_head_settled(&mut hive, &participants, &kept, &gone, survivors);
    }
}

/// The original of `op`, in `node`'s store.
fn store_original(
    node: &musubi_jj::node::NodeRepo,
    op: &musubi_jj::op_id::CanonicalOp,
) -> jj_lib::op_store::OperationId {
    if op == node.canonical_store().root_operation_id() {
        op.0.clone()
    } else {
        node.canonical_store().original_id(op).unwrap()
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

/// The newest operation in `repo`'s op log that a workspace of `machine`'s made: that
/// machine's latest work, as `repo` has it.
fn newest_of(repo: &musubi_testutil::TestRepo, machine: &str) -> String {
    let template = "id ++ \" \" ++ workspace_name ++ \"\\n\"";
    repo.jj(&["op", "log", "--no-graph", "-T", template])
        .lines()
        .find_map(|line| {
            let (id, workspace) = line.split_once(' ')?;
            workspace.starts_with(machine).then(|| id.to_owned())
        })
        .unwrap()
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
    assert_eq!(hive.hive.hub.store().record_count(), 2);
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

/// A machine taking another's abandon, which drops its op head, realizes the hub's head and
/// advances to it, which renames its history as the records name it; then its sync stops
/// before the step after, as a crash or an error stops it. If the hub then loses the records,
/// as a power cut can make it, the machine still has the drop to publish, and publishes it
/// itself, without the machine that abandoned the operation syncing first. Taking the drop as
/// renamed but not as held, it pushed the renamed history with no drop, which the hub, without
/// the records, rejected at every step.
#[test]
fn a_sync_stopped_while_taking_an_abandon_the_hub_then_loses() {
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;
    use musubi_jj::op_id::CanonicalOp;
    use musubi_jj::records::HubOp;

    for (lose, crash) in [(false, true), (true, false), (true, true)] {
        let case = format!("lose {lose}, crash {crash}");
        let (mut hive, before, dropped_hub, _) = abandoned_at_beta(Abandoned::Head);

        // Beta prepares to take the record, which drops its op head, realizes what the hub
        // has after it, and advances, moving its op heads where the record names the history.
        hive.hive.fetch(1).unwrap();
        let member = &mut hive.hive.members[1];
        let mut advanced = false;
        for _ in 0..8 {
            match member.core.step(&mut member.adapter).unwrap() {
                Step::Realized(_) => {}
                Step::Advanced(_) => {
                    advanced = true;
                    break;
                }
                step => panic!("{case}: {step:?}"),
            }
        }
        assert!(advanced, "{case}");
        if crash {
            hive.reopen(1);
        }
        assert!(
            hive.node(1)
                .is_dropped(&HubOp(CanonicalOp(dropped_hub.clone()))),
            "{case}"
        );

        if lose {
            hive.hive.hub_goes_back(before).unwrap();
        }
        // Beta alone, for at most eight steps, so that a sync that gets nowhere stops.
        let mut pushes = vec![];
        let taken = hive
            .hive
            .sync_steps(1, 8, &mut |request, reply| {
                if let (
                    Request::Push {
                        expected, dropped, ..
                    },
                    Reply::Head { kind, seq, .. },
                ) = (request, &reply)
                {
                    pushes.push((
                        *kind,
                        expected.clone(),
                        dropped.contains(&dropped_hub),
                        *seq,
                    ));
                }
                reply
            })
            .unwrap();
        assert!(taken < 8, "{case}: {pushes:?}");
        if lose {
            // Its one push publishes the drop on the head the hub went back to.
            assert_eq!(
                pushes,
                [(HeadKind::Accepted, dropped_hub.clone(), true, before + 1)],
                "{case}"
            );
            assert!(hive.hive.hub.is_dropped(&dropped_hub, &[]).unwrap());
        } else {
            assert!(pushes.is_empty(), "{case}: {pushes:?}");
        }
        assert_eq!(
            hive.hive.members[1].adapter.records().unwrap(),
            hive.hive.hub.records(),
            "{case}"
        );
        assert!(hive.node(1).pending_drops().is_empty(), "{case}");

        hive.sync();
        hive.assert_converged();
        assert_eq!(hive.hive.hub.store().record_count(), 1, "{case}");
        for machine in 0..2 {
            assert!(
                !op_log(hive.repo(machine))
                    .iter()
                    .any(|(_, d)| d.starts_with("create bookmark dropped")),
                "{case}: {machine}"
            );
        }
    }
}

/// What of beta's alpha abandons.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Abandoned {
    /// The operation alpha made that is beta's op head.
    Head,
    /// The merge beta made of its own work and alpha's, its op head, with alpha's work.
    Merge,
    /// An operation below beta's op head, which alpha made.
    Below,
}

/// Alpha abandons an operation beta has, and publishes the abandon, which beta hasn't taken
/// yet. Returns the hive, the hub's sequence number with beta's op head as its head then,
/// the operation the test follows, of those alpha abandoned, and how it is described.
fn abandoned_at_beta(what: Abandoned) -> (Fixture, u64, musubi_sync::OpId, String) {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let (abandon, followed, described) = match what {
        Abandoned::Merge => {
            hive.commit(0, "a", "alpha's");
            let alphas = op_log(hive.repo(0))[0].1.clone();
            hive.commit(1, "b", "beta's");
            let betas = op_log(hive.repo(1))[0].1.clone();
            hive.hive.sync(0).unwrap();
            hive.hive.sync(1).unwrap();
            assert_eq!(op_log(hive.repo(1))[0].1, "reconcile divergent operations");
            hive.hive.sync(0).unwrap();
            let merge = op_described(hive.repo(0), "reconcile divergent operations");
            let below = op_described(hive.repo(0), &betas);
            hive.commit(0, "c", "on the merge");
            // The merge and alpha's work below it: jj abandons no merge alone.
            (format!("{below}..{merge}"), hive.hive.hub_head(), alphas)
        }
        Abandoned::Head => {
            hive.commit(0, "a", "first");
            hive.repo(0)
                .jj(&["bookmark", "create", "dropped", "-r", "@-"]);
            let dropped = op_log(hive.repo(0))[0].0.clone();
            hive.sync();
            // Beta's working copy records it.
            hive.repo(1).jj(&["status"]);
            hive.commit(0, "b", "second");
            (
                dropped,
                hive.hive.hub_head(),
                "create bookmark dropped".to_owned(),
            )
        }
        Abandoned::Below => {
            hive.commit(0, "a", "first");
            hive.repo(0).jj(&["bookmark", "create", "x", "-r", "@-"]);
            let x = op_log(hive.repo(0))[0].0.clone();
            hive.sync();
            let followed = hive.hive.hub_head();
            for name in ["y", "z"] {
                hive.repo(0).jj(&["bookmark", "create", name, "-r", "@-"]);
            }
            hive.sync();
            hive.repo(1).jj(&["status"]);
            (x, followed, "create bookmark x".to_owned())
        }
    };
    let before = hive.hive.hub.store().head().0;
    hive.repo(0).jj(&["op", "abandon", &abandon]);
    hive.hive.sync(0).unwrap();
    assert_eq!(hive.hive.hub.store().record_count(), 1);
    (hive, before, followed, described)
}

/// The operations in `repo`'s history, described, read without a snapshot, which would
/// change it.
fn history(repo: &musubi_testutil::TestRepo) -> Vec<(String, String)> {
    repo.jj(&[
        "--ignore-working-copy",
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

/// Taking that abandon stops partway, in an error that leaves the repository open, or a
/// crash, which may lose the translation cache too, or be followed by a `jj` command on the
/// op head, or a `jj op abandon` of another operation below it: the write that holds the
/// records fails, having written nothing; or it stops once that write is done, before the
/// op heads move where the records name the history, or once they have, before the
/// workspaces. Beta resumes where it stopped: it holds the records only if it wrote that it
/// does, its op heads and its working copy are on history that has none of what it dropped,
/// nothing abandoned comes back, its own work goes on, and it publishes what it dropped
/// itself if the hub then loses the records.
#[test]
fn taking_an_abandon_resumes_where_it_stopped() {
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;
    use musubi_jj::node::NodeOp;
    use musubi_jj::op_id::CanonicalOp;
    use musubi_jj::records::HubOp;

    #[derive(Debug)]
    enum Stop {
        Hold,
        Heads,
        /// Partway through moving the op heads, the new ones in and the old ones not out.
        Publishing,
        Workspaces,
    }
    #[derive(Debug, PartialEq)]
    enum Then {
        /// The repository stays open.
        Error,
        /// It is opened again.
        Crash,
        /// It is opened again, having lost the translation cache too.
        CrashLosingCache,
        /// `jj op abandon` drops another operation below beta's op head, then it is opened
        /// again.
        CrashThenAbandon,
        /// A `jj` command makes an operation on beta's op head, then it is opened again,
        /// having lost the translation cache, and again after canonicalizing that command,
        /// before reparenting it.
        CrashLosingCacheThenCommand,
        /// A `jj` command at an operation below beta's op head makes another beside it: at
        /// beta's own work, which the abandon keeps, or, losing the translation cache twice
        /// as above, at one the abandon drops.
        CrashThenCommandBeside,
        CrashThenCommandAtDropped,
    }
    use Abandoned::*;
    let cases = [
        (Stop::Hold, Head, Then::Error, true),
        (Stop::Heads, Head, Then::Crash, true),
        (Stop::Heads, Head, Then::CrashLosingCache, false),
        (Stop::Heads, Merge, Then::Error, true),
        (Stop::Workspaces, Head, Then::CrashLosingCache, false),
        (Stop::Heads, Below, Then::CrashLosingCache, false),
        (Stop::Heads, Below, Then::CrashThenAbandon, false),
        (Stop::Heads, Head, Then::CrashLosingCacheThenCommand, false),
        (Stop::Publishing, Merge, Then::Crash, false),
        (Stop::Heads, Merge, Then::CrashThenCommandBeside, false),
        (Stop::Heads, Below, Then::CrashThenCommandAtDropped, false),
    ];
    for (stop, what, then, lose) in cases {
        let case = format!("{stop:?}, {what:?}, {then:?}, lose {lose}");
        let (mut hive, before, followed, abandoned) = abandoned_at_beta(what);
        let followed_hub = HubOp(CanonicalOp(followed.clone()));
        match stop {
            Stop::Hold => hive.node(1).fail_holding_records(),
            Stop::Heads => hive.node(1).crash_taking_records(false),
            Stop::Publishing => hive.node(1).crash_publishing_taken_heads(),
            Stop::Workspaces => hive.node(1).crash_taking_records(true),
        }
        // Beta takes the records, first realizing the hub's head and advancing to it where
        // they drop its op head, and stops.
        hive.hive.fetch(1).unwrap();
        let member = &mut hive.hive.members[1];
        let mut stopped = false;
        for _ in 0..8 {
            match member.core.step(&mut member.adapter) {
                Ok(Step::Realized(_)) => {}
                Err(_) => {
                    stopped = true;
                    break;
                }
                Ok(step) => panic!("{case}: {step:?}"),
            }
        }
        assert!(stopped, "{case}");
        let mut gone = vec![abandoned.clone()];
        let beside = matches!(
            then,
            Then::CrashThenCommandBeside | Then::CrashThenCommandAtDropped
        );
        let lose_twice = matches!(
            then,
            Then::CrashLosingCacheThenCommand | Then::CrashThenCommandAtDropped
        );
        let command = beside || then == Then::CrashLosingCacheThenCommand;
        if then == Then::CrashThenCommandAtDropped {
            let (at, _) = history(hive.repo(1))
                .into_iter()
                .find(|(_, d)| d.starts_with(&format!("{abandoned} ")))
                .unwrap();
            hive.repo(1)
                .jj(&["--at-op", &at, "bookmark", "create", "late", "-r", "@-"]);
            assert_eq!(hive.node(1).local_heads().unwrap().len(), 2, "{case}");
        } else if then == Then::CrashThenCommandBeside {
            // At beta's own work below its op head, which the abandon keeps.
            let template = r#"id ++ " " ++ workspace_name ++ " " ++ description ++ "\n""#;
            let ops = hive.repo(1).jj(&[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-T",
                template,
            ]);
            let at = ops
                .lines()
                .find(|line| line.split(' ').nth(1) == Some("beta@") && line.contains(" commit "))
                .and_then(|line| line.split(' ').next())
                .unwrap()
                .to_owned();
            hive.repo(1)
                .jj(&["--at-op", &at, "bookmark", "create", "late", "-r", "@-"]);
            assert_eq!(hive.node(1).local_heads().unwrap().len(), 2, "{case}");
        } else if command {
            hive.repo(1).jj(&["bookmark", "create", "late", "-r", "@-"]);
        }
        if then == Then::CrashLosingCache || lose_twice {
            std::fs::remove_file(hive.repo(1).repo_path().join("musubi/translation")).unwrap();
        }
        if then == Then::CrashThenAbandon {
            let (q, described) = history(hive.repo(1))
                .into_iter()
                .find(|(_, d)| d.starts_with("create bookmark y "))
                .unwrap();
            hive.repo(1).jj(&["op", "abandon", &q]);
            gone.push(described);
        }
        if then != Then::Error {
            hive.reopen(1);
        }
        if lose_twice {
            // Recovery runs, and the op heads are canonicalized, but not yet moved where
            // their canonical forms are, before the cache is lost again.
            hive.node(1).check_abandon().unwrap();
            for head in hive.node(1).local_heads().unwrap() {
                hive.node(1).canonicalize(&head).unwrap();
            }
            hive.node(1).check_abandon().unwrap();
            std::fs::remove_file(hive.repo(1).repo_path().join("musubi/translation")).unwrap();
            hive.reopen(1);
        }
        // What a sync reads first, which resumes the move.
        let heads = hive.node(1).canonical_heads().unwrap();
        let held = !matches!(stop, Stop::Hold);
        assert_eq!(
            hive.hive.members[1].adapter.records().unwrap().count,
            u64::from(held),
            "{case}"
        );
        assert_eq!(hive.node(1).is_dropped(&followed_hub), held, "{case}");
        for head in heads {
            assert_eq!(
                hive.node(1).current(&head).unwrap(),
                [NodeOp(head)],
                "{case}"
            );
        }
        let beta = history(hive.repo(1));
        if held {
            for described in &gone {
                assert!(
                    !beta.iter().any(|(_, d)| d.starts_with(described.as_str())),
                    "{case}: {described} is still in beta's history"
                );
            }
        }
        // A working copy at the merge isn't moved, even where taking the records doesn't
        // stop, as no one operation stands for it now.
        if what != Merge {
            let repo = hive.repo(1);
            let recorded = recorded_op(repo, repo.path());
            assert!(
                beta.iter().any(|(id, _)| *id == recorded),
                "{case}: the working copy records {recorded}, not in its history"
            );
        }

        if lose {
            hive.hive.hub_goes_back(before).unwrap();
        }
        // Beta alone, for at most eight steps, so that a sync that gets nowhere stops.
        let mut pushes = vec![];
        let taken = hive
            .hive
            .sync_steps(1, 8, &mut |request, reply| {
                if let (
                    Request::Push {
                        expected, dropped, ..
                    },
                    Reply::Head { kind, seq, .. },
                ) = (request, &reply)
                {
                    pushes.push((*kind, expected.clone(), dropped.contains(&followed), *seq));
                }
                reply
            })
            .unwrap();
        assert!(taken < 8, "{case}: {pushes:?}");
        if lose {
            // It republishes a taken record, or one retained in custody before the failed
            // hold, on the head the hub went back to.
            assert_eq!(
                pushes,
                [(HeadKind::Accepted, followed.clone(), true, before + 1)],
                "{case}"
            );
        } else if then == Then::CrashThenAbandon || command {
            // It publishes its own abandon, or its own work.
            assert!(
                matches!(pushes.as_slice(), [(HeadKind::Accepted, _, false, _)]),
                "{case}: {pushes:?}"
            );
        } else {
            assert!(pushes.is_empty(), "{case}: {pushes:?}");
        }

        hive.sync();
        hive.assert_converged();
        assert_eq!(
            hive.hive.hub.store().record_count(),
            if then == Then::CrashThenAbandon { 2 } else { 1 },
            "{case}"
        );
        if command {
            assert!(hive.bookmarks(0).contains_key("late@"), "{case}");
        }
        for machine in 0..2 {
            for described in &gone {
                assert!(
                    !op_log(hive.repo(machine))
                        .iter()
                        .any(|(_, d)| d.starts_with(described.as_str())),
                    "{case}: {machine}: {described}"
                );
            }
        }
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
        assert_eq!(hive.hive.hub.store().record_count(), 1, "after: {after}");
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
        // Its records not pruned, as they would be once both machines took them: here the
        // hub loses them.
        hive.hive.pruning = false;
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
        assert_eq!(hive.hive.hub.store().record_count(), 1, "remade: {remade}");
        for machine in 0..2 {
            assert!(
                !has_operation(hive.repo(machine), &abandoned.1),
                "{machine}"
            );
        }
        assert!(hive.visible(0).iter().any(|c| c.ends_with("after")));
    }
}

/// A machine that hasn't heard that the hive was made again, as when the reply to its poll is
/// lost, pushes what it would have pushed before: its first view as a delta against its
/// parent's, which the new store lacks. The hub stores none of it, and rejects the push with
/// its head, which tells the machine where the hub is, rather than failing the request.
#[test]
fn a_push_to_a_hive_made_again_is_rejected() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.sync();
    hive.commit(0, "b", "second");
    let mut pushes = vec![];
    hive.hive
        .sync_through(0, &mut |request, reply| {
            if matches!(request, Request::Push { .. }) {
                pushes.push(request.clone());
            }
            reply
        })
        .unwrap();
    let push = pushes.pop().expect("alpha pushed");
    assert!(
        matches!(&push, Request::Push { ops, .. } if !ops.is_empty()),
        "{push:?}"
    );
    hive.hive.remake_hub().unwrap();
    let root = hive.hive.hub_head();
    let handled = musubi_core::hub::handle(&mut hive.hive.hub, push).unwrap();
    assert!(
        matches!(
            &handled.reply,
            Reply::Head { kind: HeadKind::Rejected, seq: 0, head, .. } if *head == root
        ),
        "{:?}",
        handled.reply
    );
    assert_eq!(hive.hive.hub_head(), root);
}

/// A sync stops just after the hub accepts a machine's push, before the machine moves its
/// base to it, as one cut short does; then `jj op abandon` drops what it pushed. The machine
/// notices the abandon and publishes it: it watches its push, once it learns that the hub took
/// it, as it watches its base. Watching only its base, which it still reached, it took the
/// hub's head for one it didn't have yet, and took back what it abandoned.
#[test]
fn abandoning_a_push_the_hub_just_accepted_drops_it() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "a", "first");
    hive.sync();
    hive.commit(1, "b", "pushed");
    let pushed = op_log(hive.repo(1)).swap_remove(0);
    assert!(pushed.1.starts_with("commit "), "{pushed:?}");
    let before = hive.hive.hub_head();
    hive.hive.sync_steps(1, 1, &mut |_, reply| reply).unwrap();
    assert_ne!(hive.hive.hub_head(), before, "the hub took the push");
    hive.repo(1)
        .jj(&["bookmark", "create", "after", "-r", "@-"]);
    hive.repo(1).jj(&["op", "abandon", &pushed.0]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(!has_operation(hive.repo(machine), &pushed.1), "{machine}");
    }
}

/// The hub takes a machine's push, another machine takes it too, and the hub goes back and loses
/// it; then the first machine abandons the push, and syncs first. It publishes the drop all the
/// same, so the other machine drops the push rather than push it again.
#[test]
fn abandoning_a_push_the_hub_lost_drops_it_everywhere() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "a", "first");
    hive.sync();
    let seq = hive.hive.hub.store().head().0;
    hive.commit(1, "b", "pushed");
    let pushed = op_log(hive.repo(1)).swap_remove(0);
    hive.hive.sync(1).unwrap();
    hive.hive.sync(0).unwrap();
    assert!(has_operation(hive.repo(0), &pushed.1));
    hive.hive.hub_goes_back(seq).unwrap();
    // So that the push isn't the op head, which jj won't abandon.
    hive.repo(1)
        .jj(&["bookmark", "create", "after", "-r", "@-"]);
    hive.repo(1).jj(&["op", "abandon", &pushed.0]);
    hive.hive.sync(1).unwrap();
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(!has_operation(hive.repo(machine), &pushed.1), "{machine}");
    }
}

/// As above, where the machine never hears that the hub took its push, as when it crashes
/// before the reply: it learns it from its next poll, which comes before it reads its op heads,
/// and notices the abandon then. So too where another machine has pushed on top meanwhile, and
/// the push comes back among what it fetches.
#[test]
fn abandoning_a_push_whose_acceptance_was_lost_drops_it() {
    for others_on_top in [false, true] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        hive.commit(1, "a", "first");
        hive.sync();
        hive.commit(1, "b", "pushed");
        let pushed = op_log(hive.repo(1)).swap_remove(0);
        assert!(pushed.1.starts_with("commit "), "{pushed:?}");
        let before = hive.hive.hub_head();
        hive.hive.sync_steps(1, 1, &mut |_, reply| reply).unwrap();
        assert_ne!(hive.hive.hub_head(), before, "the hub took the push");
        // Lost: the machine restarts knowing only that it pushed.
        std::fs::remove_file(
            hive.repo(1)
                .repo_path()
                .join("musubi")
                .join(musubi_jj::node::ACCEPTED_PUSH),
        )
        .unwrap();
        hive.reopen(1);
        if others_on_top {
            hive.hive.sync(0).unwrap();
            hive.commit(0, "c", "alpha's, on the push");
            hive.hive.sync(0).unwrap();
        }
        hive.repo(1)
            .jj(&["bookmark", "create", "after", "-r", "@-"]);
        hive.repo(1).jj(&["op", "abandon", &pushed.0]);
        hive.sync();
        hive.assert_converged();
        for machine in 0..2 {
            assert!(
                !has_operation(hive.repo(machine), &pushed.1),
                "{others_on_top}: {machine}"
            );
        }
    }
}

/// As above, where what is abandoned is below the last push, which it carried with it: only
/// that goes, and what jj rewrote above it stays, once, on every machine.
#[test]
fn abandoning_below_a_push_whose_acceptance_was_lost_drops_only_that() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "a", "first");
    hive.sync();
    hive.commit(1, "y", "abandoned");
    let abandoned = op_log(hive.repo(1)).swap_remove(0);
    hive.commit(1, "m", "kept");
    hive.commit(1, "p", "pushed last");
    hive.hive.sync_steps(1, 1, &mut |_, reply| reply).unwrap();
    std::fs::remove_file(
        hive.repo(1)
            .repo_path()
            .join("musubi")
            .join(musubi_jj::node::ACCEPTED_PUSH),
    )
    .unwrap();
    hive.reopen(1);
    hive.repo(1)
        .jj(&["bookmark", "create", "after", "-r", "@-"]);
    hive.repo(1).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
        let visible = hive.visible(machine);
        for work in [" kept", " pushed last"] {
            let count = visible.iter().filter(|c| c.ends_with(work)).count();
            assert_eq!(count, 1, "{machine}: {work}: {visible:?}");
        }
    }
}

/// As above, where what the hub accepted publishes an abandon: its head is the fix-up, on
/// history the record the reply names renames. A `jj op abandon` of the fix-up before the
/// machine takes that in is noticed and published, and the fix-up stays dropped.
#[test]
fn abandoning_a_fix_up_the_hub_just_accepted_drops_it() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    let first = op_described(hive.repo(0), &commit_op(hive.repo(0)).1);
    hive.repo(0).jj(&["op", "abandon", &first]);
    // One step at a time, stopping as soon as the hub has taken the abandon.
    let records = hive.hive.hub.store().record_count();
    while hive.hive.hub.store().record_count() == records {
        assert_eq!(
            hive.hive.sync_steps(0, 1, &mut |_, reply| reply).unwrap(),
            1,
            "the abandon was published"
        );
    }
    let timed = |hive: &Fixture, index: usize| -> Vec<String> {
        hive.repo(index)
            .jj(&[
                "op",
                "log",
                "--no-graph",
                "-T",
                r#"self.time().start() ++ " " ++ description.first_line() ++ "\n""#,
            ])
            .lines()
            .map(str::to_owned)
            .collect()
    };
    let fixup = timed(&hive, 0).swap_remove(0);
    assert!(fixup.ends_with("musubi: pass on jj op abandon"), "{fixup}");
    hive.repo(0)
        .jj(&["bookmark", "create", "after", "-r", "@-"]);
    let head = op_log(hive.repo(0)).swap_remove(0).0;
    let fixup_id = op_log(hive.repo(0))[1].0.clone();
    assert_ne!(head, fixup_id);
    hive.repo(0).jj(&["op", "abandon", &fixup_id]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(
            !timed(&hive, machine).contains(&fixup),
            "{machine}: {fixup}"
        );
    }
}

/// `jj op abandon` rewrites an operation a working copy records, but doesn't move the working
/// copy where another operation came after it, as one musubi writes can. musubi moves it to
/// the rewrite, as it moves every working copy an abandon leaves behind, even where the
/// operation isn't published yet, so that no record of the hive's renames it. Left where it
/// was, the next command there, with `snapshot.auto-update-stale`, merged what the abandon
/// dropped back in, and the hub refused every push of it: the sync never settled.
#[test]
fn a_working_copy_at_an_unpublished_operation_follows_an_abandon() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    let abandoned = op_log(hive.repo(0))
        .into_iter()
        .find(|(_, description)| description.starts_with("commit "))
        .unwrap();
    hive.commit(0, "b", "second");
    hive.sync();
    // The working copy records this operation, which isn't published.
    hive.repo(0)
        .jj(&["describe", "@-", "-m", "second, described"]);
    // musubi writes above it: any operation of musubi's will do, and a forget writes one.
    let beta = hive.machine_key(1);
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.hive.sync(0).unwrap();
    hive.commit(0, "c", "third");
    assert!(
        !has_operation(hive.repo(0), &abandoned.1),
        "jj brought it back"
    );
    hive.hive.sync(0).unwrap();
    let descriptions = hive.visible(0);
    for work in ["second, described", "third"] {
        assert!(descriptions.iter().any(|c| c.ends_with(work)), "{work}");
    }
}

/// `jj op abandon` of a forget keeps every view above it, and so the views that leave the
/// forgotten copy out, but drops the forget from the history presence is worked out from. Work
/// another machine did on one of those views before the abandon reached it is realized, after,
/// as presence at the view has it: were that worked out from the history left, the forgotten
/// copy would be present there, and realizing it on that copy would drop the copy's own
/// workspace from its view, which the view lacks, as though it were present. The contraction
/// keeps presence there as it was, so the copy stays forgotten and keeps its workspace.
#[test]
fn abandoning_a_forget_under_other_work_keeps_the_copy_forgotten() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(0, "a", "from alpha");
    hive.sync();
    let alpha = hive.machine_key(0);
    assert!(hive.node(2).forget_copy(&alpha, "alpha").unwrap());
    let forget = op_log(hive.repo(2))
        .into_iter()
        .find(|(_, description)| description == "musubi: forget alpha")
        .unwrap();
    for machine in [2, 1, 0] {
        hive.hive.sync(machine).unwrap();
    }
    hive.commit(2, "g", "gamma after the forget");
    hive.hive.sync(2).unwrap();
    hive.hive.sync(1).unwrap();
    // Beta works on gamma's work, before it hears of the abandon.
    hive.commit(1, "b", "beta before the abandon");
    hive.repo(2).jj(&["op", "abandon", &forget.0]);
    hive.sync();
    hive.assert_converged();
    assert!(!hive.shown_machines().contains(&alpha));
    assert!(
        hive.workspace_names(0).contains("alpha"),
        "{:?}",
        hive.workspace_names(0)
    );
    for machine in 0..3 {
        assert!(!has_operation(hive.repo(machine), "musubi: forget alpha"));
    }
}

/// `jj op abandon` of a copy's latest work, on a machine that has forgotten the copy: the
/// fix-up does that work again, then forgets the copy again, so the copy is present at the
/// work, whose view, written where the copy was forgotten, has none of its workspaces. The copy
/// keeps its workspaces there, and so at the forget after it, whose realization takes them from
/// the work's, rather than losing them at both.
#[test]
fn abandoning_the_latest_work_of_a_forgotten_copy_keeps_its_workspaces() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(1, "b", "from beta");
    hive.sync();
    let work = newest_of(hive.repo(0), "beta");
    let beta = hive.machine_key(1);
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.hive.sync(0).unwrap();
    hive.repo(0).jj(&["op", "abandon", &work]);
    hive.sync();
    let fixup: Vec<(String, String)> = op_log(hive.repo(1))
        .into_iter()
        .filter(|(_, d)| d.starts_with("musubi: keep ") || d == "musubi: pass on jj op abandon")
        .collect();
    assert_eq!(fixup.len(), 2, "{fixup:?}");
    for (id, description) in fixup {
        let names = hive.repo(1).jj(&[
            "--at-op",
            &id,
            "--ignore-working-copy",
            "workspace",
            "list",
            "-T",
            "name ++ \"\\n\"",
        ]);
        assert!(
            names.lines().any(|name| name == "beta"),
            "{description}: {names}"
        );
    }
    assert!(!hive.shown_machines().contains(&beta));
    hive.assert_converged();
}

/// …where the machine forgot the copy before the abandon, and hasn't published the forget: the
/// fix-up, written above the forget, does the copy's work again and then forgets it again, as
/// it is forgotten there. Below the forget, where the abandon's rewrite leaves the hive's head,
/// the copy is present: going by that, the fix-up would leave it present, with none of its
/// workspaces in the hive's view, and the copy would lose its own.
#[test]
fn abandoning_the_latest_work_of_a_copy_just_forgotten_keeps_it_forgotten() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = forget_then_abandon_latest_work(&mut hive);
    hive.sync();
    assert_stays_forgotten(&mut hive, &beta);
}

/// …and the machine crashes after writing the fix-up's work, before its forget: written again,
/// the fix-up forgets the copy all the same. Deciding afresh, it would find its own work at the
/// op head, and the copy present.
#[test]
fn a_fix_up_written_again_after_a_crash_keeps_the_copy_forgotten() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = forget_then_abandon_latest_work(&mut hive);
    crash_after_the_fixups_work(&mut hive);
    hive.sync();
    assert_stays_forgotten(&mut hive, &beta);
}

/// …and, after the crash, the machine abandons its own commit too, so that a fix-up replaces
/// the one it was writing: that one forgets the copy too.
#[test]
fn a_fix_up_replaced_after_a_crash_keeps_the_copy_forgotten() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let beta = forget_then_abandon_latest_work(&mut hive);
    crash_after_the_fixups_work(&mut hive);
    // Alpha's commit, published, which the first abandon rewrote.
    let alpha = newest_of(hive.repo(0), "alpha");
    hive.repo(0).jj(&["op", "abandon", &alpha]);
    hive.sync();
    assert_stays_forgotten(&mut hive, &beta);
}

/// Alpha publishes a commit above beta's latest work, then forgets beta and, before it syncs,
/// abandons beta's work. The abandon keeps alpha's commit, with presence as it was, which names
/// beta's work, now dropped, so the fix-up does that work again. The forget is then alpha's
/// only operation the hub lacks. Returns beta's machine key.
fn forget_then_abandon_latest_work(hive: &mut Fixture) -> String {
    hive.commit(1, "b", "from beta");
    hive.sync();
    let work = newest_of(hive.repo(0), "beta");
    hive.commit(0, "a", "from alpha");
    hive.hive.sync(0).unwrap();
    let beta = hive.machine_key(1);
    assert!(hive.node(0).forget_copy(&beta, "beta").unwrap());
    hive.repo(0).jj(&["op", "abandon", &work]);
    beta
}

/// Alpha writes the fix-up's work for beta and crashes before the forget after it, then
/// restarts.
fn crash_after_the_fixups_work(hive: &mut Fixture) {
    hive.node(0).crash_writing_fixup(1).unwrap();
    let log = op_log(hive.repo(0));
    assert!(log.iter().any(|(_, d)| d.starts_with("musubi: keep ")));
    assert!(!has_operation(
        hive.repo(0),
        "musubi: pass on jj op abandon"
    ));
    hive.reopen(0);
}

/// After [`forget_then_abandon_latest_work`] and a sync: the fix-up's one last operation forgets
/// beta, which keeps its own workspace, and the hive has converged.
fn assert_stays_forgotten(hive: &mut Fixture, beta: &str) {
    let pass_on: Vec<String> = op_log(hive.repo(0))
        .into_iter()
        .filter(|(_, d)| d == "musubi: pass on jj op abandon")
        .map(|(id, _)| id)
        .collect();
    assert_eq!(pass_on.len(), 1, "{pass_on:?}");
    let attributes = hive.repo(0).jj(&[
        "--at-op",
        &pass_on[0],
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n",
        "1",
        "-T",
        "attributes",
    ]);
    assert!(
        attributes.contains(&format!("musubi.forget: {beta}")),
        "{attributes}"
    );
    assert!(
        hive.workspace_names(1).contains("beta"),
        "{:?}",
        hive.workspace_names(1)
    );
    hive.assert_converged();
}

/// `jj op abandon` again before the machine publishes the first, of an operation the first
/// rewrote, as one it kept above what it dropped: the hub names that operation as it was. The
/// machine publishes the drop so, rather than offer the hub one it can't place, again and again.
#[test]
fn abandoning_what_an_unpublished_abandon_rewrote_publishes_both() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    // So that what becomes of `second` isn't the op head, which jj doesn't abandon.
    hive.commit(0, "c", "third");
    hive.sync();
    let commits: Vec<(String, String)> = op_log(hive.repo(0))
        .into_iter()
        .filter(|(_, d)| d.starts_with("commit "))
        .collect();
    let [second, first] = [&commits[1], &commits[2]];
    hive.repo(0).jj(&["op", "abandon", &first.0]);
    assert!(hive.node(0).check_abandon().unwrap());
    let rewritten = op_log(hive.repo(0))
        .into_iter()
        .find(|(_, d)| *d == second.1)
        .unwrap();
    assert_ne!(rewritten.0, second.0);
    hive.repo(0).jj(&["op", "abandon", &rewritten.0]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(!has_operation(hive.repo(machine), &first.1), "{machine}");
        assert!(!has_operation(hive.repo(machine), &second.1), "{machine}");
    }
}

/// …three times, each of what the last rewrote, before the machine publishes any: renamed
/// twice here, an operation is still named as the hub has it.
#[test]
fn abandoning_three_times_before_publishing_publishes_all() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for (file, message) in [
        ("a", "first"),
        ("b", "second"),
        ("c", "third"),
        ("d", "fourth"),
    ] {
        hive.commit(0, file, message);
    }
    hive.sync();
    let commits: Vec<String> = op_log(hive.repo(0))
        .into_iter()
        .filter(|(_, d)| d.starts_with("commit "))
        .map(|(_, d)| d)
        .collect();
    // The three below the newest, oldest first: what becomes of each isn't the op head.
    let abandoned: Vec<String> = commits[1..4].iter().rev().cloned().collect();
    for description in &abandoned {
        let (op, _) = op_log(hive.repo(0))
            .into_iter()
            .find(|(_, d)| d == description)
            .unwrap();
        hive.repo(0).jj(&["op", "abandon", &op]);
        assert!(hive.node(0).check_abandon().unwrap());
    }
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        for description in &abandoned {
            assert!(!has_operation(hive.repo(machine), description), "{machine}");
        }
    }
}

/// …and between the two, another machine publishes an abandon of its own, below both, so that
/// the hub's record renames what the machine abandons next; whether the machine takes that
/// record before its second abandon or after. It names both drops as the hub does.
#[test]
fn abandoning_twice_around_another_machines_record_publishes_all() {
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_jj::canonical::Contraction;
    use musubi_jj::op_id::CanonicalOp;

    for take_between in [false, true] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        hive.commit(1, "z", "beta's");
        hive.sync();
        let (_, theirs) = op_log(hive.repo(1))
            .into_iter()
            .find(|(_, d)| d.starts_with("commit "))
            .unwrap();
        for (file, message) in [("a", "first"), ("b", "second"), ("c", "third")] {
            hive.commit(0, file, message);
        }
        hive.sync();
        let commits: Vec<String> = op_log(hive.repo(0))
            .into_iter()
            .filter(|(_, d)| d.starts_with("commit "))
            .map(|(_, d)| d)
            .collect();
        let (third, second, first) = (&commits[0], &commits[1], &commits[2]);
        hive.repo(0)
            .jj(&["op", "abandon", &op_described(hive.repo(0), first)]);
        assert!(hive.node(0).check_abandon().unwrap());
        hive.repo(1)
            .jj(&["op", "abandon", &op_described(hive.repo(1), &theirs)]);
        hive.hive.sync(1).unwrap();
        assert_eq!(hive.hive.hub.store().record_count(), 1);
        if take_between {
            // One step takes the hub's record, before alpha publishes its own.
            hive.hive.sync_steps(0, 1, &mut |_, reply| reply).unwrap();
            assert_eq!(hive.node(0).record_state().0, 1);
            assert!(!hive.node(0).pending_drops().ops().is_empty());
            assert_eq!(hive.hive.hub.store().record_count(), 1);
            // Equal applied records do not make the normalizers equal: alpha also drops
            // its own unpublished original. Its complete head closure is already written
            // without either original, so contracting just the hub's drops keeps its id.
            let member = &mut hive.hive.members[0];
            let heads = member.adapter.heads_for(&member.core.known().1).unwrap();
            assert!(!heads.is_empty());
            assert_eq!(member.adapter.records().unwrap(), hive.hive.hub.records());
            let applied = member.adapter.applied_records().unwrap();
            let pending = member.adapter.pending().unwrap();
            assert!(!applied.records.is_empty() && !pending.is_empty());
            let store = member.adapter.repo().canonical_store();
            let hub_drops: Vec<_> = applied
                .records
                .iter()
                .flatten()
                .cloned()
                .map(CanonicalOp)
                .collect();
            let hub_originals: BTreeSet<_> = hub_drops
                .iter()
                .map(|op| store.original_id(op).unwrap())
                .collect();
            let mut node_originals = hub_originals.clone();
            node_originals.extend(
                pending
                    .into_iter()
                    .map(|op| store.original_id(&CanonicalOp(op)).unwrap()),
            );
            assert!(hub_originals.len() < node_originals.len());
            let mut hub_contraction = Contraction::new(store, hub_drops).unwrap();
            assert!(!hub_contraction.is_empty());
            for head in heads.into_iter().map(CanonicalOp) {
                // ancestors_until skips missing bodies; this strict traversal first reads
                // every body and view, including parents absent from that tolerant walk.
                store
                    .record_operations(std::slice::from_ref(&head))
                    .unwrap();
                let closure = store
                    .ancestors_until(std::slice::from_ref(&head), |_| false)
                    .unwrap();
                assert!(closure.contains(&head));
                for op in closure {
                    // Reading the full body excludes an incomplete metadata lookup's
                    // fallback to its input as an explanation for identity.
                    store.read_operation(&op).unwrap();
                    assert!(!node_originals.contains(&store.original_id(&op).unwrap()));
                }
                assert_eq!(
                    hub_contraction.images(store, &head).unwrap(),
                    vec![head.clone()]
                );
                assert_eq!(hive.hive.hub.store().current(&head.0), vec![head.0.clone()]);
                assert!(!hive.hive.hub.store().is_superseded(&head.0));
            }
            // Every actual remembered name or cached key has a dropped original in its
            // immutable raw closure. Include a non-named key, so the cache case is exercised.
            let hub = hive.hive.hub.store();
            let named: BTreeSet<_> = hub
                .records()
                .iter()
                .flat_map(|record| record.ops().iter().map(|op| op.0.0.clone()))
                .collect();
            assert!(!named.is_empty());
            let canonical = hub.canonical();
            let mut cached_keys = 0;
            for key in canonical.operation_ids().unwrap() {
                if !hub.is_superseded(&key.0) {
                    continue;
                }
                let closure = canonical
                    .record_operations(std::slice::from_ref(&key))
                    .unwrap();
                assert!(closure.contains(&key));
                assert!(
                    closure
                        .iter()
                        .any(|op| { hub_originals.contains(&canonical.original_id(op).unwrap()) })
                );
                if !named.contains(&key.0) {
                    cached_keys += 1;
                }
            }
            assert!(cached_keys > 0);
        }
        hive.repo(0)
            .jj(&["op", "abandon", &op_described(hive.repo(0), second)]);
        hive.sync();
        hive.assert_converged();
        let case = format!("take between: {take_between}");
        for machine in 0..2 {
            for abandoned in [first, second, &theirs] {
                assert!(
                    !has_operation(hive.repo(machine), abandoned),
                    "{machine}, {case}"
                );
            }
            assert!(
                has_operation(hive.repo(machine), third),
                "{machine}, {case}"
            );
        }
    }
}

/// With `snapshot.auto-update-stale`, a command in a workspace whose working copy recorded an
/// operation `jj op abandon` rewrote brings back what jj abandoned, as on one machine
/// (races.md, "Known jj limitations"). A later `jj op abandon` below that then moves what came
/// back onto other parents, so that two of the machine's operations stand for each of the
/// hive's, neither where the hive has it, and nothing is dropped: musubi puts its history back
/// as the hive has it, rather than stopping as if the history the hub accepted were gone, and
/// the operation jj brought back stays everywhere.
#[test]
fn an_abandon_a_stale_workspace_brought_back_stays() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    let second = hive.repo(0).path().with_file_name("alpha-second");
    let second = second.to_str().unwrap();
    hive.repo(0).jj(&["workspace", "add", second]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    // The second working copy records an operation above the one alpha abandons.
    hive.repo(0).jj(&["-R", second, "status"]);
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.commit(0, "z", "z");
    let below = op_log(hive.repo(0))[0].clone();
    assert!(below.1.starts_with("commit "), "{below:?}");
    hive.commit(0, "w", "w");
    std::fs::write(Path::new(second).join("s"), "edit").unwrap();
    hive.repo(0).jj(&["-R", second, "status"]);
    assert!(has_operation(hive.repo(0), &abandoned.1));
    hive.repo(0).jj(&["op", "abandon", &below.0]);
    hive.sync();
    hive.assert_converged();
    // Settled: a `jj` command everywhere and another sync change nothing.
    hive.assert_converged();
    for machine in 0..2 {
        assert!(has_operation(hive.repo(machine), &abandoned.1), "{machine}");
        assert!(!has_operation(hive.repo(machine), &below.1), "{machine}");
        let visible = hive.visible(machine);
        for work in [" first", " second", " z", " w"] {
            assert!(
                visible.iter().any(|c| c.ends_with(work)),
                "{machine}: {work}"
            );
        }
    }
    assert_eq!(
        std::fs::read_to_string(Path::new(second).join("s")).unwrap(),
        "edit"
    );
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
/// still reaches the other machine, and drops nothing more. jj's rewrites of the operations
/// above it, an undo among them, whose description names an operation by its local id, are
/// matched to theirs by the fingerprints the machine kept for them.
#[test]
fn op_abandon_then_gc() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.repo(0).jj(&["undo"]);
    hive.commit(0, "c", "third");
    hive.sync();
    let descriptions = |hive: &Fixture| {
        let mut counts: BTreeMap<String, usize> = BTreeMap::new();
        for (_, op) in op_log(hive.repo(0)) {
            *counts.entry(op).or_default() += 1;
        }
        counts
    };
    // The commit the undo undid.
    let ops = op_log(hive.repo(0));
    let undo = ops
        .iter()
        .position(|(_, op)| op.starts_with("undo: "))
        .unwrap();
    let abandoned = ops[undo + 1].clone();
    assert!(abandoned.1.starts_with("commit "));
    let mut kept = descriptions(&hive);
    kept.remove(&abandoned.1);
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.repo(0).jj(&["util", "gc", "--expire=now"]);
    hive.sync();
    hive.assert_converged();
    let now = descriptions(&hive);
    for (op, count) in &kept {
        assert!(now.get(op).is_some_and(|now| now >= count), "{op} is gone");
    }
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
        assert!(
            op_log(hive.repo(machine))
                .iter()
                .any(|(_, op)| op.starts_with("undo: ")),
            "{machine}: the undo is gone"
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
    assert_eq!(hive.hive.hub.store().record_count(), 0);
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
    assert_eq!(hive.hive.hub.store().record_count(), 2);
    // The hub loses both; gamma, which saw neither, abandons another and publishes first.
    hive.hive.hub_goes_back(seq).unwrap();
    let op = op_described(hive.repo(2), theirs);
    hive.repo(2).jj(&["op", "abandon", &op]);
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub.store().record_count(), 1);
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
fn recorded_op(repo: &musubi_testutil::TestRepo, path: &Path) -> String {
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

/// A node that restarts loses its protocol state and its translation cache. It recovers both,
/// and converges without duplicating or dropping anything. With the cache lost, nothing maps
/// its own operations above its join, so it looks for a `jj op abandon` there, matching each
/// of them to an operation the hive has by its fingerprint. An operation and jj's rewrite of
/// it, both in the history once a command run at an operation from before the abandon writes
/// on the operation, have the same fingerprint: which survived is ambiguous, and the node
/// stopped for good. It must find, as canonicalizing would, that each stands for an
/// operation the hive has. The undo is matched either way.
#[test]
fn restart_with_lost_cache() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "before restart");
    let latest = |hive: &Fixture, bookmark: &str| {
        let (id, description) = op_log(hive.repo(0)).swap_remove(0);
        assert!(description.starts_with(&format!("create bookmark {bookmark} ")));
        id
    };
    hive.repo(0).jj(&["bookmark", "create", "x", "-r", "@-"]);
    let x = latest(&hive, "x");
    hive.repo(0).jj(&["bookmark", "create", "y", "-r", "@-"]);
    let y = latest(&hive, "y");
    hive.repo(0).jj(&["op", "abandon", &x]);
    hive.repo(0)
        .jj(&["--at-op", &y, "bookmark", "create", "z", "-r", "@-"]);
    hive.commit(1, "u", "undone");
    hive.repo(1).jj(&["undo"]);
    hive.sync();
    for index in 0..2 {
        let heads = hive.node(index).canonical_heads().unwrap();
        std::fs::remove_file(hive.repo(index).repo_path().join("musubi/translation")).unwrap();
        hive.reopen(index);
        assert_eq!(
            hive.node(index).canonical_heads().unwrap(),
            heads,
            "translated afresh, {index}'s op heads changed"
        );
    }
    hive.commit(0, "b", "after restart");
    hive.commit(1, "c", "beta after restart");
    hive.sync();
    hive.assert_converged();
    for index in 0..2 {
        let ops = op_log(hive.repo(index));
        let count = |prefix: &str| ops.iter().filter(|(_, op)| op.starts_with(prefix)).count();
        assert_eq!(
            (count("undo: "), count("create bookmark y ")),
            (1, 2),
            "the undo, or bookmark y's operation or its rewrite, is gone: {ops:#?}"
        );
    }
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
    let before = hive.node(1).local_heads().unwrap();
    let err = hive.try_sync().unwrap_err();
    let message = format!("{err:#}");
    assert!(
        message.contains("root commit as one of the parents") && message.contains("op revert"),
        "{message}"
    );
    assert_eq!(
        hive.node(1).local_heads().unwrap(),
        before,
        "an unmergeable realization must not replace or join the published heads"
    );
    for machine in [0, 1] {
        hive.repo(machine).jj(&["status"]);
    }
}

/// The size of the hub's `heads` log, in bytes.
fn heads_log_len(hive: &Fixture) -> u64 {
    std::fs::metadata(hive.env.root().join("hub").join("heads"))
        .unwrap()
        .len()
}

/// Trims `repo`'s history, `jj op abandon ..X` of all but its two newest operations.
fn trim(repo: &musubi_testutil::TestRepo) {
    let ops = op_log(repo);
    repo.jj(&["op", "abandon", &format!("..{}", ops[2].0)]);
}

/// Once every machine has taken a trim, the hub prunes its record: it remembers none of the
/// ids it dropped or renamed, keeping only how many records it took and their digest, and its
/// `heads` log no longer names them, so that the trim makes the hub smaller, and opening it
/// takes none of them again. The hive goes on as before, and a later abandon is taken and
/// pruned in turn.
#[test]
fn a_trim_makes_the_hub_smaller() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for i in 0..4 {
        hive.commit(0, &format!("a{i}"), &format!("alpha {i}"));
    }
    hive.sync();
    hive.hive.pruning = false;
    trim(hive.repo(0));
    hive.sync();
    hive.assert_converged();
    let store = hive.hive.hub.store();
    assert_eq!((store.record_count(), store.pruned()), (1, 0));
    let (remembered, log) = (store.remembered_ids(), heads_log_len(&hive));
    assert!(remembered > 0);

    hive.hive.pruning = true;
    hive.sync();
    let store = hive.hive.hub.store();
    assert_eq!((store.record_count(), store.pruned()), (1, 1));
    assert_eq!(store.remembered_ids(), 0);
    assert!(store.records().is_empty());
    assert!(
        heads_log_len(&hive) < log,
        "{} < {log}",
        heads_log_len(&hive)
    );
    hive.hive.restart_hub().unwrap();
    let store = hive.hive.hub.store();
    assert_eq!((store.record_count(), store.pruned()), (1, 1));
    assert_eq!(store.remembered_ids(), 0);

    hive.commit(1, "b", "beta after the trim");
    hive.sync();
    hive.assert_converged();
    assert!(
        hive.visible(0)
            .iter()
            .any(|c| c.ends_with("beta after the trim"))
    );
    let abandoned = commit_op(hive.repo(1));
    hive.repo(1).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    let store = hive.hive.hub.store();
    assert_eq!((store.record_count(), store.pruned()), (2, 2));
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
    }
}

/// A machine that is offline, and that the hive hasn't forgotten, holds pruning back until it
/// syncs and has taken the record.
#[test]
fn an_offline_machine_holds_pruning_back() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    for _ in 0..3 {
        hive.hive.sync(0).unwrap();
        hive.hive.sync(1).unwrap();
    }
    let store = hive.hive.hub.store();
    assert_eq!((store.record_count(), store.pruned()), (1, 0));
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    assert!(!has_operation(hive.repo(2), &abandoned.1));
}

/// The hub doesn't wait for a copy the hive has forgotten. One that comes back from behind
/// the records the hub pruned can't take them, and could hold operations they drop: it stops
/// syncing, with the message for a history that no longer matches the hive's, and the
/// abandoned operation doesn't come back.
#[test]
fn a_forgotten_copy_behind_pruned_records_stops() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    hive.commit(2, "g", "gamma's last work");
    let gamma = hive.machine_key(2);
    assert!(hive.node(0).forget_copy(&gamma, "gamma").unwrap());
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    for _ in 0..3 {
        hive.hive.sync(0).unwrap();
        hive.hive.sync(1).unwrap();
    }
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    let head = hive.hive.hub_head();
    let err = hive.hive.sync(2).unwrap_err();
    assert!(
        matches!(
            err.downcast_ref::<musubi_jj::node::NodeError>(),
            Some(musubi_jj::node::NodeError::PrunedRecords)
        ),
        "{err:#}"
    );
    assert!(history_lost(&err));
    assert!(
        format!("{err:#}").contains("history no longer matches the hive's"),
        "{err:#}"
    );
    assert_eq!(hive.hive.hub_head(), head);
    for machine in 0..2 {
        hive.hive.sync(machine).unwrap();
        assert!(
            !hive
                .visible(machine)
                .iter()
                .any(|c| c.ends_with("gamma's last work")),
            "{machine}"
        );
    }
}

/// A copy the hive forgot that had taken the record the hub then pruned comes back with its
/// next work as any forgotten copy does: its records start with the pruned ones.
#[test]
fn a_forgotten_copy_that_took_the_pruned_records_comes_back() {
    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    let gamma = hive.machine_key(2);
    assert!(hive.node(0).forget_copy(&gamma, "gamma").unwrap());
    for _ in 0..2 {
        hive.hive.sync(0).unwrap();
        hive.hive.sync(1).unwrap();
    }
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    hive.commit(2, "g", "gamma back");
    hive.sync();
    hive.assert_converged();
    assert!(hive.shown_machines().contains(&gamma));
    assert!(hive.visible(0).iter().any(|c| c.ends_with("gamma back")));
}

/// A machine restarts, and the reply to its first poll is one held up since before the hub
/// pruned a record it took, which tells it of no records: it takes none. Restarted again, it
/// takes the hub's records from the pruned one, which the hub knows only by its count and
/// digest, as it held that record before; and the abandoned operation doesn't come back.
/// Taking none, it can no longer take the hub's records from the pruned one by what it holds,
/// and stops for good unless it remembers what it held, across a restart.
#[test]
fn a_machine_takes_records_from_a_pruned_one_it_held_before() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    let mut held = None;
    hive.hive
        .sync_through(1, &mut |request, reply| {
            if matches!(request, Request::Fetch { .. }) && held.is_none() {
                held = Some(reply.clone());
            }
            reply
        })
        .unwrap();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    hive.sync();
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    assert_eq!(hive.node(1).record_state().0, 1);
    hive.reopen(1);
    hive.hive
        .sync_steps(1, 1, &mut |_, reply| held.take().unwrap_or(reply))
        .unwrap();
    assert_eq!(hive.node(1).record_state().0, 0);
    hive.reopen(1);
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.node(1).record_state().0, 1);
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
    }
}

/// A machine that joins after the hub pruned its records starts from them as the hub keeps
/// them, knowing only how many there are and their digest: it syncs, the hub waits for it
/// once it is in the hive, and it takes a later abandon like any machine.
#[test]
fn a_machine_joins_after_a_prune() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for i in 0..3 {
        hive.commit(0, &format!("a{i}"), &format!("alpha {i}"));
    }
    hive.sync();
    trim(hive.repo(0));
    hive.sync();
    hive.sync();
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    let gamma = hive.env.init_repo("gamma");
    hive.add(gamma);
    hive.sync();
    hive.assert_converged();
    assert!(hive.visible(2).iter().any(|c| c.ends_with("alpha 2")));
    hive.commit(2, "g", "gamma's work");
    hive.sync();
    hive.assert_converged();
    assert!(hive.visible(0).iter().any(|c| c.ends_with("gamma's work")));
    hive.commit(1, "b1", "beta 1");
    let abandoned = op_log(hive.repo(1))[0].clone();
    assert!(abandoned.1.starts_with("commit "), "{abandoned:?}");
    hive.commit(1, "b2", "beta 2");
    hive.hive.sync(1).unwrap();

    // beta abandons the first of those operations of its own, which gamma doesn't take.
    hive.repo(1).jj(&["op", "abandon", &abandoned.0]);
    for _ in 0..3 {
        hive.hive.sync(1).unwrap();
        hive.hive.sync(0).unwrap();
    }
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.hive.hub.store().pruned(), 2);
    for machine in 0..3 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
    }
}

/// A hub that restarts after a prune opens with the records pruned, and replays none of
/// them. It has forgotten what each machine said it took, so it prunes a later record only
/// once every machine has said so again.
#[test]
fn hub_restarts_after_a_prune() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    hive.sync();
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    hive.hive.restart_hub().unwrap();
    hive.commit(1, "c", "after the restart");
    hive.sync();
    hive.assert_converged();
    assert!(
        hive.visible(0)
            .iter()
            .any(|c| c.ends_with("after the restart"))
    );
    // Both machines take a later record and say so, then the hub restarts: only the machine
    // that says so again counts.
    hive.hive.pruning = false;
    let later = commit_op(hive.repo(1));
    hive.repo(1).jj(&["op", "abandon", &later.0]);
    hive.sync();
    hive.sync();
    hive.hive.restart_hub().unwrap();
    hive.hive.pruning = true;
    hive.hive.sync(1).unwrap();
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    hive.hive.sync(0).unwrap();
    assert_eq!(hive.hive.hub.store().pruned(), 2);
    hive.assert_converged();
}

/// A hub that loses the `heads` log it wrote pruning, as a power cut can make it, goes back
/// to the one before, which names the records again. The machines that took them, and one
/// that joined after the prune, whose records the hub's still start with, carry on, and the
/// hub prunes again.
#[test]
fn hub_goes_back_across_a_prune() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    hive.hive.pruning = false;
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", &abandoned.0]);
    hive.sync();
    hive.sync();
    let heads = hive.env.root().join("hub").join("heads");
    let before = std::fs::read(&heads).unwrap();
    hive.hive.pruning = true;
    hive.sync();
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    let gamma = hive.env.init_repo("gamma");
    hive.add(gamma);
    hive.sync();
    hive.assert_converged();

    std::fs::write(&heads, before).unwrap();
    hive.hive.restart_hub().unwrap();
    let store = hive.hive.hub.store();
    assert_eq!((store.record_count(), store.pruned()), (1, 0));
    hive.commit(2, "g", "gamma after the hub went back");
    hive.sync();
    hive.sync();
    hive.assert_converged();
    assert_eq!(hive.hive.hub.store().pruned(), 1);
    for machine in 0..3 {
        assert!(
            !has_operation(hive.repo(machine), &abandoned.1),
            "{machine}"
        );
        assert!(
            hive.visible(machine)
                .iter()
                .any(|c| c.ends_with("gamma after the hub went back")),
            "{machine}"
        );
    }
}

/// A hive made again, empty, after its hub pruned its records, has none of them. A machine
/// that joined after the prune, knowing them only by their count and digest, can't publish
/// them again, and the machines that took them whole publish them again as one record, which
/// it can't match: holding nothing they drop, it takes the hub's records whole in their place,
/// and carries on.
#[test]
fn a_machine_that_joined_after_a_prune_carries_on_when_the_hive_is_made_again() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for i in 0..3 {
        hive.commit(0, &format!("a{i}"), &format!("alpha {i}"));
    }
    hive.sync();
    // Two records, which the machines that took them publish again as one.
    hive.hive.pruning = false;
    let mut abandoned = vec![];
    for _ in 0..2 {
        let op = commit_op(hive.repo(0));
        hive.repo(0).jj(&["op", "abandon", &op.0]);
        hive.sync();
        abandoned.push(op.1);
    }
    hive.hive.pruning = true;
    hive.sync();
    assert_eq!(hive.hive.hub.store().pruned(), 2);
    let gamma = hive.env.init_repo("gamma");
    hive.add(gamma);
    hive.sync();
    hive.hive.remake_hub().unwrap();
    hive.commit(2, "g", "gamma after the hive was made again");
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub.store().record_count(), 0);
    hive.sync();
    hive.sync();
    hive.assert_converged();
    for machine in 0..3 {
        for op in &abandoned {
            assert!(!has_operation(hive.repo(machine), op), "{machine}: {op}");
        }
        assert!(
            hive.visible(machine)
                .iter()
                .any(|c| c.ends_with("gamma after the hive was made again")),
            "{machine}"
        );
    }
    assert_eq!(hive.hive.hub.store().record_count(), 1);
}

/// A cached fix-up can be below an operation its packet drops after a remake. A receiver
/// still at that dropped operation must take the records even though its head already
/// descends from the hub's surviving head.
#[test]
fn a_receiver_takes_records_that_drop_its_head_above_a_cached_fixup() {
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;
    use musubi_jj::op_id::CanonicalOp;

    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let base = hive.hive.hub.store().head().0;

    // Alpha publishes p, which beta holds as its head, then a on top.
    hive.commit(0, "p", "alpha's drop");
    let p = op_log(hive.repo(0)).swap_remove(0);
    hive.hive.sync(0).unwrap();
    hive.hive.sync(1).unwrap();
    hive.commit(0, "a", "alpha keeps this");
    hive.hive.sync(0).unwrap();

    // Alpha abandons p and pushes its fix-up F, stopping before it takes its own record.
    hive.repo(0).jj(&["op", "abandon", &p.0]);
    hive.hive.sync_steps(0, 1, &mut |_, reply| reply).unwrap();
    let f = hive.hive.hub_head();
    assert!(!hive.node(0).pending_drops().is_empty());

    // Beta fetches F. The records drop its head p, so it realizes F without taking them; a
    // user integrates F as an op head and commits d on it.
    let before_receipt =
        std::fs::read(hive.repo(1).repo_path().join("musubi/records.json")).unwrap();
    hive.hive.fetch(1).unwrap();
    for _ in 0..32 {
        let member = &mut hive.hive.members[1];
        if member.adapter.is_local(&f).unwrap() {
            break;
        }
        let step = member.core.step(&mut member.adapter).unwrap();
        assert!(matches!(step, Step::Realized(_)), "{step:?}");
    }
    assert!(hive.hive.members[1].adapter.is_local(&f).unwrap());
    hive.node(1).settle().unwrap();
    let f_beta = hive.node(1).local_of(&CanonicalOp(f.clone())).unwrap();
    hive.repo(1)
        .jj(&["--ignore-working-copy", "op", "integrate", &f_beta.0.hex()]);
    hive.commit(1, "d", "beta's later drop");
    let d = op_log(hive.repo(1)).swap_remove(0);
    // Lose the recent custody write as a power cut can, while keeping jj's operation writes.
    std::fs::write(
        hive.repo(1).repo_path().join("musubi/records.json"),
        before_receipt,
    )
    .unwrap();
    hive.reopen(1);

    // The hub loses F and alpha's record. Beta publishes d, gamma holds exactly d, and beta
    // abandons d, publishing the record {d}.
    hive.hive.hub_goes_back(base).unwrap();
    hive.hive.sync(1).unwrap();
    let d_hub = hive.hive.hub_head();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.members[2].core.known().1, d_hub);
    hive.commit(1, "e", "beta keeps this");
    hive.repo(1).jj(&["op", "abandon", &d.0]);
    hive.hive.sync(1).unwrap();

    // Alpha takes {d} without its own record, keeping its fix-up written, then crashes.
    hive.hive.sync_steps(0, 1, &mut |_, reply| reply).unwrap();
    let saved: serde_json::Value = serde_json::from_slice(
        &std::fs::read(hive.repo(0).repo_path().join("musubi/records.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(saved["fixup_written"], true);
    assert!(!hive.node(0).pending_drops().is_empty());
    hive.reopen(0);

    // The hub loses {d}. Alpha re-adopts and pushes.
    hive.hive.hub_goes_back(base).unwrap();
    let mut pushed = vec![];
    hive.hive
        .sync_through(0, &mut |request, reply| {
            if let Request::Push {
                expected,
                new,
                dropped,
                ..
            } = request
            {
                pushed.push((expected.clone(), new.clone(), dropped.clone()));
                assert!(matches!(
                    reply,
                    Reply::Head {
                        kind: HeadKind::Accepted,
                        ..
                    }
                ));
            }
            reply
        })
        .unwrap();
    assert_eq!(pushed.len(), 1);
    assert_eq!(pushed[0].1, f);
    assert!(pushed[0].2.contains(&d_hub));
    assert_eq!(hive.hive.hub_head(), f);

    // Gamma still has d. Its head descends from F, but taking the records must replace it.
    assert_ne!(d_hub, f);
    assert_eq!(
        hive.hive.members[2].adapter.heads().unwrap(),
        vec![d_hub.clone()]
    );
    assert!(
        hive.hive.members[2]
            .adapter
            .is_ancestor(&f, &d_hub)
            .unwrap()
    );
    assert!(hive.hive.sync(2).unwrap() > 0);
    let records = hive.hive.hub.records();
    let current_head = hive.hive.hub_head();
    let member = &mut hive.hive.members[2];
    assert_eq!(member.adapter.records().unwrap(), records);
    assert_eq!(member.core.known().1, current_head);
    assert!(matches!(
        member.core.step(&mut member.adapter).unwrap(),
        Step::Idle
    ));
}

#[test]
fn record_bodies_keep_pending_drops_named_after_hub_rollback() {
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_jj::op_id::CanonicalOp;

    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    let before_a = hive.hive.hub.store().head().0;
    hive.commit(0, "a", "first drop rewrites the pending name");
    hive.hive.sync(0).unwrap();
    let a = hive.hive.hub_head();
    hive.commit(0, "p", "dropped history beta never realizes");
    let p_local = op_log(hive.repo(0))[0].0.clone();
    hive.hive.sync(0).unwrap();
    let p0 = hive.hive.hub_head();
    hive.hive.sync(2).unwrap();
    let a_gamma = hive.node(2).local_of(&CanonicalOp(a.clone())).unwrap();
    assert_eq!(hive.hive.members[2].adapter.records().unwrap().count, 0);
    hive.commit(0, "q", "alpha retains work above the later drop");
    hive.hive.sync(0).unwrap();
    hive.repo(0).jj(&["op", "abandon", &p_local]);
    hive.hive.sync(0).unwrap();
    assert!(
        hive.hive
            .hub
            .store()
            .records()
            .iter()
            .any(|r| r.ops().iter().any(|op| op.0.0 == p0))
    );
    hive.hive.sync(1).unwrap();
    assert_eq!(
        hive.hive.members[1].adapter.records().unwrap(),
        hive.hive.hub.records()
    );
    assert!(hive.node(1).pending_drops().is_empty());
    hive.hive.hub_goes_back(before_a).unwrap();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub_head(), p0);
    assert_eq!(hive.hive.hub.store().record_count(), 0);
    hive.repo(2).jj(&["op", "abandon", &a_gamma.0.hex()]);
    hive.hive.sync(2).unwrap();
    let current_p = hive.hive.hub.store().current(&p0);
    assert_eq!(current_p.len(), 1);
    let p1 = current_p[0].clone();
    assert_ne!(p1, p0);
    assert_eq!(
        hive.hive
            .hub
            .store()
            .canonical()
            .original_id(&CanonicalOp(p0.clone()))
            .unwrap(),
        hive.hive
            .hub
            .store()
            .canonical()
            .original_id(&CanonicalOp(p1.clone()))
            .unwrap()
    );
    assert!(hive.hive.hub.store().is_superseded(&p0));
    assert!(
        hive.hive
            .hub
            .store()
            .records()
            .iter()
            .all(|r| r.ops().iter().all(|op| op.0.0 != p0))
    );
    let record_count = hive.hive.hub.store().record_count();
    // Beta must rename the old record's p0 to p1 before writing its supersede. Merely
    // accepting p0 as already superseded leaves it pending and p1 alive forever.
    let taken = hive.hive.sync_steps(1, 24, &mut |_, reply| reply).unwrap();
    assert!(taken < 24, "beta did not finish republishing its lost drop");
    assert!(hive.node(1).pending_drops().is_empty());
    assert_eq!(hive.hive.hub.store().record_count(), record_count + 1);
    assert!(
        hive.hive
            .hub
            .store()
            .records()
            .last()
            .unwrap()
            .ops()
            .iter()
            .any(|op| op.0.0 == p1)
    );
    assert_eq!(
        hive.hive.members[1].adapter.records().unwrap(),
        hive.hive.hub.records()
    );
    assert!(!hive.hive.hub.store().is_accepted(&p1));
    assert!(
        hive.node(1)
            .canonical_store()
            .has_operation(&CanonicalOp(p0))
    );
}

/// Receiving a drop of an already rewritten operation must preserve its older name for a
/// rollback, even when this receiver never fetched that older operation.
#[test]
fn lost_records_follow_an_older_name_the_receiver_never_held() {
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_jj::op_id::CanonicalOp;

    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.hive.pruning = false;
    let before_a = hive.hive.hub.store().head().0;
    hive.commit(0, "a", "ancestor abandoned before the later drop");
    let a_local = op_log(hive.repo(0))[0].0.clone();
    hive.hive.sync(0).unwrap();
    let a = hive.hive.hub_head();
    hive.commit(0, "p", "operation whose two aliases are dropped");
    hive.hive.sync(0).unwrap();
    let p0 = hive.hive.hub_head();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.members[2].adapter.records().unwrap().count, 0);
    hive.commit(0, "q", "work retained above both abandons");
    hive.hive.sync(0).unwrap();

    hive.repo(0).jj(&["op", "abandon", &a_local]);
    hive.hive.sync(0).unwrap();
    let current = hive.hive.hub.store().current(&p0);
    assert_eq!(current.len(), 1);
    let p1 = current[0].clone();
    assert_ne!(p0, p1);
    let p1_local = hive.node(0).local_of(&CanonicalOp(p1.clone())).unwrap();
    hive.repo(0).jj(&["op", "abandon", &p1_local.0.hex()]);
    hive.hive.sync(0).unwrap();
    let records = hive.hive.hub.store().records();
    assert_eq!(records.len(), 2);
    assert!(records[0].ops().iter().any(|op| op.0.0 == a));
    assert!(records[1].ops().iter().any(|op| op.0.0 == p1));

    // Beta sees neither p0 nor p1 as a live hub operation. Only record metadata supplies p1.
    assert!(
        !hive
            .node(1)
            .canonical_store()
            .has_operation(&CanonicalOp(p0.clone()))
    );
    hive.hive.sync(1).unwrap();
    assert!(
        hive.node(1)
            .canonical_store()
            .has_operation(&CanonicalOp(p1.clone()))
    );
    assert!(
        !hive
            .node(1)
            .canonical_store()
            .has_operation(&CanonicalOp(p0.clone()))
    );
    assert!(hive.node(1).pending_drops().is_empty());
    assert_eq!(
        hive.hive.members[1].adapter.records().unwrap(),
        hive.hive.hub.records()
    );

    hive.hive.hub_goes_back(before_a).unwrap();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub_head(), p0);
    assert_eq!(hive.hive.hub.store().record_count(), 0);
    let steps = hive.hive.sync_steps(1, 24, &mut |_, reply| reply).unwrap();
    assert!(
        steps < 24,
        "beta did not finish republishing the two lost drops"
    );
    assert!(hive.node(1).pending_drops().is_empty());
    assert!(!hive.hive.hub.store().is_accepted(&p0));
    assert!(!hive.hive.hub.store().is_accepted(&p1));
    assert!(
        hive.hive
            .hub
            .store()
            .records()
            .last()
            .unwrap()
            .ops()
            .iter()
            .any(|op| op.0.0 == p0)
    );

    // A replacement hub has none of the drop bodies. Republishing must carry them too,
    // although they are absent from the operation history the machine publishes.
    hive.hive.remake_hub().unwrap();
    hive.hive.sync(1).unwrap();
    assert!(hive.node(1).pending_drops().is_empty());
    assert!(
        hive.hive
            .hub
            .store()
            .canonical()
            .has_operation(&CanonicalOp(p0.clone()))
    );
    assert!(!hive.hive.hub.store().is_accepted(&p0));
}

/// A receiver writes rewritten operations before taking their records. The producer leaves,
/// then the hub loses the records twice. Receiving the operations must preserve record
/// custody, and taking a later record must drop every physical alias of its original.
#[test]
fn received_records_survive_departure_and_drop_local_aliases() {
    use crate::oracle::Oracle;
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::hub::HubStorage as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;
    use musubi_jj::op_id::CanonicalOp;
    use serde_json::json;

    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(0, "base", "common base before the two names");
    hive.sync();
    let (base_seq, base) = hive.hive.hub.store().head();
    let (base_seq, base) = (base_seq, base.clone());
    let beta_base = hive.node(1).local_of(&CanonicalOp(base.clone())).unwrap();
    let alpha_base = hive.node(0).local_of(&CanonicalOp(base.clone())).unwrap();
    hive.commit(0, "a", "rewrite the future pending operation");
    let a_alpha = op_log(hive.repo(0))[0].0.clone();
    hive.hive.sync(0).unwrap();
    let a = hive.hive.hub_head();
    hive.hive.fetch(1).unwrap();
    for _ in 0..16 {
        let member = &mut hive.hive.members[1];
        if member.adapter.is_local(&a).unwrap() {
            break;
        }
        assert!(matches!(
            member.core.step(&mut member.adapter).unwrap(),
            Step::Realized(_)
        ));
    }
    hive.node(1).settle().unwrap();
    let a_beta = hive.node(1).local_of(&CanonicalOp(a.clone())).unwrap();
    hive.repo(1)
        .jj(&["--ignore-working-copy", "op", "integrate", &a_beta.0.hex()]);
    assert_eq!(hive.hive.members[1].adapter.accepted_base().unwrap(), base);
    hive.commit(0, "p", "the two aliases later dropped twice");
    hive.hive.sync(0).unwrap();
    let p0 = hive.hive.hub_head();
    hive.hive.sync(2).unwrap();
    let p0_gamma = hive.node(2).local_of(&CanonicalOp(p0.clone())).unwrap();
    hive.commit(0, "q", "work retained above the rewritten operation");
    hive.hive.sync(0).unwrap();
    hive.repo(0).jj(&[
        "op",
        "abandon",
        &format!("{}..{}", alpha_base.0.hex(), a_alpha),
    ]);
    let mut accepted = false;
    hive.hive
        .sync_steps(0, 1, &mut |request, reply| {
            if let (
                Request::Push { dropped, .. },
                Reply::Head {
                    kind: HeadKind::Accepted,
                    ..
                },
            ) = (request, &reply)
            {
                assert!(dropped.contains(&a));
                accepted = true;
            }
            reply
        })
        .unwrap();
    assert!(accepted);
    let f = hive.hive.hub_head();
    let received_state = hive.hive.hub.records();
    let p1s = hive.hive.hub.store().current(&p0);
    assert_eq!(p1s.len(), 1);
    let p1 = p1s[0].clone();
    assert_ne!(p0, p1);
    hive.hive.fetch(1).unwrap();
    for _ in 0..16 {
        let member = &mut hive.hive.members[1];
        if member.adapter.is_local(&f).unwrap() {
            break;
        }
        assert!(matches!(
            member.core.step(&mut member.adapter).unwrap(),
            Step::Realized(_)
        ));
    }
    hive.node(1).settle().unwrap();
    let f_beta = hive.node(1).local_of(&CanonicalOp(f)).unwrap();
    assert_eq!(hive.hive.members[1].adapter.records().unwrap().count, 0);
    // As `musubi leave` does: publish the departure, verify it took, and restore the local
    // workspaces. Alpha never syncs again, so it cannot republish the lost record for beta.
    let removed = hive.node(0).forget_self().unwrap().unwrap();
    hive.hive.sync(0).unwrap();
    let key = hive.node(0).machine().key().to_owned();
    let (_, presence) = hive.node(0).present_copies().unwrap();
    assert!(!presence.is_present(&key));
    hive.node(0).restore_workspaces(&removed).unwrap();
    hive.reopen(1);
    hive.repo(1).jj(&[
        "--ignore-working-copy",
        "--at-op",
        &f_beta.0.hex(),
        "describe",
        "-m",
        "blind child retaining P1",
    ]);
    hive.repo(1).jj(&[
        "--ignore-working-copy",
        "--at-op",
        &a_beta.0.hex(),
        "describe",
        "-m",
        "child of the old A head",
    ]);
    hive.repo(1).jj(&[
        "--ignore-working-copy",
        "op",
        "abandon",
        &format!("{}..{}", beta_base.0.hex(), a_beta.0.hex()),
    ]);
    assert!(!hive.node(1).check_abandon().unwrap());
    assert!(hive.node(1).pending_drops().is_empty());
    hive.hive.hub_goes_back(base_seq).unwrap();
    assert!(hive.node(1).has_record_custody());
    assert!(
        hive.hive.members[1]
            .adapter
            .held(&received_state)
            .unwrap()
            .is_none()
    );
    // The equal-record receipt recovery is also checked against the executable control
    // model: fetched keeps an announcement, and taking it spends the persistent debt.
    let mut oracle = Oracle::spawn();
    let fetched = oracle.call(&json!({
        "op": "recordEpoch", "current": 0, "applied": 0, "announced": null,
        "stalePlan": false, "receipts": true, "action": "fetched"
    }));
    assert_eq!(fetched["ok"], true, "{fetched}");
    assert_eq!(fetched["announced"], 0);
    assert_eq!(
        fetched["needsRecords"], true,
        "equal records still have receipt work"
    );
    hive.hive.fetch(1).unwrap();
    let adopted = oracle.call(&json!({
        "op": "recordEpoch", "current": 0, "applied": 0,
        "announced": fetched["announced"], "stalePlan": false,
        "receipts": true, "action": "adopt", "records": 0
    }));
    assert_eq!(adopted["ok"], true, "{adopted}");
    assert_eq!(adopted["beforeNeedsRecords"], true);
    assert_eq!(adopted["needsRecords"], false);
    {
        let member = &mut hive.hive.members[1];
        assert!(matches!(
            member.core.step(&mut member.adapter).unwrap(),
            Step::Adopted
        ));
    }
    assert_eq!(
        hive.hive.members[1].adapter.records().unwrap().count,
        adopted["applied"].as_u64().unwrap()
    );
    assert_eq!(
        hive.node(1).has_record_custody(),
        adopted["receipts"].as_bool().unwrap()
    );
    assert_eq!(adopted["adopts"], true);
    assert!(adopted["credit"].as_u64().unwrap() < adopted["beforeCredit"].as_u64().unwrap());
    let held = hive.hive.members[1]
        .adapter
        .held(&received_state)
        .unwrap()
        .unwrap();
    assert!(held.records.iter().flatten().any(|op| *op == a));
    let mut republished = false;
    let taken = hive
        .hive
        .sync_steps(1, 24, &mut |request, reply| {
            if let (
                Request::Push { dropped, .. },
                Reply::Head {
                    kind: HeadKind::Accepted,
                    ..
                },
            ) = (request, &reply)
                && dropped.contains(&a)
            {
                republished = true;
            }
            reply
        })
        .unwrap();
    assert!(taken < 24);
    assert!(republished, "the received abandonment was not republished");
    assert_eq!(hive.hive.hub.store().record_count(), 1);
    assert_eq!(
        hive.hive.members[1].adapter.accepted_base().unwrap(),
        hive.hive.hub_head()
    );
    let recovered_head = hive.hive.hub_head();
    assert!(
        hive.node(1)
            .canonical_store()
            .is_ancestor_of(&CanonicalOp(p1.clone()), &CanonicalOp(recovered_head))
            .unwrap()
    );

    hive.hive.hub_goes_back(base_seq).unwrap();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub_head(), p0);
    hive.commit(2, "r", "gamma retains work after dropping P0");
    hive.repo(2).jj(&["op", "abandon", &p0_gamma.0.hex()]);
    hive.hive.sync(2).unwrap();
    assert!(
        hive.hive
            .hub
            .store()
            .records()
            .iter()
            .any(|r| r.ops().iter().any(|op| op.0.0 == p0))
    );
    hive.hive.fetch(1).unwrap();
    {
        let member = &mut hive.hive.members[1];
        assert!(matches!(
            member.core.step(&mut member.adapter).unwrap(),
            Step::Adopted
        ));
    }
    let applied = hive.hive.members[1].adapter.applied_records().unwrap();
    assert!(applied.records.iter().flatten().any(|op| *op == p0));
    assert_eq!(
        hive.hive.members[1].adapter.records().unwrap(),
        hive.hive.hub.records()
    );
    assert!(
        hive.node(1)
            .pending_drops()
            .ops()
            .iter()
            .any(|op| op.0.0 == a),
        "the second rollback lost beta's recovered abandonment"
    );
    let heads = hive.node(1).canonical_heads().unwrap();
    let store = hive.node(1).canonical_store();
    let original_p = store.original_id(&CanonicalOp(p0.clone())).unwrap();
    assert_eq!(
        store.original_id(&CanonicalOp(p1.clone())).unwrap(),
        original_p
    );
    let history = store.ancestors_until(&heads, |_| false).unwrap();
    assert!(
        history
            .iter()
            .all(|op| store.original_id(op).unwrap() != original_p),
        "taking the record left another raw version of the dropped original in local history"
    );
    // The off-frontier record name needs its durable image too, even though only P1 was
    // physically reachable when the record was taken.
    hive.reopen(1);
    for old in [p0, p1] {
        let images = hive.node(1).current(&CanonicalOp(old)).unwrap();
        assert!(!images.is_empty());
        let store = hive.node(1).canonical_store();
        assert!(
            images
                .iter()
                .all(|op| store.original_id(&op.0).unwrap() != original_p)
        );
    }
    let steps = hive.hive.sync_steps(1, 24, &mut |_, reply| reply).unwrap();
    assert!(
        steps < 24,
        "beta could not publish after taking the aliased drop"
    );
    assert!(hive.node(1).pending_drops().is_empty());
    let final_records = hive.hive.members[1].adapter.applied_records().unwrap();
    assert_eq!(final_records.records.len(), applied.records.len() + 1);
    assert!(final_records.records.last().unwrap().contains(&a));
    assert_eq!(
        hive.hive.members[1].adapter.records().unwrap(),
        hive.hive.hub.records()
    );
}

#[test]
fn an_operation_first_received_after_rollback_uses_the_applied_namespace() {
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_jj::node::NodeOp;
    use musubi_jj::op_id::CanonicalOp;

    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.commit(0, "base", "base before the eager image namespaces");
    hive.sync();
    let (before_a, base) = hive.hive.hub.store().head();
    let (before_a, base) = (before_a, base.clone());
    let alpha_base = hive.node(0).local_of(&CanonicalOp(base)).unwrap();
    hive.commit(0, "a", "ancestor dropped before beta learns P");
    let a_local = op_log(hive.repo(0))[0].0.clone();
    hive.hive.sync(0).unwrap();
    let a = hive.hive.hub_head();
    // No new files: P is an immediate child of A, without a pre-command snapshot.
    hive.repo(0).jj(&[
        "--ignore-working-copy",
        "describe",
        "-m",
        "P directly above old A",
    ]);
    hive.hive.sync(0).unwrap();
    let p0 = hive.hive.hub_head();
    assert_eq!(
        hive.hive
            .hub
            .store()
            .canonical()
            .read_operation(&CanonicalOp(p0.clone()))
            .unwrap()
            .parents
            .as_slice(),
        std::slice::from_ref(&a)
    );
    hive.hive.sync(2).unwrap();
    let p0_gamma = hive.node(2).local_of(&CanonicalOp(p0.clone())).unwrap();
    hive.repo(0)
        .jj(&["--ignore-working-copy", "describe", "-m", "Q kept above P"]);
    hive.hive.sync(0).unwrap();
    hive.repo(0).jj(&[
        "op",
        "abandon",
        &format!("{}..{}", alpha_base.0.hex(), a_local),
    ]);
    hive.hive.sync(0).unwrap();
    let p1 = hive.hive.hub.store().current(&p0);
    assert_eq!(p1.len(), 1);
    assert_ne!(p1[0], p0);
    hive.hive.sync(1).unwrap();
    assert!(hive.node(1).pending_drops().is_empty());
    assert!(
        !hive
            .node(1)
            .canonical_store()
            .has_operation(&CanonicalOp(p0.clone()))
    );
    assert_ne!(
        hive.node(1).current(&CanonicalOp(a.clone())).unwrap(),
        [NodeOp(CanonicalOp(a.clone()))]
    );
    assert!(
        hive.hive.members[1]
            .adapter
            .applied_records()
            .unwrap()
            .records
            .iter()
            .flatten()
            .any(|id| *id == a)
    );

    hive.hive.hub_goes_back(before_a).unwrap();
    hive.hive.sync(2).unwrap();
    assert_eq!(hive.hive.hub_head(), p0);
    hive.repo(2).jj(&[
        "--ignore-working-copy",
        "describe",
        "-m",
        "gamma keeps a child after P",
    ]);
    hive.repo(2)
        .jj(&["--ignore-working-copy", "op", "abandon", &p0_gamma.0.hex()]);
    hive.hive.sync(2).unwrap();
    assert!(
        hive.hive
            .hub
            .store()
            .records()
            .iter()
            .any(|r| r.ops().iter().any(|op| op.0.0 == p0))
    );
    hive.hive.fetch(1).unwrap();
    assert!(hive.node(1).pending_drops().is_empty());
    assert_eq!(
        hive.node(1).current(&CanonicalOp(p0.clone())).unwrap(),
        [NodeOp(CanonicalOp(p1[0].clone()))]
    );
    let member = &mut hive.hive.members[1];
    assert!(matches!(
        member.core.step(&mut member.adapter).unwrap(),
        musubi_core::node::Step::Adopted
    ));
    let steps = hive.hive.sync_steps(1, 24, &mut |_, reply| reply).unwrap();
    assert!(steps < 24);
    assert!(hive.node(1).pending_drops().is_empty());
}

/// Recovering a received drop must preserve its latest-work timestamp when the receiver
/// realized a rewritten descendant but never the publisher's work-restoring fix-up.
#[test]
fn lost_received_records_preserve_work_before_the_fixup_arrives() {
    use jj_lib::object_id::ObjectId as _;
    use musubi_core::node::LocalRepo as _;
    use musubi_core::node::Step;
    use musubi_jj::op_id::CanonicalOp;

    let mut hive = Fixture::new(&["alpha", "beta", "gamma"]);
    hive.hive.pruning = false;
    let base = hive.hive.hub_head();
    hive.commit(2, "g", "gamma's latest work before the abandon");
    hive.hive.sync(2).unwrap();
    let a = hive.hive.hub_head();
    let restore_seq = hive.hive.hub.store().head().0;
    let gamma = hive.machine_key(2);
    hive.hive.sync(0).unwrap();
    let a_alpha = hive.node(0).local_of(&CanonicalOp(a.clone())).unwrap();
    let expected = hive
        .node(0)
        .activity()
        .unwrap()
        .into_iter()
        .find(|copy| copy.key == gamma)
        .unwrap()
        .last_work;

    // Beta has A as a physical head but has not advanced its accepted base to it.
    hive.hive.fetch(1).unwrap();
    for _ in 0..16 {
        if hive.hive.members[1].adapter.is_local(&a).unwrap() {
            break;
        }
        let member = &mut hive.hive.members[1];
        assert!(matches!(
            member.core.step(&mut member.adapter).unwrap(),
            Step::Realized(_)
        ));
    }
    hive.node(1).settle().unwrap();
    let a_beta = hive.node(1).local_of(&CanonicalOp(a.clone())).unwrap();
    hive.repo(1)
        .jj(&["--ignore-working-copy", "op", "integrate", &a_beta.0.hex()]);
    assert_eq!(hive.hive.members[1].adapter.accepted_base().unwrap(), base);

    hive.commit(0, "q", "rewritten descendant before the publisher's fix-up");
    hive.hive.sync(0).unwrap();
    let q = hive.hive.hub_head();
    hive.repo(0).jj(&["op", "abandon", &a_alpha.0.hex()]);
    hive.hive.sync(0).unwrap();
    let f = hive.hive.hub_head();
    let rewritten = hive.hive.hub.store().current(&q);
    assert_eq!(rewritten.len(), 1);
    let q_rewritten = rewritten[0].clone();
    assert_ne!(q_rewritten, q);
    let publisher = hive
        .node(0)
        .activity()
        .unwrap()
        .into_iter()
        .find(|copy| copy.key == gamma)
        .unwrap()
        .last_work;
    assert_eq!(
        publisher, expected,
        "the normal fix-up preserves gamma's work time"
    );

    hive.hive.fetch(1).unwrap();
    for _ in 0..24 {
        if hive.hive.members[1].adapter.is_local(&q_rewritten).unwrap() {
            break;
        }
        let member = &mut hive.hive.members[1];
        assert!(matches!(
            member.core.step(&mut member.adapter).unwrap(),
            Step::Realized(_)
        ));
    }
    assert!(hive.hive.members[1].adapter.is_local(&q_rewritten).unwrap());
    assert!(!hive.hive.members[1].adapter.is_local(&f).unwrap());
    hive.node(1).settle().unwrap();
    assert!(hive.node(1).has_record_custody());
    let orphan = hive.node(1).local_of(&CanonicalOp(q_rewritten)).unwrap();

    // Alpha completes the same successful departure as musubi leave, then never runs again.
    let removed = hive.node(0).forget_self().unwrap().unwrap();
    hive.hive.sync(0).unwrap();
    let alpha = hive.machine_key(0);
    assert!(!hive.node(0).present_copies().unwrap().1.is_present(&alpha));
    hive.node(0).restore_workspaces(&removed).unwrap();
    hive.reopen(1);
    hive.repo(1).jj(&[
        "--ignore-working-copy",
        "--at-op",
        &orphan.0.hex(),
        "describe",
        "-m",
        "child of the partial orphan before the publisher's work restoration",
    ]);
    hive.hive.hub_goes_back(restore_seq).unwrap();
    let steps = hive.hive.sync_steps(1, 24, &mut |_, reply| reply).unwrap();
    assert!(steps < 24, "custody recovery must finish");
    assert!(hive.node(1).pending_drops().is_empty());
    assert!(!hive.node(1).has_record_custody());
    let recovered = hive
        .node(1)
        .activity()
        .unwrap()
        .into_iter()
        .find(|copy| copy.key == gamma)
        .unwrap()
        .last_work;
    assert_eq!(
        recovered, expected,
        "custody recovery lost gamma's original work timestamp"
    );
}
