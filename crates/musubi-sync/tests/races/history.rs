//! Operation-log level races: undo, op abandon, offline machines, restarts.

use std::collections::BTreeMap;
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
            assert_eq!(hive.node(1).current(&head), [NodeOp(head)], "{case}");
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
        if held && lose {
            // It publishes the drop it took on the head the hub went back to.
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
