//! Operation-log level races: undo, op abandon, offline machines, restarts.

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
    let heads = member.adapter.heads().unwrap();
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
                Step::Realized(_) => {}
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
    let mut heads_before = member.adapter.heads().unwrap();
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
    let heads_after = member.adapter.heads().unwrap();
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
}

/// `jj op abandon` of operations the hub accepted stops that copy syncing for good, publishing
/// nothing: the hub keeps its history, and the other machine keeps the abandoned operations
/// and goes on syncing its own work.
#[test]
fn op_abandon_of_published_history_stops_that_copy() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    hive.sync();
    hive.assert_converged();
    let abandoned = commit_op(hive.repo(0));
    hive.repo(0).jj(&["op", "abandon", "..@-"]);
    assert!(!has_operation(hive.repo(0), &abandoned.1));
    let head = hive.hive.hub_head();
    let ops = op_log(hive.repo(0));
    for _ in 0..2 {
        let err = hive.hive.sync(0).unwrap_err();
        assert!(history_lost(&err), "{err:#}");
        assert_eq!(hive.hive.hub_head(), head);
        assert_eq!(
            op_log(hive.repo(0)),
            ops,
            "the stop changed alpha's history"
        );
    }

    hive.commit(1, "c", "beta's");
    hive.hive.sync(1).unwrap();
    assert_ne!(hive.hive.hub_head(), head);
    assert!(has_operation(hive.repo(1), &abandoned.1));
    let visible = hive.visible(1);
    for work in [" first", " second", " beta's"] {
        assert!(visible.iter().any(|c| c.ends_with(work)), "{work}");
    }
    let err = hive.hive.sync(0).unwrap_err();
    assert!(history_lost(&err), "{err:#}");
}

/// `jj op abandon` of operations the hub hasn't accepted works as on one machine: no machine
/// ever has them, and the work they recorded stays.
#[test]
fn op_abandon_of_unpublished_operations_stays_here() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.sync();
    hive.commit(0, "b", "second");
    let (id, description) = op_log(hive.repo(0))
        .into_iter()
        .find(|(_, d)| d.starts_with("commit "))
        .unwrap();
    hive.repo(0).jj(&["describe", "-m", "third"]);
    hive.repo(0).jj(&["op", "abandon", &id]);
    hive.sync();
    hive.assert_converged();
    for machine in 0..2 {
        assert!(
            !has_operation(hive.repo(machine), &description),
            "{machine}"
        );
        let visible = hive.visible(machine);
        for work in [" first", " second", " third"] {
            assert!(
                visible.iter().any(|c| c.ends_with(work)),
                "{machine}: {work}"
            );
        }
    }
}

/// So too where the copy has never synced, and abandons every operation below its latest, as
/// `jj op abandon ..@-` does, which jj moves onto the root: none of them was ever sent, so it
/// syncs on.
#[test]
fn abandoning_everything_before_the_first_sync_syncs_on() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    let mut hive = Fixture::unsynced(env, vec![alpha, beta]);
    hive.commit(0, "a", "first");
    hive.commit(0, "b", "second");
    let (_, description) = commit_op(hive.repo(0));
    // As a sync held back before sending would.
    hive.node(0).canonical_heads().unwrap();
    hive.repo(0).jj(&["op", "abandon", "..@-"]);
    hive.sync();
    hive.assert_converged();
    assert!(!has_operation(hive.repo(1), &description));
    assert!(hive.visible(1).iter().any(|c| c.ends_with(" second")));
}

/// A copy that recorded drops to publish, after `jj op abandon` under a release that passed it
/// on, and was upgraded before publishing them, or that was taking the hub's records, stops as
/// any other copy that lost history the hive has does, publishing nothing, and keeps what that
/// release recorded. Nothing in this release records either, so the test writes them into
/// `records.json` as that release did.
///
/// Compatibility until 2027-02-21: remove with `NodeRepo::refuse_legacy_drops`.
#[test]
fn drops_recorded_before_upgrading_stop_that_copy() {
    for case in ["pending", "custody", "realign"] {
        let mut hive = Fixture::new(&["alpha", "beta"]);
        hive.commit(0, "a", "first");
        hive.sync();
        let head = hive.hive.hub_head();
        let hex = jj_lib::object_id::ObjectId::hex(&head);
        let path = hive.repo(0).repo_path().join("musubi/records.json");
        let mut records = serde_json::json!({
            "applied": [],
            "pending": [],
            "fixup": null,
            "fixup_written": false,
        });
        match case {
            "pending" => records["pending"] = serde_json::json!([hex]),
            "custody" => records["custody"] = serde_json::json!([["a", [hex]]]),
            _ => {
                records["realign"] =
                    serde_json::json!({"from": [[hex, [hex]]], "to": [hex], "canonical": []});
            }
        }
        std::fs::write(&path, serde_json::to_vec(&records).unwrap()).unwrap();
        hive.reopen(0);
        hive.commit(0, "b", "second");
        let err = hive.hive.sync(0).unwrap_err();
        assert!(history_lost(&err), "{case}: {err:#}");
        assert!(path.exists(), "{case}");
        assert_eq!(hive.hive.hub_head(), head, "{case}");
        hive.commit(1, "c", "beta's");
        hive.hive.sync(1).unwrap();
    }
}

/// What earlier releases kept in a copy's `musubi` directory to replicate `jj op abandon` is
/// removed when the copy opens, if it records no drops it hadn't published, and the copy syncs
/// on as before.
///
/// Compatibility until 2027-02-21: remove with `legacy::remove_records`.
#[test]
fn files_an_earlier_release_kept_for_abandons_are_removed() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    hive.commit(0, "a", "first");
    hive.sync();
    let dir = hive.repo(0).repo_path().join("musubi");
    let files = ["records.json", "superseded", "hub-renamings", "originals"];
    for name in files {
        std::fs::write(dir.join(name), "{\"pending\": []}").unwrap();
    }
    hive.reopen(0);
    for name in files {
        assert!(!dir.join(name).exists(), "{name}");
    }
    hive.commit(0, "b", "second");
    hive.sync();
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
    let mut hive = Hive::new(&env.root().join("hub"), Backend::GIT).unwrap();
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

/// Concurrently abandoning a child of the root and merging it with another commit
/// converges: jj drops the root parent when rebasing the merge.
#[test]
fn abandoning_a_root_child_beside_a_merge_converges() {
    let mut hive = Fixture::new(&["alpha", "beta"]);
    for message in ["x", "y"] {
        hive.repo(0).jj(&["new", "root()"]);
        hive.commit(0, message, message);
    }
    hive.sync();
    let (x, y) = (hive.commit_id(0, "x"), hive.commit_id(0, "y"));
    hive.repo(0).jj(&["abandon", &x]);
    hive.repo(1).jj(&["new", &x, &y, "-m", "merge"]);
    hive.sync();
    hive.assert_converged();
}
