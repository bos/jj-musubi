//! Canonicalization and realization between real colocated repositories.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;
use std::time::SystemTime;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::CHANGE_ID_LENGTH;
use musubi_jj::objects::GitHash;
use musubi_jj::objects::GitObjects;
use musubi_jj::objects::GitStore;
use musubi_jj::objects::ObjectError;
use musubi_jj::objects::ObjectStore;
use musubi_jj::objects::bundle::BundleWriter;
use musubi_jj::objects::git_extras::CommitExtras;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_jj::ref_locks;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use prost::Message as _;
use serde_json::json;

use crate::oracle;

fn repeated_restore_ops(repo: &TestRepo) -> (LocalOp, LocalOp, LocalOp) {
    let target = repo.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n",
        "1",
        "-T",
        "id",
    ]);
    let restore = || {
        let output = repo
            .program(Path::new("jj"))
            .args(["--ignore-working-copy", "op", "restore", target.trim()])
            .env("JJ_OP_TIMESTAMP", "2001-02-03T04:05:06Z")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let id = repo.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n",
            "1",
            "-T",
            "id",
        ]);
        LocalOp(jj_lib::op_store::OperationId::try_from_hex(id.trim()).unwrap())
    };
    repo.jj(&["describe", "-m", "before"]);
    let a_local = restore();
    repo.jj(&["describe", "-m", "between"]);
    let between = repo.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n",
        "1",
        "-T",
        "id",
    ]);
    let between = LocalOp(jj_lib::op_store::OperationId::try_from_hex(between.trim()).unwrap());
    let x_local = restore();
    assert_ne!(a_local, x_local);
    (a_local, between, x_local)
}

#[test]
fn repeated_restores_keep_distinct_identities_when_contracted() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let (a_local, between, x_local) = repeated_restore_ops(&repo);
    let mut node = open(&repo);
    let a = node.canonicalize(&a_local).unwrap();
    let x = node.canonicalize(&x_local).unwrap();
    let between = node.canonicalize(&between).unwrap();
    let store = node.canonical_store();
    let mut a_content = store.read_operation(&a).unwrap();
    let mut x_content = store.read_operation(&x).unwrap();
    a_content.parents.clear();
    x_content.parents.clear();
    a_content
        .metadata
        .attributes
        .remove("musubi.original-parents");
    x_content
        .metadata
        .attributes
        .remove("musubi.original-parents");
    assert_eq!(a_content, x_content);
    let mut contraction =
        musubi_jj::canonical::Contraction::new(store, [a.clone(), between]).unwrap();
    assert_ne!(contraction.images(store, &x).unwrap(), vec![a]);

    // jj itself has no discriminator: its reparented survivor is byte-for-byte the old a.
    // Refuse before interpreting that a as a survivor and publishing the wrong drops.
    repo.jj(&[
        "--ignore-working-copy",
        "op",
        "abandon",
        &format!("{}-..{}-", a_local.0.hex(), x_local.0.hex()),
    ]);
    let head = repo.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n1",
        "-T",
        "id",
    ]);
    assert_eq!(head.trim(), a_local.0.hex());
    let err = node
        .notice_abandon(&musubi_jj::records::HubOp(x.clone()))
        .unwrap_err();
    assert!(
        matches!(err, musubi_jj::node::NodeError::AmbiguousAbandon(_)),
        "{err}"
    );
    assert!(node.pending_drops().is_empty());
    repo.jj(&["--ignore-working-copy", "op", "integrate", &x_local.0.hex()]);
    assert!(!node.notice_abandon(&musubi_jj::records::HubOp(x)).unwrap());
}

/// Reparenting unpublished work to root must retain its actual namespace, including an
/// owned literal that used to name another copy's workspace.
#[test]
fn an_orphaned_command_keeps_its_native_workspace_owners() {
    use jj_lib::workspace::WorkspaceLoaderFactory as _;
    use musubi_jj::records::{HubOp, Record, RecordPrefix};
    use pollster::FutureExt as _;

    for (own_alias, collect_source) in [(false, false), (true, false), (false, true)] {
        let env = TestEnv::new();
        let a = env.init_repo("alpha");
        let b = env.init_repo("beta");
        let mut node = open(&a);
        let mut other = open(&b);
        let first = single_canonical_head(&mut node);
        sync(&node, &mut other, &first);
        let joined = single_canonical_head(&mut other);
        sync(&other, &mut node, &joined);
        let basis = node.local_heads().unwrap().pop().unwrap();
        let base = node.canonicalize(&basis).unwrap();
        let foreign = node
            .machine_workspaces()
            .unwrap()
            .into_iter()
            .map(|(name, _)| name)
            .find(|name| name.contains('/'))
            .unwrap();
        let foreign_key = format!(
            "{}/{}",
            other.machine().key(),
            foreign.split_once('/').unwrap().1
        );
        let drops = node
            .canonical_store()
            .ancestors_until(&[base], |_| false)
            .unwrap();
        let root = node.canonical_store().root_operation_id().clone();
        node.prepare_records(
            &RecordPrefix::none(),
            &[Record::new(drops.into_iter().map(HubOp))],
        )
        .unwrap();
        node.crash_taking_records(false);
        node.advance_to(&[root]).unwrap_err();
        drop(node);

        if own_alias {
            a.jj(&["workspace", "forget", &foreign]);
            a.jj(&[
                "workspace",
                "add",
                "--name",
                &foreign,
                env.root().join("own-alias").to_str().unwrap(),
            ]);
        }
        a.jj(&["describe", "-m", "unpublished survivor"]);
        let source = a.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n1",
            "-T",
            "id",
        ]);
        let source_id =
            LocalOp(jj_lib::op_store::OperationId::try_from_hex(source.trim()).unwrap());
        let node = open(&a);
        let source_op = node
            .loader()
            .op_store()
            .read_operation(&source_id.0)
            .block_on()
            .unwrap();
        let source_view = node
            .loader()
            .op_store()
            .read_view(&source_op.view_id)
            .block_on()
            .unwrap();
        assert!(
            source_view
                .wc_commit_ids
                .keys()
                .any(|name| name.as_str() == foreign)
        );
        let target = source_view
            .wc_commit_ids
            .get(jj_lib::ref_name::WorkspaceName::new(&foreign))
            .unwrap()
            .clone();
        drop(node);
        a.jj(&["op", "abandon", &format!("..{}-", source.trim())]);
        let working_copy = a.path().join(".jj/working_copy");
        let saved_working_copy = env.root().join("working-copy-before-normalizing");
        musubi_testutil::copy_tree(&working_copy, &saved_working_copy);
        let mut node = open(&a);
        let orphan = node.local_heads().unwrap().pop().unwrap();
        let orphan_op = node
            .loader()
            .op_store()
            .read_operation(&orphan.0)
            .block_on()
            .unwrap();
        assert_eq!(
            orphan_op.parents,
            vec![node.loader().op_store().root_operation_id().clone()]
        );
        if collect_source {
            a.jj(&["--ignore-working-copy", "util", "gc", "--expire", "now"]);
            assert!(
                !a.repo_path()
                    .join("op_store/operations")
                    .join(source.trim())
                    .exists()
            );
            let error = node.canonical_heads().unwrap_err();
            assert!(
                matches!(error, musubi_jj::node::NodeError::UnreachableHistory),
                "{error}"
            );
            assert!(node.pending_drops().is_empty());
            continue;
        }
        let head = node.canonical_heads().unwrap().pop().unwrap();
        let view = node.canonical_store().read_operation_view(&head).unwrap();
        let own = format!("{}/{}", node.machine().key(), foreign);
        let expected_key = if own_alias { &own } else { &foreign_key };
        assert_eq!(
            view.wc_commit_ids
                .get(jj_lib::ref_name::WorkspaceName::new(expected_key)),
            Some(&target)
        );
        assert_eq!(
            view.wc_commit_ids
                .contains_key(jj_lib::ref_name::WorkspaceName::new(&own)),
            own_alias
        );
        // A power cut can retain the counted source aliases and new heads while losing
        // the workspace move and final moving=false write.
        drop(node);
        std::fs::remove_dir_all(&working_copy).unwrap();
        musubi_testutil::copy_tree(&saved_working_copy, &working_copy);
        let records = a.repo_path().join("musubi/records.json");
        let mut state: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&records).unwrap()).unwrap();
        state["moving"] = true.into();
        std::fs::write(&records, serde_json::to_vec(&state).unwrap()).unwrap();
        std::fs::remove_file(a.repo_path().join("musubi/translation")).unwrap();
        node = open(&a);
        node.check_abandon().unwrap();
        let workspace = jj_lib::workspace::DefaultWorkspaceLoaderFactory
            .create(a.path())
            .unwrap()
            .load(
                node.loader().settings(),
                &jj_lib::default_backend_factories::default_backend_factories(),
                &jj_lib::default_backend_factories::default_working_copy_factories(),
            )
            .unwrap();
        let recorded = LocalOp(workspace.working_copy().operation_id().clone());
        let mut reachable = BTreeSet::new();
        let mut pending = node.local_heads().unwrap();
        while let Some(local) = pending.pop() {
            if reachable.insert(local.clone()) {
                let op = node
                    .loader()
                    .op_store()
                    .read_operation(&local.0)
                    .block_on()
                    .unwrap();
                pending.extend(op.parents.into_iter().map(LocalOp));
            }
        }
        assert!(
            reachable.contains(&recorded),
            "the recovered workspace must record a surviving native operation"
        );
        drop(workspace);

        // Both native aliases must retain ownership, with a warm translation cache and
        // after that disposable cache has gone.
        for delayed_parent in [&source_id, &orphan] {
            for lose_cache in [false, true] {
                drop(node);
                if lose_cache {
                    std::fs::remove_file(a.repo_path().join("musubi/translation")).unwrap();
                }
                a.jj(&[
                    "--ignore-working-copy",
                    "--at-op",
                    &delayed_parent.0.hex(),
                    "describe",
                    "-m",
                    "delayed survivor",
                ]);
                node = open(&a);
                let delayed = node.local_heads().unwrap();
                let heads = node.canonical_heads().unwrap();
                assert!(!heads.is_empty());
                for local in delayed {
                    let canonical = node.canonicalize(&local).unwrap();
                    let view = node
                        .canonical_store()
                        .read_operation_view(&canonical)
                        .unwrap();
                    assert_eq!(
                        view.wc_commit_ids
                            .get(jj_lib::ref_name::WorkspaceName::new(expected_key)),
                        Some(&target)
                    );
                    assert_eq!(
                        view.wc_commit_ids.keys().any(|name| name.as_str() == own),
                        own_alias
                    );
                }
            }
        }
    }
}

/// A new native child can still name an old parent while its canonical image is root.
/// Trimming the parent changes membership, not the ownership of names in that child's view.
#[test]
fn a_fresh_child_of_trimmed_parents_keeps_its_source_namespace() {
    use musubi_jj::records::{HubOp, Record, RecordPrefix};
    use pollster::FutureExt as _;

    for cold in [false, true] {
        let env = TestEnv::new();
        let a = env.init_repo("alpha");
        let b = env.init_repo("beta");
        let mut node = open(&a);
        let mut other = open(&b);
        let first = single_canonical_head(&mut node);
        sync(&node, &mut other, &first);
        let joined = single_canonical_head(&mut other);
        sync(&other, &mut node, &joined);
        let basis = node.local_heads().unwrap().pop().unwrap();
        let base = node.canonicalize(&basis).unwrap();
        let foreign = node
            .machine_workspaces()
            .unwrap()
            .into_iter()
            .map(|(name, _)| name)
            .find(|name| name.contains('/'))
            .unwrap();
        let drops = node
            .canonical_store()
            .ancestors_until(&[base], |_| false)
            .unwrap();
        node.prepare_records(
            &RecordPrefix::none(),
            &[Record::new(drops.into_iter().map(HubOp))],
        )
        .unwrap();
        node.crash_taking_records(false);
        let root = node.canonical_store().root_operation_id().clone();
        node.advance_to(std::slice::from_ref(&root)).unwrap_err();
        drop(node);
        // No physical op abandon: the native command still inherits the old namespace.
        a.jj(&["--ignore-working-copy", "describe", "-m", "fresh child"]);
        if cold {
            std::fs::remove_file(a.repo_path().join("musubi/translation")).unwrap();
        }
        node = open(&a);
        let child = node.local_heads().unwrap().pop().unwrap();
        let raw = node
            .loader()
            .op_store()
            .read_operation(&child.0)
            .block_on()
            .unwrap();
        assert_eq!(raw.parents, vec![basis.0.clone()]);
        let head = node.canonicalize(&child).unwrap();
        let op = node.canonical_store().read_operation(&head).unwrap();
        assert_eq!(op.parents, vec![root.0]);
        let view = node.canonical_store().read_operation_view(&head).unwrap();
        assert!(
            !view
                .wc_commit_ids
                .keys()
                .any(|key| { key.as_str() == format!("{}/{}", node.machine().key(), foreign) }),
            "a foreign alias must not become this machine's workspace: {:?}",
            view.wc_commit_ids
        );
        assert!(
            view.wc_commit_ids
                .keys()
                .all(|key| { key.as_str() == format!("{}/alpha", node.machine().key()) })
        );
        assert_eq!(view.wc_commit_ids.len(), 1);
    }
}

/// A root from private history is not an orphan whose ownership needs recovering.
#[test]
fn a_private_root_workspace_is_not_a_lost_shared_source() {
    use musubi_jj::records::{HubOp, Record, RecordPrefix};
    use pollster::FutureExt as _;

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let node = open(&repo);
    let root = node.loader().op_store().root_operation_id().hex();
    drop(node);
    repo.jj(&[
        "--at-op",
        &root,
        "workspace",
        "add",
        "--name",
        "own/slash",
        env.root().join("private-workspace").to_str().unwrap(),
    ]);
    let mut node = open(&repo);
    let mut ancestry = node.local_heads().unwrap();
    let mut seen = BTreeSet::new();
    let private = loop {
        let head = ancestry.pop().expect("a root operation creates own/slash");
        if !seen.insert(head.clone()) {
            continue;
        }
        let op = node
            .loader()
            .op_store()
            .read_operation(&head.0)
            .block_on()
            .unwrap();
        if op.parents == [node.loader().op_store().root_operation_id().clone()] {
            let view = node
                .loader()
                .op_store()
                .read_view(&op.view_id)
                .block_on()
                .unwrap();
            if view
                .wc_commit_ids
                .contains_key(jj_lib::ref_name::WorkspaceName::new("own/slash"))
            {
                break head;
            }
        }
        ancestry.extend(op.parents.into_iter().map(LocalOp));
    };
    let operation = node
        .loader()
        .op_store()
        .read_operation(&private.0)
        .block_on()
        .unwrap();
    assert_eq!(
        operation.parents,
        vec![node.loader().op_store().root_operation_id().clone()]
    );
    let view = node
        .loader()
        .op_store()
        .read_view(&operation.view_id)
        .block_on()
        .unwrap();
    let commit = view.wc_commit_ids[jj_lib::ref_name::WorkspaceName::new("own/slash")].hex();
    let joined = node.create_join_operation("musubi: alpha joins").unwrap();
    let join_point = node.local_of(&joined).unwrap();
    repo.jj(&["describe", "-m", "shared survivor"]);
    let shared = node.canonical_heads().unwrap();
    let dropped = node
        .canonical_store()
        .ancestors_until(&shared, |_| false)
        .unwrap();
    let root = node.canonical_store().root_operation_id().clone();
    node.prepare_records(
        &RecordPrefix::none(),
        &[Record::new(dropped.into_iter().map(HubOp))],
    )
    .unwrap();
    node.advance_to(&[root]).unwrap();
    drop(node);
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &join_point.0.hex(),
        "describe",
        "-r",
        &commit,
        "-m",
        "delayed shared",
    ]);
    let before = open(&repo).local_heads().unwrap();
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &private.0.hex(),
        "describe",
        "-r",
        &commit,
        "-m",
        "delayed private",
    ]);
    let mut node = open(&repo);
    let delayed = node
        .local_heads()
        .unwrap()
        .into_iter()
        .find(|head| !before.contains(head))
        .unwrap();
    drop(node);
    std::fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
    node = open(&repo);
    let error = node.canonicalize(&delayed).unwrap_err();
    assert!(
        matches!(error, musubi_jj::node::NodeError::BeforeJoin(_)),
        "{error}"
    );
    assert!(node.pending_drops().is_empty());
}

/// A record can name a different version of a merge this copy already dropped.
#[test]
fn another_version_of_a_dropped_merge_does_not_drop_its_parents() {
    use musubi_jj::canonical::Contraction;
    use musubi_jj::records::{HubOp, Record, RecordPrefix};

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = open(&repo);
    let base = node.local_heads().unwrap().pop().unwrap();
    node.canonicalize(&base).unwrap();
    for name in ["left", "right"] {
        repo.jj(&[
            "--ignore-working-copy",
            "--at-op",
            &base.0.hex(),
            "new",
            "--no-edit",
            "-m",
            name,
        ]);
    }
    let merge = node.merge_heads().unwrap();
    let merge = node.canonicalize(&merge).unwrap();
    let parents = node.canonical_store().parents(&merge).unwrap();
    assert_eq!(parents.len(), 2);
    repo.jj(&["bookmark", "create", "survivor", "-r", "root()"]);
    node.canonical_heads().unwrap();
    let mut contraction = Contraction::new(node.canonical_store(), [parents[1].clone()]).unwrap();
    let alternate = contraction.images(node.canonical_store(), &merge).unwrap()[0].clone();
    node.adopt_records(&RecordPrefix::none(), &[Record::new([HubOp(merge)])])
        .unwrap();
    // A peer joined after the parent's drop was pruned, then the hub was made again:
    // it can publish this version's drop without the record that produced the version.
    node.adopt_records(&RecordPrefix::none(), &[Record::new([HubOp(alternate)])])
        .unwrap();
    assert_eq!(
        node.current(&parents[0]).unwrap(),
        vec![musubi_jj::node::NodeOp(parents[0].clone())]
    );
}

/// A dropped operation's one surviving parent is not another name for that operation.
#[test]
fn a_pending_drop_is_not_named_as_an_already_dropped_child() {
    use musubi_jj::records::{HubOp, Record, RecordPrefix};

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = open(&repo);
    let start = node.local_heads().unwrap().pop().unwrap();
    node.canonicalize(&start).unwrap();
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &start.0.hex(),
        "describe",
        "-m",
        "parent",
    ]);
    let local_parent = node.local_heads().unwrap().pop().unwrap();
    let parent = node.canonicalize(&local_parent).unwrap();
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &local_parent.0.hex(),
        "describe",
        "-m",
        "child",
    ]);
    let local_child = node.local_heads().unwrap().pop().unwrap();
    let child = node.canonicalize(&local_child).unwrap();
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &start.0.hex(),
        "describe",
        "-m",
        "sibling",
    ]);
    let local_sibling = node
        .local_heads()
        .unwrap()
        .into_iter()
        .find(|head| *head != local_child)
        .unwrap();
    let sibling = node.canonicalize(&local_sibling).unwrap();
    assert_eq!(
        node.canonical_store().generation(&parent).unwrap(),
        node.canonical_store().generation(&sibling).unwrap()
    );
    node.merge_heads().unwrap();
    repo.jj(&["bookmark", "create", "survivor", "-r", "root()"]);
    let base = node.canonical_heads().unwrap().pop().unwrap();
    node.adopt_records(&RecordPrefix::none(), &[Record::new([HubOp(child)])])
        .unwrap();
    // An existing sibling drop sets the reverse-name walk's floor at the parent:
    // it visits the dropped child but stops before visiting the parent itself.
    repo.jj(&["op", "abandon", &local_sibling.0.hex()]);
    assert!(node.notice_abandon(&HubOp(base.clone())).unwrap());
    assert_eq!(node.pending_drops(), &Record::new([HubOp(sibling.clone())]));
    let current = node.current(&parent).unwrap().pop().unwrap();
    let local_parent = node.local_of(&current.0).unwrap();
    repo.jj(&["op", "abandon", &local_parent.0.hex()]);
    assert!(node.notice_abandon(&HubOp(base)).unwrap());
    assert_eq!(
        node.pending_drops(),
        &Record::new([HubOp(sibling), HubOp(parent)])
    );
}

/// Losing a prepared record leaves its drop pending, even while taking another record.
#[test]
fn a_lost_receipt_keeps_the_dropped_original_pending() {
    use musubi_jj::records::{HubOp, Record, RecordPrefix};

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = open(&repo);
    repo.jj(&["describe", "-m", "prepared drop"]);
    let a = node.canonical_heads().unwrap().pop().unwrap();
    repo.jj(&["describe", "-m", "incoming drop"]);
    let b = node.canonical_heads().unwrap().pop().unwrap();
    repo.jj(&["describe", "-m", "survives both drops"]);
    node.canonical_heads().unwrap();
    let lost = Record::new([HubOp(a)]);
    node.prepare_records(&RecordPrefix::none(), std::slice::from_ref(&lost))
        .unwrap();
    assert!(node.has_record_custody());
    assert!(node.applied_records().is_empty());
    let incoming = Record::new([HubOp(b)]);
    node.adopt_records(&RecordPrefix::none(), std::slice::from_ref(&incoming))
        .unwrap();
    assert_eq!(node.pending_drops(), &lost);
    node.adopt_records(&RecordPrefix::none(), &[incoming, lost])
        .unwrap();
    assert!(node.pending_drops().is_empty());
}

#[test]
fn taking_an_abandon_preserves_original_identity_after_cache_loss() {
    use musubi_jj::canonical::Contraction;
    use musubi_jj::records::{HubOp, Record, RecordPrefix};

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    repo.jj(&["describe", "-m", "unchanged ancestor"]);
    repo.jj(&["describe", "-m", "unchanged prefix"]);
    let (a_local, between, x_local) = repeated_restore_ops(&repo);
    let mut node = open(&repo);
    let a = node.canonicalize(&a_local).unwrap();
    let between = node.canonicalize(&between).unwrap();
    let x = node.canonicalize(&x_local).unwrap();
    let mut contraction =
        Contraction::new(node.canonical_store(), [a.clone(), between.clone()]).unwrap();
    let expected = contraction.images(node.canonical_store(), &x).unwrap()[0].clone();
    node.crash_taking_records(false);
    node.adopt_records(
        &RecordPrefix::none(),
        &[Record::new([HubOp(a), HubOp(between)])],
    )
    .unwrap_err();
    drop(node);
    std::fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
    let mut node = open(&repo);
    node.check_abandon().unwrap();
    let head = node.local_heads().unwrap().pop().unwrap();
    assert_ne!(
        head, a_local,
        "the survivor must not coalesce into the dropped local id"
    );
    assert_eq!(node.canonicalize(&head).unwrap(), expected);
    let mut pending = vec![head.clone()];
    let mut seen = BTreeSet::new();
    while let Some(local) = pending.pop() {
        if !seen.insert(local.clone()) {
            continue;
        }
        assert!(
            node.canonical_of(&local).is_some(),
            "recovery identities must not hide unmapped ancestors"
        );
        let op =
            futures::executor::block_on(node.loader().op_store().read_operation(&local.0)).unwrap();
        pending.extend(op.parents.into_iter().map(LocalOp));
    }

    // A command that loaded the old history is canonicalized on the renamed parents and
    // then reparented locally by reparent_late, a second path that needs the durable marker.
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &x_local.0.hex(),
        "new",
        "-m",
        "late work",
    ]);
    node.canonical_heads().unwrap();
    let heads: Vec<_> = node
        .local_heads()
        .unwrap()
        .into_iter()
        .map(|head| {
            let canonical = node.canonicalize(&head).unwrap();
            (head, canonical)
        })
        .collect();
    drop(node);
    std::fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
    let mut node = open(&repo);
    for (local, canonical) in heads {
        assert_eq!(node.canonicalize(&local).unwrap(), canonical);
    }
}

#[test]
fn coalesced_history_after_gc_is_refused_before_publishing_drops() {
    use musubi_jj::records::HubOp;

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let (a, _, x) = repeated_restore_ops(&repo);
    let mut node = open(&repo);
    let base = node.canonicalize(&x).unwrap();
    repo.jj(&[
        "--ignore-working-copy",
        "op",
        "abandon",
        &format!("{}-..{}-", a.0.hex(), x.0.hex()),
    ]);
    repo.jj(&["--ignore-working-copy", "util", "gc", "--expire", "now"]);
    assert!(
        !repo
            .repo_path()
            .join("op_store/operations")
            .join(x.0.hex())
            .exists()
    );
    repo.jj(&["--ignore-working-copy", "describe", "-m", "after gc"]);
    let err = node.notice_abandon(&HubOp(base)).unwrap_err();
    assert!(
        matches!(err, musubi_jj::node::NodeError::UnreachableHistory),
        "{err}"
    );
    assert!(node.pending_drops().is_empty());
}

#[test]
fn a_delayed_child_of_a_jj_rewrite_keeps_its_origin_after_cache_loss() {
    use musubi_jj::records::HubOp;

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let op_head = || {
        repo.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-n1",
            "-T",
            "id",
        ])
    };
    repo.jj(&["describe", "-m", "first"]);
    let first = op_head();
    repo.jj(&["describe", "-m", "middle"]);
    let middle = LocalOp(jj_lib::op_store::OperationId::try_from_hex(op_head().trim()).unwrap());
    repo.jj(&["describe", "-m", "last"]);
    let last = LocalOp(jj_lib::op_store::OperationId::try_from_hex(op_head().trim()).unwrap());
    let mut node = open(&repo);
    let base = node.canonicalize(&last).unwrap();
    let original = node.canonicalize(&middle).unwrap();
    repo.jj(&["--ignore-working-copy", "op", "abandon", first.trim()]);
    let log = repo.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n2",
        "-T",
        "id ++ \"\\n\"",
    ]);
    let source =
        LocalOp(jj_lib::op_store::OperationId::try_from_hex(log.lines().nth(1).unwrap()).unwrap());
    let raw_head =
        LocalOp(jj_lib::op_store::OperationId::try_from_hex(log.lines().next().unwrap()).unwrap());
    assert_ne!(source, middle);
    assert!(node.notice_abandon(&HubOp(base.clone())).unwrap());
    let expected = node.current(&original).unwrap()[0].0.clone();
    let expected_head = node.current(&base).unwrap()[0].0.clone();
    drop(node);
    std::fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
    // A power cut can retain the counted step while losing the head move and final
    // moving=false write. Source aliases must not hide that unfinished physical move.
    let heads = repo.repo_path().join("op_heads/heads");
    for head in std::fs::read_dir(&heads).unwrap() {
        std::fs::remove_file(head.unwrap().path()).unwrap();
    }
    std::fs::write(heads.join(raw_head.0.hex()), "").unwrap();
    let records = repo.repo_path().join("musubi/records.json");
    let mut state: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&records).unwrap()).unwrap();
    state["moving"] = true.into();
    std::fs::write(&records, serde_json::to_vec(&state).unwrap()).unwrap();
    let mut node = open(&repo);
    assert!(node.notice_abandon(&HubOp(base)).unwrap());
    assert!(!node.local_heads().unwrap().contains(&raw_head));
    assert_eq!(node.canonical_heads().unwrap(), vec![expected_head]);
    drop(node);
    std::fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
    // A command loaded the unmarked source before the sync, and publishes after restart.
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &source.0.hex(),
        "new",
        "-m",
        "delayed",
    ]);
    let mut node = open(&repo);
    assert_eq!(node.canonicalize(&source).unwrap(), expected);
    let raw =
        futures::executor::block_on(node.loader().op_store().read_operation(&source.0)).unwrap();
    for parent in raw.parents {
        let parent = LocalOp(parent);
        assert!(
            node.canonical_of(&parent).is_some(),
            "a source alias must not hide an unmapped parent"
        );
    }
    node.canonical_heads().unwrap();
    assert_ne!(
        node.local_of(&expected),
        Some(source.clone()),
        "an alias is not the preferred realization"
    );
    // A second delayed command sees the cached alias, without another cache loss.
    repo.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &source.0.hex(),
        "new",
        "-m",
        "delayed again",
    ]);
    node.canonical_heads().unwrap();
    let mut pending = node.local_heads().unwrap();
    let mut reachable = BTreeSet::new();
    while let Some(local) = pending.pop() {
        if !reachable.insert(local.clone()) {
            continue;
        }
        let op =
            futures::executor::block_on(node.loader().op_store().read_operation(&local.0)).unwrap();
        pending.extend(op.parents.into_iter().map(LocalOp));
    }
    assert!(
        !reachable.contains(&source),
        "a warm-cache command must use the normalized source"
    );
}

fn open(repo: &TestRepo) -> NodeRepo {
    NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap()
}

#[test]
fn fresh_equal_time_operation_is_not_an_old_counterpart() {
    use musubi_jj::node::NodeError;
    use musubi_jj::records::HubOp;
    use pollster::FutureExt as _;

    for (collect, lose_evidence) in [(false, false), (true, false), (true, true)] {
        let env = TestEnv::new();
        let repo = env.init_repo("alpha");
        let op_head = || {
            let hex = repo.jj(&[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-n1",
                "-T",
                "id",
            ]);
            LocalOp(jj_lib::op_store::OperationId::try_from_hex(hex.trim()).unwrap())
        };
        let new_at_same_time = |message: &str| {
            let output = repo
                .program(Path::new("jj"))
                .args(["--ignore-working-copy", "new", "-m", message])
                .env("JJ_OP_TIMESTAMP", "2001-02-03T04:05:06Z")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            op_head()
        };
        repo.jj(&["describe", "-m", "published ancestor"]);
        let p = op_head();
        let a = new_at_same_time("published old view");
        let mut node = open(&repo);
        let base = node.canonicalize(&a).unwrap();
        let x = new_at_same_time("unpublished new view");
        let x_op = node
            .loader()
            .op_store()
            .read_operation(&x.0)
            .block_on()
            .unwrap();
        let x_view = node
            .loader()
            .op_store()
            .read_view(&x_op.view_id)
            .block_on()
            .unwrap();
        let expected = x_view.wc_commit_ids.values().next().unwrap().clone();
        repo.jj(&[
            "--ignore-working-copy",
            "op",
            "abandon",
            &format!("{}-..{}-", p.0.hex(), x.0.hex()),
        ]);
        if collect {
            repo.jj(&["--ignore-working-copy", "util", "gc", "--expire", "now"]);
            assert!(
                !repo
                    .repo_path()
                    .join("op_store/operations")
                    .join(a.0.hex())
                    .exists()
            );
        }
        drop(node);
        std::fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
        if lose_evidence {
            std::fs::remove_file(repo.repo_path().join("musubi/originals")).unwrap();
        }
        let mut node = open(&repo);
        if lose_evidence {
            assert!(matches!(
                node.notice_abandon(&HubOp(base)),
                Err(NodeError::UnreachableHistory)
            ));
            assert!(node.pending_drops().is_empty());
            continue;
        }
        assert!(node.notice_abandon(&HubOp(base)).unwrap());
        let heads = node.canonical_heads().unwrap();
        assert_eq!(heads.len(), 1);
        let replicated = node
            .canonical_store()
            .read_operation_view(&heads[0])
            .unwrap();
        assert!(
            replicated.wc_commit_ids.values().any(|id| *id == expected),
            "the fresh operation's working-copy commit {expected:?} was omitted: {replicated:?}"
        );
    }
}

/// Ships the objects that the canonical operations reachable from `head` require and `to`
/// lacks, as a pack plus extras entries.
fn ship_objects(from: &NodeRepo, to: &NodeRepo, head: &CanonicalOp) {
    let mut wants = BTreeSet::new();
    let mut stack = vec![head.clone()];
    let mut seen = BTreeSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id.clone()) || id == *from.canonical_store().root_operation_id() {
            continue;
        }
        wants.extend(from.required_commits(std::slice::from_ref(&id)).unwrap());
        stack.extend(CanonicalOp::parents_of(
            &from.canonical_store().read_operation(&id).unwrap(),
        ));
    }
    let wants: Vec<_> = wants.into_iter().collect();
    let to_store = to.object_store().unwrap();
    let missing = to_store.missing(&wants).unwrap();
    let haves: Vec<_> = wants
        .iter()
        .filter(|id| !missing.contains(id))
        .cloned()
        .collect();
    let bundle = tempfile::NamedTempFile::new().unwrap();
    from.object_store()
        .unwrap()
        .export(&missing, &haves, bundle.path())
        .unwrap();
    to_store.import(bundle.path(), &missing, &haves).unwrap();
    drop(to_store);
}

/// Ships objects and canonical operations, then makes `head` an op head of `to`.
fn sync(from: &NodeRepo, to: &mut NodeRepo, head: &CanonicalOp) {
    ship_objects(from, to, head);
    ship_operations(from, to, head);
    to.advance(head).unwrap();
}

/// Copies the canonical operations reachable from `head` that `to` lacks, as a bundle.
fn ship_operations(from: &NodeRepo, to: &NodeRepo, head: &CanonicalOp) {
    let (src, dst) = (from.canonical_store(), to.canonical_store());
    let ops = src
        .ancestors_until(std::slice::from_ref(head), |id| dst.has_operation(id))
        .unwrap();
    let bundle = tempfile::NamedTempFile::new().unwrap();
    src.export_operations(&ops, bundle.path()).unwrap();
    let imported: Vec<CanonicalOp> = dst
        .import_operations(bundle.path())
        .unwrap()
        .into_iter()
        .map(|(id, _)| id)
        .collect();
    assert_eq!(imported, ops);
}

fn single_canonical_head(node: &mut NodeRepo) -> CanonicalOp {
    node.merge_heads().unwrap();
    let heads = node.canonical_heads().unwrap();
    assert_eq!(heads.len(), 1, "expected one head, got {heads:?}");
    heads.into_iter().next().unwrap()
}

/// Local bookmarks. (Remote bookmarks include the labels each machine shows for the
/// other machines' workspaces, which legitimately differ between machines.)
fn bookmarks(repo: &TestRepo) -> String {
    let template = r#"if(present && !remote, name ++ "@ " ++ normal_target.commit_id() ++ "\n")"#;
    repo.jj(&["bookmark", "list", "-T", template])
}

fn op_descriptions(repo: &TestRepo) -> BTreeSet<String> {
    repo.jj(&[
        "op",
        "log",
        "--no-graph",
        "-T",
        r#"description.first_line() ++ "\n""#,
    ])
    .lines()
    .map(str::to_owned)
    .collect()
}

fn commit(repo: &TestRepo, file: &str, message: &str) {
    repo.write_file(file, message);
    repo.jj(&["commit", "-m", message]);
}

#[test]
fn realized_bookmark_moves_survive_colocated_import() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    commit(&a, "one", "one");
    a.jj(&["bookmark", "create", "main", "-r", "@-"]);
    commit(&a, "two", "two");
    a.jj(&["bookmark", "move", "main", "--to", "@-"]);
    let main_on_a = a.git(&["rev-parse", "refs/heads/main"]);
    commit(&b, "b0", "b0");
    let b_head_before = b.git(&["rev-parse", "HEAD"]);

    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let a_head = single_canonical_head(&mut a_node);
    sync(&a_node, &mut b_node, &a_head);

    // B's next commands import git refs and merge B's own concurrent init operations with
    // the realization. Neither may move `main` back.
    assert_eq!(b.git(&["rev-parse", "refs/heads/main"]), main_on_a);
    let after_first = bookmarks(&b);
    b.jj(&["status"]);
    assert_eq!(bookmarks(&b), after_first);
    assert!(
        after_first.contains(&format!("main@ {}", main_on_a.trim())),
        "{after_first}"
    );
    assert_eq!(b.git(&["rev-parse", "HEAD"]), b_head_before);
    assert!(op_descriptions(&b).is_superset(&op_descriptions(&a)));
}

/// A received root-based history has no private binding to inherit from its parent.
/// Realizing it ahead of record receipt still preserves this copy's native namespace.
#[test]
fn root_realizations_keep_current_private_workspaces_without_a_receipt() {
    use musubi_jj::canonical::Contraction;
    use pollster::FutureExt as _;

    for change in [
        "unchanged",
        "rename",
        "delete",
        "owned alias",
        "rename after",
        "delete after",
        "cached child",
        "restart child",
        "multi child",
        "noncolocated child",
    ] {
        let env = TestEnv::new();
        let a = env.init_repo("alpha");
        let b = if change == "noncolocated child" {
            env.init_non_colocated_repo("beta")
        } else {
            env.init_repo("beta")
        };
        a.jj(&["workspace", "rename", "default"]);
        b.jj(&["workspace", "rename", "default"]);
        if change == "owned alias" {
            a.jj(&[
                "workspace",
                "add",
                "--name",
                "second",
                env.root().join("alpha-second").to_str().unwrap(),
            ]);
        }
        let mut a_node = open(&a);
        let mut b_node = open(&b);
        let initial = single_canonical_head(&mut a_node);
        sync(&a_node, &mut b_node, &initial);
        let joined = single_canonical_head(&mut b_node);
        sync(&b_node, &mut a_node, &joined);
        a_node.forget_copy(b_node.machine().key(), "beta").unwrap();
        a.jj(&["new", "--no-edit", "-m", "after forgetting beta"]);
        // Exporting this bookmark changes the published parent's Git record, while
        // children prepared before that export still have the root's empty record.
        a.jj(&["bookmark", "create", "kept", "-r", "@"]);
        let tip = single_canonical_head(&mut a_node);
        let child = if change.ends_with("child") {
            a.jj(&["bookmark", "create", "later", "-r", "@"]);
            single_canonical_head(&mut a_node);
            a.jj(&["bookmark", "create", "last", "-r", "@"]);
            Some(single_canonical_head(&mut a_node))
        } else {
            None
        };
        let store = a_node.canonical_store();
        let drops = store
            .ancestors_until(std::slice::from_ref(&tip), |_| false)
            .unwrap()
            .into_iter()
            .filter(|id| *id != tip)
            .collect::<Vec<_>>();
        let mut contraction = Contraction::new(store, drops).unwrap();
        let incoming = contraction.images(store, &tip).unwrap().pop().unwrap();
        assert_eq!(
            store.parents(&incoming).unwrap(),
            [store.root_operation_id().clone()]
        );
        let child = child.map(|id| contraction.images(store, &id).unwrap().pop().unwrap());
        let middle = child
            .as_ref()
            .map(|id| store.parents(id).unwrap()[0].clone());
        let last = child.as_ref().unwrap_or(&incoming);
        ship_objects(&a_node, &b_node, last);
        ship_operations(&a_node, &b_node, last);
        if let Some(child) = &child {
            b_node.realize(child).unwrap();
        }

        assert!(
            !b_node
                .presence(&incoming)
                .unwrap()
                .is_present(b_node.machine().key())
        );
        let original_heads = b_node.local_heads().unwrap();
        if change == "rename" {
            b.jj(&["workspace", "rename", "private"]);
        } else if change == "delete" {
            b.jj(&["workspace", "forget", "default"]);
        } else if change == "owned alias" {
            b.jj(&["workspace", "forget", "alpha/default"]);
            b.jj(&[
                "workspace",
                "add",
                "--name",
                "alpha/default",
                env.root().join("owned").to_str().unwrap(),
            ]);
        }
        let read_own = |node: &NodeRepo, local: &LocalOp| {
            let op = node
                .loader()
                .op_store()
                .read_operation(&local.0)
                .block_on()
                .unwrap();
            let view = node
                .loader()
                .op_store()
                .read_view(&op.view_id)
                .block_on()
                .unwrap();
            view.wc_commit_ids
                .iter()
                .filter(|(name, _)| {
                    !name.as_str().contains('/')
                        || name.as_str() == "alpha/default" && change == "owned alias"
                })
                .map(|(name, target)| (name.as_str().to_owned(), target.clone()))
                .collect::<BTreeMap<_, _>>()
        };
        let mut expected = read_own(&b_node, &b_node.local_heads().unwrap()[0]);
        let realized = b_node.realize(&incoming).unwrap();
        assert_eq!(read_own(&b_node, &realized), expected, "{change}");
        let raw = b_node
            .loader()
            .op_store()
            .read_operation(&realized.0)
            .block_on()
            .unwrap();
        if change == "owned alias" {
            let context: serde_json::Value = serde_json::from_str(
                raw.metadata
                    .attributes
                    .get("musubi.local-workspaces")
                    .expect("owned slash binding needs a private ownership witness"),
            )
            .unwrap();
            assert!(
                context["names"]
                    .as_object()
                    .unwrap()
                    .contains_key("alpha/default")
            );
        }
        if let Some(context) = raw.metadata.attributes.get("musubi.local-workspaces") {
            let context: serde_json::Value = serde_json::from_str(context).unwrap();
            assert!(
                context["names"]
                    .as_object()
                    .unwrap()
                    .keys()
                    .all(|name| expected.contains_key(name)),
                "foreign aliases became private: {change}"
            );
        }
        assert_eq!(b_node.canonicalize(&realized).unwrap(), incoming);
        if change == "unchanged" {
            assert_eq!(
                b_node.local_heads().unwrap(),
                original_heads,
                "realizing ahead publishes nothing"
            );
        }
        if change == "rename after" || change.ends_with("child") {
            b.jj(&["workspace", "rename", "private"]);
        } else if change == "delete after" {
            b.jj(&["workspace", "forget", "default"]);
        }
        if change.ends_with("after") || change.ends_with("child") {
            expected = read_own(&b_node, &b_node.local_heads().unwrap()[0]);
            if change == "multi child" {
                b_node
                    .advance_to(&[incoming.clone(), child.clone().unwrap()])
                    .unwrap();
            } else {
                b_node.advance(&incoming).unwrap();
                if let Some(child) = &child {
                    b.jj(&["bookmark", "create", "native", "-r", "root()"]);
                    if change == "restart child" {
                        drop(b_node);
                        b_node = open(&b);
                    }
                    b_node.advance(child).unwrap();
                }
            }
            for head in b_node.local_heads().unwrap() {
                assert_eq!(read_own(&b_node, &head), expected, "{change}");
            }
        }
        // A refreshed parent and a cached child may never publish two physical aliases
        // of the same canonical operation, including after reopening disposable caches.
        let mut pending = b_node.local_heads().unwrap();
        let mut native = BTreeSet::new();
        let mut counted = BTreeMap::new();
        while let Some(local) = pending.pop() {
            if !native.insert(local.clone()) {
                continue;
            }
            let op = b_node
                .loader()
                .op_store()
                .read_operation(&local.0)
                .block_on()
                .unwrap();
            pending.extend(LocalOp::parents_of(&op));
            if let Some(canonical) = b_node.canonical_of(&local) {
                assert!(
                    counted.insert(canonical, local).is_none(),
                    "duplicate realization: {change}"
                );
            }
        }
        if let Some(middle) = middle {
            let local = &counted[&middle];
            let op = b_node
                .loader()
                .op_store()
                .read_operation(&local.0)
                .block_on()
                .unwrap();
            let view = b_node
                .loader()
                .op_store()
                .read_view(&op.view_id)
                .block_on()
                .unwrap();
            assert_eq!(op.parents.len(), 1);
            let parent = b_node
                .loader()
                .op_store()
                .read_operation(&op.parents[0])
                .block_on()
                .unwrap();
            let parent_view = b_node
                .loader()
                .op_store()
                .read_view(&parent.view_id)
                .block_on()
                .unwrap();
            assert_eq!(
                view.git_heads, parent_view.git_heads,
                "inherited Git heads: {change}"
            );
            assert_eq!(
                view.git_refs, parent_view.git_refs,
                "inherited Git refs: {change}"
            );
            let git = jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
            assert_eq!(
                view.remote_views.get(git),
                parent_view.remote_views.get(git),
                "inherited Git remote: {change}"
            );
        }
    }
}

#[test]
fn canonicalizing_a_realization_returns_its_canonical_operation() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    commit(&a, "one", "one");

    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let a_head = single_canonical_head(&mut a_node);
    ship_objects(&a_node, &b_node, &a_head);
    ship_operations(&a_node, &b_node, &a_head);
    let local = b_node.advance(&a_head).unwrap();
    assert_eq!(b_node.canonicalize(&local).unwrap(), a_head);

    // A node that lost its translation cache recovers the same answer from the attribute.
    std::fs::remove_file(b.repo_path().join("musubi/translation")).unwrap();
    let mut fresh = open(&b);
    assert_eq!(fresh.canonicalize(&local).unwrap(), a_head);
    assert_ne!(
        local.0.hex(),
        a_head.0.hex(),
        "per-machine fields differ, so ids should too"
    );
}

/// Feed histories observed in the canonical store to the executable Lean model. Only
/// identity, parents and local operation membership are projected here: commit objects and
/// ref values have their own conformance tests.
fn model_history(
    oracle: &mut oracle::Oracle,
    node: &NodeRepo,
    machine: usize,
    heads: &[CanonicalOp],
    ids: &mut BTreeMap<CanonicalOp, u64>,
) -> Vec<u64> {
    let ops = node
        .canonical_store()
        .ancestors_until(heads, |op| ids.contains_key(op))
        .unwrap();
    ops.into_iter()
        .map(|op| {
            let parents: Vec<_> = node
                .canonical_store()
                .parents(&op)
                .unwrap()
                .iter()
                .map(|p| ids[p])
                .collect();
            let action = match parents.as_slice() {
                [parent] => {
                    json!({"kind": "userOp", "node": machine, "parent": parent, "objs": []})
                }
                _ => json!({"kind": "merge", "node": machine, "parents": parents, "objs": []}),
            };
            let state = oracle.step(&action).unwrap();
            let id = state["next"].as_u64().unwrap() - 1;
            ids.insert(op, id);
            id
        })
        .collect()
}

/// Dropping the ancestor too renames both survivors: unlike literal parents of the old head,
/// they pass left_beside, and the other realization is also among taken_beside's heads.
#[test]
fn prepared_advance_merges_each_survivor_once() {
    use musubi_jj::canonical::Contraction;
    use musubi_jj::records::{HubOp, Record, RecordPrefix};
    use pollster::FutureExt as _;

    let env = TestEnv::new();
    let repo = env.init_repo("beta");
    let mut node = open(&repo);
    let x = node.local_heads().unwrap().pop().unwrap();
    let canonical_x = node.canonicalize(&x).unwrap();
    for name in ["p", "q"] {
        repo.jj(&[
            "--ignore-working-copy",
            "--at-op",
            &x.0.hex(),
            "new",
            "--no-edit",
            "-m",
            name,
        ]);
    }
    assert_eq!(node.local_heads().unwrap().len(), 2);
    let merged = node.merge_heads().unwrap();
    let canonical = node.canonicalize(&merged).unwrap();
    let old_parents = node.canonical_store().parents(&canonical).unwrap();
    let drops = [canonical_x, canonical.clone()];
    let mut contraction = Contraction::new(node.canonical_store(), drops.clone()).unwrap();
    let survivors = contraction
        .images(node.canonical_store(), &canonical)
        .unwrap();
    let record = Record::new(drops.into_iter().map(HubOp));
    assert!(
        node.prepare_records(&RecordPrefix::none(), &[record])
            .unwrap()
    );
    assert_eq!(
        survivors.len(),
        2,
        "old parents: {old_parents:?}; survivors: {survivors:?}"
    );
    assert!(survivors.iter().all(|op| !old_parents.contains(op)));
    assert_eq!(node.local_heads().unwrap(), vec![merged]);
    node.advance_to(&survivors).unwrap();
    // No head-merging helper or jj command may hide the actual published parent list.
    let heads = node.local_heads().unwrap();
    assert_eq!(heads.len(), 1);
    let raw = node
        .loader()
        .op_store()
        .read_operation(&heads[0].0)
        .block_on()
        .unwrap();
    assert_eq!(
        raw.parents.len(),
        2,
        "each survivor must be merged exactly once"
    );
    let parents: BTreeSet<_> = raw
        .parents
        .into_iter()
        .map(|id| node.canonicalize(&LocalOp(id)).unwrap())
        .collect();
    assert_eq!(parents, survivors.into_iter().collect());
}

/// Unlike the core's fake, this observes the real op-head store before any jj command can
/// merge it after advance returns. Dropping a concurrent parent or losing an old operation
/// must disagree with the oracle's advance followed by merge. This observes the final graph,
/// not the interval between advance's own publication and working-copy cleanup.
#[test]
fn advance_with_concurrent_heads_refines_advance_then_merge() {
    use pollster::FutureExt as _;

    let mut oracle = oracle::Oracle::spawn();
    for colocated in [true, false] {
        oracle.reset(2);
        let env = TestEnv::new();
        let a = env.init_repo("alpha");
        let b = if colocated {
            env.init_repo("beta")
        } else {
            env.init_non_colocated_repo("beta")
        };
        a.jj(&["bookmark", "create", "incoming", "-r", "@"]);
        let incoming_ref = a.git(&["rev-parse", "refs/heads/incoming"]);
        let mut a_node = open(&a);
        let mut b_node = open(&b);
        let base = b_node.local_heads().unwrap().pop().unwrap();
        for name in ["left", "right"] {
            b.jj(&[
                "--ignore-working-copy",
                "--at-op",
                &base.0.hex(),
                "bookmark",
                "create",
                name,
                "-r",
                "@",
            ]);
        }
        let old_heads = b_node.canonical_heads().unwrap();
        assert_eq!(old_heads.len(), 2);
        let incoming = single_canonical_head(&mut a_node);
        let mut ids = BTreeMap::from([(a_node.canonical_store().root_operation_id().clone(), 0)]);
        let incoming_ops = model_history(
            &mut oracle,
            &a_node,
            0,
            std::slice::from_ref(&incoming),
            &mut ids,
        );
        model_history(&mut oracle, &b_node, 1, &old_heads, &mut ids);
        let remote = ids[&incoming];
        oracle
            .step(&json!({"kind": "pushAll", "node": 0, "ops": incoming_ops,
            "objs": [], "expected": 0, "new": remote}))
            .unwrap();
        oracle
            .step(
                &json!({"kind": "hubPushAccept", "node": 0, "ops": incoming_ops,
            "objs": [], "expected": 0, "new": remote}),
            )
            .unwrap();
        oracle
            .step(&json!({"kind": "learn", "node": 1, "headKind": "notify",
            "seq": 1, "head": remote}))
            .unwrap();
        oracle
            .step(&json!({"kind": "fetchOps", "node": 1, "ops": incoming_ops}))
            .unwrap();
        oracle
            .step(&json!({"kind": "hubGetOps", "node": 1, "ops": incoming_ops}))
            .unwrap();
        oracle
            .step(&json!({"kind": "recvOps", "node": 1, "ops": incoming_ops}))
            .unwrap();
        ship_objects(&a_node, &b_node, &incoming);
        ship_operations(&a_node, &b_node, &incoming);
        b_node.realize(&incoming).unwrap();
        for op in &incoming_ops {
            oracle
                .step(&json!({"kind": "realize", "node": 1, "opId": op}))
                .unwrap();
        }
        let advanced = oracle.step(&json!({"kind": "advance", "node": 1})).unwrap();
        let before = ids.len();
        let realization = b_node.advance(&incoming).unwrap();
        // Read raw heads and their parents before canonical_heads, merge_heads or a
        // subsequent jj command gets a chance to repair the returned state. The method's own
        // working-copy cleanup has already run; this is not an intermediate observer.
        let raw_heads = b_node.local_heads().unwrap();
        assert_eq!(raw_heads.len(), 1);
        assert_ne!(raw_heads[0], realization);
        assert_eq!(b_node.canonicalize(&realization).unwrap(), incoming);
        let raw = b_node
            .loader()
            .op_store()
            .read_operation(&raw_heads[0].0)
            .block_on()
            .unwrap();
        let actual_parents: BTreeSet<_> = raw
            .parents
            .into_iter()
            .map(|p| ids[&b_node.canonicalize(&LocalOp(p)).unwrap()])
            .collect();
        let expected_parents: BTreeSet<u64> =
            serde_json::from_value(advanced["nodes"][1]["heads"].clone()).unwrap();
        assert_eq!(actual_parents, expected_parents);
        let final_head = b_node.canonicalize(&raw_heads[0]).unwrap();
        let parents: Vec<_> = b_node
            .canonical_store()
            .parents(&final_head)
            .unwrap()
            .iter()
            .map(|op| ids[op])
            .collect();
        let state = oracle
            .step(&json!({"kind": "merge", "node": 1,
            "parents": parents, "objs": []}))
            .unwrap();
        let fresh = state["next"].as_u64().unwrap() - 1;
        ids.insert(final_head.clone(), fresh);
        assert_eq!(state["nodes"][1]["heads"], json!([fresh]));
        assert_eq!(ids.len(), before + 1);
        let retained: BTreeSet<_> = b_node
            .canonical_store()
            .ancestors_until(std::slice::from_ref(&final_head), |_| false)
            .unwrap()
            .iter()
            .map(|op| ids[op])
            .chain([0])
            .collect();
        let local: BTreeSet<u64> =
            serde_json::from_value(state["nodes"][1]["lops"].clone()).unwrap();
        assert_eq!(retained, local);
        assert_eq!(
            retained.len(),
            before + 1,
            "one merge, no realization feedback"
        );
        if colocated {
            assert_eq!(b.git(&["rev-parse", "refs/heads/incoming"]), incoming_ref);
            let merged = b_node
                .loader()
                .load_at(
                    &b_node
                        .loader()
                        .load_operation(&raw_heads[0].0)
                        .block_on()
                        .unwrap(),
                )
                .block_on()
                .unwrap();
            for name in ["left", "right"] {
                let target = merged
                    .view()
                    .get_local_bookmark(jj_lib::ref_name::RefName::new(name));
                assert_eq!(
                    b.git(&["rev-parse", &format!("refs/heads/{name}")]).trim(),
                    target.as_normal().unwrap().hex()
                );
            }
        }
    }
}

#[test]
fn concurrent_work_merges_and_round_trips() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    commit(&a, "base", "base");
    a.jj(&["bookmark", "create", "main", "-r", "@-"]);

    // B adopts A's state.
    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let a_head = single_canonical_head(&mut a_node);
    sync(&a_node, &mut b_node, &a_head);

    // Both work concurrently: A adds a commit on main, B adds a different bookmark.
    commit(&a, "a-file", "from alpha");
    a.jj(&["bookmark", "move", "main", "--to", "@-"]);
    b.jj(&["new", "main"]);
    commit(&b, "b-file", "from beta");
    b.jj(&["bookmark", "create", "side", "-r", "@-"]);

    let a_head = single_canonical_head(&mut a_node);
    sync(&a_node, &mut b_node, &a_head);
    let b_head = single_canonical_head(&mut b_node);

    sync(&b_node, &mut a_node, &b_head);

    let a_bookmarks = bookmarks(&a);
    assert_eq!(a_bookmarks, bookmarks(&b));
    assert!(a_bookmarks.contains("side@ "), "{a_bookmarks}");
    for repo in [&a, &b] {
        let log = repo.jj(&["log", "-r", "all()", "--no-graph", "-T", r#"description"#]);
        assert!(
            log.contains("from alpha") && log.contains("from beta"),
            "{log}"
        );
    }
}

/// The hazard translation exists for: replicating an operation verbatim, with the source
/// machine's record of its git refs, makes the destination's next colocated import move the
/// bookmark back. If this ever stops failing, jj has changed how it imports refs and the
/// design should be revisited.
#[test]
fn verbatim_replication_reverts_bookmarks() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    commit(&a, "one", "one");
    a.jj(&["bookmark", "create", "main", "-r", "@-"]);
    // B starts from A's state, through musubi, so both record main = one.
    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let a_head = single_canonical_head(&mut a_node);
    sync(&a_node, &mut b_node, &a_head);
    b.jj(&["status"]);
    let main_before = b.git(&["rev-parse", "refs/heads/main"]);

    // A moves main; copy A's raw operation files to B and add A's head as an op head.
    commit(&a, "two", "two");
    a.jj(&["bookmark", "move", "main", "--to", "@-"]);
    let a_head = single_canonical_head(&mut a_node);
    ship_objects(&a_node, &b_node, &a_head);
    let copy_dir = |dir: &str| {
        for entry in std::fs::read_dir(a.repo_path().join("op_store").join(dir)).unwrap() {
            let entry = entry.unwrap();
            let dest = b
                .repo_path()
                .join("op_store")
                .join(dir)
                .join(entry.file_name());
            if !dest.exists() {
                std::fs::copy(entry.path(), dest).unwrap();
            }
        }
    };
    copy_dir("views");
    copy_dir("operations");
    for head in std::fs::read_dir(a.repo_path().join("op_heads/heads")).unwrap() {
        let name = head.unwrap().file_name();
        if name != "lock" {
            std::fs::write(b.repo_path().join("op_heads/heads").join(name), "").unwrap();
        }
    }
    let main_on_a = a.git(&["rev-parse", "refs/heads/main"]);
    assert_ne!(main_on_a, main_before);

    b.jj(&["status"]);
    let main_on_b = b.jj(&["log", "--no-graph", "-r", "main", "-T", "commit_id"]);
    assert_eq!(
        main_on_b.trim(),
        main_before.trim(),
        "jj kept A's move; translation may be unnecessary"
    );
}

/// A commit without a `change-id` header keeps its change id only in jj's extras table. The
/// receiver must get the same change id, not one derived from the commit id.
#[test]
fn change_ids_without_headers_survive_transfer() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    a.write_file("file", "contents");
    a.jj(&[
        "--config",
        "git.write-change-id-header=false",
        "commit",
        "-m",
        "headerless",
    ]);
    let template = r#"change_id ++ " " ++ commit_id ++ "\n""#;
    let on_a = a.jj(&[
        "log",
        "--no-graph",
        "-r",
        "description(substring:headerless)",
        "-T",
        template,
    ]);
    let commit_id = on_a.split_whitespace().nth(1).unwrap().to_owned();
    let raw = a.git(&["cat-file", "commit", &commit_id]);
    assert!(!raw.contains("change-id"), "{raw}");

    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let a_head = single_canonical_head(&mut a_node);
    sync(&a_node, &mut b_node, &a_head);
    let on_b = b.jj(&["log", "--no-graph", "-r", &commit_id, "-T", template]);
    assert_eq!(on_b, on_a);
}

/// Extras jj can't take, as a buggy or hostile peer can send, are refused with their bundle:
/// for a commit id of another length than a git commit's, which a node's table of extras would
/// panic on, and a hub would name a file after; or that jj would panic on as it reads the
/// commit: not its encoding, or with a change id of another length or an even number of terms
/// of the root tree. Extras jj writes are taken: with a change id, or none, and with a root tree
/// of any odd number of terms, as jj wrote for a conflict before the `jj:trees` header.
#[test]
fn malformed_extras_are_refused() {
    let env = TestEnv::new();
    let node = open(&env.init_repo("alpha"));
    let (git, hub_git, hub_extras) = (
        Path::new("git"),
        env.root().join("hub/git"),
        env.root().join("hub/extras"),
    );
    GitObjects::init_bare(git, &hub_git, GitHash::Sha1).unwrap();
    std::fs::create_dir_all(&hub_extras).unwrap();
    let hub = GitStore::for_hub(git, &hub_git, &hub_extras);
    assert_eq!(node.loader().store().change_id_length(), CHANGE_ID_LENGTH);
    let stores: [Box<dyn ObjectStore + '_>; 2] = [node.object_store().unwrap(), Box::new(hub)];
    let extras = |change_id: usize, terms: usize| {
        CommitExtras {
            change_id: vec![1; change_id],
            root_tree: vec![vec![1; 20]; terms],
            uses_tree_conflict_format: true,
            ..Default::default()
        }
        .encode_to_vec()
    };
    let bundle = |n: usize, len: usize, value: &[u8]| {
        let bundle = env.root().join(format!("extras-{n}"));
        let mut writer = BundleWriter::create(&bundle).unwrap();
        writer.extras(&vec![n as u8; len], value).unwrap();
        writer.finish().unwrap();
        bundle
    };
    let bad_ids = [1, 32].map(|len| (len, extras(16, 0)));
    let bad_values = [b"\xff".to_vec(), extras(15, 0), extras(16, 2)].map(|value| (20, value));
    for (n, (len, value)) in bad_ids.into_iter().chain(bad_values).enumerate() {
        let bundle = bundle(n, len, &value);
        for store in &stores {
            let err = store.import(&bundle, &[], &[]).unwrap_err();
            if len == 20 {
                assert!(
                    matches!(err, ObjectError::MalformedExtras(_)),
                    "{n}: {err:?}"
                );
            } else {
                assert!(
                    matches!(err, ObjectError::MalformedBundle(_)),
                    "{n}: {err:?}"
                );
            }
        }
    }
    assert_eq!(std::fs::read_dir(&hub_extras).unwrap().count(), 0);
    let good = [extras(16, 0), extras(0, 0), extras(16, 1), extras(16, 3)];
    for (n, value) in good.iter().enumerate() {
        let bundle = bundle(100 + n, 20, value);
        for store in &stores {
            store.import(&bundle, &[], &[]).unwrap();
        }
    }
    assert_eq!(std::fs::read_dir(&hub_extras).unwrap().count(), good.len());
}

/// After the translation cache is lost, realizing a descendant must reuse the existing
/// realization of its parent instead of realizing the parent a second time.
#[test]
fn lost_cache_does_not_duplicate_realizations() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    commit(&a, "one", "one");
    // A bookmark makes the published realization (after exporting refs) differ from the
    // deterministic one, which is what a duplicate realization would reproduce.
    a.jj(&["bookmark", "create", "main", "-r", "@-"]);
    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let first = single_canonical_head(&mut a_node);
    sync(&a_node, &mut b_node, &first);
    let first_local = b_node.local_of(&first).unwrap();

    commit(&a, "two", "two");
    let second = single_canonical_head(&mut a_node);
    std::fs::remove_file(b.repo_path().join("musubi/translation")).unwrap();
    let mut b_node = open(&b);
    ship_objects(&a_node, &b_node, &second);
    ship_operations(&a_node, &b_node, &second);
    let second_local = b_node.advance(&second).unwrap();
    // Exactly one local operation reachable from the new head represents `first`: the
    // realization that existed before the cache was lost.
    let op_store = b_node.loader().op_store().clone();
    let mut representing_first = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![second_local];
    while let Some(id) = stack.pop() {
        if !seen.insert(id.clone()) || id.0 == *op_store.root_operation_id() {
            continue;
        }
        if b_node.canonicalize(&id).unwrap() == first {
            representing_first.insert(id.clone());
        }
        stack.extend(LocalOp::parents_of(
            &pollster::block_on(op_store.read_operation(&id.0)).unwrap(),
        ));
    }
    assert_eq!(representing_first, BTreeSet::from([first_local]));
    b.jj(&["status"]);
}

/// A crash while realized operations are still being written leaves them unrecorded, some
/// written in full and some only as far as their views. After the restart they are realized
/// again, as the same operations, and each canonical operation once.
#[test]
fn crash_with_writes_in_flight() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    for i in 0..4 {
        commit(&a, &format!("f{i}"), &format!("in flight {i}"));
    }
    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let head = single_canonical_head(&mut a_node);
    ship_objects(&a_node, &b_node, &head);
    ship_operations(&a_node, &b_node, &head);
    b_node.realize_pending(&head, &[]).unwrap();
    let in_flight = b_node.crash_before_settling();
    assert!(in_flight.len() >= 4, "{in_flight:?}");
    // Every other one stopped between its view and itself.
    let operations = b.repo_path().join("op_store/operations");
    for local in in_flight.iter().step_by(2) {
        std::fs::remove_file(operations.join(local.0.hex())).unwrap();
    }
    drop(b_node);

    let mut b_node = open(&b);
    let head_local = b_node.advance(&head).unwrap();
    let op_store = b_node.loader().op_store().clone();
    let mut realizations: BTreeMap<CanonicalOp, BTreeSet<LocalOp>> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![head_local];
    while let Some(id) = stack.pop() {
        if !seen.insert(id.clone()) || id.0 == *op_store.root_operation_id() {
            continue;
        }
        let canonical = b_node.canonicalize(&id).unwrap();
        realizations
            .entry(canonical)
            .or_default()
            .insert(id.clone());
        stack.extend(LocalOp::parents_of(
            &pollster::block_on(op_store.read_operation(&id.0)).unwrap(),
        ));
    }
    for local in &in_flight {
        let canonical = b_node.canonicalize(local).unwrap();
        assert_eq!(realizations[&canonical], BTreeSet::from([local.clone()]));
    }
    b.jj(&["status"]);
}

/// A failed view or operation write invalidates its whole unpublished batch, including
/// successful children whose parent never made it to the store. Both a retry on the same
/// handle and reopening must reproduce the healthy realizations, then publish closed history.
#[test]
fn failed_realization_writes_forget_the_batch() {
    let fixture = musubi_testutil::recorded(
        Path::new(env!("CARGO_TARGET_TMPDIR")),
        "realization-write-failure",
        |dir| {
            let env = TestEnv::new();
            let a = env.init_repo("alpha");
            let b = env.init_repo("beta");
            commit(&a, "f", "published");
            let mut a_node = open(&a);
            let mut b_node = open(&b);
            let first = single_canonical_head(&mut a_node);
            sync(&a_node, &mut b_node, &first);
            for i in 0..4 {
                a.jj(&["describe", "-m", &format!("unpublished {i}")]);
            }
            let head = single_canonical_head(&mut a_node);
            ship_objects(&a_node, &b_node, &head);
            ship_operations(&a_node, &b_node, &head);
            drop((a_node, b_node));
            env.save(dir);
        },
    );
    for (fail_view, reopen) in [(true, false), (false, false), (false, true)] {
        let env = TestEnv::restore(&fixture);
        let (a, b) = (env.repo_handle("alpha"), env.repo_handle("beta"));
        let head = single_canonical_head(&mut open(&a));
        let mut node = open(&b);
        let published = node.local_heads().unwrap();
        let published_canonical = node.canonical_heads().unwrap();
        let ops = node
            .canonical_store()
            .ancestors_until(std::slice::from_ref(&head), |id| {
                node.local_of(id).is_some()
            })
            .unwrap();
        assert_eq!(ops.len(), 4);

        // Get exact expected operations from the shipping path in a healthy copy, rather
        // than duplicating realization or its hashing. Leave one hinted view prepared.
        let control_path = env.root().join("control");
        musubi_testutil::copy_tree(b.path(), &control_path);
        let mut control = NodeRepo::open(&control_path.join(".jj/repo"), &b.settings()).unwrap();
        let expected: Vec<_> = ops
            .iter()
            .enumerate()
            .map(|(i, op)| control.realize_pending(op, &ops[i + 1..]).unwrap())
            .collect();
        control.settle().unwrap();
        let store = control.loader().op_store();
        let contents: Vec<_> = expected
            .iter()
            .map(|local| pollster::block_on(store.read_operation(&local.0)).unwrap())
            .collect();
        assert_eq!(contents[2].parents, vec![expected[1].0.clone()]);
        assert_ne!(contents[0].view_id, contents[1].view_id);
        assert_ne!(contents[2].view_id, contents[1].view_id);

        // A directory at one content-addressed destination makes jj's real tempfile
        // persistence fail, without preventing the other writers from completing. No
        // permissions, timing, production hooks, or replacement OpStore are involved.
        let (directory, id) = if fail_view {
            ("views", contents[1].view_id.hex())
        } else {
            ("operations", expected[1].0.hex())
        };
        let blocked = b.repo_path().join("op_store").join(directory).join(id);
        std::fs::create_dir(&blocked).unwrap();
        let translation_path = b.repo_path().join("musubi/translation");
        let before = std::fs::read(&translation_path).unwrap();
        for (i, op) in ops[..3].iter().enumerate() {
            assert_eq!(
                node.realize_pending(op, &ops[i + 1..]).unwrap(),
                expected[i]
            );
            assert_eq!(node.local_of(op), Some(expected[i].clone()));
        }
        assert_eq!(std::fs::read(&translation_path).unwrap(), before);
        let err = node.settle().unwrap_err();
        let musubi_jj::node::NodeError::OpStore(jj_lib::op_store::OpStoreError::WriteObject {
            object_type,
            source,
        }) = err
        else {
            panic!("unexpected write error: {err:?}");
        };
        assert_eq!(object_type, if fail_view { "view" } else { "operation" });
        assert!(source.to_string().contains(blocked.to_str().unwrap()));
        let store = node.loader().op_store();
        assert!(pollster::block_on(store.read_operation(&expected[1].0)).is_err());
        for i in [0, 2] {
            assert_eq!(
                pollster::block_on(store.read_operation(&expected[i].0)).unwrap(),
                contents[i]
            );
        }
        for (op, local) in ops[..3].iter().zip(&expected) {
            assert_eq!(node.local_of(op), None, "batch entry still mapped: {op:?}");
            assert_eq!(node.canonical_of(local), None);
        }
        assert_eq!(std::fs::read(&translation_path).unwrap(), before);
        assert_eq!(node.local_heads().unwrap(), published);
        assert_eq!(node.canonical_heads().unwrap(), published_canonical);
        // No outstanding writer or stale mapping can escape a second settle or Drop.
        node.settle().unwrap();
        if reopen {
            drop(node);
            node = open(&b);
            for op in &ops[..3] {
                assert_eq!(node.local_of(op), None);
            }
        }
        std::fs::remove_dir(&blocked).unwrap();

        // One bounded replay repairs the missing parent, reuses the successful writes,
        // and consumes the hinted fourth view with the same result as a healthy run.
        assert_eq!(node.realize(&head).unwrap(), expected[3]);
        for ((op, local), content) in ops.iter().zip(&expected).zip(&contents) {
            assert_eq!(node.local_of(op), Some(local.clone()));
            assert_eq!(node.canonical_of(local), Some(op.clone()));
            let store = node.loader().op_store();
            assert_eq!(
                pollster::block_on(store.read_operation(&local.0)).unwrap(),
                *content
            );
            assert!(pollster::block_on(store.read_view(&content.view_id)).is_ok());
        }
        node.advance(&head).unwrap();
        let published_after = node.local_heads().unwrap();
        assert_eq!(published_after.len(), 1);
        // Independently walk the real store: every published operation and view loads,
        // the failed batch is reachable, and the previous published work still is too.
        let store = node.loader().op_store();
        let mut seen = BTreeSet::new();
        let mut stack = published_after.clone();
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone()) {
                continue;
            }
            let op = pollster::block_on(store.read_operation(&local.0)).unwrap();
            pollster::block_on(store.read_view(&op.view_id)).unwrap();
            stack.extend(LocalOp::parents_of(&op));
        }
        assert!(expected.iter().all(|local| seen.contains(local)));
        assert!(published.iter().all(|local| seen.contains(local)));
        drop(node);
        let node = open(&b);
        for (op, local) in ops.iter().zip(&expected) {
            assert_eq!(node.local_of(op), Some(local.clone()));
        }
        b.jj(&["status"]);
    }
}

/// jj makes a keep ref for each commit it imports, the last step of an import, after the
/// commit's objects have arrived. A lock that a process killed partway through left on one
/// would fail the import, and the commit, no longer missing, would never get its keep ref.
#[test]
fn a_lock_left_on_a_keep_ref_does_not_fail_an_import() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    commit(&a, "f", "locked");
    let mut a_node = open(&a);
    let b_node = open(&b);
    let head = single_canonical_head(&mut a_node);
    let keep_ref = format!(
        "refs/jj/keep/{}",
        a.jj(&["log", "--no-graph", "-r", "@-", "-T", "commit_id"])
    );
    let lock = b.path().join(format!(".git/{keep_ref}.lock"));
    std::fs::create_dir_all(lock.parent().unwrap()).unwrap();
    std::fs::File::create(&lock)
        .unwrap()
        .set_modified(SystemTime::now() - 2 * ref_locks::STALE)
        .unwrap();
    ship_objects(&a_node, &b_node, &head);
    assert!(!lock.exists());
    b.git(&["rev-parse", "--verify", "--quiet", &keep_ref]);
}

/// A bookmark that fails to export to `.git` is exported again by the next export, so a
/// lock that a process killed partway through left on its ref would fail it every time.
#[test]
fn a_lock_left_on_a_bookmark_goes_after_a_failed_export() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    commit(&a, "f", "locked");
    a.jj(&["bookmark", "create", "main", "-r", "@-"]);
    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let head = single_canonical_head(&mut a_node);
    let lock = b.path().join(".git/refs/heads/main.lock");
    std::fs::File::create(&lock)
        .unwrap()
        .set_modified(SystemTime::now() - 2 * ref_locks::STALE)
        .unwrap();
    sync(&a_node, &mut b_node, &head);
    assert!(!lock.exists());
    b.jj(&["git", "export"]);
    assert_eq!(
        b.git(&["rev-parse", "refs/heads/main"]),
        a.git(&["rev-parse", "refs/heads/main"])
    );
}

/// The simple backend replicates through the same path, with store files in place of packs.
#[test]
fn simple_backend_round_trips() {
    let env = TestEnv::new();
    let a = env.init_simple_repo("alpha");
    let b = env.init_simple_repo("beta");
    a.write_file("dir/file", "one");
    a.jj(&["commit", "-m", "from alpha"]);
    a.jj(&["bookmark", "create", "main", "-r", "@-"]);

    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let a_head = single_canonical_head(&mut a_node);
    sync(&a_node, &mut b_node, &a_head);
    b.jj(&["new", "main"]);
    b.write_file("dir/other", "two");
    b.jj(&["commit", "-m", "from beta"]);
    b.jj(&["bookmark", "move", "main", "--to", "@-"]);
    let b_head = single_canonical_head(&mut b_node);
    sync(&b_node, &mut a_node, &b_head);

    assert_eq!(bookmarks(&a), bookmarks(&b));
    let show = |repo: &TestRepo| repo.jj(&["file", "show", "-r", "main", "dir/file"]);
    assert_eq!(show(&a), "one");
    assert_eq!(show(&b), "one");
    assert_eq!(a.jj(&["file", "show", "-r", "main", "dir/other"]), "two");
}

/// A git repository naming objects with SHA-256 replicates as one with SHA-1 does: commits,
/// their files and change ids, both ways.
#[test]
fn sha256_round_trips() {
    let env = TestEnv::new();
    let a = env.init_sha256_repo("alpha");
    let b = env.init_sha256_repo("beta");
    a.write_file("dir/file", "one");
    a.jj(&["commit", "-m", "from alpha"]);
    a.jj(&["bookmark", "create", "main", "-r", "@-"]);

    let mut a_node = open(&a);
    let mut b_node = open(&b);
    let a_head = single_canonical_head(&mut a_node);
    sync(&a_node, &mut b_node, &a_head);
    b.jj(&["new", "main"]);
    b.write_file("dir/other", "two");
    b.jj(&["commit", "-m", "from beta"]);
    b.jj(&["bookmark", "move", "main", "--to", "@-"]);
    let b_head = single_canonical_head(&mut b_node);
    sync(&b_node, &mut a_node, &b_head);

    assert_eq!(bookmarks(&a), bookmarks(&b));
    let ids = |repo: &TestRepo| {
        repo.jj(&[
            "log",
            "--no-graph",
            "-r",
            "::main",
            "-T",
            "commit_id ++ change_id ++ \"\\n\"",
        ])
    };
    assert_eq!(ids(&a), ids(&b));
    assert_eq!(a.git(&["rev-parse", "main"]).trim().len(), 64);
    assert_eq!(a.jj(&["file", "show", "-r", "main", "dir/other"]), "two");
}

/// A bundle that leaves out commits the import wants, as a hub with wrong haves or one
/// sweeping mid-round can send, fails the import, on either backend. The node relies on that
/// (`stage_objects`) to fail its sync rather than ask for the same objects again.
#[test]
fn an_import_missing_wanted_commits_fails() {
    let env = TestEnv::new();
    for (source, dest) in [
        (env.init_repo("alpha"), env.init_repo("beta")),
        (env.init_simple_repo("gamma"), env.init_simple_repo("delta")),
    ] {
        // Siblings, so that the bundle of one can't be a thin pack against the other.
        commit(&source, "one", "one");
        source.jj(&["new", "root()"]);
        commit(&source, "two", "two");
        let id = |message: &str| {
            let hex = source.jj(&[
                "log",
                "--no-graph",
                "-r",
                &format!("description(substring:{message})"),
                "-T",
                "commit_id",
            ]);
            CommitId::try_from_hex(hex.trim()).unwrap()
        };
        let (one, two) = (id("one"), id("two"));
        let wants = [one, two.clone()];
        let (source, dest) = (open(&source), open(&dest));
        let (from, to) = (source.object_store().unwrap(), dest.object_store().unwrap());
        let partial = tempfile::NamedTempFile::new().unwrap();
        from.export(&[two], &[], partial.path()).unwrap();
        let err = to.import(partial.path(), &wants, &[]).unwrap_err();
        assert!(matches!(err, ObjectError::NotConnected(_)), "{err:?}");
        let whole = tempfile::NamedTempFile::new().unwrap();
        from.export(&wants, &[], whole.path()).unwrap();
        to.import(whole.path(), &wants, &[]).unwrap();
    }
}

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let to = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &to);
        } else {
            std::fs::copy(entry.path(), to).unwrap();
        }
    }
}

/// Realizing an operation makes the views of those likely realized next ready, which must
/// change nothing: a history with a merge, realized one operation at a time with the rest
/// as the hint, as the sync adapter does, and published partway, which changes the
/// per-machine fields the rest inherit, gives the same operations as without the hint.
#[test]
fn realizing_ahead_changes_nothing() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    // Per-machine fields of B's own, for its realizations to inherit.
    commit(&b, "b0", "b0");
    b.jj(&["bookmark", "create", "beta", "-r", "@-"]);
    for i in 0..4 {
        commit(&a, &format!("one-{i}"), &format!("one {i}"));
        a.jj(&["bookmark", "set", "main", "-r", "@-"]);
    }
    // Concurrent operations, which the next command merges.
    let fork = a.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
    a.jj(&["bookmark", "create", "side", "-r", "@-"]);
    a.jj(&[
        "--at-op",
        fork.trim(),
        "bookmark",
        "create",
        "other",
        "-r",
        "@-",
    ]);
    for i in 0..4 {
        commit(&a, &format!("two-{i}"), &format!("two {i}"));
        a.jj(&["bookmark", "set", "main", "-r", "@-"]);
    }
    let mut a_node = open(&a);
    let head = single_canonical_head(&mut a_node);
    let b_node = open(&b);
    ship_objects(&a_node, &b_node, &head);
    ship_operations(&a_node, &b_node, &head);
    drop(b_node);
    let copy = env.root().join("beta-copy");
    copy_dir(b.path(), &copy);
    let realize = |repo_path: &Path, hinted: bool| {
        let mut node = NodeRepo::open(repo_path, &b.settings()).unwrap();
        let ops = node
            .canonical_store()
            .ancestors_until(std::slice::from_ref(&head), |id| {
                node.local_of(id).is_some()
            })
            .unwrap();
        let mut locals = vec![];
        for (i, op) in ops.iter().enumerate() {
            let next = if hinted { &ops[i + 1..] } else { &[] };
            locals.push(node.realize_pending(op, next).unwrap());
            if i == 4 {
                locals.push(node.advance(op).unwrap());
            }
        }
        node.settle().unwrap();
        locals
    };
    assert_eq!(
        realize(&b.repo_path(), true),
        realize(&copy.join(".jj/repo"), false)
    );
}
