//! Canonicalization and realization between real colocated repositories.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;
use std::time::SystemTime;

use jj_lib::object_id::ObjectId as _;
use jj_lib::protos::git_store;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::CHANGE_ID_LENGTH;
use musubi_jj::objects::GitObjects;
use musubi_jj::objects::GitStore;
use musubi_jj::objects::ObjectError;
use musubi_jj::objects::ObjectStore;
use musubi_jj::objects::bundle::BundleWriter;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_jj::ref_locks;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use prost::Message as _;

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

#[test]
fn taking_an_abandon_preserves_original_identity_after_cache_loss() {
    use musubi_jj::canonical::Contraction;
    use musubi_jj::records::{HubOp, Record};

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let (a_local, between, x_local) = repeated_restore_ops(&repo);
    let mut node = open(&repo);
    let a = node.canonicalize(&a_local).unwrap();
    let between = node.canonicalize(&between).unwrap();
    let x = node.canonicalize(&x_local).unwrap();
    let mut contraction =
        Contraction::new(node.canonical_store(), [a.clone(), between.clone()]).unwrap();
    let expected = contraction.images(node.canonical_store(), &x).unwrap()[0].clone();
    node.adopt_records(&[Record::new([HubOp(a), HubOp(between)])])
        .unwrap();
    let head = repo.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n1",
        "-T",
        "id",
    ]);
    let head = LocalOp(jj_lib::op_store::OperationId::try_from_hex(head.trim()).unwrap());
    assert_ne!(
        head, a_local,
        "the survivor must not coalesce into the dropped local id"
    );
    drop(node);
    std::fs::remove_file(repo.repo_path().join("musubi/translation")).unwrap();
    let mut node = open(&repo);
    assert_eq!(node.canonicalize(&head).unwrap(), expected);

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
    let expected = node.current(&original)[0].0.clone();
    let expected_head = node.current(&base)[0].0.clone();
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
    node.canonical_heads().unwrap();
    assert_ne!(
        node.local_of(&expected),
        Some(source),
        "an alias is not the preferred realization"
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
    GitObjects::init_bare(git, &hub_git).unwrap();
    std::fs::create_dir_all(&hub_extras).unwrap();
    let hub = GitStore::for_hub(git, &hub_git, &hub_extras);
    assert_eq!(node.loader().store().change_id_length(), CHANGE_ID_LENGTH);
    let stores: [Box<dyn ObjectStore + '_>; 2] = [node.object_store().unwrap(), Box::new(hub)];
    let extras = |change_id: usize, terms: usize| {
        git_store::Commit {
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
