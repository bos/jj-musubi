//! Canonicalization and realization between real colocated repositories.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use musubi_jj::node::NodeRepo;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

fn open(repo: &TestRepo) -> NodeRepo {
    NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap()
}

/// Ships the objects that the canonical operations reachable from `head` require and `to`
/// lacks, as a pack plus extras entries.
fn ship_objects(from: &NodeRepo, to: &NodeRepo, head: &OperationId) {
    let mut wants = BTreeSet::new();
    let mut stack = vec![head.clone()];
    let mut seen = BTreeSet::new();
    while let Some(id) = stack.pop() {
        if !seen.insert(id.clone()) || id == *from.canonical_store().root_operation_id() {
            continue;
        }
        wants.extend(from.required_commits(std::slice::from_ref(&id)).unwrap());
        stack.extend(from.canonical_store().read_operation(&id).unwrap().parents);
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
fn sync(from: &NodeRepo, to: &mut NodeRepo, head: &OperationId) {
    ship_objects(from, to, head);
    ship_operations(from, to, head);
    to.advance(head).unwrap();
}

/// Copies the canonical operations reachable from `head` that `to` lacks, as a bundle.
fn ship_operations(from: &NodeRepo, to: &NodeRepo, head: &OperationId) {
    let (src, dst) = (from.canonical_store(), to.canonical_store());
    let ops = src
        .ancestors_until(std::slice::from_ref(head), |id| dst.has_operation(id))
        .unwrap();
    let bundle = tempfile::NamedTempFile::new().unwrap();
    src.export_operations(&ops, bundle.path()).unwrap();
    let imported: Vec<OperationId> = dst
        .import_operations(bundle.path())
        .unwrap()
        .into_iter()
        .map(|(id, _)| id)
        .collect();
    assert_eq!(imported, ops);
}

fn single_canonical_head(node: &mut NodeRepo) -> OperationId {
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
        local.hex(),
        a_head.hex(),
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
        if !seen.insert(id.clone()) || id == *op_store.root_operation_id() {
            continue;
        }
        if b_node.canonicalize(&id).unwrap() == first {
            representing_first.insert(id.clone());
        }
        stack.extend(
            pollster::block_on(op_store.read_operation(&id))
                .unwrap()
                .parents,
        );
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
        std::fs::remove_file(operations.join(local.hex())).unwrap();
    }
    drop(b_node);

    let mut b_node = open(&b);
    let head_local = b_node.advance(&head).unwrap();
    let op_store = b_node.loader().op_store().clone();
    let mut realizations: BTreeMap<OperationId, BTreeSet<OperationId>> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![head_local];
    while let Some(id) = stack.pop() {
        if !seen.insert(id.clone()) || id == *op_store.root_operation_id() {
            continue;
        }
        let canonical = b_node.canonicalize(&id).unwrap();
        realizations
            .entry(canonical)
            .or_default()
            .insert(id.clone());
        stack.extend(
            pollster::block_on(op_store.read_operation(&id))
                .unwrap()
                .parents,
        );
    }
    for local in &in_flight {
        let canonical = b_node.canonicalize(local).unwrap();
        assert_eq!(realizations[&canonical], BTreeSet::from([local.clone()]));
    }
    b.jj(&["status"]);
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
