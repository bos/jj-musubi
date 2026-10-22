//! Joining existing repositories: state is replicated, earlier operation history is not.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeSet;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use musubi_jj::node::NodeRepo;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;

fn open(repo: &TestRepo) -> NodeRepo {
    NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap()
}

fn canonical_ancestry(node: &NodeRepo, head: &OperationId) -> Vec<OperationId> {
    let store = node.canonical_store();
    let mut seen = BTreeSet::new();
    let mut stack = vec![head.clone()];
    let mut order = vec![];
    while let Some(id) = stack.pop() {
        if id == *store.root_operation_id() || !seen.insert(id.clone()) {
            continue;
        }
        stack.extend(store.read_operation(&id).unwrap().parents);
        order.push(id);
    }
    order
}

fn sync(from: &NodeRepo, to: &mut NodeRepo, head: &OperationId) {
    let ops = canonical_ancestry(from, head);
    let wants: Vec<_> = from.required_commits(&ops).unwrap().into_iter().collect();
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
    let (src, dst) = (from.canonical_store(), to.canonical_store());
    for id in &ops {
        let op = src.read_operation(id).unwrap();
        dst.import_view(&op.view_id, &src.view_bytes(&op.view_id).unwrap())
            .unwrap();
        dst.import_operation(id, &src.operation_bytes(id).unwrap())
            .unwrap();
    }
    to.advance(head).unwrap();
}

fn descriptions(repo: &TestRepo) -> BTreeSet<String> {
    repo.jj(&[
        "log",
        "-r",
        "all()",
        "--no-graph",
        "-T",
        r#"description.first_line() ++ "\n""#,
    ])
    .lines()
    .filter(|line| !line.is_empty())
    .map(str::to_owned)
    .collect()
}

#[test]
fn independent_repositories_join_and_merge() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    for (repo, name) in [(&a, "alpha"), (&b, "beta")] {
        for i in 0..3 {
            repo.write_file(&format!("{name}-{i}"), "x");
            repo.jj(&["commit", "-m", &format!("{name} {i}")]);
        }
        repo.jj(&["bookmark", "create", name, "-r", "@-"]);
    }

    let mut a_node = open(&a);
    let a_join = a_node.create_join_operation("musubi: alpha joins").unwrap();
    // Only the join operation is replicated, not the dozen operations before it.
    assert_eq!(canonical_ancestry(&a_node, &a_join), vec![a_join.clone()]);
    assert_eq!(a_node.canonical_heads().unwrap(), vec![a_join.clone()]);

    let mut b_node = open(&b);
    let b_join = b_node.create_join_operation("musubi: beta joins").unwrap();
    sync(&a_node, &mut b_node, &a_join);
    // B's join and A's join meet at the root operation; jj merges them.
    b_node.merge_heads().unwrap();
    let b_head = b_node.canonical_heads().unwrap().pop().unwrap();
    let ancestry: BTreeSet<_> = canonical_ancestry(&b_node, &b_head).into_iter().collect();
    assert!(ancestry.contains(&a_join) && ancestry.contains(&b_join));
    assert_eq!(ancestry.len(), 3, "two joins and one merge");

    sync(&b_node, &mut a_node, &b_head);
    assert_eq!(descriptions(&a), descriptions(&b));
    assert!(descriptions(&a).contains("beta 2") && descriptions(&b).contains("alpha 2"));

    // Joins survive losing the translation cache.
    std::fs::remove_file(a.repo_path().join("musubi/translation")).unwrap();
    let mut fresh = open(&a);
    assert_eq!(fresh.canonical_heads().unwrap(), vec![b_head]);
}

/// A machine whose `git` remote view is left empty, by deleting the last bookmark it
/// exported, joins: realizing the merge of its join with another machine's, whose fields
/// here are the root's, gives what jj's merge would (which debug builds check).
#[test]
fn join_after_deleting_every_exported_bookmark() {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    for (repo, name) in [(&a, "alpha"), (&b, "beta")] {
        for i in 0..3 {
            repo.write_file(&format!("{name}-{i}"), "x");
            repo.jj(&["commit", "-m", &format!("{name} {i}")]);
        }
        repo.jj(&["bookmark", "create", name, "-r", "@-"]);
    }
    a.jj(&["bookmark", "delete", "alpha"]);

    let mut a_node = open(&a);
    let a_join = a_node.create_join_operation("musubi: alpha joins").unwrap();
    let mut b_node = open(&b);
    b_node.create_join_operation("musubi: beta joins").unwrap();
    sync(&a_node, &mut b_node, &a_join);
    b_node.merge_heads().unwrap();
    let b_head = b_node.canonical_heads().unwrap().pop().unwrap();
    sync(&b_node, &mut a_node, &b_head);
}

/// A join record a killed `musubi join` tore names nothing, and the record the next join
/// writes after it stands.
#[test]
fn a_torn_join_record_names_nothing() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = open(&repo);
    let head = node.merge_heads().unwrap();
    let first = node.create_join_operation("musubi: alpha joins").unwrap();
    drop(node);
    // As if the join had been killed while it wrote its record, before it recorded anything
    // else.
    let musubi = repo.repo_path().join("musubi");
    let torn = format!("{} {}", head.hex(), &first.hex()[..40]);
    std::fs::write(musubi.join("joins"), torn).unwrap();
    std::fs::remove_file(musubi.join("translation")).unwrap();
    let mut node = open(&repo);
    assert_eq!(node.canonical_of(&head), None);
    let second = node.create_join_operation("musubi: alpha joins").unwrap();
    drop(node);
    // The record alone.
    std::fs::remove_file(musubi.join("translation")).unwrap();
    let node = open(&repo);
    assert_eq!(node.canonical_of(&head), Some(second));
}
