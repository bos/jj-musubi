//! Hub storage against operations canonicalized from a real repository.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeSet;

use jj_lib::op_store::OperationId;
use musubi_hub::store::Backend;
use musubi_hub::store::HubStore;
use musubi_jj::node::NodeRepo;
use musubi_testutil::TestEnv;

fn canonical_ancestry(node: &NodeRepo, head: &OperationId) -> Vec<OperationId> {
    let store = node.canonical_store();
    let mut order = vec![];
    let mut seen = BTreeSet::new();
    let mut stack = vec![head.clone()];
    while let Some(id) = stack.pop() {
        if id == *store.root_operation_id() || !seen.insert(id.clone()) {
            continue;
        }
        stack.extend(store.read_operation(&id).unwrap().parents);
        order.push(id);
    }
    order
}

#[test]
fn closure_and_head_persist() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    repo.write_file("f", "one");
    repo.jj(&["commit", "-m", "one"]);
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    let head = node.canonical_heads().unwrap().pop().unwrap();

    let hub_dir = env.root().join("hub");
    let mut hub = HubStore::init(&hub_dir, Backend::Git).unwrap();
    assert!(!hub.descends_from_head(&head).unwrap() || hub.head().1 == &head);
    assert!(!hub.missing_closure(&head).unwrap().is_empty());

    // Operations alone are not enough: the commits are missing.
    let ops = canonical_ancestry(&node, &head);
    for id in &ops {
        let op = node.canonical_store().read_operation(id).unwrap();
        let view_bytes = node.canonical_store().view_bytes(&op.view_id).unwrap();
        hub.canonical()
            .import_view(&op.view_id, &view_bytes)
            .unwrap();
        let op_bytes = node.canonical_store().operation_bytes(id).unwrap();
        hub.canonical().import_operation(id, &op_bytes).unwrap();
    }
    assert!(hub.descends_from_head(&head).unwrap());
    let missing = hub.missing_closure(&head).unwrap();
    assert!(
        missing.iter().all(|m| m.starts_with("commit ")),
        "{missing:?}"
    );

    let wants: Vec<_> = ops
        .iter()
        .flat_map(|id| node.required_commits(id).unwrap())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let bundle = tempfile::NamedTempFile::new().unwrap();
    node.object_store()
        .unwrap()
        .export(&wants, &[], bundle.path())
        .unwrap();
    hub.object_store()
        .import(bundle.path(), &wants, &[])
        .unwrap();
    assert_eq!(hub.missing_closure(&head).unwrap(), Vec::<String>::new());

    hub.set_head(1, &head).unwrap();
    drop(hub);
    let hub = HubStore::open(&hub_dir).unwrap();
    assert_eq!(hub.head(), (1, &head));
    assert!(ops.iter().all(|id| hub.is_accepted(id)));
}

#[test]
fn tampered_operation_is_rejected() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    let head = node.canonical_heads().unwrap().pop().unwrap();
    let hub = HubStore::init(&env.root().join("hub"), Backend::Git).unwrap();
    let op = node.canonical_store().read_operation(&head).unwrap();
    let view_bytes = node.canonical_store().view_bytes(&op.view_id).unwrap();
    hub.canonical()
        .import_view(&op.view_id, &view_bytes)
        .unwrap();
    let mut bytes = node.canonical_store().operation_bytes(&head).unwrap();
    // Flip a bit in the description, which is part of the hashed content.
    let last = bytes.len() - 1;
    bytes[last] ^= 1;
    assert!(hub.canonical().import_operation(&head, &bytes).is_err());
    assert!(!hub.canonical().has_operation(&head));
}
