//! Hub storage against operations canonicalized from a real repository.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use jj_lib::backend::CommitId;
use jj_lib::op_store::OperationId;
use musubi_hub::store::Backend;
use musubi_hub::store::HubStore;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::bundle;
use musubi_jj::objects::bundle::Record;
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

/// Stores the operations in `anc*(head)` the hub lacks, with their views.
fn upload_ops(node: &NodeRepo, hub: &HubStore, head: &OperationId) {
    for id in canonical_ancestry(node, head) {
        if hub.canonical().has_operation(&id) {
            continue;
        }
        let op = node.canonical_store().read_operation(&id).unwrap();
        let view_bytes = node.canonical_store().view_bytes(&op.view_id).unwrap();
        hub.canonical()
            .import_view(&op.view_id, &view_bytes)
            .unwrap();
        let op_bytes = node.canonical_store().operation_bytes(&id).unwrap();
        hub.canonical().import_operation(&id, &op_bytes).unwrap();
    }
}

fn required(node: &NodeRepo, ops: &[OperationId]) -> Vec<CommitId> {
    ops.iter()
        .flat_map(|id| node.required_commits(id).unwrap())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

/// Writes the objects of a bundle into `git_dir` as loose objects.
fn unpack_loose(bundle_path: &Path, git_dir: &Path) {
    bundle::read(bundle_path, |record| {
        if let Record::Pack(pack) = record {
            let mut child = Command::new("git")
                .args(["unpack-objects", "-q"])
                .env("GIT_DIR", git_dir)
                .stdin(Stdio::piped())
                .spawn()
                .unwrap();
            std::io::copy(&mut pack.reader().unwrap(), child.stdin.as_mut().unwrap()).unwrap();
            drop(child.stdin.take());
            assert!(child.wait().unwrap().success());
        }
        Ok(())
    })
    .unwrap();
}

/// The hub accepts a head only once its closure is stored (HubClosed), so the closure check
/// of a new head need not look at accepted history again: on a large repository, walking
/// all of it took seconds per push, during which the hub served nobody else. To show that
/// the check stays out of accepted history, make a hole there that it would trip over.
#[test]
fn closure_check_skips_accepted_history() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    repo.write_file("a", "one");
    repo.jj(&["commit", "-m", "one"]);
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    let first = node.canonical_heads().unwrap().pop().unwrap();

    let hub_dir = env.root().join("hub");
    let mut hub = HubStore::init(&hub_dir, Backend::Git).unwrap();
    upload_ops(&node, &hub, &first);
    let first_ops = canonical_ancestry(&node, &first);
    let bundle_file = tempfile::NamedTempFile::new().unwrap();
    node.object_store()
        .unwrap()
        .export(&required(&node, &first_ops), &[], bundle_file.path())
        .unwrap();
    unpack_loose(bundle_file.path(), &hub_dir.join("git"));
    assert_eq!(hub.missing_closure(&first).unwrap(), Vec::<String>::new());
    hub.set_head(1, &first).unwrap();

    repo.write_file("b", "two");
    repo.jj(&["commit", "-m", "two"]);
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    let second = node.canonical_heads().unwrap().pop().unwrap();
    upload_ops(&node, &hub, &second);
    let new_ops: Vec<OperationId> = canonical_ancestry(&node, &second)
        .into_iter()
        .filter(|id| !hub.is_accepted(id))
        .collect();
    let bundle_file = tempfile::NamedTempFile::new().unwrap();
    node.object_store()
        .unwrap()
        .export(
            &required(&node, &new_ops),
            &required(&node, &first_ops),
            bundle_file.path(),
        )
        .unwrap();
    hub.object_store()
        .import(bundle_file.path(), &[], &[])
        .unwrap();

    // Lose the blob of `a`, which only accepted history has: the new commit's tree has it
    // too, but unchanged.
    let blob = repo.git(&["hash-object", "a"]);
    let blob = blob.trim();
    std::fs::remove_file(
        hub_dir
            .join("git/objects")
            .join(&blob[..2])
            .join(&blob[2..]),
    )
    .unwrap();
    assert_eq!(hub.missing_closure(&second).unwrap(), Vec::<String>::new());
}
