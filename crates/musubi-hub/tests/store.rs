//! Hub storage against operations canonicalized from a real repository.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use musubi_hub::store;
use musubi_hub::store::HubStore;
use musubi_hub::store::StoreError;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_jj::objects::ObjectError;
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

    let wants: Vec<_> = node.required_commits(&ops).unwrap().into_iter().collect();
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
    // Refs name the head's visible heads, for git to index.
    let refs = Command::new("git")
        .arg("-C")
        .arg(hub_dir.join("git"))
        .args([
            "for-each-ref",
            "--format=%(objectname)",
            "refs/musubi/head/",
        ])
        .output()
        .unwrap();
    let named: BTreeSet<String> = String::from_utf8(refs.stdout)
        .unwrap()
        .lines()
        .map(str::to_owned)
        .collect();
    let view_id = hub.canonical().read_operation(&head).unwrap().view_id;
    let heads: BTreeSet<String> = hub
        .canonical()
        .read_view(&view_id)
        .unwrap()
        .head_ids
        .iter()
        .map(|commit| commit.hex())
        .collect();
    assert!(!named.is_empty());
    assert_eq!(named, heads);
    drop(hub);
    let hub = HubStore::open(&hub_dir).unwrap();
    assert_eq!(hub.head(), (1, &head));
    assert!(ops.iter().all(|id| hub.is_accepted(id)));
}

/// A heads file with a torn line, as a power cut can leave it, is corrupt: the hub is made
/// again rather than recovered, and skipping the line would lose every head appended after
/// it.
#[test]
fn torn_heads_are_corrupt() {
    let env = TestEnv::new();
    let hub_dir = env.root().join("hub");
    let root = HubStore::init(&hub_dir, Backend::Git)
        .unwrap()
        .head()
        .1
        .hex();
    let heads = hub_dir.join("heads");
    let whole = std::fs::read_to_string(&heads).unwrap();
    for torn in [
        "1 0123456789a",
        "1 0123456789ab",
        &format!("1 0123456789a1 {root}\n"),
    ] {
        std::fs::write(&heads, format!("{whole}{torn}")).unwrap();
        assert!(
            matches!(HubStore::open(&hub_dir), Err(StoreError::CorruptHead(_))),
            "{torn:?} was taken"
        );
    }
}

/// Whatever a crash or a disk did to the files naming a store's backend and heads, the store
/// opens as it was, or fails as a corrupt one, to be made again.
#[hegel::test(test_cases = 100)]
fn damaged_stores_open_or_are_corrupt(tc: TestCase) {
    let dir = tempfile::tempdir().unwrap();
    let hub_dir = dir.path().join("hub");
    let root = HubStore::init(&hub_dir, Backend::Simple)
        .unwrap()
        .head()
        .1
        .clone();
    let file = hub_dir.join(if tc.draw(gs::booleans()) {
        "heads"
    } else {
        "backend"
    });
    let mut bytes = std::fs::read(&file).unwrap();
    for _ in 0..tc.draw(gs::integers::<u8>().min_value(1).max_value(3)) {
        let at = tc.draw(gs::integers::<usize>().max_value(bytes.len()));
        match tc.draw(gs::integers::<u8>().max_value(2)) {
            0 => bytes.truncate(at),
            1 if at < bytes.len() => bytes[at] = tc.draw(gs::integers::<u8>()),
            _ => bytes.insert(at, tc.draw(gs::integers::<u8>())),
        }
    }
    std::fs::write(&file, &bytes).unwrap();
    match HubStore::open(&hub_dir) {
        Ok(store) => assert_eq!(store.head(), (0, &root)),
        Err(err) => assert!(store::is_corrupt(&err), "{err:?} is not corrupt"),
    }
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
    node.required_commits(ops).unwrap().into_iter().collect()
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
        Ok::<_, ObjectError>(())
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

/// With a bitmap index, git sends an object it stores no delta for whole, rather than as a
/// delta against what the receiver has: an edit just pushed, which the hub keeps loose, would
/// go to every other node as the whole file. So an export to a node that has something uses
/// no bitmap.
#[test]
fn small_edits_stay_small_beside_a_bitmap() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    // A large file that compresses poorly.
    let lines: Vec<String> = (0..20_000u32)
        .map(|i| format!("{:08x}", i.wrapping_mul(2_654_435_761)))
        .collect();
    repo.write_file("big", &lines.join("\n"));
    repo.jj(&["commit", "-m", "big"]);
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    let old = node.canonical_heads().unwrap().pop().unwrap();
    let hub_dir = env.root().join("hub");
    let mut hub = HubStore::init(&hub_dir, Backend::Git).unwrap();
    upload_ops(&node, &hub, &old);
    let old_wants = required(&node, &canonical_ancestry(&node, &old));
    let bundle = tempfile::NamedTempFile::new().unwrap();
    node.object_store()
        .unwrap()
        .export(&old_wants, &[], bundle.path())
        .unwrap();
    hub.object_store()
        .import(bundle.path(), &old_wants, &[])
        .unwrap();
    hub.set_head(1, &old).unwrap();
    // A bitmap index of what the head reaches, as the hub's gc writes once it's big.
    let git_dir = hub_dir.join("git");
    let repack = Command::new("git")
        .env("GIT_DIR", &git_dir)
        .args(["repack", "-a", "-d", "-b", "-q", "--cruft"])
        .args(["--cruft-expiration=never"])
        .status()
        .unwrap();
    assert!(repack.success());
    let packs = std::fs::read_dir(git_dir.join("objects/pack")).unwrap();
    assert!(
        packs
            .flatten()
            .any(|entry| { entry.file_name().to_string_lossy().ends_with(".bitmap") })
    );
    drop(node);

    // A small edit, few enough objects that the hub stores them loose.
    let mut edited = lines.clone();
    edited[10_000] = "edited".to_owned();
    repo.write_file("big", &edited.join("\n"));
    repo.jj(&["commit", "-m", "edit"]);
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    let new = node.canonical_heads().unwrap().pop().unwrap();
    upload_ops(&node, &hub, &new);
    let new_wants = required(&node, &canonical_ancestry(&node, &new));
    let bundle = tempfile::NamedTempFile::new().unwrap();
    node.object_store()
        .unwrap()
        .export(&new_wants, &old_wants, bundle.path())
        .unwrap();
    hub.object_store()
        .import(bundle.path(), &new_wants, &old_wants)
        .unwrap();

    // To a node that has the old head, the edit goes as a delta.
    let bundle = tempfile::NamedTempFile::new().unwrap();
    hub.object_store()
        .export(&new_wants, &old_wants, bundle.path())
        .unwrap();
    let size = std::fs::metadata(bundle.path()).unwrap().len();
    assert!(size < 10_000, "{size} bytes for a one-line edit");
}
