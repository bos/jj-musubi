//! What `OpHeadsRace.lean` assumes of jj, and `heads.rs` relies on, against jj itself, as
//! `ref_laws` does for refs (docs/internals/conformance.md, "Moving op heads"): a command that
//! changes the op heads publishes under the op-heads lock, but `jj op abandon` and `jj op
//! integrate` put their operation in with no lock; `update_op_heads` adds before it removes
//! and takes no notice of a head that isn't there; and jj's rewrite of an operation keeps its
//! fingerprint, the content but for its parents, and takes another id, which is how a join point
//! that `jj op abandon` rewrote is known. The lock is held here by the test, in process, as a jj
//! command in another process would hold it.

#![allow(clippy::unwrap_used)]

use std::io::Read as _;
use std::path::Path;
use std::process::Child;
use std::process::Stdio;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;

use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_heads_store::OpHeadsStore;
use jj_lib::op_store::OperationId;
use jj_lib::repo::RepoLoader;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use pollster::FutureExt as _;

use super::join::fingerprint;

fn loader(repo: &TestRepo) -> RepoLoader {
    RepoLoader::init_from_file_system(
        &repo.settings(),
        &repo.repo_path(),
        &default_backend_factories(),
    )
    .unwrap()
}

fn heads(store: &Arc<dyn OpHeadsStore>) -> Vec<OperationId> {
    let mut heads = store.get_op_heads().block_on().unwrap();
    heads.sort();
    heads
}

/// A repository with three operations above the root's: a snapshot, then two descriptions.
/// Returns the operations that last two commands made, the older first.
fn repo_with_history(env: &TestEnv) -> (TestRepo, OperationId, OperationId) {
    let repo = env.init_repo("alpha");
    repo.write_file("a", "1");
    repo.jj(&["describe", "-m", "one"]);
    repo.jj(&["describe", "-m", "two"]);
    let store = loader(&repo).op_heads_store().clone();
    let [newest] = heads(&store).try_into().unwrap();
    let op = loader(&repo)
        .op_store()
        .read_operation(&newest)
        .block_on()
        .unwrap();
    let [older] = op.parents.clone().try_into().unwrap();
    (repo, older, newest)
}

/// `jj` with `args`, left running.
fn spawn(repo: &TestRepo, args: &[&str]) -> Child {
    repo.program(Path::new("jj"))
        .args(args)
        .env("COLUMNS", "80")
        .env("RAYON_NUM_THREADS", "1")
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap()
}

/// Waits for `child` to finish successfully, as long as a test of jj's locks can need: a
/// command that waits on a lock the test holds would wait forever.
fn finish(mut child: Child, what: &str) {
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut wait = Duration::from_millis(1);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            let mut stderr = String::new();
            child
                .stderr
                .take()
                .unwrap()
                .read_to_string(&mut stderr)
                .unwrap();
            assert!(status.success(), "{what} failed: {stderr}");
            return;
        }
        if Instant::now() > deadline {
            child.kill().unwrap();
            panic!("{what} didn't finish");
        }
        std::thread::sleep(wait);
        wait = (wait * 2).min(Duration::from_millis(100));
    }
}

/// How many operations the repository has written.
fn operations(repo: &TestRepo) -> usize {
    std::fs::read_dir(repo.repo_path().join("op_store/operations"))
        .unwrap()
        .count()
}

/// Whether `child` is still running after the time a command that isn't waiting on anything
/// takes to finish several times over. Nothing else says that a command waits, and a command
/// slower than that to reach its lock would pass: this can miss jj taking no lock, never
/// report that it takes one.
fn still_running(child: &mut Child) -> bool {
    std::thread::sleep(Duration::from_millis(400));
    child.try_wait().unwrap().is_none()
}

/// `jj op abandon` finishes while another process holds the op-heads lock, having put its
/// rewrite in place of the op head it read: it takes no lock.
#[test]
fn jj_op_abandon_takes_no_lock() {
    let env = TestEnv::new();
    let (repo, older, newest) = repo_with_history(&env);
    let store = loader(&repo).op_heads_store().clone();
    let lock = store.lock().block_on().unwrap();
    let child = spawn(&repo, &["op", "abandon", &older.hex()]);
    finish(child, "jj op abandon");
    let now = heads(&store);
    assert_eq!(now.len(), 1);
    assert_ne!(now[0], newest);
    drop(lock);
}

/// `jj op integrate` adds its operation to the op heads while another process holds the lock,
/// and only then waits for it, to merge the op heads: it takes no lock to land.
#[test]
fn jj_op_integrate_lands_with_no_lock_and_merges_under_it() {
    let env = TestEnv::new();
    let (repo, older, _) = repo_with_history(&env);
    repo.jj(&["op", "abandon", &older.hex()]);
    let store = loader(&repo).op_heads_store().clone();
    let lock = store.lock().block_on().unwrap();
    let mut child = spawn(&repo, &["op", "integrate", &older.hex()]);
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut wait = Duration::from_millis(1);
    while !heads(&store).contains(&older) {
        assert!(Instant::now() < deadline, "jj op integrate didn't land");
        assert!(
            child.try_wait().unwrap().is_none(),
            "it finished without landing"
        );
        std::thread::sleep(wait);
        wait = (wait * 2).min(Duration::from_millis(100));
    }
    // It is a second op head now, and the command, which merges them, waits for the lock.
    assert_eq!(heads(&store).len(), 2);
    assert!(
        still_running(&mut child),
        "it merged the op heads without the lock"
    );
    drop(lock);
    finish(child, "jj op integrate");
    assert_eq!(heads(&store).len(), 1);
}

/// A `jj` command that changes the op heads, a description here, publishes its operation under
/// the lock, in place of the op head it loaded; where there are several it merges them under
/// the lock first, whether or not it writes anything else.
#[test]
fn a_jj_command_publishes_and_merges_under_the_lock() {
    let env = TestEnv::new();
    let (repo, older, newest) = repo_with_history(&env);
    let store = loader(&repo).op_heads_store().clone();
    let lock = store.lock().block_on().unwrap();
    let written = operations(&repo);
    let mut child = spawn(&repo, &["describe", "-m", "three"]);
    // It writes its operation before it takes the lock, so that has happened once there is one
    // more: the command is at the lock.
    let deadline = Instant::now() + Duration::from_secs(60);
    while operations(&repo) == written {
        assert!(Instant::now() < deadline, "jj describe wrote no operation");
        assert!(
            child.try_wait().unwrap().is_none(),
            "it finished beside the lock"
        );
        std::thread::sleep(Duration::from_millis(2));
    }
    assert!(
        still_running(&mut child),
        "a command published without the lock"
    );
    assert_eq!(heads(&store), vec![newest.clone()]);
    drop(lock);
    finish(child, "jj describe");
    let [published] = heads(&store).try_into().unwrap();
    assert_ne!(published, newest);
    // A command at an older operation leaves a second op head: the next command merges them.
    repo.jj(&["--at-op", &older.hex(), "describe", "-m", "beside"]);
    assert_eq!(heads(&store).len(), 2);
    let lock = store.lock().block_on().unwrap();
    let mut child = spawn(&repo, &["log", "--no-graph", "-T", "''"]);
    assert!(
        still_running(&mut child),
        "a command merged the op heads without the lock"
    );
    assert_eq!(heads(&store).len(), 2);
    drop(lock);
    finish(child, "jj log");
    assert_eq!(heads(&store).len(), 1);
}

/// A `jj` command that loads several op heads merges them before it writes anything, so that its
/// operation has the merge for its parent, and never sits beside another op head built on one of
/// them. A command run `--at-op` writes on the operation it names, with no merge, and so does
/// sit beside the op heads that are there.
#[test]
fn a_command_that_loads_several_op_heads_merges_them_before_it_writes() {
    let env = TestEnv::new();
    let (repo, older, newest) = repo_with_history(&env);
    let store = loader(&repo).op_heads_store().clone();
    let read = |id: &OperationId| {
        loader(&repo)
            .op_store()
            .read_operation(id)
            .block_on()
            .unwrap()
    };
    // Run at an older operation, a command writes on it, and the op heads are two.
    repo.jj(&["--at-op", &older.hex(), "describe", "-m", "beside"]);
    let before = heads(&store);
    assert_eq!(before.len(), 2);
    let beside = before.iter().find(|id| **id != newest).unwrap();
    assert_eq!(read(beside).parents, vec![older.clone()]);
    // Loading both, a command merges them first, and writes its own on the merge.
    repo.jj(&["describe", "-m", "after"]);
    let [written] = heads(&store).try_into().unwrap();
    let [merge] = read(&written).parents.try_into().unwrap();
    let mut merged = read(&merge).parents;
    merged.sort();
    assert_eq!(merged, before);
}

/// `update_op_heads` adds the new op head before it removes the old, so that a failure partway
/// leaves extra op heads rather than none; an op head it replaces with itself stays; and one
/// that isn't an op head is ignored.
#[test]
fn update_op_heads_adds_before_it_removes_and_ignores_a_head_that_is_gone() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let store = loader(&repo).op_heads_store().clone();
    let id = |byte: u8| OperationId::new(vec![byte; 64]);
    let [root] = heads(&store).try_into().unwrap();
    let with = |extra: &[OperationId]| {
        let mut all = vec![root.clone()];
        all.extend(extra.iter().cloned());
        all.sort();
        all
    };
    // `7` was never an op head: only the new one goes in.
    store.update_op_heads(&[id(7)], &id(1)).block_on().unwrap();
    assert_eq!(heads(&store), with(&[id(1)]));
    // Replaced by itself, an op head stays.
    store.update_op_heads(&[id(1)], &id(1)).block_on().unwrap();
    assert_eq!(heads(&store), with(&[id(1)]));
    // The old one's removal fails, as when a file can't be removed: the new one is in already.
    let stuck = repo.repo_path().join("op_heads/heads").join(id(2).hex());
    std::fs::create_dir(&stuck).unwrap();
    assert!(store.update_op_heads(&[id(2)], &id(3)).block_on().is_err());
    std::fs::remove_dir(&stuck).unwrap();
    assert_eq!(heads(&store), with(&[id(1), id(3)]));
}

/// jj's rewrite of an operation, as `jj op abandon` of one below it makes, has the same
/// fingerprint and another id; another command's operation has another fingerprint.
#[test]
fn a_rewritten_operation_keeps_its_fingerprint_and_gets_another_id() {
    let env = TestEnv::new();
    let (repo, older, newest) = repo_with_history(&env);
    let store = loader(&repo).op_heads_store().clone();
    let read = |id: &OperationId| {
        loader(&repo)
            .op_store()
            .read_operation(id)
            .block_on()
            .unwrap()
    };
    let before = read(&newest);
    let below = read(&older);
    repo.jj(&["op", "abandon", &older.hex()]);
    let [rewrite] = heads(&store).try_into().unwrap();
    assert_ne!(rewrite, newest);
    let after = read(&rewrite);
    assert_ne!(after.parents, before.parents);
    assert_eq!(fingerprint(&after), fingerprint(&before));
    assert_ne!(fingerprint(&before), fingerprint(&below));
}
