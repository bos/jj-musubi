//! What `Realize.lean` assumes of jj's merge of op heads (`Jj`), against jj itself, as
//! `heads_laws` does for how commands publish (docs/internals/conformance.md, "Realization"):
//! jj drops an op head below another without writing a merge (`load_drop`); it merges the rest in
//! the order they ended (`load_congr`); and beside one op head it merges workspaces name by name,
//! so that an operation that leaves a workspace alone doesn't move it, and one that changes a
//! workspace the op head left alone has its change kept, whichever ended first (`load_keeps`,
//! `load_takes`). An operation that leaves a workspace alone but rewrites the commit the op head
//! put it on does move it, which is why `keeps` names that commit. The operations are written
//! with jj-lib on an older operation and put beside the op heads, as a realization or a command
//! run `--at-op` would be; the `jj` binary then loads them. The tests can't choose the order the
//! file system lists op heads in, so `load_congr` is pinned as "the one that ended first wins,
//! whatever it does". `load_single` and `load_local` are how jj loads at all, and aren't pinned.

#![allow(clippy::unwrap_used)]

use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::op_heads_store::OpHeadsStore;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::ref_name::RefName;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::MutableRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use pollster::FutureExt as _;

fn loader(repo: &TestRepo) -> RepoLoader {
    default_backend_factories()
        .load_repo(&repo.settings(), &repo.repo_path())
        .unwrap()
}

fn heads(store: &Arc<dyn OpHeadsStore>) -> Vec<OperationId> {
    let mut heads = store.get_op_heads().block_on().unwrap();
    heads.sort();
    heads
}

/// How many operations the repository has written.
fn operations(repo: &TestRepo) -> usize {
    std::fs::read_dir(repo.repo_path().join("op_store/operations"))
        .unwrap()
        .count()
}

/// Writes an operation on `at`, with what `edit` does, and doesn't publish it.
fn write_at(repo: &TestRepo, at: &OperationId, edit: impl FnOnce(&mut MutableRepo)) -> OperationId {
    let loader = loader(repo);
    let op = loader.load_operation(at).block_on().unwrap();
    let mut tx = loader.load_at(&op).block_on().unwrap().start_transaction();
    edit(tx.repo_mut());
    tx.write("law")
        .block_on()
        .unwrap()
        .leave_unpublished()
        .op_id()
        .clone()
}

/// Makes the op heads `ops`, each put in beside the others with no merge.
fn set_heads(repo: &TestRepo, ops: &[OperationId]) {
    let store = loader(repo).op_heads_store().clone();
    let old = heads(&store);
    for op in ops {
        store.update_op_heads(&[], op).block_on().unwrap();
    }
    let gone: Vec<_> = old.into_iter().filter(|head| !ops.contains(head)).collect();
    store.update_op_heads(&gone, &ops[0]).block_on().unwrap();
    let mut wanted = ops.to_vec();
    wanted.sort();
    assert_eq!(heads(&store), wanted);
}

/// Has the `jj` binary load the repository, which merges the op heads, and returns the one op
/// head it leaves.
fn load(repo: &TestRepo) -> OperationId {
    repo.jj(&["--ignore-working-copy", "log", "-r", "root()", "-T", "''"]);
    let [head] = heads(loader(repo).op_heads_store()).try_into().unwrap();
    head
}

fn commit_at(repo: &TestRepo, op: &OperationId, name: &str) -> Option<CommitId> {
    let loader = loader(repo);
    let op = loader.load_operation(op).block_on().unwrap();
    let repo = loader.load_at(&op).block_on().unwrap();
    repo.view()
        .get_wc_commit_id(WorkspaceName::new(name))
        .cloned()
}

fn commit_of(repo: &TestRepo, revision: &str) -> CommitId {
    let hex = repo.jj(&[
        "--ignore-working-copy",
        "log",
        "--no-graph",
        "-r",
        revision,
        "-T",
        "commit_id",
    ]);
    CommitId::try_from_hex(hex.trim()).unwrap()
}

/// A repository with commits `p` and `q`, neither the working copy's, and its one op head.
fn repo_with_commits(env: &TestEnv) -> (TestRepo, OperationId, CommitId, CommitId) {
    let repo = env.init_non_colocated_repo("alpha");
    repo.jj(&["new", "-m", "p"]);
    let p = commit_of(&repo, "@");
    repo.jj(&["new", "root()", "-m", "q"]);
    let q = commit_of(&repo, "@");
    repo.jj(&["new", "root()"]);
    let [base] = heads(loader(&repo).op_heads_store()).try_into().unwrap();
    (repo, base, p, q)
}

fn set_wc(name: &str, commit: &CommitId) -> impl FnOnce(&mut MutableRepo) {
    let (name, commit) = (WorkspaceNameBuf::from(name), commit.clone());
    move |repo| repo.set_wc_commit(name, commit).unwrap()
}

/// An op head below another is dropped when jj loads them, and nothing is merged: jj writes no
/// operation, and the other is the one op head.
#[test]
fn jj_drops_an_op_head_below_another_without_merging() {
    let env = TestEnv::new();
    let repo = env.init_non_colocated_repo("alpha");
    repo.jj(&["describe", "-m", "one"]);
    repo.jj(&["describe", "-m", "two"]);
    let store = loader(&repo).op_heads_store().clone();
    let [newest] = heads(&store).try_into().unwrap();
    let op = loader(&repo).load_operation(&newest).block_on().unwrap();
    let [older] = op.parent_ids().to_vec().try_into().unwrap();
    store.update_op_heads(&[], &older).block_on().unwrap();
    assert_eq!(heads(&store).len(), 2);
    let written = operations(&repo);
    assert_eq!(load(&repo), newest);
    assert_eq!(operations(&repo), written, "jj wrote a merge");
}

/// jj merges op heads in the order they ended, so the order it finds them in doesn't matter:
/// where two move a workspace apart, the one that ended first keeps it, whichever that is.
#[test]
fn jj_merges_op_heads_in_the_order_they_ended() {
    for p_first in [true, false] {
        let env = TestEnv::new();
        let (repo, base, p, q) = repo_with_commits(&env);
        let (first, second) = if p_first { (&p, &q) } else { (&q, &p) };
        let earlier = write_at(&repo, &base, set_wc("default", first));
        let later = write_at(&repo, &base, set_wc("default", second));
        set_heads(&repo, &[later, earlier]);
        let merged = load(&repo);
        assert_eq!(
            commit_at(&repo, &merged, "default").as_ref(),
            Some(first),
            "p first: {p_first}"
        );
    }
}

/// jj merges workspaces name by name. Beside an op head that moves this machine's workspace and
/// sets a bookmark, an operation on its base that leaves that workspace alone and adds another
/// machine's leaves this machine's where the op head moved it, and the other machine's appears
/// as the operation records it, whichever of the two ended first.
#[test]
fn jj_merges_workspaces_name_by_name() {
    for realization_first in [false, true] {
        let env = TestEnv::new();
        let (repo, base, p, q) = repo_with_commits(&env);
        let head = |repo: &TestRepo| {
            write_at(repo, &base, |m| {
                m.set_wc_commit(WorkspaceNameBuf::from("default"), p.clone())
                    .unwrap();
                m.set_local_bookmark_target(RefName::new("y"), RefTarget::normal(q.clone()));
            })
        };
        let (moved, other) = if realization_first {
            let other = write_at(&repo, &base, set_wc("laptop/w", &q));
            (head(&repo), other)
        } else {
            (head(&repo), write_at(&repo, &base, set_wc("laptop/w", &q)))
        };
        set_heads(&repo, &[moved, other]);
        let merged = load(&repo);
        let first = format!("realization first: {realization_first}");
        assert_eq!(
            commit_at(&repo, &merged, "default").as_ref(),
            Some(&p),
            "{first}"
        );
        assert_eq!(
            commit_at(&repo, &merged, "laptop/w").as_ref(),
            Some(&q),
            "{first}"
        );
    }
}

/// Why `keeps` names a commit: an operation that leaves a workspace alone still moves it in jj's
/// merge if it rewrites the commit the op head beside it put the workspace on, as jj moves a
/// workspace whose commit a command in another workspace rewrote.
#[test]
fn jj_moves_a_workspace_whose_commit_the_other_operation_rewrote() {
    let env = TestEnv::new();
    let (repo, base, p, _) = repo_with_commits(&env);
    let moved = write_at(&repo, &base, set_wc("default", &p));
    let rewrite = write_at(&repo, &base, |m| {
        let commit = m.store().get_commit(&p).unwrap();
        m.rewrite_commit(&commit)
            .set_description("p rewritten")
            .write()
            .block_on()
            .unwrap();
        m.rebase_descendants().block_on().unwrap();
    });
    assert_ne!(commit_at(&repo, &rewrite, "default").as_ref(), Some(&p));
    set_heads(&repo, &[moved, rewrite]);
    let merged = load(&repo);
    let now = commit_at(&repo, &merged, "default").unwrap();
    assert_ne!(now, p, "the workspace stayed on the rewritten commit");
    let description = loader(&repo)
        .store()
        .get_commit(&now)
        .unwrap()
        .description()
        .to_owned();
    assert_eq!(description.trim(), "p rewritten");
}
