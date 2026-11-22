//! Real `jj` commands racing a realization, and a realization interrupted on its way to the op
//! heads, through the shipping `advance` and `merge_heads` paths.
//!
//! Each test runs real jj against real colocated repositories, interposing only at the op
//! stores' edge (`Interpose`, which is why they live in the crate: they replace the node's
//! loader) to run a command at a chosen point in the code under test, or `fs` faults. What they
//! check is what a user sees afterwards: no operation or bookmark move is lost, `.git` agrees
//! with the op heads before any `jj` command can see them, a workspace of this machine keeps its
//! commit, and a repository an interruption left converges when realization resumes. They don't
//! pin how often the code reads the op heads, but for one test that notes where it does. Two of
//! them check, too, that what jj shows once the realization is published is what `Realize.lean`
//! predicts, jj's own merge of the op heads with the realization (`assert_shows_jj_merge`).

#![allow(clippy::unwrap_used)]

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::SystemTime;

use async_trait::async_trait;
use jj_lib::backend::CommitId;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::object_id::HexPrefix;
use jj_lib::object_id::ObjectId as _;
use jj_lib::object_id::PrefixResolution;
use jj_lib::op_heads_store::OpHeadsStore;
use jj_lib::op_heads_store::OpHeadsStoreError;
use jj_lib::op_heads_store::OpHeadsStoreLock;
use jj_lib::op_heads_store::resolve_op_heads;
use jj_lib::op_store::OpStore;
use jj_lib::op_store::OpStoreResult;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::ref_name::RefName;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::simple_op_heads_store::SimpleOpHeadsStore;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use pollster::FutureExt as _;
use serde_json::json;

use super::super::NodeRepo;
use super::advance_tests::assert_exported;
use super::advance_tests::fixture;
use super::advance_tests::git_bookmark;
use super::advance_tests::open;
use super::advance_tests::reachable;
use super::advance_tests::transfer;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::oracle::Oracle;

type Hook = Box<dyn FnOnce() + Send>;
type Update = Box<dyn Fn(&OperationId) + Send + Sync>;

#[derive(Default)]
struct Hooks {
    /// Runs before the next operation is written.
    write: Option<Hook>,
    /// Runs before the `n`th read of the op heads from now, `1` being the next.
    read: Option<(usize, Hook)>,
}

/// The op stores of a repository, passing everything through to the real ones, but for
/// running what a test says at a chosen point, as another process would.
struct Interpose {
    ops: Arc<dyn OpStore>,
    heads: Arc<dyn OpHeadsStore>,
    hooks: Mutex<Hooks>,
    /// Runs before the op heads are updated to the operation it is given.
    update: Mutex<Option<Update>>,
}

impl std::fmt::Debug for Interpose {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Interpose").finish_non_exhaustive()
    }
}

impl Interpose {
    fn before_write(&self, run: impl FnOnce() + Send + 'static) {
        self.hooks.lock().unwrap().write = Some(Box::new(run));
    }

    fn before_read(&self, nth: usize, run: impl FnOnce() + Send + 'static) {
        self.hooks.lock().unwrap().read = Some((nth, Box::new(run)));
    }

    fn before_update(&self, run: impl Fn(&OperationId) + Send + Sync + 'static) {
        *self.update.lock().unwrap() = Some(Box::new(run));
    }
}

#[async_trait]
impl OpStore for Interpose {
    fn name(&self) -> &str {
        self.ops.name()
    }

    fn root_operation_id(&self) -> &OperationId {
        self.ops.root_operation_id()
    }

    async fn read_view(&self, id: &ViewId) -> OpStoreResult<View> {
        self.ops.read_view(id).await
    }

    async fn write_view(&self, view: &View) -> OpStoreResult<ViewId> {
        self.ops.write_view(view).await
    }

    async fn read_operation(&self, id: &OperationId) -> OpStoreResult<StoreOperation> {
        self.ops.read_operation(id).await
    }

    async fn write_operation(&self, op: &StoreOperation) -> OpStoreResult<OperationId> {
        let hook = self.hooks.lock().unwrap().write.take();
        if let Some(hook) = hook {
            hook();
        }
        self.ops.write_operation(op).await
    }

    async fn resolve_operation_id_prefix(
        &self,
        prefix: &HexPrefix,
    ) -> OpStoreResult<PrefixResolution<OperationId>> {
        self.ops.resolve_operation_id_prefix(prefix).await
    }

    async fn gc(&self, heads: &[OperationId], newer: SystemTime) -> OpStoreResult<()> {
        self.ops.gc(heads, newer).await
    }
}

#[async_trait]
impl OpHeadsStore for Interpose {
    fn name(&self) -> &str {
        self.heads.name()
    }

    async fn get_op_heads(&self) -> Result<Vec<OperationId>, OpHeadsStoreError> {
        let hook = {
            let mut hooks = self.hooks.lock().unwrap();
            match hooks.read.take() {
                Some((1, hook)) => Some(hook),
                Some((nth, hook)) => {
                    hooks.read = Some((nth - 1, hook));
                    None
                }
                None => None,
            }
        };
        if let Some(hook) = hook {
            hook();
        }
        self.heads.get_op_heads().await
    }

    async fn lock(&self) -> Result<Box<dyn OpHeadsStoreLock + '_>, OpHeadsStoreError> {
        self.heads.lock().await
    }

    async fn update_op_heads(
        &self,
        old: &[OperationId],
        new: &OperationId,
    ) -> Result<(), OpHeadsStoreError> {
        if let Some(update) = &*self.update.lock().unwrap() {
            update(new);
        }
        self.heads.update_op_heads(old, new).await
    }
}

fn interpose(node: &mut NodeRepo) -> Arc<Interpose> {
    let loader = &node.loader;
    let stores = Arc::new(Interpose {
        ops: loader.op_store().clone(),
        heads: loader.op_heads_store().clone(),
        hooks: Mutex::default(),
        update: Mutex::default(),
    });
    node.loader = RepoLoader::new(
        loader.settings().clone(),
        loader.store().clone(),
        loader.workspace_store().clone(),
        stores.clone(),
        stores.clone(),
        loader.index_store().clone(),
        loader.submodule_store().clone(),
    );
    stores
}

fn commit_of(repo: &TestRepo, revision: &str) -> String {
    repo.jj(&[
        "--ignore-working-copy",
        "log",
        "--no-graph",
        "-r",
        revision,
        "-T",
        "commit_id",
    ])
    .trim()
    .to_owned()
}

fn local_bookmarks(repo: &TestRepo) -> String {
    let template = r#"if(present && !remote, name ++ "@ " ++ normal_target.commit_id() ++ "\n")"#;
    repo.jj(&["--ignore-working-copy", "bookmark", "list", "-T", template])
}

/// Two machines in one hive: `beta`, whose node realizes `incoming`, work of `alpha`'s, has the
/// workspaces `a` and `b` and a bookmark `x`; `alpha` has a workspace `a` of its own, which
/// `beta` shows as `alpha/a`. The work `alpha` sends also adds a workspace `c`, which `beta` shows
/// as `alpha/c`.
struct Hive {
    env: TestEnv,
    alpha: TestRepo,
    beta: TestRepo,
    node: NodeRepo,
    incoming: CanonicalOp,
}

/// `forgotten` says whether `alpha` forgets `beta`'s copy before it sends the work.
fn hive(forgotten: bool) -> Hive {
    let env = TestEnv::new();
    let alpha = env.init_repo_with_workspace("alpha", "a");
    let beta = env.init_repo_with_workspace("beta", "a");
    beta.jj(&[
        "workspace",
        "add",
        "--name",
        "b",
        env.root().join("second").to_str().unwrap(),
    ]);
    beta.jj(&["new", "-m", "beta's own work"]);
    beta.jj(&["bookmark", "create", "x", "-r", "@"]);
    let mut source = open(&alpha);
    let mut node = open(&beta);
    let initial = single_head(&mut source);
    transfer(&source, &mut node, &initial);
    node.advance(&initial).unwrap();
    let joined = single_head(&mut node);
    transfer(&node, &mut source, &joined);
    source.advance(&joined).unwrap();
    if forgotten {
        source.forget_copy(node.machine().key(), "beta").unwrap();
    }
    alpha.jj(&["new", "--no-edit", "-m", "remote work"]);
    alpha.jj(&[
        "workspace",
        "add",
        "--name",
        "c",
        env.root().join("alpha-c").to_str().unwrap(),
    ]);
    let incoming = single_head(&mut source);
    transfer(&source, &mut node, &incoming);
    Hive {
        env,
        alpha,
        beta,
        node,
        incoming,
    }
}

fn single_head(node: &mut NodeRepo) -> CanonicalOp {
    let heads = node.canonical_heads().unwrap();
    assert_eq!(heads.len(), 1, "{heads:?}");
    heads[0].clone()
}

/// What a `jj` command on `repo` does that moves a bookmark of its own: a new commit, and `x` on
/// it. Returns the commit `x` is on, which `.git` has too, since colocated commands export, and
/// the command's last operation.
fn late_command(repo: &TestRepo) -> (String, OperationId) {
    repo.jj(&["new", "-m", "late command"]);
    repo.jj(&["bookmark", "set", "x", "-r", "@"]);
    let commit = commit_of(repo, "x");
    assert_eq!(git_bookmark(repo, "x"), commit);
    let op = repo.jj(&[
        "--ignore-working-copy",
        "op",
        "log",
        "--no-graph",
        "-n",
        "1",
        "-T",
        "id",
    ]);
    (commit, OperationId::try_from_hex(op.trim()).unwrap())
}

/// What `Realize.lean` predicts once `realized` is published beside `read`, the op heads before
/// publication, checked with real jj (docs/internals/conformance.md, "Realization"). The oracle's
/// `realization` request answers, for the operations below them, `merge`, the operations whose
/// merge jj shows (`publish_shows_merge`), and `kept`, those that stay in the op log
/// (`log_kept`). jj itself then resolves op heads made of `merge`, in a store of their own, as
/// it would on loading them: `published`, the op head musubi published, must show the same, but
/// for this machine's record of `.git`, and every operation of `kept` must be in the op log now.
fn assert_shows_jj_merge(
    node: &NodeRepo,
    read: &[OperationId],
    realized: &LocalOp,
    published: &OperationId,
) {
    let store = node.loader.op_store();
    let root = store.root_operation_id().clone();
    // Number the operations parents first, the root 0.
    let mut numbers = HashMap::from([(root.clone(), 0)]);
    let mut ids = vec![root.clone()];
    let mut parents = vec![];
    let mut todo: Vec<_> = read
        .iter()
        .chain([&realized.0])
        .map(|id| (id.clone(), false))
        .collect();
    while let Some((id, ready)) = todo.pop() {
        if numbers.contains_key(&id) {
            continue;
        }
        let ps = store.read_operation(&id).block_on().unwrap().parents;
        if ready {
            numbers.insert(id.clone(), ids.len());
            parents.push(json!([
                ids.len(),
                ps.iter().map(|p| numbers[p]).collect::<Vec<_>>()
            ]));
            ids.push(id);
        } else {
            todo.push((id, true));
            todo.extend(ps.into_iter().map(|p| (p, false)));
        }
    }
    let request = json!({
        "op": "realization",
        "parents": parents,
        "heads": read.iter().map(|id| numbers[id]).collect::<Vec<_>>(),
        "realization": numbers[&realized.0],
    });
    let reply = Oracle::with(|oracle| oracle.call(&request));
    let ops = |key: &str| -> Vec<OperationId> {
        let numbers = reply[key].as_array().unwrap_or_else(|| panic!("{reply}"));
        numbers
            .iter()
            .map(|n| ids[usize::try_from(n.as_u64().unwrap()).unwrap()].clone())
            .collect()
    };
    let (merge, kept) = (ops("merge"), ops("kept"));

    let dir = musubi_testutil::tempdir();
    let heads = SimpleOpHeadsStore::init(dir.path(), &root).unwrap();
    for op in &merge {
        heads.update_op_heads(&[], op).block_on().unwrap();
    }
    if !merge.contains(&root) {
        heads
            .update_op_heads(&[root], &merge[0])
            .block_on()
            .unwrap();
    }
    let loader = &node.loader;
    let expected = resolve_op_heads(&heads, store, async |ops| {
        let merged = loader
            .merge_operations(ops, None, Some("reconcile divergent operations"), [])
            .await
            .map_err(|err| Box::new(err) as Box<dyn std::error::Error + Send + Sync>)?;
        Ok::<_, Box<dyn std::error::Error + Send + Sync>>(merged.0.operation().clone())
    })
    .block_on()
    .unwrap();
    // A merge that rewrites a commit records when it did, and one that gives a workspace a new
    // commit picks it a random change id, so another merge doing the same makes other ids:
    // commits are compared by change, description, tree and parents, and a change no input had
    // by its description, tree and parents.
    let commits = node.loader.store().clone();
    let view_of = |id: &OperationId| {
        let op = store.read_operation(id).block_on().unwrap();
        store.read_view(&op.view_id).block_on().unwrap()
    };
    let mut known = BTreeSet::new();
    for id in &ids {
        let view = view_of(id);
        let named = view
            .local_bookmarks
            .values()
            .flat_map(|t| t.iter().flatten().cloned());
        for c in view
            .head_ids
            .iter()
            .cloned()
            .chain(view.wc_commit_ids.values().cloned())
            .chain(named)
        {
            known.insert(commits.get_commit(&c).unwrap().change_id().clone());
        }
    }
    fn key(
        commits: &Arc<jj_lib::store::Store>,
        known: &BTreeSet<jj_lib::backend::ChangeId>,
        id: &CommitId,
    ) -> String {
        let commit = commits.get_commit(id).unwrap();
        let tree = format!("{:?}", commit.store_commit().root_tree);
        let parents: Vec<_> = commit
            .parent_ids()
            .iter()
            .filter(|p| *p != commits.root_commit_id())
            .map(|p| key(commits, known, p))
            .collect();
        let change = if known.contains(commit.change_id()) {
            commit.change_id().hex()
        } else {
            "new".to_owned()
        };
        format!("{change} {:?} {tree} on {parents:?}", commit.description())
    }
    let commit = |id: &CommitId| key(&commits, &known, id);
    let target = |target: &RefTarget| -> Vec<_> {
        target
            .iter()
            .map(|term| term.as_ref().map(commit))
            .collect()
    };
    let shared = |op: &OperationId| {
        let view = view_of(op);
        let mut heads: Vec<_> = view.head_ids.iter().map(commit).collect();
        heads.sort();
        let bookmarks: Vec<_> = view
            .local_bookmarks
            .iter()
            .map(|(n, t)| (n.clone(), target(t)))
            .collect();
        let tags: Vec<_> = view
            .local_tags
            .iter()
            .map(|(n, t)| (n.clone(), target(t)))
            .collect();
        let remotes: Vec<_> = view
            .remote_views
            .iter()
            .filter(|(name, _)| name.as_str() != REMOTE_NAME_FOR_LOCAL_GIT_REPO.as_str())
            .flat_map(|(remote, refs)| {
                refs.bookmarks.iter().map(move |(n, r)| {
                    (
                        remote.clone(),
                        n.clone(),
                        target(&r.target),
                        format!("{:?}", r.state),
                    )
                })
            })
            .collect();
        let workspaces: Vec<_> = view
            .wc_commit_ids
            .iter()
            .map(|(n, c)| (n.clone(), commit(c)))
            .collect();
        format!("{heads:#?}\n{bookmarks:#?}\n{tags:#?}\n{remotes:#?}\n{workspaces:#?}")
    };
    assert_eq!(shared(published), shared(expected.id()), "{request}");
    let log = reachable(node);
    for op in kept {
        assert!(
            log.contains(&LocalOp(op.clone())),
            "{} left the op log",
            op.hex()
        );
    }
}

/// A `jj` command that finishes after the realization was prepared, or while it is, is not
/// lost. The first op head `advance` publishes already has the command's operation in its
/// history, beside the received work: the code finds out the op heads moved when it takes the
/// publication locks, and prepares again, as published as it was, the realization would
/// leave the command's operation to a second op head that the cleanup after publication merges,
/// with `.git` in between holding the bookmark where the realization had it. Afterwards the one
/// op head has the command's operations and its bookmark move, `.git` agrees, a later `jj`
/// command moves nothing back, and the workspaces keep their commits.
#[test]
fn a_command_finishing_before_publication_is_merged_and_exported() {
    for (forgotten, meanwhile) in [(false, false), (false, true), (true, false), (true, true)] {
        let mut hive = hive(forgotten);
        let before = hive.node.local_heads().unwrap();
        let a_before = commit_of(&hive.beta, "a@");
        let b_before = commit_of(&hive.beta, "b@");
        let command = hive.beta.another_copy(hive.beta.path());
        let moved = Arc::new(Mutex::new(None));
        let stores = interpose(&mut hive.node);
        // Whether the first op head published has the command's operation behind it.
        let published = Arc::new(Mutex::new(vec![]));
        let updates = Arc::new(Mutex::new(vec![]));
        let (seen, ran, plain) = (published.clone(), moved.clone(), hive.node.loader.clone());
        let updated = updates.clone();
        stores.before_update(move |new| {
            updated.lock().unwrap().push(new.clone());
            let Some((_, op)) = &*ran.lock().unwrap() else {
                return seen.lock().unwrap().push(false);
            };
            let mut todo = vec![new.clone()];
            let mut history = BTreeSet::new();
            while let Some(id) = todo.pop() {
                if history.insert(id.clone()) {
                    todo.extend(
                        plain
                            .op_store()
                            .read_operation(&id)
                            .block_on()
                            .unwrap()
                            .parents,
                    );
                }
            }
            seen.lock().unwrap().push(history.contains(op));
        });
        if meanwhile {
            let moved = moved.clone();
            stores.before_write(move || *moved.lock().unwrap() = Some(late_command(&command)));
        } else {
            hive.node.realize(&hive.incoming).unwrap();
            *moved.lock().unwrap() = Some(late_command(&command));
        }
        hive.node.advance(&hive.incoming).unwrap();
        let (moved, command) = moved.lock().unwrap().clone().expect("the command ran");
        let realized = hive.node.local_of(&hive.incoming).unwrap();
        let mut read: Vec<_> = before.iter().map(|op| op.0.clone()).collect();
        read.push(command);
        assert_shows_jj_merge(&hive.node, &read, &realized, &updates.lock().unwrap()[0]);
        let published = published.lock().unwrap().clone();
        assert_eq!(
            published.first(),
            Some(&true),
            "forgotten: {forgotten}, meanwhile: {meanwhile}: the first head published lacks the command's operation"
        );

        let heads = hive.node.local_heads().unwrap();
        assert_eq!(
            heads.len(),
            1,
            "forgotten: {forgotten}, meanwhile: {meanwhile}"
        );
        let repo = hive.node.repo_at(&heads[0]).unwrap();
        let x = repo.view().get_local_bookmark(RefName::new("x"));
        assert_eq!(
            x.as_normal().unwrap().hex(),
            moved,
            "forgotten: {forgotten}, meanwhile: {meanwhile}"
        );
        assert_eq!(git_bookmark(&hive.beta, "x"), moved);
        let wc = |name| repo.view().get_wc_commit_id(WorkspaceName::new(name));
        // The command's `jj new` moved `a`, the workspace it ran in, and only that, unless
        // the hive forgot this copy: it takes new working copies then.
        assert_ne!(wc("a").unwrap().hex(), a_before);
        if forgotten {
            assert!(wc("b").is_some());
        } else {
            assert_eq!(wc("b").unwrap().hex(), b_before);
        }
        assert!(wc("alpha/a").is_some());
        assert!(!commit_of(&hive.beta, "description(substring:\"remote work\")").is_empty());
        // Every operation of the command is in the history of the op head.
        let history = hive.beta.jj(&[
            "--ignore-working-copy",
            "op",
            "log",
            "--no-graph",
            "-T",
            r#"description.first_line() ++ "\n""#,
        ]);
        assert!(history.contains("new empty commit"), "{history}");
        assert!(history.contains("point bookmark x"), "{history}");

        let before = local_bookmarks(&hive.beta);
        hive.beta.jj(&["status"]);
        hive.beta.jj(&["git", "import"]);
        assert_eq!(local_bookmarks(&hive.beta), before);
        assert_eq!(git_bookmark(&hive.beta, "x"), moved);
    }
}

/// Another machine's workspace is shown clear of the names of this machine's own, so a
/// workspace the user named `alpha/c` is theirs, not alpha's, however the race goes. Prepared
/// before the workspace existed, the realization shows alpha's as `alpha/c`, which merged with
/// the user's would be one workspace to jj: the user's directory would snapshot into alpha's
/// working copy.
#[test]
fn a_workspace_named_like_another_machines_stays_this_machines() {
    for prepared_first in [false, true] {
        let mut hive = hive(false);
        let alpha_working_copy = commit_of(&hive.alpha, "c@");
        if prepared_first {
            hive.node.realize(&hive.incoming).unwrap();
        }
        hive.beta.jj(&[
            "workspace",
            "add",
            "--name",
            "alpha/c",
            hive.env.root().join("clash").to_str().unwrap(),
        ]);
        let own = commit_of(&hive.beta, "alpha/c@");
        let before: Vec<_> = ["a", "b"]
            .map(|name| commit_of(&hive.beta, &format!("{name}@")))
            .into();
        hive.node.advance(&hive.incoming).unwrap();

        let heads = hive.node.local_heads().unwrap();
        assert_eq!(heads.len(), 1, "prepared first: {prepared_first}");
        let repo = hive.node.repo_at(&heads[0]).unwrap();
        let workspaces = repo.view().wc_commit_ids();
        assert_eq!(
            workspaces[WorkspaceName::new("alpha/c")].hex(),
            own,
            "prepared first: {prepared_first}: {workspaces:?}"
        );
        for (name, before) in ["a", "b"].into_iter().zip(&before) {
            assert_eq!(workspaces[WorkspaceName::new(name)].hex(), *before);
        }
        let alpha_name = workspaces
            .iter()
            .find(|(_, commit)| commit.hex() == alpha_working_copy)
            .map(|(name, _)| name.as_str().to_owned())
            .expect("alpha's workspace is still shown");
        assert!(alpha_name.contains("alpha"), "{alpha_name}");
        assert_ne!(alpha_name, "alpha/c");
    }
}

/// A second head arriving while `merge_heads` looks at the op heads is merged and exported
/// as one that was there at the start: the bookmark the merge rebases is moved in `.git`
/// before any `jj` command can import it from the old place, which would move it back.
#[test]
fn merge_heads_exports_when_a_second_head_arrives() {
    for arrives_meanwhile in [false, true] {
        let env = TestEnv::new();
        let repo = env.init_repo("alpha");
        repo.jj(&["describe", "-m", "base"]);
        let base = commit_of(&repo, "@");
        let old = repo
            .jj(&["op", "log", "--no-graph", "-n", "1", "-T", "id"])
            .trim()
            .to_owned();
        repo.jj(&["new", "-m", "topic"]);
        repo.jj(&["bookmark", "create", "topic", "-r", "@"]);
        let mut node = open(&repo);
        let before = git_bookmark(&repo, "topic");
        let command = repo.another_copy(repo.path());
        // Rewrites `base`, under `topic`, in an operation that doesn't know `topic`.
        let rewrite = move || {
            command.jj(&[
                "--ignore-working-copy",
                "--at-op",
                &old,
                "describe",
                "-r",
                &base,
                "-m",
                "base rewritten",
            ]);
        };
        if arrives_meanwhile {
            let stores = interpose(&mut node);
            // The read that finds the head to load, after the first found there is one. This
            // counts reads, so the test fails, not passes, if `merged_repo` reads another way:
            // without the second head arriving, the merge it expects doesn't happen.
            stores.before_read(2, rewrite);
        } else {
            rewrite();
        }
        let merged = node.merge_heads().unwrap();

        let heads = node.local_heads().unwrap();
        assert_eq!(heads, [merged], "arrives meanwhile: {arrives_meanwhile}");
        let loaded = node.repo_at(&heads[0]).unwrap();
        let topic = loaded.view().get_local_bookmark(RefName::new("topic"));
        let target = topic.as_normal().unwrap().hex();
        assert_ne!(target, before, "the merge rebases the bookmark");
        assert_eq!(
            git_bookmark(&repo, "topic"),
            target,
            "arrives meanwhile: {arrives_meanwhile}"
        );
        repo.jj(&["--ignore-working-copy", "git", "import"]);
        assert_eq!(commit_of(&repo, "topic"), target);
    }
}

/// `.git` has every bookmark of the op head `advance` publishes by the time it publishes it:
/// a `jj` command that loads the new head before then would import the old ones from `.git`
/// as moves, and move them back. Observed where jj's op-heads store would show the head.
#[test]
fn advance_exports_the_merge_before_publishing_it() {
    for colocated in [true, false] {
        let (env, incoming) = fixture(colocated);
        let beta = env.repo_handle("beta");
        let mut node = open(&beta);
        let old_left = colocated.then(|| git_bookmark(&beta, "left"));
        let stores = interpose(&mut node);
        let seen = Arc::new(Mutex::new(vec![]));
        let visible = seen.clone();
        let plain = node.loader.clone();
        let path = beta.path().to_owned();
        stores.before_update(move |new| {
            let op = plain.load_operation(new).block_on().unwrap();
            let repo = plain.load_at(&op).block_on().unwrap();
            let mut mismatched = vec![];
            for (name, target) in repo.view().local_bookmarks() {
                let git = gix::open(&path)
                    .ok()
                    .and_then(|git| {
                        git.find_reference(&format!("refs/heads/{}", name.as_str()))
                            .ok()
                            .map(|reference| reference.target().id().to_string())
                    })
                    .unwrap_or_default();
                if git != target.as_normal().unwrap().hex() {
                    mismatched.push(name.as_str().to_owned());
                }
            }
            visible.lock().unwrap().push(mismatched);
        });
        let published = node.advance(&incoming).unwrap();
        let seen = seen.lock().unwrap();
        assert!(!seen.is_empty(), "the op heads are updated");
        if colocated {
            assert!(
                seen.iter().all(|mismatched| mismatched.is_empty()),
                "bookmarks not yet in .git when published: {seen:?}"
            );
            let heads = node.local_heads().unwrap();
            assert_exported(&node, &beta, &heads[0], old_left.as_ref().unwrap());
        }
        assert_eq!(node.canonicalize(&published).unwrap(), incoming);
    }
}

/// Publication interrupted between putting the new op head in and taking the old ones out
/// loses no operation, and realization resumed after a restart converges on one head with
/// everything: jj's op-heads store puts a head in before it takes any out, so an interruption
/// leaves extra heads, not fewer. Here taking out one old head fails, as its removal would if
/// the process died first; the head is a directory, which `remove_file` refuses. Colocated only:
/// without `.git` to export, `advance` takes out what it replaces by another route, and the
/// stuck head, one of two concurrent heads, is not among what it takes out.
#[test]
fn publication_interrupted_before_the_old_heads_go_loses_nothing() {
    {
        let colocated = true;
        let (env, incoming) = fixture(colocated);
        let beta = env.repo_handle("beta");
        let mut node = open(&beta);
        let old = reachable(&node);
        let old_left = colocated.then(|| git_bookmark(&beta, "left"));
        let old_heads = node.local_heads().unwrap();
        assert_eq!(old_heads.len(), 2);
        let stuck = beta
            .repo_path()
            .join("op_heads/heads")
            .join(old_heads[0].0.hex());
        std::fs::remove_file(&stuck).unwrap();
        std::fs::create_dir(&stuck).unwrap();

        let error = node.advance(&incoming).unwrap_err();
        assert!(format!("{error:?}").contains("OpHeads"), "{error:?}");
        // Read before any jj command or musubi merge could repair the heads.
        let heads: BTreeSet<_> = node.local_heads().unwrap().into_iter().collect();
        assert!(heads.contains(&old_heads[0]));
        assert!(
            heads.len() > 1,
            "the new head went in beside the old: {heads:?}"
        );
        let kept = reachable(&node);
        assert!(old.is_subset(&kept), "no operation lost");
        assert!(kept.contains(&node.local_of(&incoming).unwrap()));
        drop(node);

        // The restart: the head is a file again, as it was.
        std::fs::remove_dir(&stuck).unwrap();
        std::fs::write(&stuck, "").unwrap();
        let mut node = open(&beta);
        node.advance(&incoming).unwrap();
        let heads = node.local_heads().unwrap();
        assert_eq!(heads.len(), 1, "colocated: {colocated}");
        let kept = reachable(&node);
        assert!(old.is_subset(&kept), "no operation lost");
        assert_eq!(
            node.canonicalize(&node.local_of(&incoming).unwrap())
                .unwrap(),
            incoming
        );
        if colocated {
            assert_exported(&node, &beta, &heads[0], old_left.as_ref().unwrap());
        }
        // Where an uninterrupted run would end.
        let read: Vec<_> = old_heads.iter().map(|op| op.0.clone()).collect();
        assert_shows_jj_merge(
            &node,
            &read,
            &node.local_of(&incoming).unwrap(),
            &heads[0].0,
        );
        let before = local_bookmarks(&beta);
        beta.jj(&["--ignore-working-copy", "git", "import"]);
        assert_eq!(
            local_bookmarks(&beta),
            before,
            "import must not revert a bookmark"
        );
    }
}

/// An operation realized ahead of its parent keeps what exporting the parent did. The parent is
/// published, and exported, before its child is: the child was rendered against the parent's
/// unpublished realization, which publication replaced, so it is rendered again from the
/// published one, with its Git record. Reusing the old rendering's record would leave the
/// bookmark the parent exported out of it, and the next import would move the bookmark.
#[test]
fn a_child_realized_ahead_of_its_published_parent_keeps_the_parents_exports() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    alpha.jj(&["describe", "-m", "shared base"]);
    let mut source = open(&alpha);
    let mut node = open(&beta);
    let base = single_head(&mut source);
    transfer(&source, &mut node, &base);
    node.advance(&base).unwrap();
    alpha.jj(&["bookmark", "create", "x", "-r", "@"]);
    let first = single_head(&mut source);
    alpha.jj(&["new", "-m", "second"]);
    alpha.jj(&["bookmark", "set", "x", "-r", "@"]);
    let second = single_head(&mut source);
    transfer(&source, &mut node, &second);
    node.realize(&first).unwrap();
    node.realize(&second).unwrap();
    node.advance(&first).unwrap();
    node.advance(&second).unwrap();

    let moved = commit_of(&alpha, "x");
    assert_eq!(commit_of(&beta, "x"), moved);
    assert_eq!(git_bookmark(&beta, "x"), moved);
    let before = local_bookmarks(&beta);
    beta.jj(&["--ignore-working-copy", "git", "import"]);
    assert_eq!(
        local_bookmarks(&beta),
        before,
        "import must not move a bookmark"
    );
}

/// Promise 6 says realization never moves your workspace, except when you moved it two ways at
/// once, where jj's own tie-break decides, as it would without musubi. Two op heads of this
/// machine's move its workspace `a` apart: a command, then one run `--at-op` on the operation
/// before it. jj, merging them, keeps the move of the one that ended first. musubi then publishes
/// a realization of another machine's later work on the first, which jj puts in its place;
/// merged with the second, in the order they ended, the realization, which carries the other
/// machine's later end time, comes last, and jj keeps the second's move instead. That is jj's
/// rule, the same as plain jj with a later operation from another workspace, and what
/// `Realize.lean`'s `publish_shows_merge` says; `own_workspace_kept` excludes it, since the
/// second op head doesn't descend from the realization's parent.
#[test]
fn a_workspace_moved_two_ways_follows_jjs_tie_break_after_realization() {
    let env = TestEnv::new();
    let alpha = env.init_repo_with_workspace("alpha", "a");
    let beta = env.init_repo_with_workspace("beta", "a");
    let mut source = open(&alpha);
    let mut node = open(&beta);
    let initial = single_head(&mut source);
    transfer(&source, &mut node, &initial);
    node.advance(&initial).unwrap();
    let joined = single_head(&mut node);
    transfer(&node, &mut source, &joined);
    source.advance(&joined).unwrap();
    let [base] = node.local_heads().unwrap().try_into().unwrap();
    beta.jj(&["new", "-m", "x"]);
    let published = single_head(&mut node);
    transfer(&node, &mut source, &published);
    source.advance(&published).unwrap();
    beta.jj(&["--at-op", &base.0.hex(), "new", "-m", "y"]);
    assert_eq!(node.local_heads().unwrap().len(), 2);
    alpha.jj(&["new", "--no-edit", "-m", "remote work"]);
    let incoming = single_head(&mut source);
    transfer(&source, &mut node, &incoming);
    let described = |repo: &Arc<jj_lib::repo::ReadonlyRepo>| {
        let commit = repo
            .view()
            .get_wc_commit_id(WorkspaceName::new("a"))
            .unwrap();
        repo.store()
            .get_commit(commit)
            .unwrap()
            .description()
            .to_owned()
    };
    // What jj shows before the realization: its merge of the two keeps `x`, which ended first.
    let mut heads: Vec<_> = node
        .local_heads()
        .unwrap()
        .iter()
        .map(|head| node.loader.load_operation(&head.0).block_on().unwrap())
        .collect();
    heads.sort_by_key(|op| op.metadata().time.end.timestamp);
    let (before, _) = node
        .loader
        .merge_operations(heads, None, None, [])
        .block_on()
        .unwrap();
    assert_eq!(described(&before), "x\n");
    node.advance(&incoming).unwrap();
    let head = node.merge_heads().unwrap();
    let after = node.repo_at(&head).unwrap();
    assert_eq!(
        described(&after),
        "y\n",
        "jj's tie-break keeps the move that ended last, as without musubi"
    );
}
