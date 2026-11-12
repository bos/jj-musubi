//! Late store failures after the merge preflight, through the shipping advance path.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeSet;
use std::fs;
use std::os::unix::fs::PermissionsExt as _;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::SystemTime;

use async_trait::async_trait;
use jj_lib::object_id::HexPrefix;
use jj_lib::object_id::ObjectId as _;
use jj_lib::object_id::PrefixResolution;
use jj_lib::op_store::OpStore;
use jj_lib::op_store::OpStoreError;
use jj_lib::op_store::OpStoreResult;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::repo::RepoLoader;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use pollster::FutureExt as _;

use super::super::NodeRepo;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;

#[derive(Debug, Default)]
struct Writes {
    merges: usize,
    failures: usize,
}

/// Delegates to the real simple op store, denying writes only while a selected late merge
/// is written. Reads, exports, head publication and both preflight merges remain real.
#[derive(Debug)]
struct LateMergeError {
    inner: Arc<dyn OpStore>,
    operations: PathBuf,
    once: bool,
    writes: Mutex<Writes>,
}

struct RestorePermissions(PathBuf, fs::Permissions);

impl Drop for RestorePermissions {
    fn drop(&mut self) {
        fs::set_permissions(&self.0, self.1.clone()).unwrap();
    }
}

#[async_trait]
impl OpStore for LateMergeError {
    fn name(&self) -> &str {
        self.inner.name()
    }

    fn root_operation_id(&self) -> &OperationId {
        self.inner.root_operation_id()
    }

    async fn read_view(&self, id: &ViewId) -> OpStoreResult<View> {
        self.inner.read_view(id).await
    }

    async fn write_view(&self, view: &View) -> OpStoreResult<ViewId> {
        self.inner.write_view(view).await
    }

    async fn read_operation(&self, id: &OperationId) -> OpStoreResult<StoreOperation> {
        self.inner.read_operation(id).await
    }

    async fn write_operation(&self, op: &StoreOperation) -> OpStoreResult<OperationId> {
        let deny = {
            let mut writes = self.writes.lock().unwrap();
            if op.metadata.description == "reconcile divergent operations" {
                writes.merges += 1;
                // check_mergeable writes the same merge in both parent orders first.
                writes.merges > 2 && (!self.once || writes.failures == 0)
            } else {
                false
            }
        };
        if !deny {
            return self.inner.write_operation(op).await;
        }
        let permissions = fs::metadata(&self.operations).unwrap().permissions();
        let _restore = RestorePermissions(self.operations.clone(), permissions.clone());
        fs::set_permissions(
            &self.operations,
            fs::Permissions::from_mode(permissions.mode() & !0o222),
        )
        .unwrap();
        let result = self.inner.write_operation(op).await;
        let err = result.as_ref().unwrap_err();
        assert!(matches!(
            err,
            OpStoreError::WriteObject {
                object_type: "operation",
                ..
            }
        ));
        let mut cause: &(dyn std::error::Error + 'static) = err;
        while let Some(source) = cause.source() {
            cause = source;
        }
        assert_eq!(
            cause.downcast_ref::<std::io::Error>().unwrap().kind(),
            std::io::ErrorKind::PermissionDenied,
        );
        self.writes.lock().unwrap().failures += 1;
        result
    }

    async fn resolve_operation_id_prefix(
        &self,
        prefix: &HexPrefix,
    ) -> OpStoreResult<PrefixResolution<OperationId>> {
        self.inner.resolve_operation_id_prefix(prefix).await
    }

    async fn gc(&self, heads: &[OperationId], newer: SystemTime) -> OpStoreResult<()> {
        self.inner.gc(heads, newer).await
    }
}

fn open(repo: &TestRepo) -> NodeRepo {
    NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap()
}

/// No helper here loads at the op heads: reachability must be observed before jj repairs it.
fn reachable(node: &NodeRepo) -> BTreeSet<LocalOp> {
    let mut seen = BTreeSet::new();
    let mut todo = node.local_heads().unwrap();
    while let Some(op) = todo.pop() {
        if seen.insert(op.clone()) {
            let op = node
                .loader
                .op_store()
                .read_operation(&op.0)
                .block_on()
                .unwrap();
            node.loader
                .op_store()
                .read_view(&op.view_id)
                .block_on()
                .unwrap();
            todo.extend(op.parents.into_iter().map(LocalOp));
        }
    }
    seen
}

fn git_bookmark(repo: &TestRepo, name: &str) -> String {
    let git = gix::open(repo.path()).unwrap();
    git.find_reference(&format!("refs/heads/{name}"))
        .unwrap()
        .target()
        .try_id()
        .unwrap()
        .to_string()
}

fn assert_exported(node: &NodeRepo, repo: &TestRepo, head: &LocalOp, old_left: &str) {
    let merged = node.repo_at(head).unwrap();
    assert_ne!(git_bookmark(repo, "left"), old_left);
    for name in ["left", "right", "incoming", "main"] {
        let target = merged
            .view()
            .get_local_bookmark(jj_lib::ref_name::RefName::new(name));
        assert_eq!(git_bookmark(repo, name), target.as_normal().unwrap().hex());
    }
}

fn transfer(from: &NodeRepo, to: &mut NodeRepo, head: &CanonicalOp) {
    let dir = musubi_testutil::tempdir();
    let ops = from
        .canonical
        .ancestors_until(std::slice::from_ref(head), |_| false)
        .unwrap();
    let bundle = dir.path().join("operations");
    from.canonical.export_operations(&ops, &bundle).unwrap();
    to.canonical.import_operations(&bundle).unwrap();
    let commits: Vec<_> = from.required_commits(&ops).unwrap().into_iter().collect();
    let objects = dir.path().join("objects");
    from.object_store()
        .unwrap()
        .export(&commits, &[], &objects)
        .unwrap();
    to.object_store()
        .unwrap()
        .import(&objects, &commits, &[])
        .unwrap();
    to.reload().unwrap();
}

fn fixture(colocated: bool) -> (TestEnv, CanonicalOp) {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = if colocated {
        env.init_repo("beta")
    } else {
        env.init_non_colocated_repo("beta")
    };
    a.jj(&["describe", "-m", "shared base"]);
    a.jj(&["bookmark", "create", "main", "-r", "@"]);
    let mut source = open(&a);
    let shared = source.canonical_heads().unwrap().pop().unwrap();
    let mut node = open(&b);
    transfer(&source, &mut node, &shared);
    node.advance(&shared).unwrap();
    let base = node.local_heads().unwrap().pop().unwrap();
    b.jj(&["--ignore-working-copy", "new", "main", "-m", "local child"]);
    b.jj(&[
        "--ignore-working-copy",
        "bookmark",
        "create",
        "left",
        "-r",
        "@",
    ]);
    if colocated {
        // Commands ignoring the working copy need not export Git refs automatically.
        b.jj(&["--ignore-working-copy", "git", "export"]);
    }
    b.jj(&[
        "--ignore-working-copy",
        "--at-op",
        &base.0.hex(),
        "bookmark",
        "create",
        "right",
        "-r",
        "main",
    ]);
    // Merging the incoming rewrite must rebase the local child and move left in .git.
    a.jj(&["describe", "-r", "main", "-m", "remote rewrite"]);
    a.jj(&["bookmark", "create", "incoming", "-r", "main"]);
    let incoming = source.canonical_heads().unwrap().pop().unwrap();
    transfer(&source, &mut node, &incoming);
    node.realize(&incoming).unwrap();
    drop((source, node));
    (env, incoming)
}

/// A failed late merge may already have advanced the heads. A retry must retain both histories
/// and export the eventual merge before a colocated jj command can import the refs again.
#[test]
fn late_merge_store_errors_preserve_heads_and_recover() {
    // Root can write through mode bits; don't turn a missing fault into false coverage.
    let probe = musubi_testutil::tempdir();
    let permissions = fs::metadata(probe.path()).unwrap().permissions();
    fs::set_permissions(probe.path(), fs::Permissions::from_mode(0o555)).unwrap();
    let denied = fs::write(probe.path().join("probe"), "");
    fs::set_permissions(probe.path(), permissions).unwrap();
    if denied.is_ok() {
        eprintln!("skipping late store failure: directory mode bits do not deny writes");
        return;
    }
    assert_eq!(
        denied.unwrap_err().kind(),
        std::io::ErrorKind::PermissionDenied
    );

    for colocated in [true, false] {
        let (env, incoming) = fixture(colocated);
        let saved = musubi_testutil::tempdir();
        env.save(saved.path());
        drop(env);
        for once in if colocated {
            &[true, false][..]
        } else {
            &[false][..]
        } {
            let env = TestEnv::restore(saved.path());
            let b = env.repo_handle("beta");
            let mut node = open(&b);
            let old = reachable(&node);
            let old_left = if colocated {
                Some(git_bookmark(&b, "left"))
            } else {
                None
            };
            let old_heads: BTreeSet<_> = node.local_heads().unwrap().into_iter().collect();
            assert_eq!(old_heads.len(), 2);
            let faults = Arc::new(LateMergeError {
                inner: node.loader.op_store().clone(),
                operations: b.repo_path().join("op_store/operations"),
                once: *once,
                writes: Mutex::new(Writes::default()),
            });
            let loader = &node.loader;
            node.loader = RepoLoader::new(
                loader.settings().clone(),
                loader.store().clone(),
                loader.workspace_store().clone(),
                faults.clone(),
                loader.op_heads_store().clone(),
                loader.index_store().clone(),
                loader.submodule_store().clone(),
            );
            let result = node.advance(&incoming);
            // Observe raw heads immediately, before canonical_heads, merge_heads or a command.
            let heads: BTreeSet<_> = node.local_heads().unwrap().into_iter().collect();
            let realization = node.local_of(&incoming).unwrap();
            if *once {
                assert_eq!(result.unwrap(), realization);
                assert_eq!(heads.len(), 1);
                assert!(!heads.contains(&realization));
                let head = heads.first().unwrap();
                let parents = node
                    .loader
                    .op_store()
                    .read_operation(&head.0)
                    .block_on()
                    .unwrap()
                    .parents;
                assert_eq!(parents.len(), old_heads.len() + 1);
                assert_eq!(
                    parents.into_iter().map(LocalOp).collect::<BTreeSet<_>>(),
                    old_heads
                        .iter()
                        .cloned()
                        .chain([realization.clone()])
                        .collect()
                );
                assert_exported(&node, &b, head, old_left.as_ref().unwrap());
            } else {
                let err = result.unwrap_err();
                assert!(format!("{err:?}").contains("PermissionDenied"), "{err:?}");
                assert_eq!(
                    heads,
                    old_heads
                        .iter()
                        .cloned()
                        .chain([realization.clone()])
                        .collect()
                );
            }
            assert_eq!(
                faults.writes.lock().unwrap().failures,
                if colocated && !once { 2 } else { 1 },
            );
            let retained = reachable(&node);
            assert!(old.is_subset(&retained));
            assert!(retained.contains(&realization));
            assert_eq!(node.canonicalize(&realization).unwrap(), incoming);
            drop(node);

            // The daemon reopens after an error. No jj command repairs the split heads first.
            let mut node = open(&b);
            node.advance(&incoming).unwrap();
            let merged = node.local_heads().unwrap();
            assert_eq!(merged.len(), 1);
            let retained = reachable(&node);
            assert!(old.is_subset(&retained));
            assert!(retained.contains(&realization));
            let head = node.canonicalize(&merged[0]).unwrap();
            let a = env.repo_handle("alpha");
            let mut source = open(&a);
            transfer(&node, &mut source, &head);
            source.advance(&head).unwrap();
            assert_eq!(source.canonical_heads().unwrap(), vec![head.clone()]);
            assert_eq!(node.canonical_heads().unwrap(), vec![head]);
            if colocated {
                assert_exported(&node, &b, &merged[0], old_left.as_ref().unwrap());
            }
            let before = node.canonical_heads().unwrap();
            b.jj(&["--ignore-working-copy", "git", "import"]);
            assert_eq!(
                node.canonical_heads().unwrap(),
                before,
                "colocated import must not revert a bookmark"
            );
        }
    }
}
