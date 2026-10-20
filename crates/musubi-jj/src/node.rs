//! A node's local jj repository: canonicalization, realization, and op heads.
//!
//! See "Per-machine state in a replicated view" in docs/design.md and "Translation layer" in
//! docs/protocol.md.

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use jj_lib::content_hash::blake2b_hash;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::git::GitExportError;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::lock::FileLock;
use jj_lib::lock::FileLockError;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_heads_store::OpHeadsStoreError;
use jj_lib::op_store::OpStoreError;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::RemoteRef;
use jj_lib::op_store::RemoteRefState;
use jj_lib::op_store::RemoteView;
use jj_lib::op_store::View;
use jj_lib::op_walk;
use jj_lib::ref_name::GitRefNameBuf;
use jj_lib::ref_name::RefNameBuf;
use jj_lib::ref_name::RemoteName;
use jj_lib::ref_name::RemoteNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::repo::RepoLoaderError;
use jj_lib::repo::StoreLoadError;
use jj_lib::settings::UserSettings;
use jj_lib::simple_op_store::SimpleOpStore;
use pollster::FutureExt as _;
use thiserror::Error;

use std::collections::BTreeSet;

use jj_lib::backend::BackendError;
use jj_lib::backend::CommitId;
use jj_lib::backend::Timestamp;
use jj_lib::op_store::OperationMetadata;
use jj_lib::op_store::TimestampRange;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;

use crate::canonical::CanonicalError;
use crate::canonical::CanonicalStore;
use crate::canonical::strip_git_records;
use crate::format_guard;
use crate::format_guard::FormatError;
use crate::objects;
use crate::objects::GitStore;
use crate::objects::ObjectError;
use crate::objects::ObjectStore;
use crate::objects::SimpleStore;
use crate::translation_map::TranslationMap;
use crate::workspaces;
use crate::workspaces::Machine;

/// The operation attribute naming the canonical operation a realization represents.
pub const CANONICAL_ATTRIBUTE: &str = "musubi.canonical";

#[derive(Debug, Error)]
pub enum NodeError {
    #[error("failed to load repository")]
    Load(#[from] StoreLoadError),
    #[error("unsupported op store {0:?}; musubi needs simple_op_store")]
    UnsupportedOpStore(String),
    #[error(transparent)]
    OpStore(#[from] OpStoreError),
    #[error(transparent)]
    OpHeads(#[from] OpHeadsStoreError),
    #[error(transparent)]
    RepoLoader(#[from] RepoLoaderError),
    /// A jj 0.46 bug, until jj fixes it: jj cannot merge concurrent operations when the
    /// merge would rebase a merge commit onto the root commit, and until then every jj
    /// command fails to load the repository (docs/races.md, "Known jj limitations").
    #[error(
        "jj cannot merge this machine's concurrent operations: the merge would create a merge \
         commit on the root commit (a jj bug). On this machine, run `jj --at-op <head> op log \
         -n1` for each head in .jj/repo/op_heads/heads, then `jj --at-op <head> op revert @` \
         at the head whose operation made the merge commit"
    )]
    RootParentMerge(#[source] RepoLoaderError),
    #[error(transparent)]
    Canonical(#[from] CanonicalError),
    #[error("operation {op}: {source}")]
    Format { op: String, source: FormatError },
    #[error(transparent)]
    GitExport(#[from] GitExportError),
    #[error(transparent)]
    Lock(#[from] FileLockError),
    #[error("I/O error on {path}")]
    Io { path: PathBuf, source: io::Error },
    #[error("canonical operation {0} is not realized and cannot be: {1}")]
    NotRealizable(String, &'static str),
    #[error("operation {op} names canonical operation {canonical}, which is not stored")]
    DanglingAttribute { op: String, canonical: String },
    #[error(
        "operation {op} realizes canonical operation {canonical} but no longer has its parents \
         (was `jj op abandon` run?); musubi does not replicate op abandon yet, so replication is \
         paused for this repository"
    )]
    RewrittenRealization { op: String, canonical: String },
    #[error(transparent)]
    Objects(#[from] ObjectError),
    #[error(transparent)]
    Backend(#[from] BackendError),
    #[error("musubi supports the git and simple backends, not {0:?}")]
    UnsupportedBackend(String),
    #[error(transparent)]
    CheckOut(#[from] jj_lib::repo::CheckOutCommitError),
    #[error("index error: {0}")]
    Index(String),
    #[error(transparent)]
    Commit(#[from] jj_lib::transaction::TransactionCommitError),
}

/// Per-machine fields of a view: this machine's record of its own `.git` (`git_refs` and the
/// `git` pseudo-remote) and its own workspaces (`wc_commit_ids` and `git_heads`). See
/// "Per-machine state in a replicated view" in docs/design.md.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct PerMachine {
    git_refs: BTreeMap<GitRefNameBuf, RefTarget>,
    git_remote: Option<RemoteView>,
    wc_commit_ids: BTreeMap<WorkspaceNameBuf, CommitId>,
    git_heads: BTreeMap<WorkspaceNameBuf, RefTarget>,
}

impl PerMachine {
    fn of(view: &View) -> Self {
        Self {
            git_refs: view.git_refs.clone(),
            git_remote: view
                .remote_views
                .get(REMOTE_NAME_FOR_LOCAL_GIT_REPO)
                .cloned(),
            wc_commit_ids: view.wc_commit_ids.clone(),
            git_heads: view.git_heads.clone(),
        }
    }

    fn apply_to(self, view: &mut View) {
        view.git_refs = self.git_refs;
        if let Some(remote) = self.git_remote {
            view.remote_views
                .insert(REMOTE_NAME_FOR_LOCAL_GIT_REPO.to_owned(), remote);
        }
        view.wc_commit_ids = self.wc_commit_ids;
        view.git_heads = self.git_heads;
    }

    /// Moves this machine's working-copy commits along the rewrites `op` records, as jj
    /// moves a workspace's `@` when it rewrites it.
    fn follow_rewrites(&mut self, op: &StoreOperation) {
        workspaces::follow_rewrites(&mut self.wc_commit_ids, op.commit_predecessors.as_ref());
    }
}

pub struct NodeRepo {
    repo_path: PathBuf,
    loader: RepoLoader,
    canonical: CanonicalStore,
    map: TranslationMap,
    colocated: bool,
    /// Whether every operation reachable from the op heads has been mapped since opening.
    heads_mapped: bool,
    machine: Machine,
    /// The canonical join operation each join point maps to, by the join point's
    /// fingerprint, so that a copy of it that `jj op abandon` rewrote maps there too.
    joins: BTreeMap<String, OperationId>,
}

impl NodeRepo {
    /// Opens the repository whose `.jj/repo` directory is `repo_path`.
    pub fn open(repo_path: &Path, settings: &UserSettings) -> Result<Self, NodeError> {
        let loader =
            RepoLoader::init_from_file_system(settings, repo_path, &default_backend_factories())?;
        if loader.op_store().name() != SimpleOpStore::NAME {
            return Err(NodeError::UnsupportedOpStore(
                loader.op_store().name().to_owned(),
            ));
        }
        let musubi_dir = repo_path.join("musubi");
        let canonical = CanonicalStore::open(
            &musubi_dir.join("canonical"),
            loader.store().root_commit_id().clone(),
        )?;
        let map_path = musubi_dir.join("translation");
        let map = TranslationMap::open(&map_path).map_err(|source| NodeError::Io {
            path: map_path,
            source,
        })?;
        let colocated = is_colocated(repo_path, &loader);
        let mut node = Self {
            repo_path: repo_path.to_owned(),
            loader,
            canonical,
            map,
            colocated,
            heads_mapped: false,
            joins: BTreeMap::new(),
            machine: Machine::load_or_create(
                &musubi_dir.join("machine"),
                settings.operation_hostname(),
            )
            .map_err(|source| NodeError::Io {
                path: musubi_dir.join("machine"),
                source,
            })?,
        };
        for (local, canonical, fingerprint) in node.read_joins()? {
            node.joins.insert(fingerprint, canonical.clone());
            node.insert_map(local, canonical)?;
        }
        Ok(node)
    }

    fn joins_path(&self) -> PathBuf {
        self.repo_path.join("musubi/joins")
    }

    /// Join records are the one part of the translation that cannot be recomputed, so
    /// unlike the translation cache they are written durably: each line holds the local
    /// join point, the canonical join operation, and the join point's fingerprint.
    fn read_joins(&self) -> Result<Vec<(OperationId, OperationId, String)>, NodeError> {
        let path = self.joins_path();
        let text = match fs::read_to_string(&path) {
            Ok(text) => text,
            Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(vec![]),
            Err(source) => return Err(NodeError::Io { path, source }),
        };
        Ok(text
            .lines()
            .filter_map(|line| {
                let mut fields = line.split(' ');
                Some((
                    OperationId::try_from_hex(fields.next()?)?,
                    OperationId::try_from_hex(fields.next()?)?,
                    fields.next()?.to_owned(),
                ))
            })
            .collect())
    }

    fn record_join(
        &mut self,
        local: OperationId,
        local_op: &StoreOperation,
        canonical: OperationId,
    ) -> Result<(), NodeError> {
        let path = self.joins_path();
        let io_err = |source| NodeError::Io {
            path: path.clone(),
            source,
        };
        let mut file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .map_err(io_err)?;
        let fingerprint = fingerprint(local_op);
        writeln!(file, "{} {} {fingerprint}", local.hex(), canonical.hex()).map_err(io_err)?;
        file.sync_all().map_err(io_err)?;
        self.joins.insert(fingerprint, canonical.clone());
        self.insert_map(local, canonical)
    }

    /// Creates the canonical operation that replicates this repository's current state in
    /// place of its operation history, and durably records that the current op head
    /// canonicalizes to it. See "Joining" in docs/design.md.
    pub fn create_join_operation(&mut self, description: &str) -> Result<OperationId, NodeError> {
        let head = self.merge_heads()?;
        if let Some(canonical) = self.canonical_of(&head) {
            return Ok(canonical);
        }
        let op = self.loader.op_store().read_operation(&head).block_on()?;
        self.check_format(&head, &op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let root = self.canonical.root_operation_id().clone();
        let view = self.canonical_view(view, std::slice::from_ref(&root), None)?;
        let settings = self.loader.settings();
        let now = settings
            .operation_timestamp()
            .unwrap_or_else(Timestamp::now);
        let join = StoreOperation {
            view_id: self.canonical.write_view(&view)?,
            parents: vec![self.canonical.root_operation_id().clone()],
            metadata: OperationMetadata {
                time: TimestampRange {
                    start: now,
                    end: now,
                },
                description: description.to_owned(),
                hostname: settings.operation_hostname().to_owned(),
                username: settings.operation_username().to_owned(),
                is_snapshot: false,
                workspace_name: None,
                attributes: BTreeMap::new(),
            },
            commit_predecessors: Some(BTreeMap::new()),
        };
        let canonical = self.canonical.write_operation(&join)?;
        self.record_join(head, &op, canonical.clone())?;
        Ok(canonical)
    }

    /// This machine's identity in the hive.
    pub fn machine(&self) -> &Machine {
        &self.machine
    }

    /// The canonical form of a local view: no records of this machine's `.git`, and every
    /// machine's workspaces under machine-qualified keys, with this machine's from `view`
    /// and the others' carried over from the canonical parents and along `predecessors`. The
    /// labels showing other machines' workspaces are removed. Depends only on its
    /// arguments, so canonicalizing again after a crash gives the same result.
    fn canonical_view(
        &self,
        mut view: View,
        canonical_parents: &[OperationId],
        predecessors: Option<&BTreeMap<CommitId, Vec<CommitId>>>,
    ) -> Result<View, NodeError> {
        for parent in canonical_parents {
            if parent == self.canonical.root_operation_id() {
                continue;
            }
            let parent_view = self
                .canonical
                .read_view(&self.canonical.read_operation(parent)?.view_id)?;
            // The labels this machine showed for the parent's workspaces, exactly as
            // `realize_one` named them.
            for remote in self.label_remotes(&parent_view).into_values() {
                view.remote_views.remove(RemoteName::new(&remote));
            }
        }
        let mut workspaces_by_key = self.merged_workspaces(canonical_parents)?;
        workspaces_by_key.retain(|key, _| {
            workspaces::split_key(key.as_str())
                .is_none_or(|(machine, _)| machine != self.machine.key())
        });
        workspaces::follow_rewrites(&mut workspaces_by_key, predecessors);
        for (workspace, commit) in std::mem::take(&mut view.wc_commit_ids) {
            workspaces_by_key.insert(
                workspaces::workspace_key(self.machine.key(), workspace.as_str()),
                commit,
            );
        }
        strip_git_records(&mut view);
        view.wc_commit_ids = workspaces_by_key;
        Ok(view)
    }

    /// Where every machine's workspaces were, as of the canonical form of this machine's
    /// (merged) op head: `(machine name, workspace, commit)`.
    pub fn machine_workspaces(&mut self) -> Result<Vec<(String, String, CommitId)>, NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        Ok(self
            .workspaces_of(&canonical)?
            .into_iter()
            .filter_map(|(key, commit)| {
                let (machine, workspace) = workspaces::split_key(key.as_str())?;
                let name = machine.split_once('#').map_or(machine, |(name, _)| name);
                Some((name.to_owned(), workspace.to_owned(), commit))
            })
            .collect())
    }

    /// The machine-qualified workspaces of a canonical view.
    fn workspaces_of(
        &self,
        op: &OperationId,
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        if op == self.canonical.root_operation_id() {
            return Ok(BTreeMap::new());
        }
        let view = self
            .canonical
            .read_view(&self.canonical.read_operation(op)?.view_id)?;
        Ok(view.wc_commit_ids)
    }

    /// The parents' machine-qualified workspaces merged three-way, as jj merges views: an
    /// entry one side changed since the merge base wins; when both changed it, the later
    /// parent wins.
    fn merged_workspaces(
        &self,
        parents: &[OperationId],
    ) -> Result<BTreeMap<WorkspaceNameBuf, CommitId>, NodeError> {
        let Some((first, rest)) = parents.split_first() else {
            return Ok(BTreeMap::new());
        };
        let mut merged = self.workspaces_of(first)?;
        let mut merged_parents = vec![first.clone()];
        for other in rest {
            let base = match self
                .canonical
                .closest_common_ancestors(&merged_parents, std::slice::from_ref(other))?
                .first()
            {
                Some(base) => self.workspaces_of(base)?,
                None => BTreeMap::new(),
            };
            let theirs = self.workspaces_of(other)?;
            let keys: BTreeSet<WorkspaceNameBuf> = merged
                .keys()
                .chain(theirs.keys())
                .chain(base.keys())
                .cloned()
                .collect();
            let mut next = BTreeMap::new();
            for key in keys {
                let (ours, theirs, base) = (merged.get(&key), theirs.get(&key), base.get(&key));
                let value = if ours == base {
                    theirs
                } else if theirs == base {
                    ours
                } else {
                    theirs
                };
                if let Some(commit) = value {
                    next.insert(key, commit.clone());
                }
            }
            merged = next;
            merged_parents.push(other.clone());
        }
        Ok(merged)
    }

    /// The remote names under which this machine shows the other machines' workspaces in a
    /// canonical view, keyed by machine.
    fn label_remotes(&self, canonical_view: &View) -> BTreeMap<String, String> {
        let machines: BTreeSet<String> = canonical_view
            .wc_commit_ids
            .keys()
            .filter_map(|key| workspaces::split_key(key.as_str()))
            .map(|(machine, _)| machine.to_owned())
            .filter(|machine| machine != self.machine.key())
            .collect();
        workspaces::remote_names(&machines, |name| {
            canonical_view
                .remote_views
                .keys()
                .any(|remote| remote.as_str() == name)
        })
    }

    /// The repository's `.jj/repo` directory.
    pub fn repo_path(&self) -> &Path {
        &self.repo_path
    }

    pub fn canonical_store(&self) -> &CanonicalStore {
        &self.canonical
    }

    pub fn loader(&self) -> &RepoLoader {
        &self.loader
    }

    pub fn is_colocated(&self) -> bool {
        self.colocated
    }

    /// The commits a stored canonical operation requires, excluding the root commit.
    pub fn required_commits(
        &self,
        canonical: &OperationId,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        if canonical == self.canonical.root_operation_id() {
            return Ok(BTreeSet::new());
        }
        let op = self.canonical.read_operation(canonical)?;
        let view = self.canonical.read_view(&op.view_id)?;
        let mut commits = objects::referenced_commits(&op, &view);
        commits.remove(self.loader.store().root_commit_id());
        Ok(commits)
    }

    /// The object store of this repository's backend.
    pub fn object_store(&self) -> Result<Box<dyn ObjectStore + '_>, NodeError> {
        let store = self.loader.store();
        let store_path = self.repo_path.join("store");
        if let Ok(backend) = jj_lib::git::get_git_backend(store) {
            Ok(Box::new(GitStore::for_node(&store_path, backend)))
        } else if store.backend().name() == jj_lib::simple_backend::SimpleBackend::NAME {
            Ok(Box::new(SimpleStore::new(&store_path)))
        } else {
            Err(NodeError::UnsupportedBackend(
                store.backend().name().to_owned(),
            ))
        }
    }

    fn root_op_id(&self) -> &OperationId {
        self.loader.op_store().root_operation_id()
    }

    pub fn local_heads(&self) -> Result<Vec<OperationId>, NodeError> {
        Ok(self.loader.op_heads_store().get_op_heads().block_on()?)
    }

    /// Lets jj merge the op heads if there are several, as any `jj` command would. Returns
    /// the resulting single head.
    ///
    /// The merge can move bookmarks (jj rebases descendants of rewritten commits, and their
    /// bookmarks with them), so in a colocated repository it is exported to `.git` before
    /// becoming the op head, under jj's import/export lock, like every other op head musubi
    /// publishes. The exported copy has the same canonical form as the merge.
    pub fn merge_heads(&self) -> Result<OperationId, NodeError> {
        if !self.colocated || self.local_heads()?.len() <= 1 {
            let repo = self.load_at_head()?;
            return Ok(repo.op_id().clone());
        }
        let _lock = FileLock::lock(self.repo_path.join("git_import_export.lock"))?;
        let merged = self.load_at_head()?.op_id().clone();
        let exported = self.export_refs(&merged)?;
        if exported != merged {
            self.loader
                .op_heads_store()
                .update_op_heads(std::slice::from_ref(&merged), &exported)
                .block_on()?;
        }
        Ok(exported)
    }

    /// Loads the repository at its op head, letting jj merge concurrent heads.
    fn load_at_head(&self) -> Result<Arc<ReadonlyRepo>, NodeError> {
        self.loader.load_at_head().block_on().map_err(|err| {
            if format!("{err:?}").contains("root commit as one of the parents") {
                NodeError::RootParentMerge(err)
            } else {
                err.into()
            }
        })
    }

    /// The canonical form of each local op head.
    pub fn canonical_heads(&mut self) -> Result<Vec<OperationId>, NodeError> {
        let heads = self.local_heads()?;
        heads.iter().map(|head| self.canonicalize(head)).collect()
    }

    pub fn canonical_of(&self, local: &OperationId) -> Option<OperationId> {
        if local == self.root_op_id() {
            return Some(self.canonical.root_operation_id().clone());
        }
        self.map.canonical_of(local).cloned()
    }

    pub fn local_of(&self, canonical: &OperationId) -> Option<OperationId> {
        if canonical == self.canonical.root_operation_id() {
            return Some(self.root_op_id().clone());
        }
        self.map.local_of(canonical).cloned()
    }

    /// Records that `local` canonicalizes to `canonical` without deriving it, as `musubi
    /// join` does for the operation it replicates in place of the local history.
    pub fn record_translation(
        &mut self,
        local: OperationId,
        canonical: OperationId,
    ) -> Result<(), NodeError> {
        self.insert_map(local, canonical)
    }

    /// Returns the canonical id of a local operation, canonicalizing it and any
    /// not-yet-canonicalized ancestors.
    pub fn canonicalize(&mut self, local: &OperationId) -> Result<OperationId, NodeError> {
        let op_store = self.loader.op_store().clone();
        // Post-order walk: an operation is canonicalized once all its parents are.
        let mut stack: Vec<(OperationId, Option<StoreOperation>)> = vec![(local.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if self.canonical_of(&id).is_some() {
                continue;
            }
            let op = match loaded {
                Some(op) => op,
                None => op_store.read_operation(&id).block_on()?,
            };
            let missing: Vec<_> = op
                .parents
                .iter()
                .filter(|parent| self.canonical_of(parent).is_none())
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.push((id, Some(op)));
                stack.extend(missing.into_iter().map(|parent| (parent, None)));
                continue;
            }
            let canonical_id =
                if let Some(canonical) = op.metadata.attributes.get(CANONICAL_ATTRIBUTE) {
                    self.realized_canonical(&id, &op, canonical)?
                } else if let Some(join) = self.joins.get(&fingerprint(&op)) {
                    // A join point that `jj op abandon` rewrote, abandoning history from before
                    // the join, which no other machine has.
                    join.clone()
                } else {
                    self.write_canonical(&id, &op)?
                };
            self.insert_map(id, canonical_id)?;
        }
        Ok(self.canonical_of(local).expect("canonicalized above"))
    }

    /// The canonical operation a realization names in its `musubi.canonical` attribute.
    /// `jj op abandon` rewrites the operations above the ones it abandons, keeping their
    /// metadata, so a rewritten realization still names its canonical operation, but has
    /// other parents. Its parents must already be canonicalized.
    fn realized_canonical(
        &self,
        id: &OperationId,
        op: &StoreOperation,
        canonical: &str,
    ) -> Result<OperationId, NodeError> {
        let canonical_id = OperationId::try_from_hex(canonical)
            .filter(|c| self.canonical.has_operation(c))
            .ok_or_else(|| NodeError::DanglingAttribute {
                op: id.hex(),
                canonical: canonical.to_owned(),
            })?;
        let parents: Vec<OperationId> = op
            .parents
            .iter()
            .map(|parent| {
                self.canonical_of(parent)
                    .expect("parents canonicalized first")
            })
            .collect();
        if parents != self.canonical.read_operation(&canonical_id)?.parents {
            return Err(NodeError::RewrittenRealization {
                op: id.hex(),
                canonical: canonical_id.hex(),
            });
        }
        Ok(canonical_id)
    }

    fn write_canonical(
        &self,
        id: &OperationId,
        op: &StoreOperation,
    ) -> Result<OperationId, NodeError> {
        self.check_format(id, op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let parents: Vec<OperationId> = op
            .parents
            .iter()
            .map(|parent| {
                self.canonical_of(parent)
                    .expect("parents canonicalized first")
            })
            .collect();
        let view = self.canonical_view(view, &parents, op.commit_predecessors.as_ref())?;
        let mut metadata = op.metadata.clone();
        // Which workspace made an operation is per-machine, like the view's working copies:
        // qualify it, so that each machine can tell its own workspaces' operations from
        // another machine's workspace of the same name (see `realized_workspace_name`).
        metadata.workspace_name = metadata
            .workspace_name
            .map(|name| workspaces::workspace_key(self.machine.key(), name.as_str()));
        let canonical_op = StoreOperation {
            view_id: self.canonical.write_view(&view)?,
            parents,
            metadata,
            commit_predecessors: op.commit_predecessors.clone(),
        };
        Ok(self.canonical.write_operation(&canonical_op)?)
    }

    /// Refuses operations whose files contain fields this jj-lib would drop.
    fn check_format(&self, id: &OperationId, op: &StoreOperation) -> Result<(), NodeError> {
        let op_store_dir = self.repo_path.join("op_store");
        type Check = fn(&[u8]) -> Result<(), FormatError>;
        let checks: [(PathBuf, Check); 2] = [
            (
                op_store_dir.join("operations").join(id.hex()),
                format_guard::check_operation,
            ),
            (
                op_store_dir.join("views").join(op.view_id.hex()),
                format_guard::check_view,
            ),
        ];
        for (path, check) in checks {
            if op.view_id.as_bytes().iter().all(|&b| b == 0) && path.ends_with(op.view_id.hex()) {
                continue;
            }
            let bytes = fs::read(&path).map_err(|source| NodeError::Io { path, source })?;
            check(&bytes).map_err(|source| NodeError::Format {
                op: id.hex(),
                source,
            })?;
        }
        Ok(())
    }

    /// Realizes a stored canonical operation, and any unrealized ancestors, without
    /// publishing it. Returns the local operation id.
    pub fn realize(&mut self, canonical: &OperationId) -> Result<OperationId, NodeError> {
        // Map everything reachable from the op heads first. Otherwise, after losing the
        // translation cache, an operation that already has a reachable realization would be
        // realized again, and two reachable local operations would share a canonical form.
        if !self.heads_mapped {
            self.canonical_heads()?;
            self.heads_mapped = true;
        }
        let mut stack: Vec<(OperationId, Option<StoreOperation>)> = vec![(canonical.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if self.local_of(&id).is_some() {
                continue;
            }
            if !self.canonical.has_operation(&id) {
                return Err(NodeError::NotRealizable(id.hex(), "operation not stored"));
            }
            let op = match loaded {
                Some(op) => op,
                None => self.canonical.read_operation(&id)?,
            };
            let missing: Vec<_> = op
                .parents
                .iter()
                .filter(|p| self.local_of(p).is_none())
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.push((id, Some(op)));
                stack.extend(missing.into_iter().map(|parent| (parent, None)));
                continue;
            }
            let local = self.realize_one(&id, &op)?;
            self.insert_map(local, id)?;
        }
        Ok(self.local_of(canonical).expect("realized above"))
    }

    fn realize_one(
        &self,
        canonical_id: &OperationId,
        op: &StoreOperation,
    ) -> Result<OperationId, NodeError> {
        let parents: Vec<OperationId> = op
            .parents
            .iter()
            .map(|parent| self.local_of(parent).expect("parents realized first"))
            .collect();
        let mut view = self.canonical.read_view(&op.view_id)?;
        // Other machines' workspaces become labels: remote bookmarks of a pseudo-remote per
        // machine, so beta's `default` shows as `default@beta`. Tracked, because jj's
        // default `immutable_heads()` includes every *untracked* remote bookmark, which
        // would make the other machine's work, and everything under it, immutable here.
        let remotes = self.label_remotes(&view);
        for (key, commit) in std::mem::take(&mut view.wc_commit_ids) {
            let Some((machine, workspace)) = workspaces::split_key(key.as_str()) else {
                continue;
            };
            let Some(remote) = remotes.get(machine) else {
                continue;
            };
            view.remote_views
                .entry(RemoteNameBuf::from(remote.as_str()))
                .or_default()
                .bookmarks
                .insert(
                    RefNameBuf::from(workspace),
                    RemoteRef {
                        target: RefTarget::normal(commit),
                        state: RemoteRefState::Tracked,
                    },
                );
        }
        let mut per_machine = self.inherited_per_machine(&parents)?;
        per_machine.follow_rewrites(op);
        per_machine.apply_to(&mut view);
        let mut metadata = op.metadata.clone();
        metadata.workspace_name = metadata
            .workspace_name
            .map(|key| self.realized_workspace_name(&key, &remotes));
        metadata
            .attributes
            .insert(CANONICAL_ATTRIBUTE.to_owned(), canonical_id.hex());
        let local_op = StoreOperation {
            view_id: self.loader.op_store().write_view(&view).block_on()?,
            parents,
            metadata,
            commit_predecessors: op.commit_predecessors.clone(),
        };
        Ok(self
            .loader
            .op_store()
            .write_operation(&local_op)
            .block_on()?)
    }

    /// The local name of the workspace that made a canonical operation. This machine's own
    /// workspaces keep their names. Another machine's are named like their labels, as in
    /// `default@beta`. jj's `undo` and `redo` refuse to undo another workspace's operation,
    /// and they tell workspaces apart only by name, so with the plain name `jj undo` here
    /// would undo beta's latest operation as if it were this machine's own.
    fn realized_workspace_name(
        &self,
        key: &WorkspaceName,
        remotes: &BTreeMap<String, String>,
    ) -> WorkspaceNameBuf {
        match workspaces::split_key(key.as_str()) {
            Some((machine, workspace)) if machine == self.machine.key() => workspace.into(),
            Some((machine, workspace)) => {
                // A machine with no workspaces left in this view has no label to name.
                let remote = remotes
                    .get(machine)
                    .map_or_else(|| workspaces::machine_name(machine), String::as_str);
                format!("{workspace}@{remote}").into()
            }
            None => key.to_owned(),
        }
    }

    /// The per-machine fields a realization starts from: its parent's, or for a merge, the
    /// parents' merged three-way by jj, as a local merge of the same operations would.
    fn inherited_per_machine(&self, parents: &[OperationId]) -> Result<PerMachine, NodeError> {
        let (first, rest) = parents.split_first().expect("operations have parents");
        let first_op = self.loader.load_operation(first).block_on()?;
        if rest.is_empty() {
            return Ok(PerMachine::of(
                &first_op.view().block_on()?.store_view().clone(),
            ));
        }
        let repo = self.loader.load_at(&first_op).block_on()?;
        let mut tx = repo.start_transaction();
        let mut merged = vec![first_op];
        for other in rest {
            let other_op = self.loader.load_operation(other).block_on()?;
            let bases =
                op_walk::closest_common_ancestors(merged.clone(), [other_op.clone()]).block_on()?;
            // Several closest common ancestors would need jj's recursive merge. Per-machine
            // fields only describe this machine's `.git`, and the op head's export corrects
            // them, so the first base is good enough.
            let base = match bases.into_iter().next() {
                Some(base) => base,
                None => self.loader.root_operation().block_on(),
            };
            tx.merge_operation(&base, &other_op).block_on()?;
            merged.push(other_op);
        }
        Ok(PerMachine::of(tx.repo().view().store_view()))
    }

    /// Realizes a canonical operation and publishes it as an op head. In a colocated
    /// repository the realization first exports its refs to `.git`, holding jj's colocated
    /// import/export lock, so that no `jj` command sees the operation before `.git` matches
    /// it.
    pub fn advance(&mut self, canonical: &OperationId) -> Result<OperationId, NodeError> {
        let realized = self.realize(canonical)?;
        let _lock = if self.colocated {
            Some(FileLock::lock(
                self.repo_path.join("git_import_export.lock"),
            )?)
        } else {
            None
        };
        let head = if self.colocated {
            let exported = self.export_refs(&realized)?;
            self.insert_map(exported.clone(), canonical.clone())?;
            exported
        } else {
            realized
        };
        let parents = self
            .loader
            .op_store()
            .read_operation(&head)
            .block_on()?
            .parents;
        self.loader
            .op_heads_store()
            .update_op_heads(&parents, &head)
            .block_on()?;
        drop(_lock);
        self.replace_abandoned_working_copies()?;
        Ok(head)
    }

    /// Gives each workspace on this machine whose working-copy commit another machine
    /// abandoned a fresh working-copy commit, as jj does when it abandons a working-copy
    /// commit locally. Returns the workspaces it moved.
    pub fn replace_abandoned_working_copies(&mut self) -> Result<Vec<String>, NodeError> {
        // Merge through `merge_heads`, which exports to `.git`: a bare `load_at_head` would
        // merge without exporting the bookmarks the merge moves.
        let head = self.merge_heads()?;
        let repo = self
            .loader
            .load_at(&self.loader.load_operation(&head).block_on()?)
            .block_on()?;
        let mut abandoned = vec![];
        for (name, wc) in repo.view().wc_commit_ids() {
            if !is_visible(&repo, wc)? {
                abandoned.push((name.clone(), wc.clone()));
            }
        }
        if abandoned.is_empty() {
            return Ok(vec![]);
        }
        let mut tx = repo.start_transaction();
        let mut moved = vec![];
        for (name, wc) in abandoned {
            // The nearest visible ancestor along first parents: where jj would have put the
            // new working copy had the abandon happened on this machine.
            let mut parent = repo.store().get_commit_async(&wc).block_on()?;
            while !is_visible(&repo, parent.id())? {
                let Some(first) = parent.parent_ids().first().cloned() else {
                    break;
                };
                parent = repo.store().get_commit_async(&first).block_on()?;
            }
            tx.repo_mut().check_out(name.clone(), &parent).block_on()?;
            moved.push(name.as_str().to_owned());
        }
        let description = format!(
            "musubi: new working copy for {} (abandoned elsewhere)",
            moved.join(", ")
        );
        tx.commit(description).block_on()?;
        Ok(moved)
    }

    /// Runs jj's `export_refs` on top of a realization and returns the operation that
    /// records the result: the same operation if nothing changed, otherwise a copy with the
    /// updated per-machine fields.
    fn export_refs(&self, realized: &OperationId) -> Result<OperationId, NodeError> {
        let op = self.loader.load_operation(realized).block_on()?;
        let repo: Arc<ReadonlyRepo> = self.loader.load_at(&op).block_on()?;
        let mut tx = repo.start_transaction();
        // Refs that fail to export keep their recorded values, exactly as after a failed
        // export in a local `jj` command; jj's next import reconciles them.
        let _stats = jj_lib::git::export_refs(tx.repo_mut())?;
        let view = tx.repo().view().store_view();
        if view == repo.view().store_view() {
            return Ok(realized.clone());
        }
        let mut store_op = op.store_operation().clone();
        store_op.view_id = self.loader.op_store().write_view(view).block_on()?;
        Ok(self
            .loader
            .op_store()
            .write_operation(&store_op)
            .block_on()?)
    }

    fn insert_map(&mut self, local: OperationId, canonical: OperationId) -> Result<(), NodeError> {
        self.map
            .insert(local, canonical)
            .map_err(|source| NodeError::Io {
                path: self.repo_path.join("musubi/translation"),
                source,
            })
    }
}

/// Whether the repository shares its git repository with a working copy, so that every
/// `jj` command imports and exports refs automatically.
fn is_colocated(repo_path: &Path, loader: &RepoLoader) -> bool {
    let Ok(backend) = jj_lib::git::get_git_backend(loader.store()) else {
        return false;
    };
    let git_path = backend.git_repo_path();
    git_path.file_name().is_some_and(|name| name == ".git")
        && !git_path.starts_with(repo_path.join("store"))
}

/// Whether `commit` is visible: reachable from the view's heads.
fn is_visible(repo: &ReadonlyRepo, commit: &CommitId) -> Result<bool, NodeError> {
    if commit == repo.store().root_commit_id() {
        return Ok(true);
    }
    let index = repo.index();
    if !index.has_id(commit).block_on().map_err(index_err)? {
        return Ok(false);
    }
    for head in repo.view().heads() {
        if index
            .is_ancestor(commit, head)
            .block_on()
            .map_err(index_err)?
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn index_err(err: impl std::fmt::Display) -> NodeError {
    NodeError::Index(err.to_string())
}

/// What identifies an operation apart from its parents: its view, metadata, and the
/// rewrites it records. `jj op abandon` changes only the parents of the operations it
/// rewrites.
fn fingerprint(op: &StoreOperation) -> String {
    let without_parents = StoreOperation {
        parents: vec![],
        ..op.clone()
    };
    OperationId::new(blake2b_hash(&without_parents).to_vec()).hex()
}
