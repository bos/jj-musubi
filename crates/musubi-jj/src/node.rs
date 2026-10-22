//! A node's local jj repository: canonicalization, realization, and op heads.
//!
//! See "Per-machine state in a replicated view" in docs/design.md and "Translation layer" in
//! docs/protocol.md. What a node does only when its backend is git is in `node/git.rs`.

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::thread;

use futures::TryStreamExt as _;
use jj_lib::config::ConfigFile;
use jj_lib::config::ConfigGetError;
use jj_lib::config::ConfigNamePathBuf;
use jj_lib::config::ConfigSource;
use jj_lib::config::ConfigValue;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::git::GitExportError;
use jj_lib::git::GitSubprocessOptions;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::lock::FileLockError;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_heads_store::OpHeadsStoreError;
use jj_lib::op_store::OpStoreError;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::op_store::RemoteView;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::op_walk;
use jj_lib::operation::Operation;
use jj_lib::ref_name::GitRefNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::repo::RepoLoaderError;
use jj_lib::repo::StoreLoadError;
use jj_lib::revset::RevsetExpression;
use jj_lib::settings::UserSettings;
use jj_lib::simple_op_store::SimpleOpStore;
use pollster::FutureExt as _;
use serde::Deserialize;
use serde::Serialize;
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
use crate::git_command::GitError;
use crate::hive_settings;
use crate::hive_settings::Entry;
use crate::hive_settings::HiveSettings;
use crate::hive_settings::SettingValues;
use crate::hive_settings::Stamp;
use crate::objects::Backend;
use crate::objects::GitStore;
use crate::objects::Incompleteness;
use crate::objects::ObjectError;
use crate::objects::ObjectStore;
use crate::objects::SimpleStore;
use crate::remote_url::without_credentials;
use crate::translation_map::TranslationMap;
use crate::workspaces;
use crate::workspaces::Machine;

mod git;
mod git_config;

use git::Colocation;
use git::NodeGit;

/// What a hub matches a joining repository against: see [`NodeRepo::join_summary`].
#[derive(Clone, Debug)]
pub struct JoinSummary {
    pub backend: Backend,
    pub remotes: BTreeMap<String, hive_settings::Remote>,
    /// Visible commits whose parent is the root commit, other than an empty working-copy
    /// commit with no description.
    pub roots: Vec<CommitId>,
    /// The commits remote bookmarks point to.
    pub remote_targets: Vec<CommitId>,
}

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
    #[error("the op store wrote realized operation {0} under another id")]
    MisnamedWrite(String),
    #[error("canonical operation {0} is not realized and cannot be: {1}")]
    NotRealizable(String, &'static str),
    #[error("operation {op} names canonical operation {canonical}, which is not stored")]
    DanglingAttribute { op: String, canonical: String },
    #[error("bad hive settings in {op}: {message}")]
    Settings { op: String, message: String },
    /// jj cannot merge this machine's concurrent operations with the hive's, as when two
    /// machines' rebases form a loop: jj 0.46 then panics ("graph has cycle").
    #[error(
        "jj cannot merge this machine's operations with the hive's ({reason}). musubi has not \
         applied the hive's latest operations here, so jj keeps working. To go on, revert this \
         machine's operation that conflicts with them, one of those the hive doesn't have yet \
         (newest first: {listed}), with `jj op revert <id>`; musubi then catches up"
    )]
    Unmergeable {
        /// This machine's operations the hive doesn't have, newest first.
        ours: Vec<OperationId>,
        listed: String,
        reason: String,
    },
    #[error("repo config {path}: {message}")]
    Config { path: PathBuf, message: String },
    #[error(
        "operation {op} realizes canonical operation {canonical} but no longer has its parents \
         (was `jj op abandon` run?); musubi does not replicate op abandon yet, so replication is \
         paused for this repository"
    )]
    RewrittenRealization { op: String, canonical: String },
    /// The hub accepts an operation only with everything it requires, which a shallow or
    /// partial clone can't send.
    #[error(
        "musubi needs all of a repository's history, and this one is {0}. `musubi clone <hive> \
         <dir>` makes a full copy of a hive from its hub, and `jj git clone`, without \
         `--depth`, a full clone of a remote"
    )]
    Incomplete(Incompleteness),
    #[error(transparent)]
    Objects(#[from] ObjectError),
    #[error(transparent)]
    Git(#[from] GitError),
    #[error(transparent)]
    UserSettings(#[from] ConfigGetError),
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

/// Per-machine fields of a view that a realization inherits: this machine's record of its
/// own `.git` (`git_refs`, the `git` pseudo-remote, and each workspace's `git_heads`). The
/// working copies come from the canonical view instead. See "Per-machine state in a
/// replicated view" in docs/design.md.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct PerMachine {
    git_refs: BTreeMap<GitRefNameBuf, RefTarget>,
    git_remote: Option<RemoteView>,
    git_heads: BTreeMap<WorkspaceNameBuf, RefTarget>,
}

impl PerMachine {
    fn of(view: &View) -> Self {
        Self {
            git_refs: view.git_refs.clone(),
            // An empty `git` remote, which jj leaves when the last ref it exported goes,
            // counts as none, as it does when jj merges views.
            git_remote: view
                .remote_views
                .get(REMOTE_NAME_FOR_LOCAL_GIT_REPO)
                .filter(|remote| **remote != RemoteView::default())
                .cloned(),
            git_heads: view.git_heads.clone(),
        }
    }

    /// Gives `view` these fields, in place of any it has.
    fn apply_to(&self, view: &mut View) {
        strip_git_records(view);
        view.git_refs = self.git_refs.clone();
        if let Some(remote) = &self.git_remote {
            view.remote_views
                .insert(REMOTE_NAME_FOR_LOCAL_GIT_REPO.to_owned(), remote.clone());
        }
        view.git_heads = self.git_heads.clone();
    }
}

pub struct NodeRepo {
    repo_path: PathBuf,
    loader: RepoLoader,
    canonical: CanonicalStore,
    map: TranslationMap,
    backend: Backend,
    /// The repository's git repository, if its backend is git.
    git: Option<NodeGit>,
    /// Whether every operation reachable from the op heads has been mapped since opening.
    heads_mapped: bool,
    machine: Machine,
    /// The canonical join operation each join point maps to, by the join point's
    /// fingerprint, so that a copy of it that `jj op abandon` rewrote maps there too.
    joins: BTreeMap<String, OperationId>,
    /// The hive's settings as of canonical operations, as computed so far.
    settings: HashMap<OperationId, Option<HiveSettings>>,
    /// jj's repo config file for this repository, which holds the config the hive shares.
    repo_config: Option<PathBuf>,
    /// The last operation realized here, with its per-machine fields: usually the next
    /// one's parent, which then needn't be read back.
    last_realized: Option<(OperationId, Arc<PerMachine>)>,
    /// Realized operations still being written (see [`Self::realize_pending`]).
    unwritten: Vec<Unwritten>,
    /// Local views made ahead of their operations' realization, by canonical operation, with
    /// the per-machine fields they were made with: used only while those are what the
    /// operations inherit (see [`Self::realize_pending`]).
    prepared: Option<(Arc<PerMachine>, HashMap<OperationId, LocalView>)>,
}

/// How many realized operations may be written at once. jj's op store syncs each file it
/// writes to disk, which takes milliseconds on a cloud disk, so realizing many operations
/// one write at a time mostly waits.
const MAX_UNWRITTEN: usize = 32;

/// How many operations, each the only parent of the next, have their views made local at
/// once (see [`NodeRepo::realize_pending`]).
pub const REALIZE_AT_ONCE: usize = MAX_UNWRITTEN;

/// A realized operation being written, and the canonical operation it realizes.
struct Unwritten {
    write: thread::JoinHandle<Result<(), NodeError>>,
    local: OperationId,
    canonical: OperationId,
}

/// A realized operation, not yet written.
struct Realization {
    id: OperationId,
    op: StoreOperation,
    view: View,
    per_machine: Arc<PerMachine>,
}

/// A canonical operation's view made local, with its id and the local names of the
/// canonical view's workspaces.
struct LocalView {
    view: View,
    id: ViewId,
    names: BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>,
}

/// The per-machine fields of a local operation's view.
fn fields_of(op: &Operation) -> Result<PerMachine, NodeError> {
    Ok(PerMachine::of(op.view().block_on()?.store_view()))
}

/// The settings this machine and the hive agreed on when they were last reconciled.
#[derive(Serialize, Deserialize)]
struct SettingsState {
    /// The canonical operation they were reconciled at.
    op: String,
    /// The hive's settings there, if any machine had recorded some.
    hive: Option<HiveSettings>,
    /// The settings both had afterwards.
    settings: HiveSettings,
}

impl Drop for NodeRepo {
    fn drop(&mut self) {
        // While unwinding, a writer's panic passed on would abort the process; the writes
        // finish anyway, and what they wrote is realized again, identically, next time.
        if thread::panicking() {
            return;
        }
        // So that what was realized needn't be realized again.
        if let Err(err) = self.settle() {
            tracing::warn!("writing realized operations: {err}");
        }
    }
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
        let store = loader.store();
        let backend = Backend::of(store)
            .ok_or_else(|| NodeError::UnsupportedBackend(store.backend().name().to_owned()))?;
        // musubi runs the git jj runs for fetches and pushes, from jj's own setting, which jj
        // reads only for the git backend.
        let git = match backend {
            Backend::Git => {
                let executable = GitSubprocessOptions::from_settings(settings)?.executable_path;
                NodeGit::open(&executable, repo_path, store)
            }
            Backend::Simple => None,
        };
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
        let mut node = Self {
            repo_path: repo_path.to_owned(),
            loader,
            canonical,
            map,
            backend,
            git,
            heads_mapped: false,
            last_realized: None,
            prepared: None,
            unwritten: vec![],
            joins: BTreeMap::new(),
            settings: HashMap::new(),
            repo_config: None,
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
        let view = self.canonical_view(&head, view, std::slice::from_ref(&root), None)?;
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

    /// Fails if this repository lacks history that musubi would need to send.
    pub fn check_complete(&self) -> Result<(), NodeError> {
        match &self.git {
            Some(git) => match git.incompleteness()? {
                Some(incompleteness) => Err(NodeError::Incomplete(incompleteness)),
                None => Ok(()),
            },
            None => Ok(()),
        }
    }

    /// What a hub needs to know to decide which hive this repository belongs to.
    pub fn join_summary(&self) -> Result<JoinSummary, NodeError> {
        self.check_complete()?;
        let repo = self.load_at_head()?;
        let view = repo.view();
        let working_copies: BTreeSet<&CommitId> = view.wc_commit_ids().values().collect();
        let empty_tree = repo.store().empty_merged_tree().tree_ids().clone();
        let children: Vec<CommitId> = RevsetExpression::root()
            .children()
            .evaluate(repo.as_ref())
            .map_err(|err| NodeError::Index(err.to_string()))?
            .stream()
            .try_collect()
            .block_on()
            .map_err(|err| NodeError::Index(err.to_string()))?;
        let mut roots = vec![];
        for id in children {
            let commit = repo.store().get_commit(&id)?;
            // A new repository's working-copy commit is no history to share.
            let placeholder = working_copies.contains(&id)
                && commit.description().is_empty()
                && *commit.tree_ids() == empty_tree;
            if !placeholder {
                roots.push(id);
            }
        }
        let remote_targets = view
            .all_remote_bookmarks()
            .filter(|(symbol, _)| symbol.remote != REMOTE_NAME_FOR_LOCAL_GIT_REPO)
            .flat_map(|(_, remote)| remote.target.adds().flatten().cloned())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        Ok(JoinSummary {
            backend: self.backend,
            remotes: self.remotes()?,
            roots,
            remote_targets,
        })
    }

    /// The canonical form of a local view: no records of this machine's `.git`, and every
    /// machine's workspaces under machine-qualified keys. This machine's come from `view`.
    /// The others' come from the canonical parents, except where this operation moved them:
    /// they are workspaces in `view` too, which jj moves when it rewrites or abandons their
    /// commits, or restores an older view. Adding, forgetting or renaming another machine's
    /// workspace here changes nothing: its workspaces are its own. Depends only on its
    /// arguments, so canonicalizing again after a crash gives the same result.
    fn canonical_view(
        &self,
        local_op: &OperationId,
        mut view: View,
        canonical_parents: &[OperationId],
        predecessors: Option<&BTreeMap<CommitId, Vec<CommitId>>>,
    ) -> Result<View, NodeError> {
        // The names under which this machine showed the parents' other workspaces, exactly
        // as `realize_one` named them.
        let mut others: BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf> = BTreeMap::new();
        let mut parent_heads: BTreeSet<CommitId> = BTreeSet::new();
        for parent in canonical_parents {
            if parent == self.canonical.root_operation_id() {
                continue;
            }
            let parent_view = self
                .canonical
                .read_view(&self.canonical.read_operation(parent)?.view_id)?;
            parent_heads.extend(parent_view.head_ids.iter().cloned());
            for (key, name) in self.local_names(&parent_view) {
                if !self.is_own_key(&key) {
                    others.insert(name, key);
                }
            }
        }
        let mut workspaces_by_key = self.merged_workspaces(canonical_parents)?;
        workspaces_by_key.retain(|key, _| !self.is_own_key(key));
        let mut local = std::mem::take(&mut view.wc_commit_ids);
        let mut moved_here = BTreeSet::new();
        for (name, key) in &others {
            if let Some(commit) = local.remove(name)
                && let Some(entry) = workspaces_by_key.get_mut(key)
            {
                *entry = commit;
                moved_here.insert(key.clone());
            }
        }
        // Another machine's workspace forgotten here can't be moved by jj; follow the
        // rewrites this operation records instead.
        let mut forgotten: BTreeMap<WorkspaceNameBuf, CommitId> = workspaces_by_key
            .iter()
            .filter(|(key, _)| !moved_here.contains(*key))
            .map(|(key, commit)| (key.clone(), commit.clone()))
            .collect();
        workspaces::follow_rewrites(&mut forgotten, predecessors);
        // Forgetting a workspace abandons its working-copy commit if it's empty, as
        // `jj workspace forget` does. Forgetting another machine's workspace here mustn't
        // abandon that machine's working copy: keep the commit visible. But only while its
        // parents are visible here: jj, no longer seeing the commit, doesn't rebase it when
        // this machine rewrites or abandons them, and keeping it would bring them back.
        // Its machine then replaces it, as if jj had abandoned it here
        // (`replace_abandoned_working_copies`).
        let mut repo = None;
        for commit in forgotten.values() {
            if !parent_heads.contains(commit) || view.head_ids.contains(commit) {
                continue;
            }
            let repo = match &repo {
                Some(repo) => repo,
                None => repo.insert(
                    self.loader
                        .load_at(&self.loader.load_operation(local_op).block_on()?)
                        .block_on()?,
                ),
            };
            let parents = repo.store().get_commit_async(commit).block_on()?;
            let mut parents_visible = true;
            for parent in parents.parent_ids() {
                parents_visible &= is_visible(repo, parent)?;
            }
            if parents_visible {
                view.head_ids.insert(commit.clone());
            }
        }
        workspaces_by_key.extend(forgotten);
        for (workspace, commit) in local {
            workspaces_by_key.insert(
                workspaces::workspace_key(self.machine.key(), workspace.as_str()),
                commit,
            );
        }
        strip_git_records(&mut view);
        view.wc_commit_ids = workspaces_by_key;
        Ok(view)
    }

    fn is_own_key(&self, key: &WorkspaceName) -> bool {
        workspaces::split_key(key.as_str())
            .is_some_and(|(machine, _)| machine == self.machine.key())
    }

    /// The local name of each workspace in a canonical view: this machine's own keep their
    /// names, and another machine's are prefixed with the machine's name, as in
    /// `beta/default`, or with its name and part of its id when two machines share a name
    /// or the prefix would make a name of this machine's own.
    fn local_names(&self, canonical_view: &View) -> BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf> {
        let keys = &canonical_view.wc_commit_ids;
        let machines: BTreeSet<String> = keys
            .keys()
            .filter_map(|key| workspaces::split_key(key.as_str()))
            .map(|(machine, _)| machine.to_owned())
            .filter(|machine| machine != self.machine.key())
            .collect();
        let own: Vec<&str> = keys
            .keys()
            .filter(|key| self.is_own_key(key))
            .map(|key| key_workspace(key))
            .collect();
        let prefixes = workspaces::display_names(&machines, |name| {
            own.iter()
                .any(|workspace| workspace.starts_with(&format!("{name}/")))
        });
        keys.keys()
            .filter_map(|key| {
                let (machine, workspace) = workspaces::split_key(key.as_str())?;
                let name = if machine == self.machine.key() {
                    workspace.to_owned()
                } else {
                    format!("{}/{workspace}", prefixes.get(machine)?)
                };
                Some((key.clone(), WorkspaceNameBuf::from(name)))
            })
            .collect()
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

    /// The parents' machine-qualified workspaces merged three-way, as jj merges views
    /// (`workspaces::merge_working_copy`). A removal wins over a move, which matters here:
    /// only a workspace's own machine removes it, and its removal must win over another
    /// machine moving it meanwhile.
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
                let value = workspaces::merge_working_copy(
                    merged.get(&key),
                    base.get(&key),
                    theirs.get(&key),
                );
                if let Some(commit) = value {
                    next.insert(key, commit.clone());
                }
            }
            merged = next;
            merged_parents.push(other.clone());
        }
        Ok(merged)
    }

    /// The hive's settings as of a canonical operation: what its nearest recording
    /// ancestor recorded, combined where concurrent operations met, the later write to each
    /// setting winning, or `None` if no ancestor recorded any.
    pub fn settings_at(&mut self, op: &OperationId) -> Result<Option<HiveSettings>, NodeError> {
        let root = self.canonical.root_operation_id().clone();
        let mut stack = vec![op.clone()];
        while let Some(id) = stack.last().cloned() {
            if self.settings.contains_key(&id) {
                stack.pop();
                continue;
            }
            if id == root {
                self.settings.insert(id, None);
                stack.pop();
                continue;
            }
            let operation = self.canonical.read_operation(&id)?;
            if let Some(text) = operation.metadata.attributes.get(hive_settings::ATTRIBUTE) {
                let mut settings =
                    HiveSettings::parse(text).map_err(|err| NodeError::Settings {
                        op: id.hex(),
                        message: err.to_string(),
                    })?;
                settings.date_untimed(operation.metadata.time.end.timestamp.0);
                self.settings.insert(id, Some(settings));
                stack.pop();
                continue;
            }
            let missing: Vec<OperationId> = operation
                .parents
                .iter()
                .filter(|parent| !self.settings.contains_key(*parent))
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.extend(missing);
                continue;
            }
            let merged = operation
                .parents
                .iter()
                .filter_map(|parent| self.settings[parent].clone())
                .reduce(|a, b| HiveSettings::merge(&a, &b));
            self.settings.insert(id, merged);
            stack.pop();
        }
        Ok(self.settings[op].clone())
    }

    /// Brings this machine's settings and the hive's together: records this machine's
    /// changes for the hive, in an operation of its own, and applies the hive's here,
    /// setting by setting, the later write winning (docs/settings-merge.md). A setting
    /// that differs from what this machine last applied is a change, written when the file
    /// holding it was last modified. A machine reconciling for the first time takes the
    /// hive's value of every setting the hive has, and adds its own others. Remotes compare
    /// by the repositories they name ([`hive_settings::Remote`]), so a machine's own
    /// spelling of one is never a change. Returns whether it recorded a change, which then
    /// needs uploading.
    pub fn reconcile_settings(&mut self) -> Result<bool, NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        let state = self.read_settings_state()?;
        // A state from before writes were timed has no times to offer the cache.
        if let Some((op, hive, _)) = &state
            && hive.as_ref().is_none_or(HiveSettings::is_timed)
        {
            self.settings
                .entry(op.clone())
                .or_insert_with(|| hive.clone());
        }
        let hive = self.settings_at(&canonical)?;
        let current = hive.clone().unwrap_or_default();
        let mut extra = current.values().extra_config_keys();
        if let Some((_, _, applied)) = &state {
            extra.extend(applied.values().extra_config_keys());
        }
        let local = self.local_settings(&extra)?;
        let applied = state
            .as_ref()
            .map(|(_, _, applied)| applied.clone())
            .unwrap_or_default();
        let machine = self.machine.key().to_owned();
        let remotes_time = self.git.as_ref().map(|git| modified(&git.config_path()));
        let config_time = self.repo_config.as_deref().map(modified);
        let mut ours = HiveSettings {
            remotes: stamp_changes(&local.remotes, &applied.remotes, || Stamp {
                time: remotes_time.unwrap_or_else(now),
                machine: machine.clone(),
            }),
            config: stamp_changes(&local.config, &applied.config, || Stamp {
                time: config_time.unwrap_or_else(now),
                machine: machine.clone(),
            }),
        };
        // What this machine last applied before writes were timed has no time, so it loses
        // to the hive's value, and where the hive has none, the hive removed it.
        ours.remotes
            .retain(|name, entry| entry.stamp.time != 0 || current.remotes.contains_key(name));
        ours.config
            .retain(|key, entry| entry.stamp.time != 0 || current.config.contains_key(key));
        if state.is_none() {
            // Joining: the hive's values stand, whatever this machine has, but its own
            // others join them, however recently the hive removed one by that name.
            outlive_removals(&mut ours.remotes, &current.remotes);
            outlive_removals(&mut ours.config, &current.config);
            let present = current.without_removed();
            ours.remotes.extend(present.remotes);
            ours.config.extend(present.config);
        }
        let merged = HiveSettings::merge(&ours, &current);
        let (mut at, mut hive_now, mut recorded) = (canonical, hive, false);
        if merged != current {
            let op = self.record_settings(&head, &merged)?;
            at = self.canonicalize(&op)?;
            self.settings.insert(at.clone(), Some(merged.clone()));
            hive_now = Some(merged.clone());
            recorded = true;
        }
        let values = merged.values();
        if values != local {
            log_replaced(&local, &merged);
            self.apply_settings(&local, &values)?;
        }
        self.write_settings_state(&SettingsState {
            op: at.hex(),
            hive: hive_now,
            settings: merged,
        })?;
        Ok(recorded)
    }

    /// Whether this machine shares the credentials an http(s) remote URL may carry, as
    /// `musubi.share-credentials` in jj's config says; by default it doesn't.
    fn share_credentials(&self) -> bool {
        self.loader
            .settings()
            .get_bool("musubi.share-credentials")
            .unwrap_or(false)
    }

    /// This machine's git remotes, if its backend is git.
    fn remotes(&self) -> Result<BTreeMap<String, hive_settings::Remote>, NodeError> {
        Ok(match &self.git {
            Some(git) => git.remotes(self.share_credentials())?,
            None => BTreeMap::new(),
        })
    }

    /// The settings this machine has now: its git remotes, and the shared keys of its repo
    /// config, including `extra` keys.
    fn local_settings(&self, extra: &[String]) -> Result<SettingValues, NodeError> {
        Ok(SettingValues {
            remotes: self.remotes()?,
            config: self.read_shared_config(extra)?,
        })
    }

    fn apply_settings(&self, from: &SettingValues, to: &SettingValues) -> Result<(), NodeError> {
        if let Some(git) = &self.git {
            git.change_remotes(&from.remotes, &to.remotes)?;
        }
        self.write_shared_config(&from.config, &to.config)
    }

    fn repo_config_file(&self) -> Result<Option<ConfigFile>, NodeError> {
        let Some(path) = &self.repo_config else {
            return Ok(None);
        };
        ConfigFile::load_or_empty(ConfigSource::Repo, path)
            .map(Some)
            .map_err(|err| config_err(path, err))
    }

    /// The shared keys this machine's repo config sets: the default ones, those its own
    /// `musubi.shared-config` names, and `extra`.
    fn read_shared_config(&self, extra: &[String]) -> Result<BTreeMap<String, String>, NodeError> {
        let Some(file) = self.repo_config_file()? else {
            return Ok(BTreeMap::new());
        };
        let value_of = |key: &str| -> Option<String> {
            let name: ConfigNamePathBuf = key.parse().ok()?;
            let item = file.layer().look_up_item(&name).ok()??;
            hive_settings::normalize_value(&item.as_value()?.to_string())
        };
        let mut keys: BTreeSet<String> = hive_settings::SHARED_CONFIG
            .iter()
            .map(|key| (*key).to_owned())
            .chain(extra.iter().cloned())
            .collect();
        if let Some(value) = value_of(hive_settings::SHARED_CONFIG_KEY) {
            keys.extend(hive_settings::config_keys(&value));
        }
        Ok(keys
            .into_iter()
            .filter_map(|key| {
                let value = value_of(&key)?;
                Some((key, value))
            })
            .collect())
    }

    fn write_shared_config(
        &self,
        from: &BTreeMap<String, String>,
        to: &BTreeMap<String, String>,
    ) -> Result<(), NodeError> {
        if from == to {
            return Ok(());
        }
        let Some(mut file) = self.repo_config_file()? else {
            return Ok(());
        };
        let path = file.path().to_owned();
        let keys: BTreeSet<&String> = from.keys().chain(to.keys()).collect();
        for key in keys {
            if from.get(key) == to.get(key) {
                continue;
            }
            let name: ConfigNamePathBuf = key.parse().map_err(|err| config_err(&path, err))?;
            match to.get(key) {
                Some(text) => {
                    let value: ConfigValue = text.parse().map_err(|err| config_err(&path, err))?;
                    file.set_value(&name, value)
                        .map_err(|err| config_err(&path, err))?;
                }
                None => {
                    file.delete_value(&name)
                        .map_err(|err| config_err(&path, err))?;
                }
            }
        }
        file.save().map_err(|err| config_err(&path, err))
    }

    /// Writes an operation on top of `head` that changes nothing but records `settings`.
    fn record_settings(
        &self,
        head: &OperationId,
        settings: &HiveSettings,
    ) -> Result<OperationId, NodeError> {
        let repo = self
            .loader
            .load_at(&self.loader.load_operation(head).block_on()?)
            .block_on()?;
        let mut tx = repo.start_transaction();
        tx.set_attribute(hive_settings::ATTRIBUTE.to_owned(), settings.to_attribute());
        let repo = tx.commit("musubi: hive settings changed").block_on()?;
        Ok(repo.op_id().clone())
    }

    fn settings_state_path(&self) -> PathBuf {
        self.repo_path.join("musubi/settings.json")
    }

    /// Uses `path` as this repository's jj repo config file, which holds the config the
    /// hive shares. jj keeps it outside the repository, so the caller finds it as jj does
    /// (`jj config path --repo`). Without one, no config is shared.
    pub fn with_repo_config(mut self, path: Option<PathBuf>) -> Self {
        self.repo_config = path;
        self
    }

    /// Whether this machine has reconciled its settings with the hive's before.
    pub fn has_reconciled_settings(&self) -> bool {
        self.settings_state_path().exists()
    }

    fn read_settings_state(
        &self,
    ) -> Result<Option<(OperationId, Option<HiveSettings>, HiveSettings)>, NodeError> {
        let path = self.settings_state_path();
        let text = match fs::read_to_string(&path) {
            Ok(text) => text,
            Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(source) => return Err(NodeError::Io { path, source }),
        };
        let state: SettingsState =
            serde_json::from_str(&text).map_err(|err| NodeError::Settings {
                op: path.display().to_string(),
                message: err.to_string(),
            })?;
        let op = OperationId::try_from_hex(&state.op).ok_or_else(|| NodeError::Settings {
            op: state.op.clone(),
            message: "not an operation id".to_owned(),
        })?;
        Ok(Some((op, state.hive, state.settings)))
    }

    fn write_settings_state(&self, state: &SettingsState) -> Result<(), NodeError> {
        let path = self.settings_state_path();
        let json = serde_json::to_vec_pretty(state).expect("settings serialize");
        let dir = path.parent().expect("path has a parent");
        let io_err = |source| NodeError::Io {
            path: path.clone(),
            source,
        };
        let mut tmp = tempfile::NamedTempFile::new_in(dir).map_err(io_err)?;
        tmp.write_all(&json).map_err(io_err)?;
        tmp.persist(&path).map_err(|err| io_err(err.error))?;
        Ok(())
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

    /// Opens the repository's stores afresh. jj-lib's git backend sizes gix's table of pack
    /// indexes when it opens the repository, at a little more than the packs there were
    /// then, so packs added since can be out of its reach. Afterwards there is room for at
    /// least one more.
    pub fn reload(&mut self) -> Result<(), NodeError> {
        let settings = self.loader.settings().clone();
        self.loader = RepoLoader::init_from_file_system(
            &settings,
            &self.repo_path,
            &default_backend_factories(),
        )?;
        Ok(())
    }

    pub fn is_colocated(&self) -> bool {
        self.colocation().is_some()
    }

    /// How the repository shares its git repository with a working copy, if it does.
    fn colocation(&self) -> Option<&Colocation> {
        self.git.as_ref()?.colocation()
    }

    /// The commits the stored canonical operations `ops` require, excluding the root commit.
    pub fn required_commits(
        &self,
        canonical: &[OperationId],
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        Ok(self.canonical.required_commits(canonical)?)
    }

    /// The object store of this repository's backend.
    pub fn object_store(&self) -> Result<Box<dyn ObjectStore + '_>, NodeError> {
        let store = self.loader.store();
        let store_path = self.repo_path.join("store");
        match self.backend {
            Backend::Git => {
                let unsupported =
                    || NodeError::UnsupportedBackend(store.backend().name().to_owned());
                let git = self.git.as_ref().ok_or_else(unsupported)?;
                let backend = jj_lib::git::get_git_backend(store).map_err(|_| unsupported())?;
                Ok(Box::new(GitStore::for_node(
                    git.executable(),
                    &store_path,
                    backend,
                )))
            }
            Backend::Simple => Ok(Box::new(SimpleStore::new(&store_path))),
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
        let colocation = match self.colocation() {
            Some(colocation) if self.local_heads()?.len() > 1 => colocation,
            _ => return Ok(self.load_at_head()?.op_id().clone()),
        };
        let _lock = colocation.lock()?;
        let merged = self.load_at_head()?.op_id().clone();
        let exported = colocation.export_refs(&self.loader, &merged)?;
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
        let loaded = catch_jj_panic(|| Ok(self.loader.load_at_head().block_on()));
        match loaded {
            Ok(Ok(repo)) => Ok(repo),
            Ok(Err(err)) if format!("{err:?}").contains("root commit as one of the parents") => {
                Err(NodeError::RootParentMerge(err))
            }
            Ok(Err(err)) => Err(err.into()),
            Err(reason) => Err(self.unmergeable(&self.local_heads()?, reason)),
        }
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
        let view = self.canonical_view(id, view, &parents, op.commit_predecessors.as_ref())?;
        let mut metadata = op.metadata.clone();
        if let Some((prefix, target)) = target_of(&metadata.description)
            && let Some(canonical) = self.canonical_of(&target)
            && self.canonical.is_ancestor(&canonical, &parents)?
        {
            metadata.description = format!("{prefix}{}", canonical.hex());
        }
        // jj records the command that made an operation, which may name an http(s) URL with
        // a token meant for this machine only.
        if !self.share_credentials()
            && let Some(args) = metadata.attributes.get_mut("args")
        {
            *args = without_credentials(args);
        }
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
        let local = self.realize_pending(canonical, &[])?;
        self.settle()?;
        Ok(local)
    }

    /// [`Self::realize`], leaving the realizations to be written meanwhile: the store may
    /// lack them until [`Self::settle`], which [`Self::realize`], [`Self::advance`] and
    /// dropping this call, and so must anything else that reads them before then.
    /// [`Self::local_of`] knows them at once.
    ///
    /// `next` are the operations likely realized after this one, in order. Making a view
    /// local is most of realizing an operation, and it takes several at once to keep up with
    /// writing them, so the views of the operations that follow on, from this one's
    /// unrealized ancestors and then `next`, each with the one before as its only parent and
    /// so inheriting the same per-machine fields, are made with this one's, in parallel, and
    /// kept until they are realized.
    pub fn realize_pending(
        &mut self,
        canonical: &OperationId,
        next: &[OperationId],
    ) -> Result<OperationId, NodeError> {
        // Map everything reachable from the op heads first. Otherwise, after losing the
        // translation cache, an operation that already has a reachable realization would be
        // realized again, and two reachable local operations would share a canonical form.
        if !self.heads_mapped {
            self.canonical_heads()?;
            self.heads_mapped = true;
        }
        let order = self.unrealized(canonical)?;
        for (i, (id, op)) in order.iter().enumerate() {
            let parents: Vec<OperationId> = op
                .parents
                .iter()
                .map(|parent| self.local_of(parent).expect("parents realized first"))
                .collect();
            // Realizing it reads its parents from the store, unless its only parent is the
            // operation realized last.
            if !matches!(
                (parents.as_slice(), &self.last_realized),
                ([parent], Some((last, _))) if parent == last
            ) {
                self.settle()?;
            }
            let per_machine = self.inherited_per_machine(&parents)?;
            let prepared = match &mut self.prepared {
                Some((inherited, views)) if Arc::ptr_eq(inherited, &per_machine) => {
                    views.remove(id)
                }
                _ => None,
            };
            let view = match prepared {
                Some(view) => view,
                None => {
                    let later = order[i + 1..].iter().map(|(id, _)| id).chain(next);
                    let run = self.run_after(id, op, later)?;
                    let mut views = self.local_views(&run, &per_machine).into_iter();
                    let view = views
                        .next()
                        .expect("a run starts with its first operation")?;
                    // One that failed is made again when its turn comes.
                    let ahead = run[1..]
                        .iter()
                        .zip(views)
                        .filter_map(|((id, _), view)| Some((id.clone(), view.ok()?)))
                        .collect();
                    self.prepared = Some((per_machine.clone(), ahead));
                    view
                }
            };
            let realization = self.realize_one(id, op, parents, view, per_machine)?;
            self.write_later(realization, id.clone())?;
        }
        Ok(self.local_of(canonical).expect("realized above"))
    }

    /// `first`, and the stored, unrealized operations of `later` that follow it, each with
    /// the one before as its only parent, up to [`REALIZE_AT_ONCE`] in all.
    fn run_after<'a>(
        &self,
        first: &OperationId,
        op: &StoreOperation,
        later: impl Iterator<Item = &'a OperationId>,
    ) -> Result<Vec<(OperationId, StoreOperation)>, NodeError> {
        let mut run = vec![(first.clone(), op.clone())];
        for id in later.take(REALIZE_AT_ONCE - 1) {
            if !self.canonical.has_operation(id) || self.local_of(id).is_some() {
                break;
            }
            let op = self.canonical.read_operation(id)?;
            let (last, _) = run.last().expect("a run is never empty");
            if op.parents != std::slice::from_ref(last) {
                break;
            }
            run.push((id.clone(), op));
        }
        Ok(run)
    }

    /// The canonical operations to realize for `canonical`: it and its unrealized ancestors,
    /// parents first, each with its stored form.
    fn unrealized(
        &self,
        canonical: &OperationId,
    ) -> Result<Vec<(OperationId, StoreOperation)>, NodeError> {
        let mut order = vec![];
        let mut ordered = HashSet::new();
        let mut stack: Vec<(OperationId, Option<StoreOperation>)> = vec![(canonical.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if self.local_of(&id).is_some() || ordered.contains(&id) {
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
                .filter(|p| self.local_of(p).is_none() && !ordered.contains(*p))
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.push((id, Some(op)));
                stack.extend(missing.into_iter().map(|parent| (parent, None)));
                continue;
            }
            ordered.insert(id.clone());
            order.push((id, op));
        }
        Ok(order)
    }

    /// The local views of `ops`, which all inherit `per_machine`, made in parallel.
    fn local_views(
        &self,
        ops: &[(OperationId, StoreOperation)],
        per_machine: &PerMachine,
    ) -> Vec<Result<LocalView, NodeError>> {
        let make = |part: &[(OperationId, StoreOperation)]| -> Vec<_> {
            part.iter()
                .map(|(_, op)| self.local_view(op, per_machine))
                .collect()
        };
        if ops.len() == 1 {
            return make(ops);
        }
        let threads = thread::available_parallelism().map_or(1, |n| n.get());
        thread::scope(|scope| {
            let parts: Vec<_> = ops
                .chunks(ops.len().div_ceil(threads))
                .map(|part| {
                    let made = thread::Builder::new()
                        .name("make views local".to_owned())
                        .spawn_scoped(scope, move || make(part));
                    (part, made)
                })
                .collect();
            let mut views = Vec::with_capacity(ops.len());
            for (part, made) in parts {
                views.extend(match made {
                    Ok(made) => made
                        .join()
                        .unwrap_or_else(|panic| std::panic::resume_unwind(panic)),
                    // No thread to spare: here, then.
                    Err(_) => make(part),
                });
            }
            views
        })
    }

    /// A canonical operation's view, made local with `per_machine`.
    fn local_view(
        &self,
        op: &StoreOperation,
        per_machine: &PerMachine,
    ) -> Result<LocalView, NodeError> {
        let mut view = self.canonical.read_view(&op.view_id)?;
        // Every machine's working copies become workspaces here: this machine's under their
        // own names, the others' as `beta/default`. This machine's own may have moved: when
        // another machine rewrites, abandons or restores a working-copy commit, its jj moves
        // the workspace, and the canonical view records where to.
        let names = self.local_names(&view);
        view.wc_commit_ids = std::mem::take(&mut view.wc_commit_ids)
            .into_iter()
            .filter_map(|(key, commit)| Some((names.get(&key)?.clone(), commit)))
            .collect();
        per_machine.apply_to(&mut view);
        debug_assert_eq!(PerMachine::of(&view), *per_machine);
        // The id the op store gives it, worked out as it does.
        let id = ViewId::new(blake2b_hash(&view).to_vec());
        Ok(LocalView { view, id, names })
    }

    /// Starts writing a realization, after waiting for those being written if there are
    /// already enough of them.
    fn write_later(
        &mut self,
        realization: Realization,
        canonical: OperationId,
    ) -> Result<(), NodeError> {
        if self.unwritten.len() >= MAX_UNWRITTEN {
            self.settle()?;
        }
        let Realization {
            id,
            op,
            view,
            per_machine,
        } = realization;
        let store = self.loader.op_store().clone();
        let expected = id.clone();
        let write = thread::Builder::new()
            .name("write operation".to_owned())
            .spawn(move || {
                let view_id = store.write_view(&view).block_on()?;
                let written = store.write_operation(&op).block_on()?;
                if view_id != op.view_id || written != expected {
                    return Err(NodeError::MisnamedWrite(expected.hex()));
                }
                Ok(())
            })
            .map_err(|source| NodeError::Io {
                path: self.repo_path.join("op_store"),
                source,
            })?;
        self.map.insert_unwritten(id.clone(), canonical.clone());
        self.last_realized = Some((id.clone(), per_machine));
        self.unwritten.push(Unwritten {
            write,
            local: id,
            canonical,
        });
        Ok(())
    }

    /// Waits for the realizations being written, then records them in the translation
    /// map's file. If any write failed, the map forgets them all: a later realization may
    /// refer to the failed one, and realizing them again writes the same operations.
    pub fn settle(&mut self) -> Result<(), NodeError> {
        let unwritten = std::mem::take(&mut self.unwritten);
        let mut failed = None;
        let mut panicked = None;
        let mut translations = vec![];
        for Unwritten {
            write,
            local,
            canonical,
        } in unwritten
        {
            match write.join() {
                Ok(Ok(())) => {}
                Ok(Err(err)) => {
                    failed.get_or_insert(err);
                }
                Err(panic) => {
                    panicked.get_or_insert(panic);
                }
            }
            translations.push((local, canonical));
        }
        if let Some(panic) = panicked {
            for (local, canonical) in &translations {
                self.map.forget(local, canonical);
            }
            self.last_realized = None;
            self.prepared = None;
            std::panic::resume_unwind(panic);
        }
        if let Some(err) = failed {
            for (local, canonical) in &translations {
                self.map.forget(local, canonical);
            }
            self.last_realized = None;
            self.prepared = None;
            return Err(err);
        }
        for (local, canonical) in &translations {
            self.map
                .write(local, canonical)
                .map_err(|source| NodeError::Io {
                    path: self.repo_path.join("musubi/translation"),
                    source,
                })?;
        }
        Ok(())
    }

    /// Realizes one canonical operation whose parents are realized, as `parents`, without
    /// writing it, from its local view.
    fn realize_one(
        &self,
        canonical_id: &OperationId,
        op: &StoreOperation,
        parents: Vec<OperationId>,
        local: LocalView,
        per_machine: Arc<PerMachine>,
    ) -> Result<Realization, NodeError> {
        let LocalView { view, id, names } = local;
        let mut metadata = op.metadata.clone();
        if let Some((prefix, target)) = target_of(&metadata.description)
            && self.canonical.is_ancestor(&target, &op.parents)?
        {
            let local = self.local_of(&target).expect("ancestors realized first");
            metadata.description = format!("{prefix}{}", local.hex());
        }
        metadata.workspace_name = metadata
            .workspace_name
            .map(|key| self.realized_workspace_name(&key, &names));
        metadata
            .attributes
            .insert(CANONICAL_ATTRIBUTE.to_owned(), canonical_id.hex());
        // The id the op store gives it, worked out as it does.
        let local_op = StoreOperation {
            view_id: id,
            parents,
            metadata,
            commit_predecessors: op.commit_predecessors.clone(),
        };
        Ok(Realization {
            id: OperationId::new(blake2b_hash(&local_op).to_vec()),
            op: local_op,
            per_machine,
            view,
        })
    }

    /// The local name of the workspace that made a canonical operation, as the operation's
    /// view names it: `default` for this machine's own, `beta/default` for another's. jj's
    /// `undo` and `redo` refuse to undo another workspace's operation, and they tell
    /// workspaces apart only by name, so with the plain name `jj undo` here would undo
    /// beta's latest operation as if it were this machine's own.
    fn realized_workspace_name(
        &self,
        key: &WorkspaceName,
        names: &BTreeMap<WorkspaceNameBuf, WorkspaceNameBuf>,
    ) -> WorkspaceNameBuf {
        if let Some(name) = names.get(key) {
            return name.clone();
        }
        match workspaces::split_key(key.as_str()) {
            Some((machine, workspace)) if machine == self.machine.key() => workspace.into(),
            // A workspace the operation forgot, so its view doesn't name it.
            Some((machine, workspace)) => {
                format!("{}/{workspace}", workspaces::machine_name(machine)).into()
            }
            None => key.to_owned(),
        }
    }

    /// The per-machine fields a realization starts from: its parent's, or for a merge, the
    /// parents' merged three-way as jj merges them, as a local merge of the same operations
    /// would.
    fn inherited_per_machine(&self, parents: &[OperationId]) -> Result<Arc<PerMachine>, NodeError> {
        if let ([parent], Some((last, per_machine))) = (parents, &self.last_realized)
            && parent == last
        {
            return Ok(per_machine.clone());
        }
        let (first, rest) = parents.split_first().expect("operations have parents");
        let first_op = self.loader.load_operation(first).block_on()?;
        if rest.is_empty() {
            return Ok(Arc::new(fields_of(&first_op)?));
        }
        // jj's merge loads each parent's repository, and so its index, which for a join
        // operation, whose only ancestor is the root, means indexing all its commits anew: a
        // second or more for a large repository. Usually it isn't needed.
        if let Some(merged) = self.merged_trivially(&first_op, rest)? {
            debug_assert_eq!(*merged, *self.merged_by_jj(first_op, rest)?);
            return Ok(merged);
        }
        self.merged_by_jj(first_op, rest)
    }

    /// The per-machine fields of `first_op` and `rest` merged three-way, if at most one of
    /// them differs from its base, which the merge then takes: another machine's join
    /// operation's are its base's, the root's, as, usually, are those of other machines'
    /// operations.
    fn merged_trivially(
        &self,
        first_op: &Operation,
        rest: &[OperationId],
    ) -> Result<Option<Arc<PerMachine>>, NodeError> {
        let mut merged = fields_of(first_op)?;
        let mut ops = vec![first_op.clone()];
        for other in rest {
            let other_op = self.loader.load_operation(other).block_on()?;
            let (base, theirs) = (
                fields_of(&self.merge_base(&ops, &other_op)?)?,
                fields_of(&other_op)?,
            );
            if theirs != base {
                if merged != base {
                    return Ok(None);
                }
                merged = theirs;
            }
            ops.push(other_op);
        }
        Ok(Some(Arc::new(merged)))
    }

    /// The per-machine fields of `first_op` and `rest` merged three-way by jj.
    fn merged_by_jj(
        &self,
        first_op: Operation,
        rest: &[OperationId],
    ) -> Result<Arc<PerMachine>, NodeError> {
        let repo = self.loader.load_at(&first_op).block_on()?;
        let mut tx = repo.start_transaction();
        let mut merged = vec![first_op];
        for other in rest {
            let other_op = self.loader.load_operation(other).block_on()?;
            let base = self.merge_base(&merged, &other_op)?;
            tx.merge_operation(&base, &other_op).block_on()?;
            merged.push(other_op);
        }
        Ok(Arc::new(PerMachine::of(tx.repo().view().store_view())))
    }

    /// The base a merge of `ops` with `other` merges three-way against.
    fn merge_base(&self, ops: &[Operation], other: &Operation) -> Result<Operation, NodeError> {
        let bases = op_walk::closest_common_ancestors(ops.to_vec(), [other.clone()]).block_on()?;
        // Several closest common ancestors would need jj's recursive merge. Per-machine
        // fields only describe this machine's `.git`, and the op head's export corrects
        // them, so the first base is good enough.
        Ok(match bases.into_iter().next() {
            Some(base) => base,
            None => self.loader.root_operation().block_on(),
        })
    }

    /// Realizes a canonical operation and publishes it as an op head, in place of the op
    /// heads it descends from (heads := max(heads ∪ {op})). In a colocated
    /// repository the realization first exports its refs to `.git`, holding jj's colocated
    /// import/export lock, so that no `jj` command sees the operation before `.git` matches
    /// it.
    pub fn advance(&mut self, canonical: &OperationId) -> Result<OperationId, NodeError> {
        let realized = self.realize(canonical)?;
        // Views made ahead inherit what this changes, in a colocated repository.
        self.prepared = None;
        let superseded = self.check_mergeable(&realized)?;
        let colocation = self.colocation();
        let _lock = colocation.map(Colocation::lock).transpose()?;
        let head = match colocation {
            Some(colocation) => {
                let exported = colocation.export_refs(&self.loader, &realized)?;
                self.insert_map(exported.clone(), canonical.clone())?;
                exported
            }
            None => realized,
        };
        // The new head replaces those it descends from, as jj's own resolution of op heads
        // would: otherwise, after realizing several operations, the previous head stays, and
        // the next step merges it.
        let mut replaced = self
            .loader
            .op_store()
            .read_operation(&head)
            .block_on()?
            .parents;
        replaced.extend(superseded);
        self.loader
            .op_heads_store()
            .update_op_heads(&replaced, &head)
            .block_on()?;
        drop(_lock);
        self.replace_abandoned_working_copies()?;
        Ok(head)
    }

    /// Refuses to publish a realization that jj cannot merge with this machine's own
    /// concurrent operations. Published, it would be merged by every `jj` command here, and
    /// each would fail, or for some jj bugs panic, until someone reverted an operation by
    /// hand. Unpublished, jj keeps working, and the error says which operations to revert.
    /// Returns the op heads the realization descends from, beyond its parents, which are
    /// not concurrent with it: after a catch-up of several operations, the previous head.
    fn check_mergeable(&self, realized: &OperationId) -> Result<Vec<OperationId>, NodeError> {
        let realized_op = self.loader.load_operation(realized).block_on()?;
        let others: Vec<OperationId> = self
            .local_heads()?
            .into_iter()
            .filter(|head| head != realized && !realized_op.parent_ids().contains(head))
            .collect();
        let mut theirs = vec![];
        let mut superseded = vec![];
        for head in others {
            let op = self.loader.load_operation(&head).block_on()?;
            // Nothing of its own that the realization lacks: an ancestor.
            let beyond = std::pin::pin!(op_walk::walk_ancestors_range(
                std::slice::from_ref(&op),
                std::slice::from_ref(&realized_op),
            ))
            .try_next()
            .block_on()?;
            match beyond {
                None => superseded.push(head),
                Some(_) => theirs.push(op),
            }
        }
        if theirs.is_empty() {
            return Ok(superseded);
        }
        // This machine's operations that the hive doesn't have: one of them conflicts.
        let roots = realized_op.parents().block_on()?;
        let ours: Vec<OperationId> = op_walk::walk_ancestors_range(&theirs, &roots)
            .map_ok(|op| op.id().clone())
            .try_collect()
            .block_on()?;
        let mut operations = theirs;
        operations.push(realized_op);
        // jj merges op heads in order of their end times, and the result can depend on the
        // order, so try that order. Try the reverse too: equal times sort either way.
        operations.sort_by_key(|op| op.metadata().time.end.timestamp);
        let reversed: Vec<_> = operations.iter().rev().cloned().collect();
        for order in [operations, reversed] {
            let merged = catch_jj_panic(|| {
                self.loader
                    .merge_operations(order, None, Some("reconcile divergent operations"), [])
                    .block_on()
                    .map(|_| ())
                    .map_err(|err| format!("{err:#}"))
            });
            merged.map_err(|reason| self.unmergeable(&ours, reason))?;
        }
        Ok(superseded)
    }

    /// The error for operations of this machine's, `ours` (newest first), that jj can't
    /// merge with the hive's.
    fn unmergeable(&self, ours: &[OperationId], reason: String) -> NodeError {
        const SHOWN: usize = 5;
        let mut listed: Vec<String> = ours
            .iter()
            .take(SHOWN)
            .map(|id| {
                let description = self
                    .loader
                    .load_operation(id)
                    .block_on()
                    .map(|op| op.metadata().description.clone())
                    .unwrap_or_default();
                format!("{} ({description})", &id.hex()[..12])
            })
            .collect();
        if ours.len() > SHOWN {
            listed.push(format!("and {} older", ours.len() - SHOWN));
        }
        NodeError::Unmergeable {
            ours: ours.to_vec(),
            listed: listed.join(", "),
            reason,
        }
    }

    /// Shows other machines' workspaces in this machine's view again where they went
    /// missing: forgotten here, or dropped when jj merged a forget with concurrent
    /// operations, a removal winning. They are the other machines' own, so this machine's
    /// changes to them never count (see `canonical_view`), and the canonical view still has
    /// them. Returns whether it wrote an operation, which then needs uploading.
    pub fn show_other_workspaces(&mut self) -> Result<bool, NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        if canonical == *self.canonical.root_operation_id() {
            return Ok(false);
        }
        let view = self
            .canonical
            .read_view(&self.canonical.read_operation(&canonical)?.view_id)?;
        let names = self.local_names(&view);
        let repo = self
            .loader
            .load_at(&self.loader.load_operation(&head).block_on()?)
            .block_on()?;
        let hive_heads: Vec<CommitId> = view.head_ids.iter().cloned().collect();
        let mut tx = repo.start_transaction();
        let mut shown = false;
        for (key, commit) in &view.wc_commit_ids {
            let Some(name) = names.get(key) else {
                continue;
            };
            if self.is_own_key(key) || repo.view().get_wc_commit_id(name).is_some() {
                continue;
            }
            if !is_visible(&repo, commit)? {
                // Forgetting the workspace here hid its commit here, if it was empty, but
                // the hive kept it. Never show a commit the hive hides, though: that would
                // bring back a commit something rewrote. Such a workspace waits for its
                // machine's next operation.
                if !is_ancestor_of_any(&repo, commit, &hive_heads)? {
                    continue;
                }
                let commit = repo.store().get_commit_async(commit).block_on()?;
                tx.repo_mut().add_head(&commit).block_on()?;
            }
            tx.repo_mut()
                .set_wc_commit(name.clone(), commit.clone())
                .map_err(|err| NodeError::Index(err.to_string()))?;
            shown = true;
        }
        if !shown {
            return Ok(false);
        }
        tx.commit("musubi: show other machines' workspaces")
            .block_on()?;
        Ok(true)
    }

    /// Gives each workspace on this machine whose working-copy commit is no longer visible
    /// a fresh working-copy commit, as jj does when it abandons a working-copy commit
    /// locally. When another machine abandons it, that machine's jj already gave the
    /// workspace a new commit, which arrives with the operation; this covers the rest, such
    /// as an abandon on a machine that had forgotten this machine's workspace. Returns the
    /// workspaces it moved.
    pub fn replace_abandoned_working_copies(&mut self) -> Result<Vec<String>, NodeError> {
        // Merge through `merge_heads`, which exports to `.git`: a bare `load_at_head` would
        // merge without exporting the bookmarks the merge moves.
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        let own: BTreeSet<String> = self
            .workspaces_of(&canonical)?
            .into_keys()
            .filter(|key| self.is_own_key(key))
            .map(|key| key_workspace(&key).to_owned())
            .collect();
        let repo = self
            .loader
            .load_at(&self.loader.load_operation(&head).block_on()?)
            .block_on()?;
        let mut abandoned = vec![];
        for (name, wc) in repo.view().wc_commit_ids() {
            // Other machines replace their own.
            if own.contains(name.as_str()) && !is_visible(&repo, wc)? {
                abandoned.push((name.clone(), wc.clone()));
            }
        }
        if abandoned.is_empty() {
            return Ok(vec![]);
        }
        let mut tx = repo.start_transaction();
        let mut moved = vec![];
        for (name, wc) in abandoned {
            // Where jj would have put the new working copy had this happened on this machine:
            // the nearest visible ancestor along first parents, except that an ancestor that
            // was rewritten, not abandoned, is replaced by its rewrite. A rewrite keeps the
            // change id, so it's the change's one visible commit; a change with none was
            // abandoned, and one with several diverged, so neither says where to go.
            let mut parent = repo.store().get_commit_async(&wc).block_on()?;
            while !is_visible(&repo, parent.id())? {
                if parent.id() != &wc
                    && let Some(rewrite) = visible_rewrite(&repo, parent.change_id())?
                {
                    parent = repo.store().get_commit_async(&rewrite).block_on()?;
                    break;
                }
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

    fn insert_map(&mut self, local: OperationId, canonical: OperationId) -> Result<(), NodeError> {
        self.map
            .insert(local, canonical)
            .map_err(|source| NodeError::Io {
                path: self.repo_path.join("musubi/translation"),
                source,
            })
    }
}

/// Whether `commit` is visible: reachable from the view's heads.
/// Whether `commit` is one of `heads` or an ancestor of one.
fn is_ancestor_of_any(
    repo: &ReadonlyRepo,
    commit: &CommitId,
    heads: &[CommitId],
) -> Result<bool, NodeError> {
    let index = repo.index();
    if !index.has_id(commit).block_on().map_err(index_err)? {
        return Ok(false);
    }
    for head in heads {
        if index.has_id(head).block_on().map_err(index_err)?
            && index
                .is_ancestor(commit, head)
                .block_on()
                .map_err(index_err)?
        {
            return Ok(true);
        }
    }
    Ok(false)
}

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

/// The visible commit of `change`, if it has exactly one.
fn visible_rewrite(
    repo: &ReadonlyRepo,
    change: &jj_lib::backend::ChangeId,
) -> Result<Option<CommitId>, NodeError> {
    let Some(targets) = repo
        .resolve_change_id(change)
        .block_on()
        .map_err(index_err)?
    else {
        return Ok(None);
    };
    let mut visible = targets.visible_with_offsets().map(|(_, id)| id.clone());
    Ok(match (visible.next(), visible.next()) {
        (Some(only), None) => Some(only),
        _ => None,
    })
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

/// Descriptions in which jj names an operation's target by its id. `jj undo` and `jj redo`
/// read the id back to find where their undo stacks continue, so musubi translates it
/// between this machine's ids and canonical ones. Only targets that are ancestors are
/// translated, as they always are for undo and redo: those are canonicalized and realized
/// first, so the translation never depends on the order operations arrive in.
///
/// The `revert operation` forms of undo and redo are from a proposed jj change that makes
/// `jj undo` revert this workspace's latest operation when others' are on top of it.
const TARGET_PREFIXES: [&str; 6] = [
    "undo: restore to operation ",
    "redo: restore to operation ",
    "undo: revert operation ",
    "redo: revert operation ",
    "restore to operation ",
    "revert operation ",
];

fn target_of(description: &str) -> Option<(&'static str, OperationId)> {
    TARGET_PREFIXES.iter().find_map(|prefix| {
        let target = OperationId::try_from_hex(description.strip_prefix(prefix)?)?;
        Some((*prefix, target))
    })
}

/// The workspace part of a machine-qualified key.
fn key_workspace(key: &WorkspaceName) -> &str {
    workspaces::split_key(key.as_str()).map_or(key.as_str(), |(_, workspace)| workspace)
}

fn config_err(path: &Path, err: impl std::fmt::Display) -> NodeError {
    NodeError::Config {
        path: path.to_owned(),
        message: err.to_string(),
    }
}

/// Runs `f`, turning a panic in jj-lib into an error with the panic's message. jj 0.46
/// panics, rather than failing, when it merges concurrent operations whose rebases form a
/// loop ("graph has cycle").
fn catch_jj_panic<T>(f: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(result) => result,
        Err(panic) => Err(panic
            .downcast_ref::<&str>()
            .map(|s| (*s).to_owned())
            .or_else(|| panic.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "jj panicked".to_owned())),
    }
}

/// This machine's settings as entries: as last applied where unchanged, and otherwise
/// written now, as `stamp` says, including removals.
fn stamp_changes<T: Clone + PartialEq>(
    local: &BTreeMap<String, T>,
    applied: &BTreeMap<String, Entry<T>>,
    stamp: impl Fn() -> Stamp,
) -> BTreeMap<String, Entry<T>> {
    let names: BTreeSet<&String> = local.keys().chain(applied.keys()).collect();
    names
        .into_iter()
        .filter_map(|name| {
            let value = local.get(name);
            match applied.get(name) {
                Some(entry) if entry.value.as_ref() == value => Some(entry.clone()),
                None if value.is_none() => None,
                _ => Some(Entry {
                    value: value.cloned(),
                    stamp: stamp(),
                }),
            }
            .map(|entry| (name.clone(), entry))
        })
        .collect()
}

/// Dates each of `ours` that `hive` removed later just after the removal, so that it stands.
fn outlive_removals<T>(ours: &mut BTreeMap<String, Entry<T>>, hive: &BTreeMap<String, Entry<T>>) {
    for (name, entry) in ours {
        if let Some(removal) = hive.get(name).filter(|theirs| theirs.value.is_none())
            && removal.stamp >= entry.stamp
        {
            entry.stamp.time = removal.stamp.time + 1;
        }
    }
}

/// When `path` was last modified, in milliseconds since the epoch, if it can tell.
fn modified(path: &Path) -> i64 {
    fs::metadata(path)
        .and_then(|metadata| metadata.modified())
        .map_or_else(|_| now(), millis)
}

fn now() -> i64 {
    millis(std::time::SystemTime::now())
}

fn millis(time: std::time::SystemTime) -> i64 {
    time.duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |since| {
            i64::try_from(since.as_millis()).unwrap_or(i64::MAX)
        })
}

/// Logs each setting whose value here the hive's replaces, and whose write replaced it.
fn log_replaced(local: &SettingValues, merged: &HiveSettings) {
    fn each<T: PartialEq + std::fmt::Debug>(
        kind: &str,
        local: &BTreeMap<String, T>,
        merged: &BTreeMap<String, Entry<T>>,
    ) {
        for (name, entry) in merged {
            let old = local.get(name);
            if old != entry.value.as_ref() {
                tracing::info!(
                    "{kind} {name}: {old:?} replaced by {:?}, written by {} at {}",
                    entry.value,
                    entry.stamp.machine,
                    entry.stamp.time
                );
            }
        }
    }
    each("remote", &local.remotes, &merged.remotes);
    each("config", &local.config, &merged.config);
}
