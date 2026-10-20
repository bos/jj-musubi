//! A node's local jj repository: canonicalization, realization, and op heads.
//!
//! See "Per-machine state in a replicated view" in docs/design.md and "Translation layer" in
//! docs/protocol.md.

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use futures::TryStreamExt as _;
use jj_lib::config::ConfigFile;
use jj_lib::config::ConfigNamePathBuf;
use jj_lib::config::ConfigSource;
use jj_lib::config::ConfigValue;
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
use jj_lib::op_store::RemoteView;
use jj_lib::op_store::View;
use jj_lib::op_walk;
use jj_lib::ref_name::GitRefNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::repo::RepoLoaderError;
use jj_lib::repo::StoreLoadError;
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
use crate::hive_settings;
use crate::hive_settings::HiveSettings;
use crate::objects;
use crate::objects::GitObjects;
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
            git_remote: view
                .remote_views
                .get(REMOTE_NAME_FOR_LOCAL_GIT_REPO)
                .cloned(),
            git_heads: view.git_heads.clone(),
        }
    }

    fn apply_to(self, view: &mut View) {
        view.git_refs = self.git_refs;
        if let Some(remote) = self.git_remote {
            view.remote_views
                .insert(REMOTE_NAME_FOR_LOCAL_GIT_REPO.to_owned(), remote);
        }
        view.git_heads = self.git_heads;
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
    /// The hive's settings as of canonical operations, as computed so far.
    settings: HashMap<OperationId, Option<HiveSettings>>,
    /// jj's repo config file for this repository, which holds the config the hive shares.
    repo_config: Option<PathBuf>,
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
    /// machine's workspaces under machine-qualified keys. This machine's come from `view`.
    /// The others' come from the canonical parents, except where this operation moved them:
    /// they are workspaces in `view` too, which jj moves when it rewrites or abandons their
    /// commits, or restores an older view. Adding, forgetting or renaming another machine's
    /// workspace here changes nothing: its workspaces are its own. Depends only on its
    /// arguments, so canonicalizing again after a crash gives the same result.
    fn canonical_view(
        &self,
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
        // abandon that machine's working copy: keep the commit visible.
        for commit in forgotten.values() {
            if parent_heads.contains(commit) {
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
    /// ancestor recorded, merged three-way where concurrent operations met, or `None` if no
    /// ancestor recorded any.
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
                let settings = HiveSettings::parse(text).map_err(|err| NodeError::Settings {
                    op: id.hex(),
                    message: err.to_string(),
                })?;
                self.settings.insert(id, Some(settings));
                stack.pop();
                continue;
            }
            // A merge needs its parents' settings and its merge bases'.
            let parents = &operation.parents;
            let mut bases = vec![];
            for i in 1..parents.len() {
                let base = self
                    .canonical
                    .closest_common_ancestors(&parents[..i], &parents[i..=i])?
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| root.clone());
                bases.push(base);
            }
            let missing: Vec<OperationId> = parents
                .iter()
                .chain(&bases)
                .filter(|needed| !self.settings.contains_key(*needed))
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.extend(missing);
                continue;
            }
            let mut merged = self.settings[&parents[0]].clone();
            for (other, base) in parents[1..].iter().zip(&bases) {
                let (theirs, base) = (&self.settings[other], &self.settings[base]);
                merged = if merged.is_none() && theirs.is_none() && base.is_none() {
                    None
                } else {
                    Some(HiveSettings::merge(
                        &merged.unwrap_or_default(),
                        &base.clone().unwrap_or_default(),
                        &theirs.clone().unwrap_or_default(),
                    ))
                };
            }
            self.settings.insert(id, merged);
            stack.pop();
        }
        Ok(self.settings[op].clone())
    }

    /// Brings this machine's settings and the hive's together, three-way against what they
    /// agreed on last time: records this machine's changes for the hive, in an operation of
    /// its own, and applies the hive's changes here. A machine that joins a hive with
    /// settings adds its own remotes to the hive's, but takes the hive's where both have a
    /// remote of the same name; the first machine's settings become the hive's. Returns
    /// whether it recorded a change, which then needs uploading.
    pub fn reconcile_settings(&mut self) -> Result<bool, NodeError> {
        let head = self.merge_heads()?;
        let canonical = self.canonicalize(&head)?;
        let state = self.read_settings_state()?;
        if let Some((op, hive, _)) = &state {
            self.settings
                .entry(op.clone())
                .or_insert_with(|| hive.clone());
        }
        let hive = self.settings_at(&canonical)?;
        let mut extra: Vec<String> = hive
            .as_ref()
            .map(HiveSettings::extra_config_keys)
            .unwrap_or_default();
        if let Some((_, _, settings)) = &state {
            extra.extend(settings.extra_config_keys());
        }
        let local = self.local_settings(&extra)?;
        let base = match (&state, &hive) {
            (Some((_, _, settings)), _) => settings.clone(),
            (None, Some(hive)) => HiveSettings {
                remotes: local
                    .remotes
                    .iter()
                    .filter(|(name, _)| hive.remotes.contains_key(*name))
                    .map(|(name, remote)| (name.clone(), remote.clone()))
                    .collect(),
                config: local
                    .config
                    .iter()
                    .filter(|(key, _)| hive.config.contains_key(*key))
                    .map(|(key, value)| (key.clone(), value.clone()))
                    .collect(),
            },
            (None, None) => HiveSettings::default(),
        };
        let current = hive.clone().unwrap_or_default();
        let merged = HiveSettings::merge(&local, &base, &current);
        let (mut at, mut hive_now, mut recorded) = (canonical, hive, false);
        if merged != current {
            let op = self.record_settings(&head, &merged)?;
            at = self.canonicalize(&op)?;
            self.settings.insert(at.clone(), Some(merged.clone()));
            hive_now = Some(merged.clone());
            recorded = true;
        }
        if merged != local {
            self.apply_settings(&local, &merged)?;
        }
        self.write_settings_state(&SettingsState {
            op: at.hex(),
            hive: hive_now,
            settings: merged,
        })?;
        Ok(recorded)
    }

    fn git_objects(&self) -> Option<GitObjects> {
        let backend = jj_lib::git::get_git_backend(self.loader.store()).ok()?;
        Some(GitObjects::new(backend.git_repo_path()))
    }

    /// The settings this machine has now: its git remotes, and the shared keys of its repo
    /// config, including `extra` keys.
    fn local_settings(&self, extra: &[String]) -> Result<HiveSettings, NodeError> {
        Ok(HiveSettings {
            remotes: match self.git_objects() {
                Some(git) => git.remotes()?,
                None => BTreeMap::new(),
            },
            config: self.read_shared_config(extra)?,
        })
    }

    fn apply_settings(&self, from: &HiveSettings, to: &HiveSettings) -> Result<(), NodeError> {
        if let Some(git) = self.git_objects() {
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
        let view = self.canonical_view(view, &parents, op.commit_predecessors.as_ref())?;
        let mut metadata = op.metadata.clone();
        if let Some((prefix, target)) = target_of(&metadata.description)
            && let Some(canonical) = self.canonical_of(&target)
            && self.canonical.is_ancestor(&canonical, &parents)?
        {
            metadata.description = format!("{prefix}{}", canonical.hex());
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
        // Every machine's working copies become workspaces here: this machine's under their
        // own names, the others' as `beta/default`. This machine's own may have moved: when
        // another machine rewrites, abandons or restores a working-copy commit, its jj moves
        // the workspace, and the canonical view records where to.
        let names = self.local_names(&view);
        view.wc_commit_ids = std::mem::take(&mut view.wc_commit_ids)
            .into_iter()
            .filter_map(|(key, commit)| Some((names.get(&key)?.clone(), commit)))
            .collect();
        self.inherited_per_machine(&parents)?.apply_to(&mut view);
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
        self.check_mergeable(&realized)?;
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

    /// Refuses to publish a realization that jj cannot merge with this machine's own
    /// concurrent operations. Published, it would be merged by every `jj` command here, and
    /// each would fail, or for some jj bugs panic, until someone reverted an operation by
    /// hand. Unpublished, jj keeps working, and the error says which operations to revert.
    fn check_mergeable(&self, realized: &OperationId) -> Result<(), NodeError> {
        let realized_op = self.loader.load_operation(realized).block_on()?;
        let concurrent: Vec<OperationId> = self
            .local_heads()?
            .into_iter()
            .filter(|head| head != realized && !realized_op.parent_ids().contains(head))
            .collect();
        if concurrent.is_empty() {
            return Ok(());
        }
        let mut theirs = vec![];
        for head in &concurrent {
            theirs.push(self.loader.load_operation(head).block_on()?);
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
        Ok(())
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
        let missing: Vec<(WorkspaceNameBuf, CommitId)> = view
            .wc_commit_ids
            .iter()
            .filter(|(key, _)| !self.is_own_key(key))
            .filter_map(|(key, commit)| {
                let name = names.get(key)?;
                let shown = repo.view().get_wc_commit_id(name).is_some();
                (!shown).then(|| (name.clone(), commit.clone()))
            })
            .collect();
        if missing.is_empty() {
            return Ok(false);
        }
        let mut tx = repo.start_transaction();
        for (name, commit) in missing {
            // Forgetting the workspace here hid its commit here, if it was empty.
            let commit = repo.store().get_commit_async(&commit).block_on()?;
            tx.repo_mut().add_head(&commit).block_on()?;
            tx.repo_mut()
                .set_wc_commit(name, commit.id().clone())
                .map_err(|err| NodeError::Index(err.to_string()))?;
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
