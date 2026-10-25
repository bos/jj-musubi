//! A node's local jj repository: canonicalization, realization, and op heads.
//!
//! See "Per-machine state in a replicated view" in docs/internals/design.md and "Translation
//! layer" in docs/internals/protocol.md. [`NodeRepo`] is here, with what opens and loads it; what
//! it does is in submodules, one concern each: joining a hive (`join`), translating local
//! operations to canonical ones (`translate`) and canonical ones to local ones (`realize`), the
//! views between them (`view`), working copies (`working_copies`), the hive's settings
//! (`settings`), and what can go wrong (`error`). What a node does only when its backend is git
//! is in `git`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::thread;

use jj_lib::backend::CommitId;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::git::GitSubprocessOptions;
use jj_lib::op_store::OperationId;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::settings::UserSettings;
use jj_lib::simple_op_store::SimpleOpStore;
use pollster::FutureExt as _;

use crate::canonical::CanonicalStore;
use crate::hive_settings::HiveSettings;
use crate::objects::Backend;
use crate::objects::GitStore;
use crate::objects::ObjectStore;
use crate::objects::SimpleStore;
use crate::translation_map::TranslationMap;
use crate::workspaces::Machine;

mod error;
mod expiry;
mod git;
mod git_config;
mod join;
mod presence;
mod realize;
mod settings;
mod translate;
mod view;
mod working_copies;

pub use error::NodeError;
pub use expiry::Activity;
pub use expiry::FORGET_AFTER_KEY;
use git::Colocation;
use git::NodeGit;
pub use join::JoinSummary;
pub use realize::REALIZE_AT_ONCE;
use realize::Unwritten;
use view::LocalView;
use view::PerMachine;

/// The operation attribute naming the canonical operation a realization represents.
pub const CANONICAL_ATTRIBUTE: &str = "musubi.canonical";

pub struct NodeRepo {
    repo_path: PathBuf,
    loader: RepoLoader,
    canonical: CanonicalStore,
    map: TranslationMap,
    /// The repository's git repository, if its backend is git; otherwise it is simple.
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
    /// The last operation realized here, with this machine's own workspaces in its view:
    /// what the next one keeps where the hive has forgotten this machine.
    last_own: Option<(
        OperationId,
        Arc<BTreeMap<jj_lib::ref_name::WorkspaceNameBuf, CommitId>>,
    )>,
    /// Presence at the canonical operations asked about lately (see [`Self::presence`]).
    presences: Mutex<presence::PresenceMemo>,
    /// This machine's own workspace names as of its latest work, while the hive has forgotten
    /// it (`own_names_in`): the same for every operation until its next work.
    worked_names: Mutex<presence::WorkedNames>,
    /// The last search for the operation to revert when jj can't merge this machine's
    /// operations with the hive's (see `first_unmergeable`), so that retries of a sync stuck
    /// there don't search again.
    unmergeable: Mutex<UnmergeableMemo>,
}

/// The last search for the operation to revert, and how many searches have run.
#[derive(Clone, Default)]
struct UnmergeableMemo {
    last: Option<UnmergeableSearch>,
    searches: usize,
}

/// A search for the operation to revert: what decides its result, and the result.
#[derive(Clone)]
struct UnmergeableSearch {
    /// This machine's op heads, sorted.
    heads: Vec<OperationId>,
    /// The hive's operation, canonical, that jj can't merge with them.
    theirs: OperationId,
    culprit: Option<OperationId>,
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
        let unsupported = || NodeError::UnsupportedBackend(store.backend().name().to_owned());
        // musubi runs the git jj runs for fetches and pushes, from jj's own setting, which jj
        // reads only for the git backend.
        let git = match Backend::of(store).ok_or_else(unsupported)? {
            Backend::Git => {
                let executable = GitSubprocessOptions::from_settings(settings)?.executable_path;
                Some(NodeGit::open(&executable, repo_path, store).ok_or_else(unsupported)?)
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
            git,
            heads_mapped: false,
            last_realized: None,
            last_own: None,
            prepared: None,
            presences: Mutex::default(),
            worked_names: Mutex::default(),
            unmergeable: Mutex::default(),
            unwritten: vec![],
            joins: BTreeMap::new(),
            settings: HashMap::new(),
            repo_config: None,
            machine: load_machine(repo_path, settings.operation_hostname(), settings)?,
        };
        for (local, canonical, fingerprint) in node.read_joins()? {
            node.joins.insert(fingerprint, canonical.clone());
            node.insert_map(local, canonical)?;
        }
        Ok(node)
    }

    /// Uses `path` as this repository's jj repo config file, which holds the config the
    /// hive shares. jj keeps it outside the repository, so the caller finds it as jj does
    /// (`jj config path --repo`). Without one, no config is shared.
    pub fn with_repo_config(mut self, path: Option<PathBuf>) -> Self {
        self.repo_config = path;
        self
    }

    /// Names this machine `name` in the repository whose `.jj/repo` directory is
    /// `repo_path`, before it is first opened, which would name it after the host. Returns the
    /// machine as named, which, if it had a name already, keeps it.
    pub fn name_machine(
        repo_path: &Path,
        name: &str,
        settings: &UserSettings,
    ) -> Result<Machine, NodeError> {
        load_machine(repo_path, name, settings)
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

    /// Writes with `settings` from now on, keeping the stores open. For tests, whose
    /// clock is their own: jj-lib takes the times it gives commits and operations from the
    /// settings, and a test hands a node new ones as its clock moves on.
    pub fn set_settings(&mut self, settings: UserSettings) {
        let loader = &self.loader;
        self.loader = RepoLoader::new(
            settings,
            loader.store().clone(),
            loader.workspace_store().clone(),
            loader.op_store().clone(),
            loader.op_heads_store().clone(),
            loader.index_store().clone(),
            loader.submodule_store().clone(),
        );
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
        let Some(git) = &self.git else {
            return Ok(Box::new(SimpleStore::new(&store_path)));
        };
        // As NodeGit::open found it.
        let backend = jj_lib::git::get_git_backend(store)
            .map_err(|_| NodeError::UnsupportedBackend(store.backend().name().to_owned()))?;
        Ok(Box::new(GitStore::for_node(
            git.executable(),
            &store_path,
            backend,
        )))
    }

    /// The repository's backend, which [`Self::open`] checked is one musubi supports.
    fn backend(&self) -> Backend {
        if self.git.is_some() {
            Backend::Git
        } else {
            Backend::Simple
        }
    }

    /// Keeps what `previous`, an earlier handle on the same repository, found out about
    /// which operation to revert, as when the daemon reopens a repository after a failed
    /// sync.
    pub fn keep_found(&mut self, previous: &Self) {
        let previous = previous
            .unmergeable
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        *self
            .unmergeable
            .lock()
            .unwrap_or_else(PoisonError::into_inner) = previous;
    }

    /// How many times this handle has searched for the operation to revert, for tests.
    pub fn unmergeable_searches(&self) -> usize {
        self.unmergeable
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .searches
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
        Ok(self.merged_repo()?.op_id().clone())
    }

    /// The repository at the single head [`Self::merge_heads`] leaves.
    fn merged_repo(&self) -> Result<Arc<ReadonlyRepo>, NodeError> {
        let colocation = match self.colocation() {
            Some(colocation) if self.local_heads()?.len() > 1 => colocation,
            _ => return self.load_at_head(),
        };
        let _lock = colocation.lock()?;
        let merged = self.load_at_head()?;
        let exported =
            colocation.export_refs(&self.loader, merged.op_id(), &|op| self.is_join_point(op))?;
        if exported == *merged.op_id() {
            return Ok(merged);
        }
        self.loader
            .op_heads_store()
            .update_op_heads(std::slice::from_ref(merged.op_id()), &exported)
            .block_on()?;
        self.repo_at(&exported)
    }

    /// The repository as of its local operation `id`.
    fn repo_at(&self, id: &OperationId) -> Result<Arc<ReadonlyRepo>, NodeError> {
        let op = self.loader.load_operation(id).block_on()?;
        Ok(self.loader.load_at(&op).block_on()?)
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
            Err(reason) => Err(self.unmergeable(&self.local_heads()?, None, reason)),
        }
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

fn index_err(err: impl std::fmt::Display) -> NodeError {
    NodeError::Index(err.to_string())
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

/// This machine's identity in the repository whose `.jj/repo` directory is `repo_path`,
/// named `name` if it has none yet.
fn load_machine(
    repo_path: &Path,
    name: &str,
    settings: &UserSettings,
) -> Result<Machine, NodeError> {
    let path = repo_path.join("musubi/machine");
    Machine::load_or_create(&path, name, &settings.get_rng())
        .map_err(|source| NodeError::Io { path, source })
}

thread_local! {
    /// Whether this thread is in [`catch_jj_panic`], whose panics the hook doesn't print.
    static CATCHING_JJ_PANIC: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `f`, turning a panic in jj-lib into an error with the panic's message. jj 0.46
/// panics, rather than failing, when it merges concurrent operations whose rebases form a
/// loop ("graph has cycle"). The panic isn't printed: the error carries its message, and a
/// sync stuck there would otherwise print several at every retry.
fn catch_jj_panic<T>(f: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
    static QUIET_HOOK: std::sync::Once = std::sync::Once::new();
    QUIET_HOOK.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !CATCHING_JJ_PANIC.with(std::cell::Cell::get) {
                previous(info);
            }
        }));
    });
    let outer = CATCHING_JJ_PANIC.with(|catching| catching.replace(true));
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    CATCHING_JJ_PANIC.with(|catching| catching.set(outer));
    match caught {
        Ok(result) => result,
        Err(panic) => Err(panic
            .downcast_ref::<&str>()
            .map(|s| (*s).to_owned())
            .or_else(|| panic.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "jj panicked".to_owned())),
    }
}
