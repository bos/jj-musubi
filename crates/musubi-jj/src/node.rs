//! A node's local jj repository: canonicalization, realization, and op heads.
//!
//! See "Per-machine state in a replicated view" in docs/internals/design.md and "Translation
//! layer" in docs/internals/protocol.md. [`NodeRepo`] is here, with what opens and loads it; what
//! it does is in submodules, one concern each: joining a hive (`join`), translating local
//! operations to canonical ones (`translate`) and canonical ones to local ones (`realize`), the
//! views between them (`view`), working copies (`working_copies`), and what can go wrong
//! (`error`). What a node does only when its backend is git is in `git`.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::thread;

use jj_lib::backend::CommitId;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::git::GitSubprocessOptions;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::settings::UserSettings;
use jj_lib::simple_op_store::SimpleOpStore;
use pollster::FutureExt as _;

use crate::canonical::CanonicalStore;
use crate::objects::Backend;
use crate::objects::GitStore;
use crate::objects::ObjectStore;
use crate::objects::SimpleStore;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::translation_map::TranslationMap;
use crate::workspaces::Machine;

mod error;
mod expiry;
mod git;
mod git_config;
mod heads;
#[cfg(test)]
mod heads_conformance;
#[cfg(test)]
mod heads_laws;
mod identity;
mod join;
mod legacy;
mod presence;
mod publication;
mod realize;
#[cfg(test)]
mod realize_laws;
mod rewrites;
mod slashed;
mod translate;
mod view;
mod working_copies;

pub use error::NodeError;
pub use error::PublicationError;
pub use expiry::Activity;
pub use expiry::FORGET_AFTER_KEY;
use git::Colocation;
use git::NodeGit;
pub use identity::PendingRetirement;
pub use join::JoinSummary;
use join::Joins;
pub use publication::APPROVAL_FILE;
pub use publication::CHECKPOINT_ATTRIBUTE;
pub(crate) use publication::INTENT_ATTRIBUTE;
pub use publication::PublicationCache;
pub use publication::PublicationCleanup;
pub use publication::PublicationFile;
pub use publication::PublicationHeld;
pub use publication::PublicationLimits;
pub use publication::PublicationOperation;
pub use publication::PublicationReport;
pub use publication::approve_publication;
pub use publication::explicit_git_import;
pub use publication::publication_approved;
pub use publication::publication_lock;
pub(crate) use publication::retained_publication_intent;
use realize::MergeDiagnosis;
use realize::PublishedHistoryCache;
pub use realize::REALIZE_AT_ONCE;
use realize::State as RealizationState;
pub use slashed::SlashedWorkspaces;
pub use slashed::slashed_workspaces;
pub(crate) use view::LOCAL_WORKSPACES;
pub(crate) use view::RESERVED_WORKSPACES;

/// The operation attribute naming the canonical operation a realization represents.
pub const CANONICAL_ATTRIBUTE: &str = "musubi.canonical";

/// Where the sync adapter keeps the head this machine pushed that the hub took, once it knows.
pub const ACCEPTED_PUSH: &str = "accepted_push";

/// The workspaces in a local view, with their commits.
type LocalWorkspaces = std::collections::BTreeMap<jj_lib::ref_name::WorkspaceNameBuf, CommitId>;

/// Workspace names worked out already, kept to save working them out again. Each is kept with
/// the operations it was worked out from and used only for those same operations, so none is
/// ever cleared.
#[derive(Default)]
struct NameMemos {
    /// This machine's own workspaces with a `/` in their names as of the op heads last asked
    /// about (`NodeRepo::slashed_workspaces`).
    slashed: Mutex<slashed::SlashedMemo>,
    /// Where jj's workspace store records the directories of the names asked about, while
    /// its file is unchanged.
    records: Mutex<slashed::Records>,
    /// The workspaces, with their commits, in the view of the operation `canonical_view` last
    /// canonicalized, usually the next one's parent.
    last_view: Mutex<Option<(jj_lib::op_store::OperationId, Arc<LocalWorkspaces>)>>,
    /// Private ownership reconstructed from immutable native operation views.
    private:
        Mutex<HashMap<jj_lib::op_store::OperationId, BTreeSet<jj_lib::ref_name::WorkspaceNameBuf>>>,
    /// This machine's own workspace names as of its latest work, while the hive has forgotten
    /// it (`own_names_in`): the same for every operation until its next work.
    worked: Mutex<presence::WorkedNames>,
}

/// A local jj repository's identities, translation, and publication state.
///
/// Open with [`Self::open_as`] when joining under a chosen machine identity, or
/// [`Self::open`] for an existing copy. [`Self::loader`], [`Self::canonical_store`] and
/// [`Self::object_store`] give the integration layers access to its stores.
///
/// [`Self::canonicalize`] translates native history into shared identities. In the other
/// direction, [`Self::realize`] writes a local representation without publishing it, while
/// [`Self::advance`] also publishes its native frontier. [`Self::realize_pending`] overlaps
/// construction and writes; its returned identity is known in memory before the stores and
/// translation file are complete. Call [`Self::settle`] before reading those queued results.
///
/// Dropping a handle attempts to settle pending writes, logging any error. During unwinding
/// it leaves the writers to finish without recording their translations. Call `settle`
/// explicitly when its success matters; dropping cannot report failure to the caller.
pub struct NodeRepo {
    repo_path: PathBuf,
    loader: RepoLoader,
    /// The root of the local op store.
    local_root: LocalOp,
    canonical: CanonicalStore,
    map: TranslationMap,
    /// The repository's git repository, if its backend is git; otherwise it is simple.
    git: Option<NodeGit>,
    /// Whether every operation reachable from the op heads has been mapped since opening.
    heads_mapped: bool,
    machine: Machine,
    identities: identity::History,
    /// The join points, what they stand for, and the history from before them.
    joins: Joins,
    /// jj's repo config file for this repository, used to read this copy's expiry policy.
    repo_config: Option<PathBuf>,
    /// Construction context, prepared views, and writes not yet recorded in the map.
    realizing: RealizationState,
    /// Exact native frontier ancestry used when publishing received operations.
    published: PublishedHistoryCache,
    /// Workspace names worked out already.
    names: NameMemos,
    /// Presence at the canonical operations asked about lately (see [`Self::presence`]).
    presences: Arc<crate::canonical::PresenceMemo>,
    /// Merge diagnosis retained across retries and reopening the same repository.
    merge_diagnosis: MergeDiagnosis,
    /// Local operations canonicalized on a local operation that isn't the preferred realization
    /// of its canonical parent, as a `jj` command writes that loaded the repository before it,
    /// parents first: to reparent onto that realization.
    late: Vec<LocalOp>,
    /// Whether an earlier release left drops recorded here that it hadn't published
    /// (`legacy`).
    legacy_drops: bool,
    /// Whether this handle holds jj's op-heads lock (`heads::HeadsLock`).
    heads_locked: Arc<std::sync::atomic::AtomicBool>,
    /// For tests of races: what to run in the next move of op heads.
    head_races: heads::HeadRaces,
}

impl Drop for NodeRepo {
    fn drop(&mut self) {
        // Best-effort completion cannot report an error to the caller. While unwinding, a
        // writer's panic passed on would abort the process; the writes finish anyway, and
        // their unrecorded translations are reconstructed when needed after reopening.
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
    /// Opens the repository whose `.jj/repo` directory is `repo_path`, giving it a machine key
    /// named after the host if it has none, as tests want. musubi's commands make a key only
    /// when the hub takes a join (docs/internals/copies.md, R6), so they open with
    /// [`Self::open_as`].
    pub fn open(repo_path: &Path, settings: &UserSettings) -> Result<Self, NodeError> {
        let machine = load_machine(repo_path, settings.operation_hostname(), settings)?;
        Self::open_as(repo_path, settings, machine)
    }

    /// Opens the repository whose `.jj/repo` directory is `repo_path` as `machine`'s, whatever
    /// key it has, storing none: for a repository about to join a hive as `machine`
    /// ([`Self::machine_of`], [`Self::new_machine`]), which keeps its key only once the hub
    /// takes it ([`Self::keep_machine`]).
    pub fn open_as(
        repo_path: &Path,
        settings: &UserSettings,
        machine: Machine,
    ) -> Result<Self, NodeError> {
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
            Backend::Git(_) => {
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
        let legacy_drops = legacy::remove_records(&musubi_dir)?;
        let mut node = Self {
            repo_path: repo_path.to_owned(),
            local_root: LocalOp(loader.op_store().root_operation_id().clone()),
            loader,
            canonical,
            map,
            git,
            heads_mapped: false,
            realizing: RealizationState::default(),
            published: PublishedHistoryCache::default(),
            merge_diagnosis: MergeDiagnosis::default(),
            names: NameMemos::default(),
            presences: Arc::default(),
            joins: Joins::default(),
            repo_config: None,
            machine,
            identities: identity::History::load(&musubi_dir)?,
            late: vec![],
            legacy_drops,
            heads_locked: Arc::default(),
            head_races: heads::HeadRaces::default(),
        };
        for (local, canonical, fingerprint) in node.read_joins()? {
            node.joins
                .record(local.clone(), canonical.clone(), fingerprint);
            node.insert_map(local, canonical)?;
        }
        Ok(node)
    }

    /// Uses `path` as this repository's local jj repo config file, so that its
    /// `musubi.forget-after` can be read afresh. jj keeps this outside the repository.
    pub fn with_repo_config(mut self, path: Option<PathBuf>) -> Self {
        self.repo_config = path;
        self
    }

    /// The operation the hub accepted that this machine fetches from (the sync adapter's
    /// `accepted_base`), if it has one.
    pub(in crate::node) fn stored_base(&self) -> Option<CanonicalOp> {
        let hex = std::fs::read_to_string(self.repo_path.join("musubi/accepted_base")).ok()?;
        jj_lib::op_store::OperationId::try_from_hex(hex.trim()).map(CanonicalOp)
    }

    /// The machine whose key the repository whose `.jj/repo` directory is `repo_path` has, if
    /// it has one.
    pub fn machine_of(repo_path: &Path) -> Result<Option<Machine>, NodeError> {
        let path = machine_path(repo_path);
        Machine::load(&path).map_err(|source| NodeError::Io { path, source })
    }

    /// A new key named `name`, distinct from the checkout's retired keys even when
    /// `debug.randomness-seed` makes `settings`' randomness repeatable.
    pub fn new_machine(
        repo_path: &Path,
        name: &str,
        settings: &UserSettings,
    ) -> Result<Machine, NodeError> {
        let history = identity::History::load(&repo_path.join("musubi"))?;
        let rng = settings.get_rng();
        loop {
            let machine = Machine::new(name, &rng);
            if !history.retired(&machine) {
                return Ok(machine);
            }
        }
    }

    /// Gives the repository whose `.jj/repo` directory is `repo_path` `machine`'s key, unless
    /// it has it already. Fails if it has another.
    pub fn keep_machine(repo_path: &Path, machine: &Machine) -> Result<(), NodeError> {
        let path = machine_path(repo_path);
        let io = |source| NodeError::Io {
            path: path.clone(),
            source,
        };
        match Machine::load(&path).map_err(io)? {
            Some(kept) if kept == *machine => Ok(()),
            Some(kept) => Err(io(std::io::Error::other(format!(
                "it has machine key {} already, not {}",
                kept.key(),
                machine.key()
            )))),
            None => machine.keep(&path).map_err(io),
        }
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

    /// How the repository shares its git repository with a working copy, if it does.
    fn colocation(&self) -> Option<&Colocation> {
        self.git.as_ref()?.colocation()
    }

    /// A workspace where native jj takes the same Git import/export lock as musubi.
    /// This can be a secondary workspace of a non-colocated primary workspace.
    pub fn colocated_workspace(&self) -> Option<&Path> {
        self.git.as_ref()?.colocated_workspace()
    }

    /// The commits the stored canonical operations `ops` require, excluding the root commit.
    pub fn required_commits(
        &self,
        canonical: &[CanonicalOp],
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
        Backend::of(self.loader.store()).expect("checked when opened")
    }

    /// Keeps what `previous`, an earlier handle on the same repository, found out about
    /// which operation to revert, as when the daemon reopens a repository after a failed
    /// sync.
    pub fn keep_found(&mut self, previous: &Self) {
        self.merge_diagnosis.keep_from(&previous.merge_diagnosis);
    }

    pub fn local_heads(&self) -> Result<Vec<LocalOp>, NodeError> {
        let heads = self.loader.op_heads_store().get_op_heads().block_on()?;
        Ok(heads.into_iter().map(LocalOp).collect())
    }

    /// Lets jj merge the op heads if there are several, as any `jj` command would. Returns
    /// the resulting single head.
    ///
    /// The merge can move bookmarks as jj rebases descendants of rewritten commits. In a
    /// colocated repository musubi merges and exports under jj's import/export lock. The
    /// exported copy replaces the merge as the op head and has the same canonical form.
    pub fn merge_heads(&mut self) -> Result<LocalOp, NodeError> {
        Ok(LocalOp(self.merged_repo()?.op_id().clone()))
    }

    /// The repository at the single head [`Self::merge_heads`] leaves.
    fn merged_repo(&mut self) -> Result<Arc<ReadonlyRepo>, NodeError> {
        let repo = match self.colocation() {
            Some(colocation) => {
                let heads = self.local_heads()?;
                // A head can arrive after the first read. Reread as jj's loader would,
                // but load that exact operation on the fast path so a later arrival
                // cannot trigger a merge without the Git export lock.
                if heads.len() <= 1
                    && let [head] = self.local_heads()?.as_slice()
                {
                    self.load_head(Some(head))
                } else {
                    self.merge_and_export_heads(colocation)
                }
            }
            None => self.load_head(None),
        }?;
        Ok(repo)
    }

    fn merge_and_export_heads(
        &self,
        colocation: &Colocation,
    ) -> Result<Arc<ReadonlyRepo>, NodeError> {
        let _lock = colocation.lock()?;
        loop {
            let merged = self.load_head(None)?;
            let exported = colocation.export_refs(
                &self.loader,
                &LocalOp(merged.op_id().clone()),
                &|op| self.is_join_point(op),
                &[],
            )?;
            if exported.0 == *merged.op_id() {
                return Ok(merged);
            }
            // Only while the merge is still the op head: a `jj` command in a workspace that
            // doesn't take the colocated lock, or `jj op abandon`, which takes no lock, can
            // have replaced it. Then the heads are merged and exported again, the colocated
            // lock held throughout, so that `.git` is never ahead of the op heads it shows.
            let merged = LocalOp(merged.op_id().clone());
            let new = std::slice::from_ref(&exported);
            if self.replace_heads(std::slice::from_ref(&merged), new, true)? {
                return self.repo_at(&exported);
            }
        }
    }

    /// The repository as of its local operation `id`.
    fn repo_at(&self, id: &LocalOp) -> Result<Arc<ReadonlyRepo>, NodeError> {
        let op = self.loader.load_operation(&id.0).block_on()?;
        Ok(self.loader.load_at(&op).block_on()?)
    }

    /// Loads the observed head, or lets jj resolve the current heads if none was supplied.
    fn load_head(&self, head: Option<&LocalOp>) -> Result<Arc<ReadonlyRepo>, NodeError> {
        let loaded = catch_jj_panic(|| {
            Ok(match head {
                Some(head) => self.repo_at(head),
                None => self
                    .loader
                    .load_at_head(None)
                    .block_on()
                    .map_err(NodeError::from),
            })
        });
        match loaded {
            Ok(Ok(repo)) => Ok(repo),
            Ok(Err(err)) => Err(err),
            Err(reason) => Err(self.unmergeable_heads(&self.local_heads()?, reason)),
        }
    }

    fn insert_map(&mut self, local: LocalOp, canonical: CanonicalOp) -> Result<(), NodeError> {
        if self.published.contains(&local) && self.canonical_of(&local).as_ref() != Some(&canonical)
        {
            self.invalidate_published_history();
        }
        self.map
            .insert(local, canonical)
            .map_err(|source| NodeError::Io {
                path: self.repo_path.join("musubi/translation"),
                source,
            })
    }
}

// Deliberate test support, compiled for cross-crate integration and fault tests.
// Keep these controls separate from the normal repository API without changing coverage.
impl NodeRepo {
    /// Writes with `settings` from now on, keeping the stores open. For tests, whose
    /// clock is their own: jj-lib takes the times it gives commits and operations from the
    /// settings, and a test hands a node new ones as its clock moves on.
    #[doc(hidden)]
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

    /// How many times this handle has searched for the operation to revert, for tests.
    #[doc(hidden)]
    pub fn unmergeable_searches(&self) -> usize {
        self.merge_diagnosis.searches()
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
    let path = machine_path(repo_path);
    Machine::load_or_create(&path, name, &settings.get_rng())
        .map_err(|source| NodeError::Io { path, source })
}

/// Where the repository whose `.jj/repo` directory is `repo_path` keeps its machine key.
fn machine_path(repo_path: &Path) -> PathBuf {
    repo_path.join("musubi/machine")
}

thread_local! {
    /// Whether this thread is in [`catch_jj_panic`], whose panics the hook doesn't print.
    #[cfg_attr(
        any(target_os = "illumos", target_os = "solaris"),
        allow(
            clippy::missing_const_for_thread_local,
            reason = "clippy wrongly reports this on illumos, but only when the \
                      rust-src component is installed, so it's allowed rather than expected"
        )
    )]
    static CATCHING_JJ_PANIC: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs `f`, turning a panic in jj-lib into an error with the panic's message. jj 0.47
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
