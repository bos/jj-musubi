//! The hub's durable state: canonical operations, objects, extras, and the canonical head.
//!
//! Layout under the hub directory:
//!
//! - `canonical/`: a canonical op store (see `musubi_jj::canonical`).
//! - `backend`: `git` or `simple`, the backend of the hive's repositories.
//! - `git/` and `extras/<commit>` (git backend): a bare repository holding every object the
//!   operations require, and backend extras entries a receiver cannot derive from them.
//! - `simple/` (simple backend): store files, as in a simple-backend repository.
//! - `heads`: the log of accepted heads, one `<seq> <operation id>` line each, appended and
//!   fsynced before any reply that depends on it. Its last line is the current head.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use musubi_jj::canonical::CanonicalError;
use musubi_jj::canonical::CanonicalStore;
use musubi_jj::objects;
use musubi_jj::objects::GitObjects;
use musubi_jj::objects::GitStore;
use musubi_jj::objects::ObjectError;
use musubi_jj::objects::ObjectStore;
use musubi_jj::objects::SimpleStore;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum StoreError {
    #[error(transparent)]
    Canonical(#[from] CanonicalError),
    #[error(transparent)]
    Objects(#[from] ObjectError),
    #[error("I/O error on {path}")]
    Io { path: PathBuf, source: io::Error },
    #[error("corrupt head file {0}")]
    CorruptHead(PathBuf),
    #[error("unknown backend {0:?}")]
    UnknownBackend(String),
}

/// The backend of a hive's repositories, which decides how the hub stores objects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Backend {
    Git,
    Simple,
}

impl Backend {
    pub fn name(self) -> &'static str {
        match self {
            Self::Git => "git",
            Self::Simple => "simple",
        }
    }

    pub fn parse(name: &str) -> Result<Self, StoreError> {
        match name {
            "git" => Ok(Self::Git),
            "simple" => Ok(Self::Simple),
            name => Err(StoreError::UnknownBackend(name.to_owned())),
        }
    }

    /// The object store of the hub store in `dir`, without opening the rest of it.
    pub fn object_store(self, dir: &Path) -> Box<dyn ObjectStore + 'static> {
        match self {
            Self::Git => Box::new(GitStore::for_hub(&dir.join("git"), &dir.join("extras"))),
            Self::Simple => Box::new(SimpleStore::new(&dir.join("simple"))),
        }
    }

    /// The backend's root commit, which every view may mention and no store contains.
    fn root_commit(self) -> CommitId {
        match self {
            Self::Git => CommitId::from_bytes(&[0; 20]),
            Self::Simple => CommitId::from_bytes(&[0; 64]),
        }
    }
}

fn io_err(path: &Path) -> impl FnOnce(io::Error) -> StoreError + '_ {
    move |source| StoreError::Io {
        path: path.to_owned(),
        source,
    }
}

pub struct HubStore {
    dir: PathBuf,
    backend: Backend,
    canonical: CanonicalStore,
    seq: u64,
    head: OperationId,
    /// `anc*(head)`, each operation with the sequence number at which it was first accepted.
    /// Every member is stored and closed, so walks over newly uploaded operations stop as
    /// soon as they reach it. Because `anc*(hist[j])` is exactly the operations accepted by
    /// sequence number `j`, the range `anc*(hist[i]) \ anc*(hist[j])` is the operations
    /// accepted after `j` and by `i`.
    accepted: HashMap<OperationId, u64>,
    /// `hist`: the head accepted at each sequence number.
    history: Vec<OperationId>,
}

impl HubStore {
    /// Creates an empty hub store in `dir`, which must not exist yet.
    pub fn init(dir: &Path, backend: Backend) -> Result<Self, StoreError> {
        fs::create_dir(dir).map_err(io_err(dir))?;
        match backend {
            Backend::Git => {
                let extras = dir.join("extras");
                fs::create_dir(&extras).map_err(io_err(&extras))?;
                GitObjects::init_bare(&dir.join("git"))?;
            }
            Backend::Simple => {
                SimpleStore::init(&dir.join("simple"))?;
            }
        }
        write_atomic(&dir.join("backend"), backend.name().as_bytes())?;
        let canonical = CanonicalStore::open(&dir.join("canonical"), backend.root_commit())?;
        let root = canonical.root_operation_id().clone();
        append_head(dir, 0, &root)?;
        Self::open(dir)
    }

    pub fn open(dir: &Path) -> Result<Self, StoreError> {
        let backend_path = dir.join("backend");
        let backend =
            Backend::parse(&fs::read_to_string(&backend_path).map_err(io_err(&backend_path))?)?;
        let canonical = CanonicalStore::open(&dir.join("canonical"), backend.root_commit())?;
        let history = read_heads(dir)?;
        let seq = history.len() as u64 - 1;
        let head = history[history.len() - 1].clone();
        let mut store = Self {
            dir: dir.to_owned(),
            backend,
            canonical,
            seq,
            head,
            accepted: HashMap::new(),
            history: vec![],
        };
        for (seq, head) in history.into_iter().enumerate() {
            store.accept_ancestors(&head, seq as u64)?;
            store.history.push(head);
        }
        Ok(store)
    }

    pub fn head(&self) -> (u64, &OperationId) {
        (self.seq, &self.head)
    }

    pub fn canonical(&self) -> &CanonicalStore {
        &self.canonical
    }

    pub fn backend(&self) -> Backend {
        self.backend
    }

    pub fn object_store(&self) -> Box<dyn ObjectStore + '_> {
        self.backend.object_store(&self.dir)
    }

    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// Whether `op` is in `anc*(head)`.
    pub fn is_accepted(&self, op: &OperationId) -> bool {
        self.accepted.contains_key(op)
    }

    /// Durably replaces the head. The caller has checked that `new` is closed and descends
    /// from the current head.
    pub fn set_head(&mut self, seq: u64, new: &OperationId) -> Result<(), StoreError> {
        assert_eq!(seq, self.seq + 1, "heads are accepted in sequence");
        append_head(&self.dir, seq, new)?;
        self.seq = seq;
        self.head = new.clone();
        self.history.push(new.clone());
        self.accept_ancestors(new, seq)?;
        // Upkeep, which a push mustn't fail over.
        if let Err(err) = self.mark_head(new) {
            tracing::warn!("indexing what head {} reaches: {err}", new.hex());
        }
        Ok(())
    }

    /// Tells the object store the visible heads of `head`'s view, which reach most of what a
    /// clone fetches: not what older operations' views or predecessors name that they don't,
    /// nor hidden commits that remote bookmarks point at.
    fn mark_head(&self, head: &OperationId) -> Result<(), StoreError> {
        if self.backend != Backend::Git {
            return Ok(());
        }
        let view = self
            .canonical
            .read_view(&self.canonical.read_operation(head)?.view_id)?;
        let heads: Vec<CommitId> = view.head_ids.into_iter().collect();
        Ok(self.object_store().mark_head(&heads)?)
    }

    fn accept_ancestors(&mut self, head: &OperationId, seq: u64) -> Result<(), StoreError> {
        let mut stack = vec![head.clone()];
        while let Some(id) = stack.pop() {
            if self.accepted.contains_key(&id) {
                continue;
            }
            self.accepted.insert(id.clone(), seq);
            if id != *self.canonical.root_operation_id() {
                stack.extend(self.canonical.read_operation(&id)?.parents);
            }
        }
        Ok(())
    }

    /// The sequence number at which `head` was the accepted head, if it ever was.
    pub fn head_seq(&self, head: &OperationId) -> Option<u64> {
        self.history
            .iter()
            .rposition(|h| h == head)
            .map(|i| i as u64)
    }

    /// `anc*(head) \ anc*(base)`, ancestors first. When both were accepted heads this needs
    /// no graph walk: `anc*(hist[i])` is exactly the operations accepted by sequence number
    /// `i`, since accepted heads only ever descend from earlier ones. Otherwise it walks.
    pub fn ops_since(
        &self,
        head: &OperationId,
        base: &OperationId,
    ) -> Result<Vec<OperationId>, StoreError> {
        let (Some(head_seq), Some(base_seq)) = (self.head_seq(head), self.head_seq(base)) else {
            let excluded = self
                .canonical
                .ancestors_until(std::slice::from_ref(base), |_| false)?;
            let excluded: HashSet<OperationId> = excluded.into_iter().collect();
            return Ok(self
                .canonical
                .ancestors_until(std::slice::from_ref(head), |id| excluded.contains(id))?);
        };
        let in_range = |id: &OperationId| {
            self.accepted
                .get(id)
                .is_some_and(|&seq| base_seq < seq && seq <= head_seq)
        };
        // Order ancestors first by walking from `head` through the range.
        Ok(self
            .canonical
            .ancestors_until(std::slice::from_ref(head), |id| !in_range(id))?)
    }

    /// Whether `head ∈ anc*(op)`, judged from stored operations; a missing operation counts
    /// as having no parents. Because `accepted = anc*(head)`, an accepted operation is an
    /// ancestor of `head`, and so descends from it only if it is `head` itself. The walk
    /// therefore never needs to enter accepted history.
    pub fn descends_from_head(&self, op: &OperationId) -> Result<bool, StoreError> {
        let mut seen = HashSet::new();
        let mut stack = vec![op.clone()];
        while let Some(id) = stack.pop() {
            if id == self.head {
                return Ok(true);
            }
            if self.accepted.contains_key(&id)
                || !seen.insert(id.clone())
                || !self.canonical.has_operation(&id)
            {
                continue;
            }
            stack.extend(self.canonical.read_operation(&id)?.parents);
        }
        Ok(false)
    }

    /// The commits a stored operation requires, excluding the root commit.
    pub fn required_commits(&self, op: &OperationId) -> Result<BTreeSet<CommitId>, StoreError> {
        if op == self.canonical.root_operation_id() {
            return Ok(BTreeSet::new());
        }
        let operation = self.canonical.read_operation(op)?;
        let view = self.canonical.read_view(&operation.view_id)?;
        let mut commits = objects::referenced_commits(&operation, &view);
        commits.remove(&self.backend.root_commit());
        Ok(commits)
    }

    /// Whether `closure(op)` is stored: every operation in `anc*(op)`, its view, and every
    /// object its view requires. Returns the missing pieces' descriptions if not.
    ///
    /// Accepted operations are closed (HubClosed), so the check covers only what is new:
    /// the walk stops at accepted operations, and so does the walk over objects, at the
    /// commits of those it reached and of the head.
    pub fn missing_closure(&self, op: &OperationId) -> Result<Vec<String>, StoreError> {
        let mut missing = vec![];
        let mut wanted_commits = BTreeSet::new();
        let mut boundary = BTreeSet::from([self.head.clone()]);
        let mut seen = HashSet::new();
        let mut stack = vec![op.clone()];
        while let Some(id) = stack.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            if self.accepted.contains_key(&id) {
                boundary.insert(id);
                continue;
            }
            if !self.canonical.has_operation(&id) {
                missing.push(format!("operation {}", id.hex()));
                continue;
            }
            let operation = self.canonical.read_operation(&id)?;
            if !self.canonical.has_view(&operation.view_id) {
                missing.push(format!("view {}", operation.view_id.hex()));
                continue;
            }
            let view = self.canonical.read_view(&operation.view_id)?;
            wanted_commits.extend(objects::referenced_commits(&operation, &view));
            stack.extend(operation.parents);
        }
        wanted_commits.remove(&self.backend.root_commit());
        let wanted: Vec<CommitId> = wanted_commits.into_iter().collect();
        let objects = self.object_store();
        let absent = objects.missing(&wanted)?;
        missing.extend(absent.iter().map(|id| format!("commit {}", id.hex())));
        if absent.is_empty() && missing.is_empty() {
            // Imports check connectivity, but verify anyway: a head is accepted at most
            // once, and accepting one with a hole would break every node that adopts it.
            let mut haves = BTreeSet::new();
            for id in &boundary {
                haves.extend(self.required_commits(id)?);
            }
            let haves: Vec<CommitId> = haves.into_iter().collect();
            if let Err(err) = objects.check_connected(&wanted, &haves) {
                missing.push(err.to_string());
            }
        }
        Ok(missing)
    }
}

/// Reads the log of accepted heads. A torn last line, from a crash during an append that
/// was therefore never acknowledged, is ignored.
fn read_heads(dir: &Path) -> Result<Vec<OperationId>, StoreError> {
    let path = dir.join("heads");
    let text = fs::read_to_string(&path).map_err(io_err(&path))?;
    let mut heads = vec![];
    for line in text.lines() {
        let parsed = line.split_once(' ').and_then(|(seq, id)| {
            Some((seq.parse::<usize>().ok()?, OperationId::try_from_hex(id)?))
        });
        match parsed {
            Some((seq, id)) if seq == heads.len() => heads.push(id),
            _ => break,
        }
    }
    if heads.is_empty() {
        return Err(StoreError::CorruptHead(path));
    }
    Ok(heads)
}

fn append_head(dir: &Path, seq: u64, head: &OperationId) -> Result<(), StoreError> {
    let path = dir.join("heads");
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .map_err(io_err(&path))?;
    writeln!(file, "{seq} {}", head.hex()).map_err(io_err(&path))?;
    file.sync_all().map_err(io_err(&path))
}

/// Writes `path` so that a crash leaves either the old or the new contents, durably.
fn write_atomic(path: &Path, contents: &[u8]) -> Result<(), StoreError> {
    let dir = path.parent().expect("path has a parent");
    let mut tmp = tempfile::NamedTempFile::new_in(dir).map_err(io_err(dir))?;
    tmp.write_all(contents).map_err(io_err(path))?;
    tmp.as_file().sync_all().map_err(io_err(path))?;
    tmp.persist(path).map_err(|err| io_err(path)(err.error))?;
    // Make the rename durable. Windows can't open a directory as a file to sync it, so
    // there the rename is as durable as the filesystem makes it.
    if cfg!(unix) {
        fs::File::open(dir)
            .and_then(|d| d.sync_all())
            .map_err(io_err(dir))?;
    }
    Ok(())
}
