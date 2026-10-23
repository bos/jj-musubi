//! The hub's state on disk: canonical operations, objects, extras, and the canonical head.
//!
//! Layout under the hub directory:
//!
//! - `canonical/`: a canonical op store (see `musubi_jj::canonical`).
//! - `backend`: `git` or `simple`, the backend of the hive's repositories.
//! - `git/` and `extras/<commit>` (git backend): a bare repository holding every object the
//!   operations require, and backend extras entries a receiver cannot derive from them.
//! - `simple/` (simple backend): store files, as in a simple-backend repository.
//! - `heads`: the log of accepted heads, one `<seq> <operation id>` line each, appended
//!   before any reply that depends on it. Its last line is the current head.
//!
//! None of it is synced to disk: a hub only gathers what its machines' repositories hold,
//! so one that loses its state is made again, empty, and they fill it (see "Replacing the
//! hub" in docs/design.md).

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
use musubi_jj::objects::Backend;
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

/// The git a hub runs: whatever `git` is on its `PATH`. A node runs the git jj is configured
/// to use, but a hub has no repository, and so no jj config to name one.
const GIT: &str = "git";

/// The object store of the hub store in `dir`, without opening the rest of it.
pub(crate) fn object_store(backend: Backend, dir: &Path) -> Box<dyn ObjectStore + 'static> {
    match backend {
        Backend::Git => Box::new(GitStore::for_hub(
            Path::new(GIT),
            &dir.join("git"),
            &dir.join("extras"),
        )),
        Backend::Simple => Box::new(SimpleStore::new(&dir.join("simple"))),
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
    /// `anc*(head)`, each operation with the sequence number at which it was first accepted.
    /// Every member is stored and closed, so walks over newly uploaded operations stop as
    /// soon as they reach it. Because `anc*(hist[j])` is exactly the operations accepted by
    /// sequence number `j`, the range `anc*(hist[i]) \ anc*(hist[j])` is the operations
    /// accepted after `j` and by `i`.
    accepted: HashMap<OperationId, u64>,
    /// `hist`: the head accepted at each sequence number, the root operation at 0 and the
    /// head now last.
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
                GitObjects::init_bare(Path::new(GIT), &dir.join("git"))?;
            }
            Backend::Simple => {
                SimpleStore::init(&dir.join("simple"))?;
            }
        }
        let path = dir.join("backend");
        fs::write(&path, backend.name()).map_err(io_err(&path))?;
        let canonical = CanonicalStore::open(&dir.join("canonical"), backend.root_commit())?;
        let root = canonical.root_operation_id().clone();
        append_head(dir, 0, &root)?;
        Self::open(dir)
    }

    pub fn open(dir: &Path) -> Result<Self, StoreError> {
        let backend_path = dir.join("backend");
        let name = fs::read(&backend_path).map_err(io_err(&backend_path))?;
        let name = String::from_utf8_lossy(&name);
        let backend =
            Backend::parse(&name).ok_or_else(|| StoreError::UnknownBackend(name.into_owned()))?;
        let canonical = CanonicalStore::open(&dir.join("canonical"), backend.root_commit())?;
        let history = read_heads(dir)?;
        let mut store = Self {
            dir: dir.to_owned(),
            backend,
            canonical,
            accepted: HashMap::new(),
            history: vec![],
        };
        for head in history {
            store.accept(head)?;
        }
        Ok(store)
    }

    pub fn head(&self) -> (u64, &OperationId) {
        let head = self
            .history
            .last()
            .expect("history starts at the root operation");
        (self.history.len() as u64 - 1, head)
    }

    pub fn canonical(&self) -> &CanonicalStore {
        &self.canonical
    }

    pub fn backend(&self) -> Backend {
        self.backend
    }

    pub fn object_store(&self) -> Box<dyn ObjectStore + '_> {
        object_store(self.backend, &self.dir)
    }

    /// Whether `op` is in `anc*(head)`.
    pub fn is_accepted(&self, op: &OperationId) -> bool {
        self.accepted.contains_key(op)
    }

    /// Replaces the head. The caller has checked that `new` is closed and descends from the
    /// current head.
    pub fn set_head(&mut self, seq: u64, new: &OperationId) -> Result<(), StoreError> {
        assert_eq!(
            seq,
            self.history.len() as u64,
            "heads are accepted in sequence"
        );
        let accepted = self.unaccepted_ancestors(new)?;
        append_head(&self.dir, seq, new)?;
        for id in accepted {
            self.accepted.insert(id, seq);
        }
        self.history.push(new.clone());
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
        let view = self.canonical.read_operation_view(head)?;
        let heads: Vec<CommitId> = view.head_ids.into_iter().collect();
        Ok(self.object_store().mark_head(&heads)?)
    }

    /// Accepts `head` as the next head, as read back from the log.
    fn accept(&mut self, head: OperationId) -> Result<(), StoreError> {
        let seq = self.history.len() as u64;
        for id in self.unaccepted_ancestors(&head)? {
            self.accepted.insert(id, seq);
        }
        self.history.push(head);
        Ok(())
    }

    /// The operations in `anc*(head)` not accepted yet.
    fn unaccepted_ancestors(&self, head: &OperationId) -> Result<Vec<OperationId>, StoreError> {
        let mut found = vec![];
        let mut seen = HashSet::new();
        let mut stack = vec![head.clone()];
        while let Some(id) = stack.pop() {
            if self.accepted.contains_key(&id) || !seen.insert(id.clone()) {
                continue;
            }
            if id != *self.canonical.root_operation_id() {
                stack.extend(self.canonical.read_operation(&id)?.parents);
            }
            found.push(id);
        }
        Ok(found)
    }

    /// The sequence number at which `head` was the accepted head, if it ever was: the one at
    /// which it was first accepted, since a head is accepted with its ancestors, never before.
    fn head_seq(&self, head: &OperationId) -> Option<u64> {
        let seq = *self.accepted.get(head)?;
        (self.history[usize::try_from(seq).ok()?] == *head).then_some(seq)
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
            if id == *self.head().1 {
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

    /// The commits the stored operations `ops` require, excluding the root commit.
    pub fn required_commits(&self, ops: &[OperationId]) -> Result<BTreeSet<CommitId>, StoreError> {
        Ok(self.canonical.required_commits(ops)?)
    }

    /// Whether `closure(op)` is stored: every operation in `anc*(op)`, its view, and every
    /// object its view requires. Returns the missing pieces' descriptions if not.
    ///
    /// Accepted operations are closed (HubClosed), so the check covers only what is new:
    /// the walk stops at accepted operations, and so does the walk over objects, at the
    /// commits of those it reached and of the head.
    pub fn missing_closure(&self, op: &OperationId) -> Result<Vec<String>, StoreError> {
        let mut missing = vec![];
        let mut reached = vec![];
        let mut boundary = BTreeSet::from([self.head().1.clone()]);
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
            stack.extend(operation.parents);
            reached.push(id);
        }
        let wanted: Vec<CommitId> = self.required_commits(&reached)?.into_iter().collect();
        let objects = self.object_store();
        let absent = objects.missing(&wanted)?;
        missing.extend(absent.iter().map(|id| format!("commit {}", id.hex())));
        if absent.is_empty() && missing.is_empty() {
            // Imports check connectivity, but verify anyway: a head is accepted at most
            // once, and accepting one with a hole would break every node that adopts it.
            let boundary: Vec<OperationId> = boundary.into_iter().collect();
            let haves: Vec<CommitId> = self.required_commits(&boundary)?.into_iter().collect();
            if let Err(err) = objects.check_connected(&wanted, &haves) {
                missing.push(err.to_string());
            }
        }
        Ok(missing)
    }
}

/// Reads the log of accepted heads. A line torn by a power cut makes it corrupt: the hive
/// is made again rather than recovered (see "Replacing the hub" in docs/design.md).
fn read_heads(dir: &Path) -> Result<Vec<OperationId>, StoreError> {
    let path = dir.join("heads");
    let bytes = fs::read(&path).map_err(io_err(&path))?;
    let Ok(text) = String::from_utf8(bytes) else {
        return Err(StoreError::CorruptHead(path));
    };
    let mut heads = vec![];
    for line in text.split_terminator('\n') {
        let parsed = line.split_once(' ').and_then(|(seq, id)| {
            Some((seq.parse::<usize>().ok()?, OperationId::try_from_hex(id)?))
        });
        match parsed {
            Some((seq, id)) if seq == heads.len() => heads.push(id),
            _ => return Err(StoreError::CorruptHead(path)),
        }
    }
    if heads.is_empty() || !text.ends_with('\n') {
        return Err(StoreError::CorruptHead(path));
    }
    Ok(heads)
}

/// Whether `err`, opening a store, means it is corrupt, as a power cut can leave one, rather
/// than that something failed for now, as when the hub is out of file descriptors.
pub fn is_corrupt(err: &StoreError) -> bool {
    match err {
        StoreError::CorruptHead(_) | StoreError::UnknownBackend(_) => true,
        StoreError::Io { source, .. } => source.kind() == io::ErrorKind::NotFound,
        // An operation or view that won't decode; not one that couldn't be read.
        StoreError::Canonical(err) => !err.unreadable(),
        StoreError::Objects(_) => false,
    }
}

fn append_head(dir: &Path, seq: u64, head: &OperationId) -> Result<(), StoreError> {
    let path = dir.join("heads");
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .map_err(io_err(&path))?;
    // In one write, not writeln!'s four, so that a process killed partway seldom tears it.
    file.write_all(format!("{seq} {}\n", head.hex()).as_bytes())
        .map_err(io_err(&path))
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::fmt::Write as _;

    use hegel::TestCase;
    use hegel::generators as gs;

    use super::*;

    /// A log cut where a line ends, keeping one, reads as the heads before the cut; cut
    /// anywhere else, or to nothing, it is corrupt.
    #[hegel::test(test_cases = 200)]
    fn a_cut_log_reads_only_where_a_line_ends(tc: TestCase) {
        let dir = tempfile::tempdir().unwrap();
        let count = tc.draw(gs::integers::<u8>().min_value(1).max_value(12));
        let heads: Vec<OperationId> = (0..count).map(|i| OperationId::new(vec![i; 64])).collect();
        let mut text = String::new();
        let mut ends = vec![0];
        for (seq, head) in heads.iter().enumerate() {
            writeln!(text, "{seq} {}", head.hex()).unwrap();
            ends.push(text.len());
        }
        let cut = if tc.draw(gs::booleans()) {
            ends[tc.draw(gs::integers::<usize>().max_value(ends.len() - 1))]
        } else {
            tc.draw(gs::integers::<usize>().max_value(text.len()))
        };
        fs::write(dir.path().join("heads"), &text[..cut]).unwrap();
        match ends.iter().position(|&end| end == cut) {
            Some(lines) if lines > 0 => {
                assert_eq!(read_heads(dir.path()).unwrap(), heads[..lines]);
            }
            _ => assert!(matches!(
                read_heads(dir.path()),
                Err(StoreError::CorruptHead(_))
            )),
        }
    }
}
