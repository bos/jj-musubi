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
//!   before any reply that depends on it. Its last line is the current head. A head accepted
//!   with a record, a supersede's, has the record's operation ids after it on its line, so
//!   that a log cut short loses heads and records together (docs/internals/design.md,
//!   "Abandoning operations"). Once the hub has pruned its records, the log starts with a
//!   `pruned <count> <digest>` line, and names every head as the records left the history
//!   then; it is written again whole at each prune.
//!
//! None of it is synced to disk: a hub only gathers what its machines' repositories hold,
//! so one that loses its state is made again, empty, and they fill it (see "Replacing the
//! hub" in docs/internals/design.md).

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use musubi_jj::canonical::CanonicalError;
use musubi_jj::canonical::CanonicalStore;
use musubi_jj::canonical::Contraction;
use musubi_jj::canonical::PresenceMemo;
use musubi_jj::objects::Backend;
use musubi_jj::objects::GitObjects;
use musubi_jj::objects::GitStore;
use musubi_jj::objects::ObjectError;
use musubi_jj::objects::ObjectStore;
use musubi_jj::objects::SimpleStore;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::presence::Presence;
use musubi_jj::records::HubOp;
use musubi_jj::records::Record;
use musubi_jj::records::RecordDigest;
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
    /// Unique originals in the accepted history, indexed once at acceptance.
    accepted_origins: HashMap<OperationId, OperationId>,
    /// `hist`: the head accepted at each sequence number, the root operation at 0 and the
    /// head now last. Each as the records now name it, or as it was, if they dropped it.
    history: Vec<OperationId>,
    /// How many of its first records the hub has pruned, keeping of them only this, and
    /// their digest, `digests[0]`.
    pruned: usize,
    /// The records after those, in the order they were taken, and the digest of the pruned
    /// ones and of each first so many after them.
    records: Vec<Record>,
    digests: Vec<RecordDigest>,
    /// What each operation the records superseded became when one did: its rewrite, or for a
    /// dropped one, what its parents were then, which later records may have superseded
    /// ([`HubStore::current`] composes them). None that a pruned record superseded.
    superseded: HashMap<OperationId, Vec<OperationId>>,
    /// Every operation a record named, but a pruned one.
    named: HashSet<OperationId>,
    /// The original identity of every operation a record dropped, but a pruned one.
    named_origins: HashSet<OperationId>,
    /// Which copies are present at the head, as worked out last.
    presences: PresenceMemo,
}

/// What the history becomes with more dropped: what [`HubStore::contract`] works out.
pub struct Contracted {
    dropped_origins: HashSet<OperationId>,
    /// The head whose history this is.
    pub head: OperationId,
    pub dropped: Vec<OperationId>,
    pub images: HashMap<OperationId, Vec<OperationId>>,
}

impl Contracted {
    /// What `op` becomes.
    pub fn image(&self, op: &OperationId) -> Vec<OperationId> {
        self.images
            .get(op)
            .cloned()
            .unwrap_or_else(|| vec![op.clone()])
    }
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
        let root = canonical.root_operation_id().0.clone();
        append_head(dir, 0, &root, &[])?;
        Self::open(dir)
    }

    pub fn open(dir: &Path) -> Result<Self, StoreError> {
        let backend_path = dir.join("backend");
        let name = fs::read(&backend_path).map_err(io_err(&backend_path))?;
        let name = String::from_utf8_lossy(&name);
        let backend =
            Backend::parse(&name).ok_or_else(|| StoreError::UnknownBackend(name.into_owned()))?;
        let canonical = CanonicalStore::open(&dir.join("canonical"), backend.root_commit())?;
        let (pruned, history) = read_heads(dir)?;
        let (pruned, digest) = pruned.unwrap_or((0, RecordDigest::root()));
        let mut store = Self {
            dir: dir.to_owned(),
            backend,
            canonical,
            accepted: HashMap::new(),
            accepted_origins: HashMap::new(),
            history: vec![],
            pruned,
            records: vec![],
            digests: vec![digest],
            superseded: HashMap::new(),
            named: HashSet::new(),
            named_origins: HashSet::new(),
            presences: PresenceMemo::default(),
        };
        for (head, record) in history {
            if !record.is_empty() {
                let record: Vec<HubOp> = record.into_iter().map(hub_op).collect();
                let contracted = store.contract(&record)?;
                store.take(contracted);
            }
            store.accept(head)?;
        }
        Ok(store)
    }

    /// The records the hub remembers, those after the ones it pruned, oldest first.
    pub fn records(&self) -> &[Record] {
        &self.records
    }

    /// How many records the hub has taken, pruned or not.
    pub fn record_count(&self) -> usize {
        self.pruned + self.records.len()
    }

    /// How many of its first records the hub has pruned.
    pub fn pruned(&self) -> usize {
        self.pruned
    }

    /// The digest of the first `count` records, if there are as many and the hub hasn't
    /// pruned more.
    pub fn digest(&self, count: usize) -> Option<&RecordDigest> {
        self.digests.get(count.checked_sub(self.pruned)?)
    }

    /// Which copies are present at the head, those whose work it has but for work a forget
    /// of theirs saw, and which the history has known (docs/internals/design.md, "Presence").
    pub fn presence(&self) -> Result<Arc<Presence<CanonicalOp>>, StoreError> {
        let head = CanonicalOp(self.head().1.clone());
        Ok(self.presences.presence(&self.canonical, &head)?)
    }

    /// Prunes every record the hub has: forgets their ids, the ids they superseded and the
    /// original identities they dropped, keeping their count and digest, and writes the `heads` log again, so that opening the
    /// store takes none of them again. A head they dropped stays in the history as the first
    /// accepted operation of what it became, or the root (docs/internals/design.md, "What an
    /// abandon costs the hub").
    pub fn prune(&mut self) -> Result<(), StoreError> {
        if self.records.is_empty() {
            return Ok(());
        }
        let root = self.canonical.root_operation_id().0.clone();
        let renamed: Vec<OperationId> = self
            .history
            .iter()
            .map(|head| {
                if self.accepted.contains_key(head) {
                    return head.clone();
                }
                self.current(head)
                    .into_iter()
                    .find(|op| self.accepted.contains_key(op))
                    .unwrap_or_else(|| root.clone())
            })
            .collect();
        let digest = self.digests.last().expect("the pruned digest").clone();
        let pruned = self.record_count();
        write_heads(&self.dir, (pruned, &digest), &renamed)?;
        self.history = renamed;
        self.pruned = pruned;
        self.records.clear();
        self.digests = vec![digest];
        self.superseded = HashMap::new();
        self.named = HashSet::new();
        self.named_origins = HashSet::new();
        Ok(())
    }

    /// How many ids of the history before the records' renamings the hub keeps in memory:
    /// what the records dropped and superseded, and the original identities they dropped.
    pub fn remembered_ids(&self) -> usize {
        self.named.len() + self.superseded.len() + self.named_origins.len()
    }

    /// Whether the records dropped or superseded `op`: it was, or is, no operation of the
    /// history as they name it.
    pub fn is_superseded(&self, op: &OperationId) -> bool {
        self.named.contains(op) || self.superseded.contains_key(op)
    }

    /// What `op` is now: itself, or what the records superseded it with. Never an operation
    /// the records superseded.
    pub fn current(&self, op: &OperationId) -> Vec<OperationId> {
        musubi_jj::canonical::current(&self.superseded, op)
    }

    /// The history with `dropped` dropped too: every accepted operation's image, the rewrites
    /// written to the store. Ids the history lacks drop nothing.
    pub fn contract(&self, dropped: &[HubOp]) -> Result<Contracted, StoreError> {
        let dropped: Vec<OperationId> = dropped
            .iter()
            .map(|op| op.0.0.clone())
            .filter(|op| !self.is_superseded(op))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let mut contraction =
            Contraction::new(&self.canonical, dropped.iter().cloned().map(CanonicalOp))?;
        let head = self.head().1.clone();
        if !contraction.is_empty() {
            contraction.images(&self.canonical, &CanonicalOp(head.clone()))?;
        }
        let images = contraction
            .into_images()
            .into_iter()
            .map(|(old, new)| (old.0, new.into_iter().map(|op| op.0).collect()))
            .collect();
        let dropped_origins = dropped
            .iter()
            .filter(|id| self.canonical.has_operation(&CanonicalOp((*id).clone())))
            .map(|id| self.canonical.original_id(&CanonicalOp(id.clone())))
            .collect::<Result<_, _>>()?;
        Ok(Contracted {
            dropped_origins,
            head,
            dropped,
            images,
        })
    }

    /// Takes a contraction as the next record: renames the history and what is accepted.
    fn take(&mut self, contracted: Contracted) {
        let Contracted {
            dropped,
            images,
            dropped_origins,
            ..
        } = contracted;
        if dropped.is_empty() {
            return;
        }
        let image = |op: &OperationId| images.get(op).cloned().unwrap_or_else(|| vec![op.clone()]);
        self.accepted_origins.retain(|_, op| {
            if dropped.contains(op) {
                return false;
            }
            if let Some(rewrite) = images.get(op).and_then(|ops| ops.first()) {
                *op = rewrite.clone();
            }
            true
        });
        self.named_origins.extend(dropped_origins);
        let accepted = std::mem::take(&mut self.accepted);
        for (op, seq) in accepted {
            if let Some(images) = images.get(&op) {
                if let [rewrite] = images.as_slice()
                    && !dropped.contains(&op)
                {
                    self.accepted.insert(rewrite.clone(), seq);
                }
            } else {
                self.accepted.insert(op, seq);
            }
        }
        for head in &mut self.history {
            if let [rewrite] = image(head).as_slice()
                && !dropped.contains(head)
            {
                *head = rewrite.clone();
            }
        }
        // Composed on lookup, so that opening, which takes every record again, costs their
        // size rather than its square.
        self.superseded.extend(images);
        self.named.extend(dropped.iter().cloned());
        let record = Record::new(dropped.into_iter().map(hub_op));
        let digest = self.digests.last().expect("the root digest").then(&record);
        self.digests.push(digest);
        self.records.push(record);
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

    /// Replaces the head, taking `contracted`'s record with it, if it drops anything. The
    /// caller has checked that `new` is closed and descends from the current head, once that
    /// is dropped.
    pub fn set_head(
        &mut self,
        seq: u64,
        new: &OperationId,
        contracted: Option<Contracted>,
    ) -> Result<(), StoreError> {
        assert_eq!(
            seq,
            self.history.len() as u64,
            "heads are accepted in sequence"
        );
        let record = contracted
            .as_ref()
            .map(|contracted| contracted.dropped.clone())
            .unwrap_or_default();
        append_head(&self.dir, seq, new, &record)?;
        if let Some(contracted) = contracted {
            self.take(contracted);
        }
        let accepted = self.unaccepted_ancestors(new)?;
        for id in accepted {
            self.accepted_origins.insert(
                self.canonical.original_id(&CanonicalOp(id.clone()))?,
                id.clone(),
            );
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
        let view = self
            .canonical
            .read_operation_view(&CanonicalOp(head.clone()))?;
        let heads: Vec<CommitId> = view.head_ids.into_iter().collect();
        Ok(self.object_store().mark_head(&heads)?)
    }

    /// Accepts `head` as the next head, as read back from the log.
    fn accept(&mut self, head: OperationId) -> Result<(), StoreError> {
        let seq = self.history.len() as u64;
        for id in self.unaccepted_ancestors(&head)? {
            self.accepted_origins.insert(
                self.canonical.original_id(&CanonicalOp(id.clone()))?,
                id.clone(),
            );
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
            if id != self.canonical.root_operation_id().0 {
                stack.extend(self.parents(&id)?);
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
            // A base the records superseded, from a node behind them, stands for what it is
            // now: everything below it that is left.
            let bases = self.current(base);
            let excluded: HashSet<OperationId> = self
                .ancestors_until(&bases, |_| false)?
                .into_iter()
                .collect();
            return self.ancestors_until(std::slice::from_ref(head), |id| excluded.contains(id));
        };
        let in_range = |id: &OperationId| {
            self.accepted
                .get(id)
                .is_some_and(|&seq| base_seq < seq && seq <= head_seq)
        };
        // Order ancestors first by walking from `head` through the range.
        self.ancestors_until(std::slice::from_ref(head), |id| !in_range(id))
    }

    /// [`CanonicalStore::ancestors_until`], as the hub names operations.
    fn ancestors_until(
        &self,
        heads: &[OperationId],
        stop: impl Fn(&OperationId) -> bool,
    ) -> Result<Vec<OperationId>, StoreError> {
        let heads: Vec<CanonicalOp> = heads.iter().cloned().map(CanonicalOp).collect();
        let ops = self.canonical.ancestors_until(&heads, |op| stop(&op.0))?;
        Ok(ops.into_iter().map(|op| op.0).collect())
    }

    /// [`CanonicalStore::parents`], as the hub names operations.
    fn parents(&self, id: &OperationId) -> Result<Vec<OperationId>, StoreError> {
        let parents = self.canonical.parents(&CanonicalOp(id.clone()))?;
        Ok(parents.into_iter().map(|op| op.0).collect())
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
                || !self.canonical.has_operation(&CanonicalOp(id.clone()))
            {
                continue;
            }
            stack.extend(self.parents(&id)?);
        }
        Ok(false)
    }

    /// The commits the stored operations `ops` require, excluding the root commit.
    pub fn required_commits(&self, ops: &[OperationId]) -> Result<BTreeSet<CommitId>, StoreError> {
        let ops: Vec<CanonicalOp> = ops.iter().cloned().map(CanonicalOp).collect();
        Ok(self.canonical.required_commits(&ops)?)
    }

    /// Whether `closure(op)` is stored: every operation in `anc*(op)`, its view, and every
    /// object its view requires. Returns the missing pieces' descriptions if not.
    ///
    /// Accepted operations are closed (HubClosed), so the check covers only what is new:
    /// the walk stops at accepted operations, and so does the walk over objects, at the
    /// commits of those it reached and of the head.
    pub fn missing_closure(&self, op: &OperationId) -> Result<Vec<String>, StoreError> {
        self.missing_closure_with(op, None)
    }

    /// [`Self::missing_closure`], once the history drops what `contracted` drops: its rewrites
    /// of accepted operations are closed as those are, with the same views.
    pub fn missing_closure_with(
        &self,
        op: &OperationId,
        contracted: Option<&Contracted>,
    ) -> Result<Vec<String>, StoreError> {
        let rewrites: HashSet<&OperationId> = contracted
            .map(|contracted| {
                contracted
                    .images
                    .iter()
                    .filter(|(old, _)| !contracted.dropped.contains(old))
                    .filter_map(|(_, images)| images.first())
                    .collect()
            })
            .unwrap_or_default();
        let mut missing = vec![];
        let mut reached = vec![];
        let mut boundary = BTreeSet::from([self.head().1.clone()]);
        let mut origins = HashMap::new();
        let mut seen = HashSet::new();
        let mut stack = vec![op.clone()];
        while let Some(id) = stack.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            if self.is_superseded(&id) || contracted.is_some_and(|c| c.dropped.contains(&id)) {
                missing.push(format!("operation {} was abandoned", id.hex()));
                continue;
            }
            if self.accepted.contains_key(&id) || rewrites.contains(&id) {
                boundary.insert(id);
                continue;
            }
            let canonical = CanonicalOp(id.clone());
            if !self.canonical.has_operation(&canonical) {
                missing.push(format!("operation {}", id.hex()));
                continue;
            }
            let (operation, origin) = self.canonical.read_operation_and_original(&canonical)?;
            let dropped_here = contracted.is_some_and(|c| c.dropped_origins.contains(&origin));
            let accepted_id = self.accepted_origins.get(&origin).map(|old| {
                contracted
                    .and_then(|c| c.images.get(old))
                    .and_then(|images| images.first())
                    .unwrap_or(old)
            });
            if self.named_origins.contains(&origin)
                || dropped_here
                || accepted_id.is_some_and(|other| *other != id)
                || origins
                    .insert(origin, id.clone())
                    .is_some_and(|other| other != id)
            {
                missing.push(format!(
                    "operation {} repeats an original identity",
                    id.hex()
                ));
                continue;
            }
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

/// `op`, a canonical operation the hub names, as the protocol names it.
fn hub_op(op: OperationId) -> HubOp {
    HubOp(CanonicalOp(op))
}

/// A head as the log has it, with the record it was accepted with, if any.
type LoggedHead = (OperationId, Vec<OperationId>);

/// How many records the hub pruned, and their digest, as the log has them.
type LoggedPruned = Option<(usize, RecordDigest)>;

/// The first line of a log of a hub that pruned its records.
const PRUNED_PREFIX: &str = "pruned ";

/// Reads the log of accepted heads. A line torn by a power cut makes it corrupt: the hive
/// is made again rather than recovered (see "Replacing the hub" in docs/internals/design.md).
fn read_heads(dir: &Path) -> Result<(LoggedPruned, Vec<LoggedHead>), StoreError> {
    let path = dir.join("heads");
    let bytes = fs::read(&path).map_err(io_err(&path))?;
    let Ok(text) = String::from_utf8(bytes) else {
        return Err(StoreError::CorruptHead(path));
    };
    let mut heads = vec![];
    let mut lines = text.split_terminator('\n').peekable();
    let mut pruned = None;
    if let Some(line) = lines.next_if(|line| line.starts_with(PRUNED_PREFIX)) {
        let mut words = line[PRUNED_PREFIX.len()..].split(' ');
        let count = words.next().and_then(|count| count.parse::<usize>().ok());
        let digest = words
            .next()
            .filter(|hex| hex.len() == RecordDigest::root().bytes().len() * 2)
            .and_then(jj_lib::hex_util::decode_hex);
        match (count, digest, words.next()) {
            (Some(count), Some(digest), None) => {
                pruned = Some((count, RecordDigest::from_bytes(&digest)));
            }
            _ => return Err(StoreError::CorruptHead(path)),
        }
    }
    for line in lines {
        // Whole ids only: a line torn and another appended after it can read as a short one.
        let id = |hex: &str| OperationId::try_from_hex(hex).filter(|id| id.as_bytes().len() == 64);
        let mut words = line.split(' ');
        let seq = words.next().and_then(|seq| seq.parse::<usize>().ok());
        let head = words.next().and_then(id);
        let record: Option<Vec<OperationId>> = words.map(id).collect();
        match (seq, head, record) {
            (Some(seq), Some(head), Some(record)) if seq == heads.len() => {
                heads.push((head, record));
            }
            _ => return Err(StoreError::CorruptHead(path)),
        }
    }
    if heads.is_empty() || !text.ends_with('\n') {
        return Err(StoreError::CorruptHead(path));
    }
    Ok((pruned, heads))
}

/// Writes the log of accepted heads again, whole: `pruned`, how many records the hub pruned
/// and their digest, then each head, with no record.
fn write_heads(
    dir: &Path,
    (count, digest): (usize, &RecordDigest),
    heads: &[OperationId],
) -> Result<(), StoreError> {
    let mut text = format!(
        "{PRUNED_PREFIX}{count} {}\n",
        jj_lib::hex_util::encode_hex(digest.bytes())
    );
    for (seq, head) in heads.iter().enumerate() {
        writeln!(text, "{seq} {}", head.hex()).expect("writing to a String");
    }
    let path = dir.join("heads");
    musubi_jj::files::replace(&path, text.as_bytes()).map_err(io_err(&path))
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

fn append_head(
    dir: &Path,
    seq: u64,
    head: &OperationId,
    record: &[OperationId],
) -> Result<(), StoreError> {
    let path = dir.join("heads");
    let mut file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .map_err(io_err(&path))?;
    let mut line = format!("{seq} {}", head.hex());
    for op in record {
        line.push(' ');
        line.push_str(&op.hex());
    }
    line.push('\n');
    // In one write, not writeln!'s four, so that a process killed partway seldom tears it.
    file.write_all(line.as_bytes()).map_err(io_err(&path))
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use hegel::TestCase;
    use hegel::generators as gs;

    use super::*;

    /// A log written again, pruned, reads back as written, its count and digest first; with
    /// its first line torn, it is corrupt.
    #[test]
    fn a_pruned_log_reads_back() {
        let dir = tempfile::tempdir().unwrap();
        let heads: Vec<OperationId> = (0..3).map(|i| OperationId::new(vec![i; 64])).collect();
        let digest = RecordDigest::root().then(&Record::new([hub_op(heads[1].clone())]));
        write_heads(dir.path(), (1, &digest), &heads).unwrap();
        let (pruned, read) = read_heads(dir.path()).unwrap();
        assert_eq!(pruned, Some((1, digest)));
        let read: Vec<OperationId> = read.into_iter().map(|(head, _)| head).collect();
        assert_eq!(read, heads);
        let path = dir.path().join("heads");
        let text = fs::read_to_string(&path).unwrap();
        let first = text.find('\n').unwrap();
        fs::write(&path, format!("{}{}", &text[..first - 1], &text[first..])).unwrap();
        assert!(matches!(
            read_heads(dir.path()),
            Err(StoreError::CorruptHead(_))
        ));
    }

    /// A log cut where a line ends, keeping one, reads as the heads before the cut; cut
    /// anywhere else, or to nothing, it is corrupt.
    #[hegel::test(test_cases = 200)]
    fn a_cut_log_reads_only_where_a_line_ends(tc: TestCase) {
        let dir = tempfile::tempdir().unwrap();
        let count = tc.draw(gs::integers::<u8>().min_value(1).max_value(12));
        let heads: Vec<OperationId> = (0..count).map(|i| OperationId::new(vec![i; 64])).collect();
        // Sometimes the log of a hub that pruned its records, which starts with their count
        // and digest: a cut that keeps only that line keeps no head.
        let pruned = tc
            .draw(gs::booleans())
            .then(|| (3, RecordDigest::root().then(&Record::new([]))));
        let mut text = String::new();
        if let Some((count, digest)) = &pruned {
            writeln!(
                text,
                "{PRUNED_PREFIX}{count} {}",
                jj_lib::hex_util::encode_hex(digest.bytes())
            )
            .unwrap();
        }
        let mut ends = vec![text.len()];
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
                let (read_pruned, read) = read_heads(dir.path()).unwrap();
                assert_eq!(read_pruned, pruned);
                let read: Vec<OperationId> = read.into_iter().map(|(head, _)| head).collect();
                assert_eq!(read, heads[..lines]);
            }
            _ => assert!(matches!(
                read_heads(dir.path()),
                Err(StoreError::CorruptHead(_))
            )),
        }
    }
}
