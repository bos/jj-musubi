//! The core's `LocalRepo` over a jj repository.

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::SystemTime;

use anyhow::Context as _;
use anyhow::bail;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_core::message::OpEntry;
use musubi_core::message::RecordState;
use musubi_core::message::Records;
use musubi_core::message::Request;
use musubi_core::node::LocalRepo;
use musubi_core::node::NodeCore;
use musubi_jj::node::NodeError;
use musubi_jj::node::NodeOp;
use musubi_jj::node::NodeRepo;
use musubi_jj::node::REALIZE_AT_ONCE;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::records::HubOp;
use musubi_jj::records::Record;
use musubi_jj::records::RecordDigest;
use musubi_jj::records::RecordPrefix;

use crate::Attachment;
use crate::OpId;
use crate::open_bundle_dir;
use crate::temp_bundle;

/// Up to how much later than its `musubi.forget-after` a daemon forgets an unused copy, a
/// different time on each machine (`NodeRepo::expire_idle`): one machine's forget reaches
/// the others, which then have nothing to forget, before their own time comes.
const EXPIRY_STAGGER: std::time::Duration = std::time::Duration::from_secs(300);

/// Where a node takes the time from: the system's clock, but for tests, whose clock agrees
/// with the times they give the operations they write.
pub trait Clock: Send {
    /// The time now, by which copies go unused.
    fn now(&self) -> SystemTime;

    /// Moves `repo`'s time for the commits and operations it writes on to now, if this clock
    /// gives it one: jj-lib takes it from the settings a repository was opened with, unless
    /// they leave it to the system's clock.
    fn tick(&self, repo: &mut NodeRepo);
}

/// The system's clock, which a repository's settings leave jj-lib to read itself.
pub struct SystemClock;

impl Clock for SystemClock {
    fn now(&self) -> SystemTime {
        SystemTime::now()
    }

    fn tick(&self, _: &mut NodeRepo) {}
}

pub struct NodeAdapter {
    repo: NodeRepo,
    clock: Box<dyn Clock>,
    tmp: PathBuf,
    base_path: PathBuf,
    /// Whether the saved raw base's objects are still here, checked once per round and
    /// base. `jj util gc` may remove them after an operation restore and abandonment.
    checked_base: RefCell<Option<(OpId, bool)>>,
    /// The head this node pushed last, and that head once it learns that the hub took it,
    /// which `NodeRepo::check_abandon` watches as it watches the base.
    pushed_path: PathBuf,
    accepted_push_path: PathBuf,
    /// `anc*(base)` for the most recent `base` asked about.
    base_ancestry: RefCell<Option<(OpId, HashSet<OpId>)>>,
    /// The parents of operations a fetch staged that were not local, until they are
    /// realized, so that planning their realization needn't read each one again. A
    /// canonical operation never changes, so neither does an entry.
    staged: HashMap<OpId, Vec<OpId>>,
    /// The staged operations by parent, to find which are likely realized after one.
    staged_children: HashMap<OpId, Vec<OpId>>,
    /// The operations whose objects were staged last, with every commit they require:
    /// what checking that those objects are all here asks about next.
    staged_commits: Option<(HashSet<OpId>, Vec<CommitId>)>,
    /// A complete immutable known-head closure already used to name these pending drops.
    /// Repeating a realization step needs no second walk of that same history.
    pending_named: Option<(OpId, Record)>,
}

impl NodeAdapter {
    pub fn new(repo: NodeRepo) -> anyhow::Result<Self> {
        let musubi_dir = repo.repo_path().join("musubi");
        let tmp = musubi_dir.join("tmp");
        open_bundle_dir(&tmp)?;
        Ok(Self {
            base_path: musubi_dir.join("accepted_base"),
            checked_base: RefCell::new(None),
            pushed_path: musubi_dir.join("pushed"),
            accepted_push_path: musubi_dir.join(musubi_jj::node::ACCEPTED_PUSH),
            repo,
            clock: Box::new(SystemClock),
            tmp,
            base_ancestry: RefCell::new(None),
            staged: HashMap::new(),
            staged_children: HashMap::new(),
            staged_commits: None,
            pending_named: None,
        })
    }

    /// Takes the time from `clock`, for tests.
    pub fn set_clock(&mut self, clock: Box<dyn Clock>) {
        self.clock = clock;
    }

    /// The repository, for tests that look into it.
    pub fn repo(&self) -> &NodeRepo {
        &self.repo
    }

    /// Shows other machines' workspaces again where this machine's view lost them
    /// (`NodeRepo::show_other_workspaces`). Returns whether it wrote an operation.
    pub fn show_other_workspaces(&mut self) -> anyhow::Result<bool> {
        self.repo.settle()?;
        Ok(self.repo.show_other_workspaces()?)
    }

    /// Gets ready to sync. A repository made shallow or partial since it joined can't send
    /// what its new work requires, and the hub would refuse it.
    /// Other machines' workspaces that this machine forgot show again before anything
    /// arrives to merge with: `jj workspace forget` abandoned an empty working-copy commit
    /// here, which the hive keeps, and a merge with the abandon would rebase off it what its
    /// machine built on it meanwhile. Op heads may have changed since the last step: a
    /// fetch's haves should say so.
    pub fn before_sync(&mut self) -> anyhow::Result<()> {
        self.clock.tick(&mut self.repo);
        self.repo.check_complete()?;
        self.show_other_workspaces()?;
        self.heads()?;
        Ok(())
    }

    /// Builds the round's first Fetch, rechecking the saved base before anything can be
    /// omitted. Head discovery still waits for its reply, which may acknowledge a push.
    pub fn poll(&self, core: &NodeCore<OpId>) -> anyhow::Result<Request<OpId, Attachment>> {
        self.checked_base.borrow_mut().take();
        core.poll(self)
    }

    fn read_base(&self) -> anyhow::Result<OpId> {
        match fs::read_to_string(&self.base_path) {
            Ok(hex) => OpId::try_from_hex(hex.trim()).context("corrupt accepted_base"),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(self.root().clone()),
            Err(err) => Err(err.into()),
        }
    }

    /// What a node does once its policy has nothing left to do, having just fetched the
    /// hive's head: show other machines' workspaces again, give its
    /// own workspaces new commits where theirs were abandoned elsewhere, record this copy's
    /// `musubi.forget-after` if it changed, and forget the copies that have gone unused for
    /// longer than theirs. Each runs; any may write an operation to upload, and then it
    /// returns true, since the policy has more to do.
    ///
    /// Realizing another machine's operation replaces abandoned working copies too, but
    /// while the hive has forgotten this machine it leaves them hidden, rebasing them only
    /// where their parents went (`NodeRepo::replace_abandoned_working_copies`), and the work
    /// that shows it again, such as creating a bookmark, needn't touch them: then nothing
    /// would arrive to realize.
    pub fn when_idle(&mut self) -> anyhow::Result<bool> {
        self.clock.tick(&mut self.repo);
        let workspaces = self.show_other_workspaces()?;
        let replaced = !self.repo.replace_abandoned_working_copies()?.is_empty();
        let recorded = self.repo.record_forget_after()?;
        let forgotten = self.repo.expire_idle(self.clock.now(), EXPIRY_STAGGER)?;
        Ok(workspaces || replaced || recorded || !forgotten.is_empty())
    }

    /// The repository, for tests that act on it, as by crashing it, with its time moved on
    /// to now (`Clock::tick`).
    pub fn repo_mut(&mut self) -> &mut NodeRepo {
        self.clock.tick(&mut self.repo);
        &mut self.repo
    }

    pub fn root(&self) -> &OpId {
        &self.repo.canonical_store().root_operation_id().0
    }

    /// `ancestor ∈ anc*(op)` over the canonical graph.
    fn canonical_is_ancestor(&self, ancestor: &OpId, op: &OpId) -> anyhow::Result<bool> {
        Ok(self
            .repo
            .canonical_store()
            .is_ancestor_of(&canonical(ancestor), &canonical(op))?)
    }

    /// Notes that the hub took the head this node pushed last, if it is one of `accepted`, so
    /// that `NodeRepo::check_abandon` watches it as it watches the base.
    fn note_accepted(&mut self, accepted: &[OpId]) -> anyhow::Result<()> {
        let pushed = match fs::read_to_string(&self.pushed_path) {
            Ok(hex) => OpId::try_from_hex(hex.trim()),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => None,
            Err(err) => return Err(err.into()),
        };
        if let Some(pushed) = pushed
            && accepted.contains(&pushed)
        {
            write_op(&self.accepted_push_path, &pushed)?;
        }
        Ok(())
    }

    fn read_heads(&mut self, known: Option<&OpId>) -> anyhow::Result<Vec<OpId>> {
        let base = self.accepted_base()?;
        self.repo.settle()?;
        // This discovers local abandons before pending names are reconciled.
        let heads = op_ids(self.repo.canonical_heads()?);
        if self.repo.take_abandon_noticed() {
            self.forget_staged();
        }
        if let Some(known) = known {
            self.reconcile_pending(known)?;
        }
        // Every image of the base must be below a head. Dropping the base can leave it
        // several. `formal/Musubi/BaseImages.lean` shows that the steps which change the base,
        // the drops or the heads keep every image below a head, so this fails for lost
        // history, including history that lost only some of the images.
        let images = self.repo.to_node(&hub(&base))?;
        let mut reachable = !images.is_empty();
        for NodeOp(image) in &images {
            let mut below = false;
            for head in &heads {
                below = below || self.canonical_is_ancestor(&image.0, head)?;
            }
            reachable &= below;
        }
        if !reachable {
            return Err(NodeError::UnreachableHistory.into());
        }
        Ok(heads)
    }

    fn reconcile_pending(&mut self, known: &OpId) -> anyhow::Result<()> {
        if self.repo.pending_drops().is_empty()
            || self.pending_named.as_ref().is_some_and(|(head, pending)| {
                head == known && pending == self.repo.pending_drops()
            })
        {
            return Ok(());
        }
        let store = self.repo.canonical_store();
        let canonical = canonical(known);
        if !store.has_operation(&canonical) {
            return Ok(());
        }
        let ops = store.ancestors_until(&[canonical], |_| false)?;
        let mut complete = self
            .repo
            .pending_drops()
            .ops()
            .iter()
            .all(|op| store.has_operation(&op.0));
        for op in &ops {
            complete &= store.parents(op)?.iter().all(|p| store.has_operation(p));
        }
        if self.repo.name_pending_as(&ops)? {
            self.forget_staged();
        }
        // Missing bodies may arrive at the next fetch. Cache only a complete immutable
        // closure, whose original identities cannot change when more metadata arrives.
        self.pending_named = complete.then(|| (known.clone(), self.repo.pending_drops().clone()));
        Ok(())
    }

    /// Forgets what was staged, and the ancestry of the base, as the hub named them before
    /// this node took its records or noticed an abandon.
    fn forget_staged(&mut self) {
        self.staged.clear();
        self.staged_children.clear();
        *self.base_ancestry.borrow_mut() = None;
    }

    /// Makes `base_ancestry` hold `anc*(base)`, `base` a hub name, as this node names the
    /// history, extending what it held where `base` descends from that.
    fn cache_ancestry(&self, base: &OpId) -> anyhow::Result<()> {
        let store = self.repo.canonical_store();
        let bases: Vec<CanonicalOp> = self
            .repo
            .to_node(&hub(base))?
            .into_iter()
            .map(|NodeOp(op)| op)
            .collect();
        let mut cache = self.base_ancestry.borrow_mut();
        let set = match cache.take() {
            Some((cached, set)) if cached == *base => set,
            Some((cached, mut set))
                if bases.len() == 1 && self.canonical_is_ancestor(&cached, &bases[0].0)? =>
            {
                set.extend(op_ids(
                    store.ancestors_until(&bases, |id| set.contains(&id.0))?,
                ));
                set
            }
            _ => {
                let mut set: HashSet<OpId> = op_ids(store.ancestors_until(&bases, |_| false)?)
                    .into_iter()
                    .collect();
                set.insert(self.root().clone());
                set
            }
        };
        *cache = Some((base.clone(), set));
        Ok(())
    }

    /// The one node name of `op`, a hub name for an operation this node doesn't drop.
    fn node_name(&self, op: &OpId) -> anyhow::Result<CanonicalOp> {
        match self.repo.to_node(&hub(op))?.as_slice() {
            [NodeOp(node)] => Ok(node.clone()),
            _ => anyhow::bail!("operation {} is one this machine dropped", op.hex()),
        }
    }

    fn required_commits(&self, ops: &[OpId]) -> anyhow::Result<Vec<CommitId>> {
        Ok(self
            .repo
            .required_commits(&canonicals(ops))?
            .into_iter()
            .collect())
    }

    /// The local operations nearest to `ops` among their ancestors: where a walk up from
    /// `ops` through operations that are not local stops.
    fn local_frontier(&self, ops: &[OpId]) -> anyhow::Result<Vec<OpId>> {
        let store = self.repo.canonical_store();
        let mut frontier = vec![];
        let mut seen = HashSet::new();
        let mut stack = ops.to_vec();
        while let Some(op) = stack.pop() {
            if !seen.insert(op.clone()) {
                continue;
            }
            let id = canonical(&op);
            if self.repo.local_of(&id).is_some() {
                frontier.push(op);
            } else if store.has_operation(&id) {
                stack.extend(op_ids(store.parents(&id)?));
            }
        }
        Ok(frontier)
    }

    /// Commits this node has, with everything they reach, that the objects of `ops` are
    /// likely to share: those of the local operations `ops` descend from, of the op heads,
    /// and of the accepted base. The hub leaves out of a transfer everything they reach
    /// (docs/internals/design.md, "Joining"). Only commits present here count: jj may have
    /// collected an old operation's.
    fn haves(&self, ops: &[OpId]) -> anyhow::Result<Vec<CommitId>> {
        let mut have_ops = self.local_frontier(ops)?;
        have_ops.extend(self.canonical_heads()?);
        have_ops.push(self.accepted_base()?);
        self.present(self.required_commits(&have_ops)?)
    }

    /// The canonical forms of the op heads that are canonicalized already.
    fn canonical_heads(&self) -> anyhow::Result<Vec<OpId>> {
        Ok(self
            .repo
            .local_heads()?
            .iter()
            .filter_map(|head| Some(self.repo.canonical_of(head)?.0))
            .collect())
    }

    /// Haves for the hub, which adds `closure(accepted base)` on its own: those of `ops`'
    /// commits that are present and that the base's do not include.
    fn haves_beyond_base(&self, ops: &[OpId]) -> anyhow::Result<Attachment> {
        let base = self.accepted_base()?;
        let ops: Vec<OpId> = ops.iter().filter(|op| **op != base).cloned().collect();
        if ops.is_empty() {
            return Ok(Attachment::Haves(vec![]));
        }
        let base_commits: HashSet<CommitId> = self
            .required_commits(std::slice::from_ref(&base))?
            .into_iter()
            .collect();
        let commits = self
            .required_commits(&ops)?
            .into_iter()
            .filter(|commit| !base_commits.contains(commit))
            .collect();
        Ok(Attachment::Haves(self.present(commits)?))
    }

    /// Those of `commits` present here.
    fn present(&self, commits: Vec<CommitId>) -> anyhow::Result<Vec<CommitId>> {
        if commits.is_empty() {
            return Ok(commits);
        }
        let absent: HashSet<CommitId> = self
            .repo
            .object_store()?
            .missing(&commits)?
            .into_iter()
            .collect();
        Ok(commits
            .into_iter()
            .filter(|c| !absent.contains(c))
            .collect())
    }
}

/// The hub's name for `op`. The core speaks of the hub's history in hub names (`known`, staged
/// operations, the base, records) and of this machine's op heads, and what it pushes, in node
/// names (`musubi_jj::node::NodeOp`), which differ only while this machine has drops to
/// publish: each method below says which it takes.
fn hub(op: &OpId) -> HubOp {
    HubOp(canonical(op))
}

/// `op`, which the core names as the protocol does, as a canonical operation.
fn canonical(op: &OpId) -> CanonicalOp {
    CanonicalOp(op.clone())
}

fn canonicals(ops: &[OpId]) -> Vec<CanonicalOp> {
    ops.iter().map(canonical).collect()
}

/// Canonical operations as the core names them.
fn op_ids(ops: Vec<CanonicalOp>) -> Vec<OpId> {
    ops.into_iter().map(|op| op.0).collect()
}

/// Records from the core, in hub names.
fn records_of(records: &[Vec<OpId>]) -> Vec<Record> {
    records
        .iter()
        .map(|record| Record::new(record.iter().map(hub)))
        .collect()
}

/// `records`, as the core has them.
fn ops_of(records: &[Record]) -> Vec<Vec<OpId>> {
    records
        .iter()
        .map(|record| record.ops().iter().map(|op| op.0.0.clone()).collect())
        .collect()
}

/// The records the core's `base` stands for.
fn prefix_of(base: &RecordState) -> RecordPrefix {
    RecordPrefix {
        count: base.count,
        digest: RecordDigest::from_bytes(&base.digest),
    }
}

/// The state of records whose digest is `digest`, as the protocol carries it.
fn state_of(count: u64, digest: &RecordDigest) -> RecordState {
    RecordState {
        count,
        digest: digest.bytes().to_vec(),
    }
}

/// Whether `err` is that this repository lost history the hive has, which no `jj op abandon`
/// explains and no retry gets past.
pub fn history_lost(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| {
        matches!(
            cause.downcast_ref::<NodeError>(),
            Some(
                NodeError::UnreachableHistory
                    | NodeError::RewrittenRealization
                    | NodeError::DamagedLog
                    | NodeError::PrunedRecords
            )
        )
    })
}

impl LocalRepo for NodeAdapter {
    type Op = OpId;
    type Attachment = Attachment;
    type Error = anyhow::Error;

    fn machine(&self) -> String {
        self.repo.machine().key().to_owned()
    }

    fn heads(&mut self) -> anyhow::Result<Vec<OpId>> {
        // jj never makes an operation the hub accepted unreachable from the op heads except
        // through `jj op abandon`, which this node then publishes (docs/internals/design.md,
        // "Abandoning operations").
        self.read_heads(None)
    }

    fn heads_for(&mut self, known: &OpId) -> anyhow::Result<Vec<OpId>> {
        self.read_heads(Some(known))
    }

    fn is_local(&self, op: &OpId) -> anyhow::Result<bool> {
        let nodes = self.repo.to_node(&hub(op))?;
        Ok(!nodes.is_empty()
            && nodes
                .iter()
                .all(|node| self.repo.local_of(&node.0).is_some()))
    }

    fn is_ancestor(&self, ancestor: &OpId, op: &OpId) -> anyhow::Result<bool> {
        let ancestors = self.repo.to_node(&hub(ancestor))?;
        for NodeOp(ancestor) in &ancestors {
            if !self.canonical_is_ancestor(&ancestor.0, op)? {
                return Ok(false);
            }
        }
        Ok(!ancestors.is_empty())
    }

    fn merge_heads(&mut self) -> anyhow::Result<()> {
        self.repo.settle()?;
        self.repo.merge_heads()?;
        Ok(())
    }

    fn ops_between(&self, head: &OpId, base: &OpId) -> anyhow::Result<Vec<OpId>> {
        // Borrowed, not copied: it is the whole accepted history.
        self.cache_ancestry(base)?;
        let cache = self.base_ancestry.borrow();
        let (_, excluded) = cache.as_ref().expect("cached above");
        let store = self.repo.canonical_store();
        Ok(op_ids(store.ancestors_until(&[canonical(head)], |id| {
            excluded.contains(&id.0)
        })?))
    }

    fn ops_attachment(&self, ops: &[OpId]) -> anyhow::Result<Attachment> {
        let bundle = temp_bundle(&self.tmp)?;
        let record_ops: Vec<CanonicalOp> = self
            .repo
            .pending_drops()
            .ops()
            .iter()
            .map(|op| op.0.clone())
            .collect();
        self.repo.canonical_store().export_operations_with_records(
            &canonicals(ops),
            &record_ops,
            &bundle,
        )?;
        Ok(Attachment::bundle(bundle))
    }

    fn objects_attachment(&self, ops: &[OpId], base: &OpId) -> anyhow::Result<Attachment> {
        let wants = self.required_commits(ops)?;
        let haves = self.required_commits(std::slice::from_ref(base))?;
        let bundle = temp_bundle(&self.tmp)?;
        self.repo.object_store()?.export(&wants, &haves, &bundle)?;
        Ok(Attachment::bundle(bundle))
    }

    fn fetch_haves(&self) -> anyhow::Result<Attachment> {
        self.haves_beyond_base(&self.canonical_heads()?)
    }

    fn objects_request(&self, ops: &[OpId]) -> anyhow::Result<Attachment> {
        let mut have_ops = self.local_frontier(ops)?;
        have_ops.extend(self.canonical_heads()?);
        self.haves_beyond_base(&have_ops)
    }

    fn store_record_ops(
        &mut self,
        records: &[Vec<OpId>],
        attachment: &Attachment,
    ) -> anyhow::Result<()> {
        let store = self.repo.canonical_store();
        store.import_operations(attachment.bundle_path()?)?;
        // A lost record can become pending after rollback. Renaming that name requires its
        // body and ancestors even when none is in the current accepted history.
        let names: Vec<CanonicalOp> = records.iter().flatten().cloned().map(CanonicalOp).collect();
        store.record_operations(&names)?;
        Ok(())
    }

    fn stage_ops(&mut self, ops: &[OpEntry<OpId>], attachment: &Attachment) -> anyhow::Result<()> {
        // What the hub sends, it accepted: this node's own push among them too.
        let ids: Vec<OpId> = ops.iter().map(|entry| entry.id.clone()).collect();
        self.note_accepted(&ids)?;
        let store = self.repo.canonical_store();
        let imported: HashMap<OpId, Vec<OpId>> = store
            .import_operations(attachment.bundle_path()?)?
            .into_iter()
            .filter_map(|(id, parents)| Some((id.0, op_ids(parents?))))
            .collect();
        for entry in ops {
            let parents = match imported.get(&entry.id) {
                Some(parents) => parents.clone(),
                // Stored before, or not at all.
                None => {
                    store
                        .read_operation(&canonical(&entry.id))
                        .with_context(|| {
                            format!("operation {} missing from bundle", entry.id.hex())
                        })?
                        .parents
                }
            };
            if parents != entry.parents {
                bail!(
                    "operation {} has different parents than announced",
                    entry.id.hex()
                );
            }
            if self.repo.local_of(&canonical(&entry.id)).is_none()
                && !self.staged.contains_key(&entry.id)
            {
                for parent in parents
                    .iter()
                    .filter(|p| self.repo.local_of(&canonical(p)).is_none())
                {
                    self.staged_children
                        .entry(parent.clone())
                        .or_default()
                        .push(entry.id.clone());
                }
                self.staged.insert(entry.id.clone(), parents);
            }
        }
        Ok(())
    }

    fn stage_objects(&mut self, for_ops: &[OpId], attachment: &Attachment) -> anyhow::Result<()> {
        if matches!(attachment, Attachment::None) {
            // A remade hub may no longer know the requested old operations. Treating its
            // empty reply as progress would repeat GetObjects without learning its new head.
            anyhow::ensure!(
                self.objects_missing(for_ops)?.is_empty(),
                "the hub did not supply the objects this machine needs"
            );
            return Ok(());
        }
        let wants = self.required_commits(for_ops)?;
        self.staged_commits = Some((for_ops.iter().cloned().collect(), wants.clone()));
        let haves = self.haves(for_ops)?;
        // The import may add a pack, which jj-lib must be able to read.
        self.repo.reload()?;
        self.repo
            .object_store()?
            .import(attachment.bundle_path()?, &wants, &haves)?;
        Ok(())
    }

    fn staged_parents(&self, op: &OpId) -> anyhow::Result<Option<Vec<OpId>>> {
        if self.is_local(op)? {
            return Ok(None);
        }
        if let Some(parents) = self.staged.get(op) {
            return Ok(Some(parents.clone()));
        }
        let store = self.repo.canonical_store();
        let op = canonical(op);
        if !store.has_operation(&op) {
            return Ok(None);
        }
        Ok(Some(op_ids(store.parents(&op)?)))
    }

    fn objects_missing(&self, ops: &[OpId]) -> anyhow::Result<Vec<OpId>> {
        // One question to git for all of them. Usually nothing is missing, and then each
        // view is read only once, or not at all if these are among the operations whose
        // objects were just staged: the commits all of those require will do, since only an
        // absent commit leads to asking about each operation.
        let staged = self
            .staged_commits
            .as_ref()
            .filter(|(staged, _)| ops.iter().all(|op| staged.contains(op)))
            .map(|(_, commits)| commits.clone());
        let wanted = match staged {
            Some(commits) => commits,
            None => self.required_commits(ops)?,
        };
        let absent: HashSet<CommitId> = self
            .repo
            .object_store()?
            .missing(&wanted)?
            .into_iter()
            .collect();
        if absent.is_empty() {
            return Ok(vec![]);
        }
        let mut missing = vec![];
        for op in ops {
            if self
                .repo
                .required_commits(&[canonical(op)])?
                .iter()
                .any(|commit| absent.contains(commit))
            {
                missing.push(op.clone());
            }
        }
        Ok(missing)
    }

    fn realize(&mut self, op: &OpId) -> anyhow::Result<()> {
        // What this node has in place of an operation it dropped is what survives below it,
        // local once its parents are, as they are by now: there is nothing to write. The core
        // plans such an operation where the hub went back to one this node dropped, before its
        // parents were here.
        if self.repo.is_dropped(&hub(op)) {
            anyhow::ensure!(
                self.is_local(op)?,
                "operation {} is one this machine dropped, and what it has in its place isn't here",
                op.hex()
            );
            self.staged.remove(op);
            self.staged_children.remove(op);
            return Ok(());
        }
        // The operations likely realized after it, whose views can be made local with its:
        // each the only staged child of the one before, up to one this node dropped.
        let mut next = vec![];
        let mut last = op;
        while next.len() < REALIZE_AT_ONCE - 1 {
            let Some([child]) = self.staged_children.get(last).map(Vec::as_slice) else {
                break;
            };
            if self.staged.get(child).map(Vec::as_slice) != Some(std::slice::from_ref(last))
                || self.repo.is_dropped(&hub(child))
            {
                break;
            }
            next.push(child.clone());
            last = child;
        }
        // Written meanwhile: `advance` waits for them, and so does anything else here that
        // reads local operations.
        let node = self.node_name(op)?;
        let next = next
            .iter()
            .map(|op| self.node_name(op))
            .collect::<anyhow::Result<Vec<_>>>()?;
        self.repo.realize_pending(&node, &next)?;
        self.staged.remove(op);
        self.staged_children.remove(op);
        Ok(())
    }

    fn advance(&mut self, op: &OpId) -> anyhow::Result<()> {
        // What this node's history has in place of `op`: itself, or, where this node dropped
        // it, the maximal operations below it that survive.
        let nodes: Vec<CanonicalOp> = self
            .repo
            .to_node(&hub(op))?
            .into_iter()
            .map(|NodeOp(op)| op)
            .collect();
        anyhow::ensure!(
            !nodes.is_empty(),
            "nothing stands for operation {}",
            op.hex()
        );
        let records = self.repo.record_state();
        let advanced = self.repo.advance_to(&nodes);
        // Advancing while taking the hub's records takes them, as `adopt` does, even where it
        // fails after.
        if self.repo.record_state() != records {
            self.forget_staged();
        }
        advanced?;
        Ok(())
    }

    fn accepted_base(&self) -> anyhow::Result<OpId> {
        let base = self.read_base()?;
        if base == *self.root() {
            return Ok(base);
        }
        let cached = self
            .checked_base
            .borrow()
            .as_ref()
            .filter(|(op, _)| *op == base)
            .map(|(_, complete)| *complete);
        let complete = match cached {
            Some(complete) => complete,
            None => {
                let required = self.required_commits(std::slice::from_ref(&base))?;
                let complete = self.repo.object_store()?.missing(&required)?.is_empty();
                *self.checked_base.borrow_mut() = Some((base.clone(), complete));
                complete
            }
        };
        // The hub omits these objects unconditionally. A local image of the base does not
        // establish that its raw view's objects survived an abandon and the user's gc.
        Ok(if complete { base } else { self.root().clone() })
    }

    fn set_accepted_base(&mut self, op: &OpId) -> anyhow::Result<()> {
        if self.read_base()? == *op {
            return Ok(());
        }
        write_op(&self.base_path, op)?;
        self.checked_base.take();
        Ok(())
    }

    fn applied_records(&self) -> anyhow::Result<Records<OpId>> {
        let prefix = self.repo.record_prefix();
        Ok(Records {
            base: state_of(prefix.count, &prefix.digest),
            records: ops_of(self.repo.applied_records()),
        })
    }

    fn has_record_receipts(&self) -> anyhow::Result<bool> {
        Ok(self.repo.has_record_custody())
    }

    fn records(&self) -> anyhow::Result<RecordState> {
        let (count, digest) = self.repo.record_state();
        Ok(state_of(count, &digest))
    }

    fn records_state(&self, records: &Records<OpId>) -> anyhow::Result<RecordState> {
        let digest = records_of(&records.records)
            .iter()
            .fold(prefix_of(&records.base).digest, |digest, record| {
                digest.then(record)
            });
        Ok(state_of(records.count(), &digest))
    }

    fn pending(&self) -> anyhow::Result<Vec<OpId>> {
        Ok(self
            .repo
            .pending_drops()
            .ops()
            .iter()
            .map(|op| op.0.0.clone())
            .collect())
    }

    fn prepare_records(&mut self, records: &Records<OpId>) -> anyhow::Result<bool> {
        self.repo.settle()?;
        Ok(self
            .repo
            .prepare_records(&prefix_of(&records.base), &records_of(&records.records))?)
    }

    fn adopt(&mut self, records: &Records<OpId>) -> anyhow::Result<()> {
        self.repo.settle()?;
        let prefix = prefix_of(&records.base);
        let adopted = self
            .repo
            .adopt_records(&prefix, &records_of(&records.records));
        // Staged operations, as the hub named them before, are stale, even where taking the
        // records fails once this node holds them.
        self.forget_staged();
        // The base, as the hub names it now: what it became, or, if dropped, the first of
        // what was below it, also accepted.
        if let Some(HubOp(base)) = adopted? {
            self.set_accepted_base(&base.0)?;
        }
        Ok(())
    }

    fn fresh(&self) -> anyhow::Result<bool> {
        Ok(self.repo.is_fresh())
    }

    fn share(&mut self) -> anyhow::Result<()> {
        Ok(self.repo.share()?)
    }

    fn held(&self, prefix: &RecordState) -> anyhow::Result<Option<Records<OpId>>> {
        Ok(self
            .repo
            .held_records(&prefix_of(prefix))
            .map(|(base, records)| Records {
                base: state_of(base.count, &base.digest),
                records: ops_of(&records),
            }))
    }

    fn lacks_pruned(&self) -> anyhow::Error {
        NodeError::PrunedRecords.into()
    }

    fn is_dropped(&self, op: &OpId) -> anyhow::Result<bool> {
        Ok(self.repo.is_dropped(&hub(op)))
    }

    fn pushing(&mut self, head: &OpId) -> anyhow::Result<()> {
        write_op(&self.pushed_path, head)
    }

    fn learned(&mut self, head: &OpId) -> anyhow::Result<()> {
        self.note_accepted(std::slice::from_ref(head))
    }

    fn write_fixup(&mut self, publish_from: Option<&OpId>) -> anyhow::Result<Option<OpId>> {
        self.repo.settle()?;
        let fixup = self.repo.write_fixup()?;
        let fixup = match (fixup, publish_from) {
            (None, Some(head)) => self.repo.write_drop_tip(&hub(head))?,
            (fixup, _) => fixup,
        };
        Ok(fixup.map(|NodeOp(op)| op.0))
    }
}

/// Writes `op` to `path`, overwritten in place: it changes at every advance and push, and ext4
/// writes out at once a file renamed over another, or truncated to nothing. Operation ids are
/// all one length, so `set_len` only cuts off what isn't one.
fn write_op(path: &Path, op: &OpId) -> anyhow::Result<()> {
    let hex = op.hex();
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(false)
        .open(path)?;
    file.write_all(hex.as_bytes())?;
    file.set_len(hex.len() as u64)?;
    Ok(())
}

#[cfg(test)]
mod tests;
