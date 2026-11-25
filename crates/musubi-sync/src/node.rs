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
use musubi_core::message::Request;
use musubi_core::node::LocalRepo;
use musubi_core::node::NodeCore;
use musubi_jj::node::NodeError;
use musubi_jj::node::NodeRepo;
use musubi_jj::node::REALIZE_AT_ONCE;
use musubi_jj::op_id::CanonicalOp;

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

/// Asked before this node applies any of the hive's history to its repository: whether it
/// may. See [`crate::driver::NodeDriver::before_applying`].
pub type Gate = std::sync::Arc<dyn Fn() -> anyhow::Result<()> + Send + Sync>;

pub struct NodeAdapter {
    repo: NodeRepo,
    gate: Option<Gate>,
    clock: Box<dyn Clock>,
    tmp: PathBuf,
    base_path: PathBuf,
    /// Whether the saved raw base's objects are still here, checked once per round and
    /// base. `jj util gc` may remove them after an operation restore and abandonment.
    checked_base: RefCell<Option<(OpId, bool)>>,
    /// The head this node pushed last, and that head once it learns that the hub took it,
    /// which `read_heads` requires to stay below the op heads as it does the base.
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
    publication: RefCell<musubi_jj::node::PublicationCache>,
}

impl NodeAdapter {
    pub fn new(mut repo: NodeRepo) -> anyhow::Result<Self> {
        repo.initialize_publication_offers()?;
        let musubi_dir = repo.repo_path().join("musubi");
        let tmp = musubi_dir.join("tmp");
        open_bundle_dir(&tmp)?;
        Ok(Self {
            base_path: musubi_dir.join("accepted_base"),
            checked_base: RefCell::new(None),
            pushed_path: musubi_dir.join("pushed"),
            accepted_push_path: musubi_dir.join(musubi_jj::node::ACCEPTED_PUSH),
            repo,
            gate: None,
            clock: Box::new(SystemClock),
            tmp,
            base_ancestry: RefCell::new(None),
            staged: HashMap::new(),
            staged_children: HashMap::new(),
            staged_commits: None,
            publication: RefCell::default(),
        })
    }

    /// Asks `gate` before applying any of the hive's history, failing if it fails.
    pub fn set_gate(&mut self, gate: Option<Gate>) {
        self.gate = gate;
    }

    /// Fails if the gate does: before anything of the hive's is written to the repository.
    fn may_apply(&self) -> anyhow::Result<()> {
        self.gate.as_ref().map_or(Ok(()), |gate| gate())
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
        self.repo.forget_retired_copies()?;
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
        let retired = self.repo.forget_retired_copies()?;
        let forgotten = self.repo.expire_idle(self.clock.now(), EXPIRY_STAGGER)?;
        Ok(workspaces || replaced || recorded || retired || !forgotten.is_empty())
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
    /// that `read_heads` requires it below the op heads as it does the base.
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

    /// Fails with [`NodeError::UnreachableHistory`] if the op heads no longer reach the base the
    /// hub accepted last, or the head this node pushed that the hub took: they are history
    /// the hive has, which `jj op abandon` or something else made this copy lose. musubi
    /// doesn't pass that on, and syncing what is left would put the operations back on every
    /// machine, so this copy stops, publishing nothing, until it is replaced. Where an
    /// operation the hive has is rewritten rather than lost, as `jj op abandon` of history
    /// from before the join does to the operations above it, canonicalizing the heads names it
    /// as before, and nothing is lost.
    fn read_heads(&mut self) -> anyhow::Result<Vec<OpId>> {
        // Compatibility until 2027-02-21: remove with `NodeRepo::refuse_legacy_drops`.
        self.repo.refuse_legacy_drops()?;
        // Before canonicalizing them, which takes no name with a `/` for this machine's own.
        self.repo.refuse_slashed_workspaces()?;
        self.repo.settle()?;
        let heads = op_ids(self.repo.canonical_heads()?);
        let accepted_push = match fs::read_to_string(&self.accepted_push_path) {
            Ok(hex) => OpId::try_from_hex(hex.trim()),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => None,
            Err(err) => return Err(err.into()),
        };
        let store = self.repo.canonical_store();
        for watched in [Some(self.read_base()?), accepted_push]
            .into_iter()
            .flatten()
        {
            // One the store lacks, as where the hub was made again, says nothing about the
            // heads.
            if watched == *self.root() || !store.has_operation(&canonical(&watched)) {
                continue;
            }
            let mut reachable = false;
            for head in &heads {
                reachable = reachable || self.canonical_is_ancestor(&watched, head)?;
            }
            if !reachable {
                return Err(NodeError::UnreachableHistory.into());
            }
        }
        Ok(heads)
    }

    /// Makes `base_ancestry` hold `anc*(base)`, extending what it held where `base` descends
    /// from that.
    fn cache_ancestry(&self, base: &OpId) -> anyhow::Result<()> {
        let store = self.repo.canonical_store();
        let bases = [canonical(base)];
        let mut cache = self.base_ancestry.borrow_mut();
        let set = match cache.take() {
            Some((cached, set)) if cached == *base => set,
            Some((cached, mut set)) if self.canonical_is_ancestor(&cached, base)? => {
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

/// Whether `err` is that this repository lost history the hive has, as after `jj op abandon`,
/// which no retry gets past.
pub fn history_lost(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| {
        matches!(
            cause.downcast_ref::<NodeError>(),
            Some(NodeError::UnreachableHistory | NodeError::RewrittenRealization)
        )
    })
}

/// Whether `err` is that this copy has a workspace with a `/` in its name, which it doesn't sync
/// while it has: renaming the workspace, a local operation, lets it sync again.
pub fn slashed_workspaces(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| {
        matches!(
            cause.downcast_ref::<NodeError>(),
            Some(NodeError::SlashedWorkspaces(_))
        )
    })
}

impl LocalRepo for NodeAdapter {
    type Op = OpId;
    type Attachment = Attachment;
    type Error = anyhow::Error;

    fn heads(&mut self) -> anyhow::Result<Vec<OpId>> {
        // jj never makes an operation the hub accepted unreachable from the op heads except
        // through `jj op abandon`, which stops this node syncing for good.
        self.read_heads()
    }

    fn is_local(&self, op: &OpId) -> anyhow::Result<bool> {
        Ok(self.repo.local_of(&canonical(op)).is_some())
    }

    fn is_ancestor(&self, ancestor: &OpId, op: &OpId) -> anyhow::Result<bool> {
        self.canonical_is_ancestor(ancestor, op)
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
        self.repo
            .canonical_store()
            .export_operations(&canonicals(ops), &bundle)?;
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
        self.may_apply()?;
        // The operations likely realized after it, whose views can be made local with its:
        // each the only staged child of the one before.
        let mut next = vec![];
        let mut last = op;
        while next.len() < REALIZE_AT_ONCE - 1 {
            let Some([child]) = self.staged_children.get(last).map(Vec::as_slice) else {
                break;
            };
            if self.staged.get(child).map(Vec::as_slice) != Some(std::slice::from_ref(last)) {
                break;
            }
            next.push(child.clone());
            last = child;
        }
        // Written meanwhile: `advance` waits for them, and so does anything else here that
        // reads local operations.
        let next = canonicals(&next);
        self.repo.realize_pending(&canonical(op), &next)?;
        self.staged.remove(op);
        self.staged_children.remove(op);
        Ok(())
    }

    fn advance(&mut self, op: &OpId) -> anyhow::Result<()> {
        self.may_apply()?;
        self.repo.advance(&canonical(op))?;
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

    fn pushing(&mut self, head: &OpId) -> anyhow::Result<()> {
        self.repo.record_publication_offer(&canonical(head))?;
        write_op(&self.pushed_path, head)
    }

    fn permit_publication(&mut self, ops: &[OpId], base: &OpId) -> anyhow::Result<()> {
        self.repo.initialize_publication_offers()?;
        let limits = musubi_jj::node::PublicationLimits::load(self.repo.loader().settings())?;
        if limits.files == 0 && limits.bytes == 0 {
            return Ok(());
        }
        let report = self.repo.publication_report(
            &canonicals(ops),
            &canonical(base),
            &mut self.publication.borrow_mut(),
        )?;
        if report.held() && !musubi_jj::node::publication_approved(self.repo.repo_path(), &report) {
            return Err(musubi_jj::node::PublicationHeld {
                files: report.files.len(),
                bytes: report.bytes,
            }
            .into());
        }
        Ok(())
    }

    fn learned(&mut self, head: &OpId) -> anyhow::Result<()> {
        self.note_accepted(std::slice::from_ref(head))
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
