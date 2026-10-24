//! The core's `LocalRepo` over a jj repository.

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::io::Write as _;
use std::path::PathBuf;

use anyhow::Context as _;
use anyhow::bail;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_core::message::OpEntry;
use musubi_core::node::LocalRepo;
use musubi_jj::node::NodeRepo;
use musubi_jj::node::REALIZE_AT_ONCE;

use crate::Attachment;
use crate::OpId;
use crate::open_bundle_dir;
use crate::temp_bundle;

pub struct NodeAdapter {
    repo: NodeRepo,
    tmp: PathBuf,
    base_path: PathBuf,
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
}

impl NodeAdapter {
    pub fn new(repo: NodeRepo) -> anyhow::Result<Self> {
        let musubi_dir = repo.repo_path().join("musubi");
        let tmp = musubi_dir.join("tmp");
        open_bundle_dir(&tmp)?;
        Ok(Self {
            base_path: musubi_dir.join("accepted_base"),
            repo,
            tmp,
            base_ancestry: RefCell::new(None),
            staged: HashMap::new(),
            staged_children: HashMap::new(),
            staged_commits: None,
        })
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

    /// Reconciles this machine's settings with the hive's (`NodeRepo::reconcile_settings`).
    /// Before fetching, a machine that has never reconciled waits: it doesn't know the
    /// hive's settings yet. Returns whether it recorded a change to upload.
    pub fn reconcile_settings(&mut self, before_fetching: bool) -> anyhow::Result<bool> {
        if before_fetching && !self.repo.has_reconciled_settings() {
            return Ok(false);
        }
        self.repo.settle()?;
        Ok(self.repo.reconcile_settings()?)
    }

    /// Gets ready to sync. A repository made shallow or partial since it joined can't send
    /// what its new work requires, and the hub would refuse it. Settings changed here go up
    /// with the sync, and once the node has the hive's head, the hive's settings apply here.
    /// Op heads may have changed since the last step: a fetch's haves should say so.
    pub fn before_sync(&mut self) -> anyhow::Result<()> {
        self.repo.check_complete()?;
        self.reconcile_settings(true)?;
        self.heads()?;
        Ok(())
    }

    /// What a node does once its policy has nothing left to do: reconcile its settings, and
    /// show other machines' workspaces again. Both run; either may write an operation to
    /// upload, and then it returns true, since the policy has more to do.
    pub fn when_idle(&mut self) -> anyhow::Result<bool> {
        let settings = self.reconcile_settings(false)?;
        let workspaces = self.show_other_workspaces()?;
        Ok(settings || workspaces)
    }

    /// The repository, for tests that act on it, as by crashing it.
    pub fn repo_mut(&mut self) -> &mut NodeRepo {
        &mut self.repo
    }

    pub fn root(&self) -> &OpId {
        self.repo.canonical_store().root_operation_id()
    }

    /// `ancestor ∈ anc*(op)` over the canonical graph.
    fn canonical_is_ancestor(&self, ancestor: &OpId, op: &OpId) -> anyhow::Result<bool> {
        Ok(self.repo.canonical_store().is_ancestor_of(ancestor, op)?)
    }

    /// Makes `base_ancestry` hold `anc*(base)`, extending what it held where `base` descends
    /// from that.
    fn cache_ancestry(&self, base: &OpId) -> anyhow::Result<()> {
        let store = self.repo.canonical_store();
        let mut cache = self.base_ancestry.borrow_mut();
        let set = match cache.take() {
            Some((cached, set)) if cached == *base => set,
            Some((cached, mut set)) if self.canonical_is_ancestor(&cached, base)? => {
                set.extend(
                    store.ancestors_until(std::slice::from_ref(base), |id| set.contains(id))?,
                );
                set
            }
            _ => {
                let mut set: HashSet<OpId> = store
                    .ancestors_until(std::slice::from_ref(base), |_| false)?
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
        Ok(self.repo.required_commits(ops)?.into_iter().collect())
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
            if self.repo.local_of(&op).is_some() {
                frontier.push(op);
            } else if store.has_operation(&op) {
                stack.extend(store.read_operation(&op)?.parents);
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
            .filter_map(|head| self.repo.canonical_of(head))
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

impl LocalRepo for NodeAdapter {
    type Op = OpId;
    type Attachment = Attachment;
    type Error = anyhow::Error;

    fn heads(&mut self) -> anyhow::Result<Vec<OpId>> {
        let heads = self.repo.canonical_heads()?;
        // jj never makes an operation unreachable from the op heads except through
        // `jj op abandon`. Replicating the rewritten history would put the abandoned
        // operations back on every other machine, so stop instead (docs/internals/design.md,
        // "Abandoning operations").
        let base = self.accepted_base()?;
        let mut reachable = false;
        for head in &heads {
            reachable |= self.canonical_is_ancestor(&base, head)?;
        }
        if !reachable {
            bail!(
                "the operation history the hub accepted is no longer reachable from this \
                 repository's op heads (was `jj op abandon` run?); musubi does not replicate \
                 op abandon yet, so replication is paused for this repository"
            );
        }
        Ok(heads)
    }

    fn is_local(&self, op: &OpId) -> anyhow::Result<bool> {
        Ok(self.repo.local_of(op).is_some())
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
        Ok(store.ancestors_until(std::slice::from_ref(head), |id| excluded.contains(id))?)
    }

    fn ops_attachment(&self, ops: &[OpId]) -> anyhow::Result<Attachment> {
        let bundle = temp_bundle(&self.tmp)?;
        self.repo
            .canonical_store()
            .export_operations(ops, &bundle)?;
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
        let store = self.repo.canonical_store();
        let imported: HashMap<OpId, Vec<OpId>> = store
            .import_operations(attachment.bundle_path()?)?
            .into_iter()
            .filter_map(|(id, parents)| Some((id, parents?)))
            .collect();
        for entry in ops {
            let parents = match imported.get(&entry.id) {
                Some(parents) => parents.clone(),
                // Stored before, or not at all.
                None => {
                    store
                        .read_operation(&entry.id)
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
            if self.repo.local_of(&entry.id).is_none() && !self.staged.contains_key(&entry.id) {
                for parent in parents.iter().filter(|p| self.repo.local_of(p).is_none()) {
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
            // The hub had nothing this node lacks.
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
        if self.repo.local_of(op).is_some() {
            return Ok(None);
        }
        if let Some(parents) = self.staged.get(op) {
            return Ok(Some(parents.clone()));
        }
        let store = self.repo.canonical_store();
        if !store.has_operation(op) {
            return Ok(None);
        }
        Ok(Some(store.read_operation(op)?.parents))
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
                .required_commits(std::slice::from_ref(op))?
                .iter()
                .any(|commit| absent.contains(commit))
            {
                missing.push(op.clone());
            }
        }
        Ok(missing)
    }

    fn realize(&mut self, op: &OpId) -> anyhow::Result<()> {
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
        self.repo.realize_pending(op, &next)?;
        self.staged.remove(op);
        self.staged_children.remove(op);
        Ok(())
    }

    fn advance(&mut self, op: &OpId) -> anyhow::Result<()> {
        self.repo.advance(op)?;
        Ok(())
    }

    fn accepted_base(&self) -> anyhow::Result<OpId> {
        match fs::read_to_string(&self.base_path) {
            Ok(hex) => OpId::try_from_hex(hex.trim()).context("corrupt accepted_base"),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(self.root().clone()),
            Err(err) => Err(err.into()),
        }
    }

    fn set_accepted_base(&mut self, op: &OpId) -> anyhow::Result<()> {
        // Overwritten in place: it changes at every advance, and ext4 writes out at once a
        // file renamed over another, or truncated to nothing. Operation ids are all one
        // length, so `set_len` only cuts off what isn't one.
        let hex = op.hex();
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(false)
            .open(&self.base_path)?;
        file.write_all(hex.as_bytes())?;
        file.set_len(hex.len() as u64)?;
        Ok(())
    }
}
