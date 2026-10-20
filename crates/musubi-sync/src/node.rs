//! The core's `LocalRepo` over a jj repository.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;

use anyhow::Context as _;
use anyhow::bail;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_core::message::OpEntry;
use musubi_core::node::LocalRepo;
use musubi_jj::node::NodeRepo;

use crate::Attachment;
use crate::OpId;
use crate::temp_bundle;

pub struct NodeAdapter {
    repo: NodeRepo,
    tmp: PathBuf,
    base_path: PathBuf,
    /// Generation numbers of canonical operations (root 0, otherwise one more than the
    /// largest parent's), which bound ancestry searches.
    generations: RefCell<HashMap<OpId, u64>>,
    /// `anc*(base)` for the most recent `base` asked about.
    base_ancestry: RefCell<Option<(OpId, HashSet<OpId>)>>,
}

impl NodeAdapter {
    pub fn new(repo: NodeRepo) -> anyhow::Result<Self> {
        let musubi_dir = repo.repo_path().join("musubi");
        let tmp = musubi_dir.join("tmp");
        fs::create_dir_all(&tmp)?;
        Ok(Self {
            base_path: musubi_dir.join("accepted_base"),
            repo,
            tmp,
            generations: RefCell::new(HashMap::new()),
            base_ancestry: RefCell::new(None),
        })
    }

    pub fn repo(&self) -> &NodeRepo {
        &self.repo
    }

    /// Reconciles this machine's settings with the hive's (`NodeRepo::reconcile_settings`).
    /// Before fetching, a machine that has never reconciled waits: it doesn't know the
    /// hive's settings yet. Returns whether it recorded a change to upload.
    pub fn reconcile_settings(&mut self, before_fetching: bool) -> anyhow::Result<bool> {
        if before_fetching && !self.repo.has_reconciled_settings() {
            return Ok(false);
        }
        Ok(self.repo.reconcile_settings()?)
    }

    pub fn repo_mut(&mut self) -> &mut NodeRepo {
        &mut self.repo
    }

    fn root(&self) -> &OpId {
        self.repo.canonical_store().root_operation_id()
    }

    fn generation(&self, op: &OpId) -> anyhow::Result<u64> {
        let store = self.repo.canonical_store();
        let mut generations = self.generations.borrow_mut();
        let mut stack = vec![op.clone()];
        while let Some(id) = stack.last().cloned() {
            if generations.contains_key(&id) {
                stack.pop();
                continue;
            }
            if id == *self.root() {
                generations.insert(id, 0);
                stack.pop();
                continue;
            }
            let parents = store.read_operation(&id)?.parents;
            let missing: Vec<OpId> = parents
                .iter()
                .filter(|p| !generations.contains_key(*p))
                .cloned()
                .collect();
            if missing.is_empty() {
                let generation = parents.iter().map(|p| generations[p]).max().unwrap_or(0) + 1;
                generations.insert(id, generation);
                stack.pop();
            } else {
                stack.extend(missing);
            }
        }
        Ok(generations[op])
    }

    /// `ancestor ∈ anc*(op)` over the canonical graph. Operations whose generation is no
    /// higher than `ancestor`'s cannot lead to it, so the search never enters them.
    fn canonical_is_ancestor(&self, ancestor: &OpId, op: &OpId) -> anyhow::Result<bool> {
        if ancestor == op {
            return Ok(true);
        }
        let target = self.generation(ancestor)?;
        let store = self.repo.canonical_store();
        let mut seen = HashSet::new();
        let mut stack = vec![op.clone()];
        while let Some(id) = stack.pop() {
            if id == *ancestor {
                return Ok(true);
            }
            if !seen.insert(id.clone()) || self.generation(&id)? <= target {
                continue;
            }
            stack.extend(store.read_operation(&id)?.parents);
        }
        Ok(false)
    }

    fn ancestry_of(&self, base: &OpId) -> anyhow::Result<HashSet<OpId>> {
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
        *cache = Some((base.clone(), set.clone()));
        Ok(set)
    }

    fn required_commits(&self, ops: &[OpId]) -> anyhow::Result<Vec<CommitId>> {
        let mut commits = BTreeSet::new();
        for op in ops {
            commits.extend(self.repo.required_commits(op)?);
        }
        Ok(commits.into_iter().collect())
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
        // operations back on every other machine, so stop instead (docs/design.md,
        // "Abandoning operations and garbage collection").
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
        self.repo.merge_heads()?;
        Ok(())
    }

    fn ops_between(&self, head: &OpId, base: &OpId) -> anyhow::Result<Vec<OpId>> {
        let excluded = self.ancestry_of(base)?;
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

    fn objects_request(&self, _: &[OpId]) -> anyhow::Result<Attachment> {
        let base = self.accepted_base()?;
        Ok(Attachment::Haves(self.required_commits(&[base])?))
    }

    fn stage_ops(&mut self, ops: &[OpEntry<OpId>], attachment: &Attachment) -> anyhow::Result<()> {
        let store = self.repo.canonical_store();
        store.import_operations(attachment.bundle_path()?)?;
        for entry in ops {
            let op = store
                .read_operation(&entry.id)
                .with_context(|| format!("operation {} missing from bundle", entry.id.hex()))?;
            if op.parents != entry.parents {
                bail!(
                    "operation {} has different parents than announced",
                    entry.id.hex()
                );
            }
        }
        Ok(())
    }

    fn stage_objects(&mut self, for_ops: &[OpId], attachment: &Attachment) -> anyhow::Result<()> {
        let wants = self.required_commits(for_ops)?;
        let haves = self.required_commits(&[self.accepted_base()?])?;
        self.repo
            .object_store()?
            .import(attachment.bundle_path()?, &wants, &haves)?;
        Ok(())
    }

    fn staged_parents(&self, op: &OpId) -> anyhow::Result<Option<Vec<OpId>>> {
        let store = self.repo.canonical_store();
        if self.repo.local_of(op).is_some() || !store.has_operation(op) {
            return Ok(None);
        }
        Ok(Some(store.read_operation(op)?.parents))
    }

    fn objects_available(&self, op: &OpId) -> anyhow::Result<bool> {
        let wanted = self.required_commits(std::slice::from_ref(op))?;
        Ok(self.repo.object_store()?.missing(&wanted)?.is_empty())
    }

    fn realize(&mut self, op: &OpId) -> anyhow::Result<()> {
        self.repo.realize(op)?;
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
        let tmp = tempfile::NamedTempFile::new_in(&self.tmp)?;
        fs::write(tmp.path(), op.hex())?;
        tmp.persist(&self.base_path)?;
        Ok(())
    }
}
