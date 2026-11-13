//! Canonicalizing local operations, and finding the local operation for a canonical one.

use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use pollster::FutureExt as _;

use super::CANONICAL_ATTRIBUTE;
use super::NodeError;
use super::NodeRepo;
use super::join::fingerprint;
use super::supersede::FIXUP_ATTRIBUTE;
use crate::canonical::CanonicalError;
use crate::canonical::CanonicalStore;
use crate::canonical::Work;
use crate::format_guard;
use crate::format_guard::FormatError;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::Kind;
use crate::presence::Presence;
use crate::remote_url::without_credentials;
use crate::workspaces;

#[derive(Default)]
pub(super) struct RecoveredSources {
    pub(super) roots: HashMap<LocalOp, CanonicalOp>,
    pub(super) twins: HashMap<LocalOp, CanonicalOp>,
}

impl NodeRepo {
    /// The canonical form of each local op head, but for one from before this repository
    /// joined, which has none until a merge takes it in (see [`Self::canonicalize`]). A `jj op
    /// abandon` is noticed first, as in [`Self::merge_heads`].
    pub fn canonical_heads(&mut self) -> Result<Vec<CanonicalOp>, NodeError> {
        self.check_abandon()?;
        let heads = self.local_heads()?;
        let mut canonical = vec![];
        for head in &heads {
            match self.canonicalize(head) {
                Ok(id) => canonical.push(id),
                Err(NodeError::BeforeJoin(_)) => {}
                Err(err) => return Err(err),
            }
        }
        // Reparenting may need a genuinely missing realization. Its first step must not
        // recurse here: every reachable operation, including source aliases, is mapped now.
        self.heads_mapped = true;
        if !self.late.is_empty()
            && let Err(err) = self.reparent_late()
        {
            self.heads_mapped = false;
            return Err(err);
        }
        Ok(canonical)
    }

    /// Reparents the local operations canonicalized on operations a renaming superseded
    /// onto the rewrites, as their canonical operations have them, and moves the op heads
    /// among them there: before anything merges them with the renamed history, which would
    /// merge against an older common ancestor.
    fn reparent_late(&mut self) -> Result<(), NodeError> {
        let late = self.late.clone();
        let op_store = self.loader.op_store().clone();
        let mut rewrites: HashMap<LocalOp, LocalOp> = HashMap::new();
        for local in &late {
            let Some(canonical) = self.canonical_of(local) else {
                continue;
            };
            // Taking records can supersede an identity after it was queued. Its counted
            // rewrite already supplies the current realization; do not revive its old body.
            if self.current_ids(&canonical)? != [canonical.clone()] {
                continue;
            }
            let mut op = op_store.read_operation(&local.0).block_on()?;
            let mut parents = vec![];
            for parent in self.canonical.parents(&canonical)? {
                // A contraction can give an operation a parent not yet realized here.
                // Keep the normalization pending if making that parent fails.
                let parent = match self.local_of(&parent) {
                    Some(local) => local,
                    None => self.realize(&parent)?,
                };
                parents.push(parent.0);
            }
            if parents == op.parents
                && op.metadata.attributes.get(CANONICAL_ATTRIBUTE) == Some(&canonical.0.hex())
            {
                continue;
            }
            // A marker ends the native walk for private ownership. Capture that evidence
            // before replacing the parents, so that this marked copy is self-contained.
            let view = op_store.read_view(&op.view_id).block_on()?;
            let own = self.own_of_view(view.wc_commit_ids, &canonical, &op)?;
            self.record_private_workspaces(&mut op.metadata, own.into_keys(), &canonical)?;
            op.parents = parents;
            op.metadata
                .attributes
                .insert(CANONICAL_ATTRIBUTE.to_owned(), canonical.0.hex());
            let rewrite = LocalOp(op_store.write_operation(&op).block_on()?);
            self.insert_map(rewrite.clone(), canonical)?;
            rewrites.insert(local.clone(), rewrite);
        }
        let heads = self.local_heads()?;
        for head in &heads {
            if let Some(rewrite) = rewrites.get(head) {
                self.loader
                    .op_heads_store()
                    .update_op_heads(std::slice::from_ref(&head.0), &rewrite.0)
                    .block_on()?;
            }
        }
        self.late.clear();
        let rewrites = rewrites
            .into_iter()
            .map(|(old, new)| (old, vec![new]))
            .collect();
        self.move_workspaces(&rewrites)
    }

    /// Recover a command jj reparented to root after its accepted basis was already dropped.
    /// Only its immutable native twin supplies the erased input, never an older hive view.
    pub(super) fn unpublished_root_sources(
        &mut self,
        unmapped: &[(LocalOp, StoreOperation)],
    ) -> Result<RecoveredSources, NodeError> {
        let mut roots = HashMap::new();
        for (id, op) in unmapped {
            if op.parents == [self.root_op_id().0.clone()]
                && op.metadata.workspace_name.is_some()
                && !op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                && !op
                    .metadata
                    .attributes
                    .contains_key(crate::canonical::namespace::ATTRIBUTE)
                && self.records.source(id).is_none()
                && !self.is_before_join(id, op)?
                && roots.insert(fingerprint(op), id.clone()).is_some()
            {
                return Err(NodeError::AmbiguousAbandon(id.0.hex()));
            }
        }
        if roots.is_empty() {
            return Ok(RecoveredSources::default());
        }
        let path = self.repo_path.join("op_store/operations");
        let files = fs::read_dir(&path).map_err(|source| NodeError::Io {
            path: path.clone(),
            source,
        })?;
        let store = self.loader.op_store().clone();
        let mut sources: HashMap<LocalOp, Vec<LocalOp>> = HashMap::new();
        for file in files {
            let file = file.map_err(|source| NodeError::Io {
                path: path.clone(),
                source,
            })?;
            let Some(id) = file
                .file_name()
                .to_str()
                .and_then(OperationId::try_from_hex)
            else {
                continue;
            };
            let op = match store.read_operation(&id).block_on() {
                Ok(op) => op,
                Err(jj_lib::op_store::OpStoreError::ObjectNotFound { .. }) => continue,
                Err(err) => return Err(err.into()),
            };
            if op.parents != [self.root_op_id().0.clone()]
                && let Some(root) = roots.get(&fingerprint(&op))
            {
                sources.entry(root.clone()).or_default().push(LocalOp(id));
            }
        }
        let mut found = RecoveredSources::default();
        let mut historical = HashMap::new();
        for (root, twins) in sources {
            let mut target = None;
            let mut authenticated = vec![];
            let mut unanchored = false;
            for twin in &twins {
                let Some(original) = self.historical_native_source(twin, &mut historical)? else {
                    unanchored = true;
                    continue;
                };
                let images = self.current_ids(&original)?;
                let [now] = images.as_slice() else {
                    return Err(NodeError::AmbiguousAbandon(root.0.hex()));
                };
                if self.canonical.original_id(now)? != self.canonical.original_id(&original)?
                    || target.as_ref().is_some_and(|old| old != now)
                {
                    return Err(NodeError::AmbiguousAbandon(root.0.hex()));
                }
                target = Some(now.clone());
                authenticated.push((twin.clone(), original));
            }
            if let Some(target) = target {
                if unanchored {
                    return Err(NodeError::AmbiguousAbandon(root.0.hex()));
                }
                found.roots.insert(root, target);
                found.twins.extend(authenticated);
            }
        }
        // A root command alone cannot distinguish an owned literal from an old foreign
        // alias. Once its source is gone, refuse that ambiguity instead of inventing an
        // owner. Before joining, every native workspace belongs to this copy.
        if !self.joins.is_empty() || !self.applied_records().is_empty() {
            for (id, op) in unmapped {
                if roots.values().any(|root| root == id) && !found.roots.contains_key(id) {
                    let view = store.read_view(&op.view_id).block_on()?;
                    if view
                        .wc_commit_ids
                        .keys()
                        .any(|name| name.as_str().contains('/'))
                    {
                        return Err(NodeError::UnreachableHistory);
                    }
                }
            }
        }
        Ok(found)
    }

    /// Rebuild an unpublished source on its actual historical inputs before dropping them.
    /// A marked realization, join point or established source must anchor the native history.
    fn historical_native_source(
        &mut self,
        local: &LocalOp,
        memo: &mut HashMap<LocalOp, Option<CanonicalOp>>,
    ) -> Result<Option<CanonicalOp>, NodeError> {
        let store = self.loader.op_store().clone();
        let mut active = HashSet::new();
        let mut stack: Vec<(LocalOp, Option<StoreOperation>)> = vec![(local.clone(), None)];
        while let Some((id, expanded)) = stack.pop() {
            if memo.contains_key(&id) {
                continue;
            }
            if id == *self.root_op_id() || self.before_join.contains(&id) {
                memo.insert(id, None);
                continue;
            }
            let Some(op) = expanded else {
                if !active.insert(id.clone()) {
                    return Err(NodeError::AmbiguousAbandon(id.0.hex()));
                }
                let op = store.read_operation(&id.0).block_on()?;
                // Durable aliases establish identity, not a completed ancestry walk.
                if self.records.source(&id).is_some() && self.map.canonical_of(&id).is_none() {
                    self.canonicalize_unchecked(&id)?;
                }
                let known = self
                    .records
                    .source(&id)
                    .cloned()
                    .or_else(|| self.map.canonical_of(&id).cloned())
                    .or_else(|| self.joins.get(&fingerprint(&op)).cloned());
                if let Some(named) = op.metadata.attributes.get(CANONICAL_ATTRIBUTE) {
                    for parent in LocalOp::parents_of(&op) {
                        self.canonicalize_unchecked(&parent)?;
                    }
                    let named = OperationId::try_from_hex(named)
                        .map(CanonicalOp)
                        .filter(|id| self.canonical.has_operation(id))
                        .ok_or_else(|| NodeError::DanglingAttribute {
                            op: id.0.hex(),
                            canonical: named.clone(),
                        })?;
                    if !self.original_realization(&named, &LocalOp::parents_of(&op))? {
                        return Err(NodeError::RewrittenRealization);
                    }
                    self.insert_map(id.clone(), named.clone())?;
                    memo.insert(id.clone(), Some(named));
                    active.remove(&id);
                    continue;
                }
                if let Some(known) = known {
                    memo.insert(id.clone(), Some(known));
                    active.remove(&id);
                    continue;
                }
                let parents = LocalOp::parents_of(&op);
                stack.push((id, Some(op)));
                stack.extend(
                    parents
                        .into_iter()
                        .filter(|parent| !memo.contains_key(parent))
                        .map(|parent| (parent, None)),
                );
                continue;
            };
            let mut parents = vec![];
            let mut anchored = false;
            let mut complete = true;
            for parent in LocalOp::parents_of(&op) {
                if parent == *self.root_op_id() {
                    parents.push(self.canonical.root_operation_id().clone());
                } else if let Some(Some(canonical)) = memo.get(&parent) {
                    anchored = true;
                    if !parents.contains(canonical) {
                        parents.push(canonical.clone());
                    }
                } else if !self.before_join.contains(&parent) {
                    complete = false;
                }
            }
            let result = if anchored && complete {
                let canonical = self.write_canonical(&id, &op, parents)?;
                self.insert_map(id.clone(), canonical.clone())?;
                Some(canonical)
            } else {
                None
            };
            memo.insert(id.clone(), result);
            active.remove(&id);
        }
        Ok(memo.get(local).cloned().flatten())
    }

    /// The canonical parents of a local operation, as they are now: what renamings
    /// superseded, renamed. Also whether a name or preferred local realization changed.
    fn current_parents(&self, parents: &[LocalOp]) -> Result<(Vec<CanonicalOp>, bool), NodeError> {
        let mut renamed = false;
        let mut current = vec![];
        for parent in parents {
            if self.before_join.contains(parent) {
                continue;
            }
            let canonical = self
                .canonical_of(parent)
                .expect("parents canonicalized first");
            let now = self.current_ids(&canonical)?;
            // A warm cache can know an old source and its normalized realization under
            // the same canonical id. New children must use the preferred physical parent.
            let moved = self
                .map
                .local_of(&canonical)
                .is_some_and(|preferred| preferred != parent);
            renamed |= now != [canonical] || moved;
            for op in now {
                if !current.contains(&op) {
                    current.push(op);
                }
            }
        }
        Ok((current, renamed))
    }

    pub fn canonical_of(&self, local: &LocalOp) -> Option<CanonicalOp> {
        if local == self.root_op_id() {
            return Some(self.canonical.root_operation_id().clone());
        }
        self.map
            .canonical_of(local)
            .or_else(|| self.records.source(local))
            .cloned()
    }

    pub fn local_of(&self, canonical: &CanonicalOp) -> Option<LocalOp> {
        if canonical == self.canonical.root_operation_id() {
            return Some(self.root_op_id().clone());
        }
        self.map.local_of(canonical).cloned()
    }

    /// Returns the canonical id of a local operation, canonicalizing it and any
    /// not-yet-canonicalized ancestors.
    ///
    /// The history from before a repository joined isn't the hive's: the join operation
    /// stands for it. A `jj` command that loaded the repository before `musubi join` and wrote
    /// after it, or one run with `--at-op` at an operation from then, makes an operation on
    /// that history. Such an operation has no canonical form, and this fails with
    /// [`NodeError::BeforeJoin`] for it. A merge of it with this machine's later history,
    /// which jj makes, has the merged view, so it leaves the parents from before the join
    /// out of its canonical form.
    pub fn canonicalize(&mut self, local: &LocalOp) -> Result<CanonicalOp, NodeError> {
        if self.canonical_of(local).is_none() {
            self.check_abandon()?;
        }
        self.canonicalize_unchecked(local)
    }

    /// Canonicalizes inside an abandon already being processed, before its heads move.
    pub(super) fn canonicalize_unchecked(
        &mut self,
        local: &LocalOp,
    ) -> Result<CanonicalOp, NodeError> {
        let op_store = self.loader.op_store().clone();
        // Post-order walk: an operation is canonicalized once all its parents are.
        let mut stack: Vec<(LocalOp, Option<StoreOperation>)> = vec![(local.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            // A durable source alias establishes identity, not that its ancestors have
            // been walked. Only an actual cache entry lets realization skip that walk.
            if id == *self.root_op_id()
                || self.map.canonical_of(&id).is_some()
                || self.before_join.contains(&id)
            {
                continue;
            }
            let op = match loaded {
                Some(op) => op,
                None => op_store.read_operation(&id.0).block_on()?,
            };
            // A join point that `jj op abandon` rewrote, abandoning history from before the
            // join, which no other machine has: its parents are from before the join.
            if !op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                && let Some(join) = self.joins.get(&fingerprint(&op))
            {
                let join = join.clone();
                self.insert_map(id, join)?;
                continue;
            }
            let parents = LocalOp::parents_of(&op);
            let missing: Vec<_> = parents
                .iter()
                .filter(|parent| {
                    *parent != self.root_op_id()
                        && self.map.canonical_of(parent).is_none()
                        && !self.before_join.contains(*parent)
                })
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.push((id, Some(op)));
                stack.extend(missing.into_iter().map(|parent| (parent, None)));
                continue;
            }
            let late = parents.iter().any(|parent| self.late.contains(parent));
            let canonical_id = if let Some(source) = self.records.source(&id).cloned() {
                // Keep the established identity. An unchanged alias becomes an
                // explicitly marked realization on its canonical parents; a dropped
                // or renamed one instead makes its descendants late below.
                if self.current_ids(&source)? == [source.clone()] {
                    self.late.push(id.clone());
                }
                source
            } else if let Some(canonical) = op.metadata.attributes.get(CANONICAL_ATTRIBUTE) {
                self.realized_canonical(&id, &op, canonical)?
            } else if self.is_before_join(&id, &op)? {
                self.before_join.insert(id);
                continue;
            } else {
                let (parents, renamed) = self.current_parents(&parents)?;
                if renamed && let Some(original) = self.existing_original(&id, &op)? {
                    self.insert_map(id, original)?;
                    continue;
                }
                if renamed || late {
                    self.late.push(id.clone());
                }
                self.write_canonical(&id, &op, parents)?
            };
            self.insert_map(id, canonical_id)?;
        }
        match self.canonical_of(local) {
            Some(canonical) => Ok(canonical),
            None => Err(NodeError::BeforeJoin(local.0.hex())),
        }
    }

    /// Whether a local operation that isn't a join point or a realization, whose parents are
    /// canonicalized or from before the join, is from before the join too: all of its
    /// parents are, or it is the first of the history before a join, on the root. Another
    /// operation on the root, as `jj op abandon` leaves when it abandons everything below
    /// one, is the hive's, which then finds the history it had abandoned.
    fn is_before_join(&mut self, id: &LocalOp, op: &StoreOperation) -> Result<bool, NodeError> {
        let parents = LocalOp::parents_of(op);
        if parents
            .iter()
            .all(|parent| self.before_join.contains(parent))
        {
            return Ok(!parents.is_empty());
        }
        if parents.as_slice() != std::slice::from_ref(self.root_op_id()) || self.joins.is_empty() {
            return Ok(false);
        }
        Ok(self.join_ancestors()?.contains(id))
    }

    /// The ancestors of the join points reachable from the op heads, but for the root: the
    /// history before the joins. A join point `jj op abandon` rewrote is one by its
    /// fingerprint, as `canonicalize` takes it, with the rewritten history below it.
    fn join_ancestors(&mut self) -> Result<Arc<HashSet<LocalOp>>, NodeError> {
        if let Some(ancestors) = &self.join_ancestors {
            return Ok(ancestors.clone());
        }
        let op_store = self.loader.op_store().clone();
        let root = self.root_op_id().clone();
        let mut seen = HashSet::new();
        let mut stack = self.local_heads()?;
        let mut below_joins: Vec<LocalOp> = vec![];
        while let Some(id) = stack.pop() {
            if id == root || !seen.insert(id.clone()) {
                continue;
            }
            let op = op_store.read_operation(&id.0).block_on()?;
            if self.join_points.contains(&id)
                || (!op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                    && self.joins.contains_key(&fingerprint(&op)))
            {
                below_joins.extend(LocalOp::parents_of(&op));
            } else {
                stack.extend(LocalOp::parents_of(&op));
            }
        }
        let mut ancestors = HashSet::new();
        let mut stack = below_joins;
        while let Some(id) = stack.pop() {
            if id == *self.root_op_id() || !ancestors.insert(id.clone()) {
                continue;
            }
            stack.extend(LocalOp::parents_of(
                &op_store.read_operation(&id.0).block_on()?,
            ));
        }
        let ancestors = Arc::new(ancestors);
        self.join_ancestors = Some(ancestors.clone());
        Ok(ancestors)
    }

    /// The canonical operation a realization names in its `musubi.canonical` attribute, as
    /// renamings have it now. `jj op abandon` rewrites the operations above the ones it
    /// abandons, keeping their metadata, so a rewritten realization still names its canonical
    /// operation, but has other parents: musubi notices the abandon, and rewrites it again,
    /// before canonicalizing anything (`NodeRepo::notice_abandon`). Its parents must already
    /// be canonicalized.
    fn realized_canonical(
        &mut self,
        id: &LocalOp,
        op: &StoreOperation,
        canonical: &str,
    ) -> Result<CanonicalOp, NodeError> {
        let named = OperationId::try_from_hex(canonical)
            .map(CanonicalOp)
            .filter(|c| self.canonical.has_operation(c))
            .ok_or_else(|| NodeError::DanglingAttribute {
                op: id.0.hex(),
                canonical: canonical.to_owned(),
            })?;
        let local_parents = LocalOp::parents_of(op);
        let current = self.current_ids(&named)?;
        if current != [named.clone()] && self.original_realization(&named, &local_parents)? {
            return Ok(named);
        }
        let canonical_id = match current.as_slice() {
            [now] => now.clone(),
            _ => named,
        };
        let (parents, renamed) = self.current_parents(&local_parents)?;
        if renamed
            || local_parents
                .iter()
                .any(|parent| self.late.contains(parent))
        {
            self.late.push(id.clone());
        }
        if parents != self.canonical.parents(&canonical_id)? {
            // For the daemon's log: the error says what a user needs.
            tracing::info!(
                "operation {} realizes canonical operation {} but no longer has its parents",
                id.0.hex(),
                canonical_id.0.hex()
            );
            return Err(NodeError::RewrittenRealization);
        }
        Ok(canonical_id)
    }

    /// An obsolete marked ancestor can remain below a delayed command. Its unchanged
    /// physical body still establishes the old identity, even if contraction now drops it
    /// entirely. Its children apply the renaming; validating it as its image would instead
    /// compare the old body with a different operation (possibly the root).
    fn original_realization(
        &self,
        named: &CanonicalOp,
        parents: &[LocalOp],
    ) -> Result<bool, NodeError> {
        Ok(self.raw_parents(parents) == self.canonical.parents(named)?)
    }

    fn raw_parents(&self, parents: &[LocalOp]) -> Vec<CanonicalOp> {
        let mut raw = vec![];
        for parent in parents {
            if self.before_join.contains(parent) {
                continue;
            }
            let parent = self
                .canonical_of(parent)
                .expect("parents canonicalized first");
            if !raw.contains(&parent) {
                raw.push(parent);
            }
        }
        raw
    }

    /// Reconstruct an unchanged native ancestor's already stored original before applying
    /// renamings to a new child. This runs only when a parent has moved, not for ordinary
    /// new operations. No canonical operation or view is written speculatively.
    fn existing_original(
        &self,
        id: &LocalOp,
        op: &StoreOperation,
    ) -> Result<Option<CanonicalOp>, NodeError> {
        let (original, _, _) =
            self.canonical_form(id, op, self.raw_parents(&LocalOp::parents_of(op)), |view| {
                self.canonical.view_id(view)
            })?;
        let original = CanonicalStore::operation_id(&original);
        Ok((self.canonical.has_operation(&original)
            && self.current_ids(&original)? != [original.clone()])
        .then_some(original))
    }

    fn write_canonical(
        &mut self,
        id: &LocalOp,
        op: &StoreOperation,
        parents: Vec<CanonicalOp>,
    ) -> Result<CanonicalOp, NodeError> {
        let (canonical_op, presence, kind) =
            self.canonical_form(id, op, parents, |view| self.canonical.write_view(view))?;
        let canonical = self.canonical.write_operation(&canonical_op)?;
        self.remember_original(&canonical, op)?;
        let work = Work::of(&self.canonical, &canonical)?;
        self.remember_presence(canonical.clone(), presence.apply(&work, &kind));
        Ok(canonical)
    }

    /// The canonical operation canonicalizing would map a local operation to, where the hive
    /// has it already, and not a join point. Its parents must be in the translation map, or
    /// from before the join, as canonicalizing would give them first; otherwise None. So too
    /// where its canonical form isn't stored, which this doesn't store, as for jj's rewrite
    /// of an operation, or a realization whose parents jj changed. Notes, as canonicalizing
    /// does, an operation from before the join, and one found on parents a record renamed.
    pub(super) fn exact_canonical(
        &mut self,
        id: &LocalOp,
        op: &StoreOperation,
    ) -> Result<Option<CanonicalOp>, NodeError> {
        // Canonicalizing must walk an identity-only source alias before caching a child
        // above it too, even when the hive already has that child's canonical body.
        let local_parents = LocalOp::parents_of(op);
        if local_parents.iter().any(|parent| {
            parent != self.root_op_id()
                && self.map.canonical_of(parent).is_none()
                && !self.before_join.contains(parent)
        }) {
            return Ok(None);
        }
        if let Some(source) = self.records.source(id).cloned() {
            if self.current_ids(&source)? == [source.clone()] {
                self.late.push(id.clone());
            }
            return Ok(Some(source));
        }
        let (parents, renamed) = self.current_parents(&local_parents)?;
        let late = renamed
            || local_parents
                .iter()
                .any(|parent| self.late.contains(parent));
        let found = if let Some(named) = op.metadata.attributes.get(CANONICAL_ATTRIBUTE) {
            let Some(named) = OperationId::try_from_hex(named)
                .map(CanonicalOp)
                .filter(|c| self.canonical.has_operation(c))
            else {
                return Ok(None);
            };
            let current = self.current_ids(&named)?;
            if current != [named.clone()] && self.original_realization(&named, &local_parents)? {
                return Ok(Some(named));
            }
            let canonical = match current.as_slice() {
                [now] => now.clone(),
                _ => named,
            };
            (self.canonical.parents(&canonical)? == parents).then_some(canonical)
        } else if self.is_before_join(id, op)? {
            self.before_join.insert(id.clone());
            None
        } else {
            if renamed && let Some(original) = self.existing_original(id, op)? {
                return Ok(Some(original));
            }
            let (canonical_op, _, _) =
                self.canonical_form(id, op, parents, |view| self.canonical.view_id(view))?;
            let canonical = CanonicalStore::operation_id(&canonical_op);
            self.canonical
                .has_operation(&canonical)
                .then_some(canonical)
        };
        if found.is_some() && late {
            self.late.push(id.clone());
        }
        Ok(found)
    }

    /// The canonical form of local operation `id`, `op`, on `parents`, its view given an id by
    /// `view_id`, which may store it; and the presence its parents give it, and its kind.
    fn canonical_form(
        &self,
        id: &LocalOp,
        op: &StoreOperation,
        parents: Vec<CanonicalOp>,
        view_id: impl FnOnce(&View) -> Result<ViewId, CanonicalError>,
    ) -> Result<(StoreOperation, Presence<Work>, Kind), NodeError> {
        self.check_format(id, op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let mut metadata = op.metadata.clone();
        metadata.attributes.remove(super::view::LOCAL_WORKSPACES);
        metadata.attributes.remove(super::view::RESERVED_WORKSPACES);
        if let Some((prefix, target)) = target_of(&metadata.description)
            && let Some(canonical) = self.canonical_of(&LocalOp(target))
            && self.canonical.is_ancestor(&canonical, &parents)?
        {
            metadata.description = format!("{prefix}{}", canonical.0.hex());
        }
        // jj records the command that made an operation, which may name an http(s) URL with
        // a token meant for this machine only.
        if let Some(args) = metadata.attributes.get_mut("args") {
            *args = without_credentials(args);
        }
        // Which workspace made an operation is per-machine, like the view's working copies:
        // qualify it, so that each machine can tell its own workspaces' operations from
        // another machine's workspace of the same name (see `realized_workspace_name`).
        metadata.workspace_name = metadata
            .workspace_name
            .map(|name| workspaces::workspace_key(self.machine.key(), name.as_str()));
        // Context is local to the machine that captured it. Carry it through native
        // descendants until their canonical views and presence again describe all aliases.
        if !metadata
            .attributes
            .contains_key(crate::canonical::namespace::ATTRIBUTE)
        {
            for parent in &parents {
                let parent_op = self.canonical.read_operation(parent)?;
                if let Some(context) =
                    crate::canonical::namespace::Namespace::read(&parent_op.metadata)?
                    && context.source == self.machine.key()
                {
                    metadata.attributes.insert(
                        crate::canonical::namespace::ATTRIBUTE.to_owned(),
                        context.encode(),
                    );
                    break;
                }
            }
        }
        if let Some(context) = crate::canonical::namespace::Namespace::read(&metadata)? {
            let mut known = std::collections::BTreeSet::new();
            for parent in &parents {
                known.extend(self.presence(parent)?.known().iter().cloned());
            }
            if context.known.is_subset(&known) {
                metadata
                    .attributes
                    .remove(crate::canonical::namespace::ATTRIBUTE);
            }
        }
        let kind = Kind::of(&metadata);
        // A fix-up changes no view: it restores what musubi works out from history alone.
        let (view_id, presence) = match parents.as_slice() {
            [parent]
                if metadata.attributes.contains_key(FIXUP_ATTRIBUTE)
                    && !metadata
                        .attributes
                        .contains_key(crate::canonical::namespace::ATTRIBUTE) =>
            {
                (
                    self.canonical.read_operation(parent)?.view_id,
                    (*self.presence(parent)?).clone(),
                )
            }
            _ => {
                let (view, presence) = self.canonical_view(
                    id,
                    view,
                    &parents,
                    op.commit_predecessors.as_ref(),
                    &kind,
                    &metadata,
                )?;
                (view_id(&view)?, presence)
            }
        };
        let canonical_op = StoreOperation {
            view_id,
            parents: parents.into_iter().map(|parent| parent.0).collect(),
            metadata,
            commit_predecessors: op.commit_predecessors.clone(),
        };
        Ok((canonical_op, presence, kind))
    }

    /// Refuses operations whose files contain fields this jj-lib would drop.
    pub(super) fn check_format(&self, id: &LocalOp, op: &StoreOperation) -> Result<(), NodeError> {
        let op_store_dir = self.repo_path.join("op_store");
        type Check = fn(&[u8]) -> Result<(), FormatError>;
        let checks: [(PathBuf, Check); 2] = [
            (
                op_store_dir.join("operations").join(id.0.hex()),
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
                op: id.0.hex(),
                source,
            })?;
        }
        Ok(())
    }

    pub(super) fn root_op_id(&self) -> &LocalOp {
        &self.local_root
    }
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

pub(super) fn target_of(description: &str) -> Option<(&'static str, OperationId)> {
    TARGET_PREFIXES.iter().find_map(|prefix| {
        let target = OperationId::try_from_hex(description.strip_prefix(prefix)?)?;
        Some((*prefix, target))
    })
}
