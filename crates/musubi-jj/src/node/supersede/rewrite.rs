//! Rewriting local operations, op heads, and workspaces after a contraction.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
use std::path::PathBuf;

use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::operation::Operation;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::TakingStop;
use super::dedup;
use super::fixup::Expectation;

use crate::canonical::Contraction;
use crate::node::git;
use crate::node::join::fingerprint;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;

impl NodeRepo {
    /// The canonical operation the first op head stood for before the abandon: its own, or
    /// the nearest one below it, where it is new. Where jj put a new one on history that was
    /// intact, below what it abandoned, one of `bases` that descends from that is nearer: the
    /// op heads descended from the base.
    pub(super) fn standing_for(
        &self,
        heads: &[LocalOp],
        counterparts: &HashMap<LocalOp, CanonicalOp>,
        bases: &[CanonicalOp],
    ) -> Result<Option<CanonicalOp>, NodeError> {
        let mut stack: Vec<LocalOp> = heads.iter().take(1).cloned().collect();
        let mut seen = HashSet::new();
        while let Some(id) = stack.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            if let Some(c) = counterparts.get(&id) {
                return Ok(Some(c.clone()));
            }
            if let Some(c) = self.canonical_of(&id) {
                // The saved base may precede a push accepted since it. When a full trim
                // leaves unpublished work on the root, preserve the newer accepted state,
                // including forgets, rather than whichever watched base came first.
                let mut standing = c;
                for base in bases {
                    if *base != standing && self.canonical.is_ancestor_of(&standing, base)? {
                        standing = base.clone();
                    }
                }
                return Ok(Some(standing));
            }
            let op = self.loader.op_store().read_operation(&id.0).block_on()?;
            stack.extend(LocalOp::parents_of(&op));
        }
        Ok(None)
    }

    /// The expected value of each conflicted remote bookmark at the first of `heads` as the
    /// history before the abandon had it, under the id of its rewrite in `locals`. The walk
    /// back through history takes each operation jj rewrote as the canonical operation it
    /// stands for, as `counterparts` has them, and goes from an operation new since, among
    /// `unmapped`, to `old`, what the head stood for, rather than to what jj put under it.
    pub(super) fn expectation(
        &self,
        heads: &[LocalOp],
        old: &CanonicalOp,
        counterparts: &HashMap<LocalOp, CanonicalOp>,
        unmapped: &[(LocalOp, StoreOperation)],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> Result<Option<Expectation>, NodeError> {
        let Some(head) = heads.first() else {
            return Ok(None);
        };
        let new: HashSet<&LocalOp> = unmapped
            .iter()
            .map(|(id, _)| id)
            .filter(|id| !counterparts.contains_key(*id))
            .collect();
        let old_op = self.canonical.load_operation(old)?;
        // The walk starts among local operations and goes on among canonical ones, from a
        // counterpart or through `old_op`, so an operation here may be either, and its id is
        // taken for a local one: `counterparts` and `new` hold local ones only, which a
        // canonical id matches only at the root, the same id in both stores, which neither
        // holds.
        let local = |op: &Operation| LocalOp(op.id().clone());
        let parents = |op: &Operation| -> Result<Option<Vec<Operation>>, NodeError> {
            if let Some(c) = counterparts.get(&local(op)) {
                return Ok(Some(
                    self.canonical.load_operation(c)?.parents().block_on()?,
                ));
            }
            if !new.contains(&local(op)) {
                return Ok(None);
            }
            let mut parents = vec![];
            let mut to_old = true;
            for parent in op.parents().block_on()? {
                if new.contains(&local(&parent)) || counterparts.contains_key(&local(&parent)) {
                    parents.push(parent);
                } else if std::mem::take(&mut to_old) {
                    parents.push(old_op.clone());
                }
            }
            Ok(Some(parents))
        };
        let roots = [
            self.root_op_id().0.clone(),
            self.canonical.root_operation_id().0.clone(),
        ];
        let history = git::History {
            known: &git::Expected::new(),
            roots: &roots,
            is_join: &|op| self.is_join_point(op),
            parents: &parents,
        };
        let op = self.loader.load_operation(&head.0).block_on()?;
        let values = git::expected_values(self.loader.store(), &op, &history)?;
        if values.is_empty() {
            return Ok(None);
        }
        let at = match locals.get(head).map(Vec::as_slice) {
            Some([now]) => now.clone(),
            Some(_) => return Ok(None),
            None => head.clone(),
        };
        Ok(Some(Expectation {
            at: at.0.hex(),
            values: values
                .into_iter()
                .map(|(name, value)| {
                    (
                        name.as_str().to_owned(),
                        git::expected_token(value.as_ref()),
                    )
                })
                .collect(),
        }))
    }

    /// What `at`, the op head a fix-up's expected values were worked out at, is after an
    /// abandon: jj's rewrite of it, among `unmapped`, as this machine rewrote that in `locals`;
    /// or itself, where neither touched it. None where the abandon dropped it, as `dropped`
    /// has the canonical operations, or made it several.
    pub(super) fn rekeyed(
        &self,
        at: &LocalOp,
        dropped: &HashSet<CanonicalOp>,
        unmapped: &[(LocalOp, StoreOperation)],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> Option<LocalOp> {
        let single = |id: &LocalOp| match locals.get(id).map(Vec::as_slice) {
            Some([now]) => Some(now.clone()),
            Some(_) => None,
            None => Some(id.clone()),
        };
        if locals.contains_key(at) {
            return single(at);
        }
        let op = self
            .loader
            .op_store()
            .read_operation(&at.0)
            .block_on()
            .ok()?;
        let print = fingerprint(&op);
        let mut rewrites = unmapped.iter().filter(|(_, op)| fingerprint(op) == print);
        match (rewrites.next(), rewrites.next()) {
            (Some((id, _)), None) => single(id),
            (Some(_), Some(_)) => None,
            // Untouched by both, unless what it stands for went.
            (None, _) => self
                .canonical_of(at)
                .filter(|c| !dropped.contains(c))
                .map(|_| at.clone()),
        }
    }

    /// Rewrites the local operations reachable from `heads` to match `contraction` of the
    /// canonical history they stand for, as `counterparts` and the translation map say: each
    /// surviving canonical operation's local one with its contracted parents' local ones as
    /// parents, its view and metadata otherwise as they were, so that nothing exports and no
    /// ref moves; and each local operation that stands for none, as `unmapped` has them, on
    /// its parents' rewrites. Returns the local operations each becomes.
    pub(super) fn rewrite_locals(
        &mut self,
        contraction: &mut Contraction,
        heads: &[LocalOp],
        counterparts: &HashMap<LocalOp, CanonicalOp>,
        unmapped: &[(LocalOp, StoreOperation)],
        context: Option<&str>,
    ) -> Result<HashMap<LocalOp, Vec<LocalOp>>, NodeError> {
        let op_store = self.loader.op_store().clone();
        let canonical = &self.canonical;
        // Every canonical operation of the history that may change, with the local one now
        // standing for it.
        let mut standing: HashMap<CanonicalOp, LocalOp> = HashMap::new();
        // The local operations reachable from the heads that stand for canonical ones that may
        // change: more than one local operation can stand for a canonical one, as a
        // realization and its export do, and the translation map knows only the latest.
        let mut stack: Vec<LocalOp> = heads.to_vec();
        let mut seen = HashSet::new();
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone()) || self.joins.before.contains(&local) {
                continue;
            }
            match self.canonical_of(&local) {
                Some(c) => {
                    if !contraction.may_change(canonical, &c)? {
                        continue;
                    }
                    standing.entry(c).or_insert_with(|| local.clone());
                }
                None if counterparts.contains_key(&local) => {}
                None => {}
            }
            let op = op_store.read_operation(&local.0).block_on()?;
            stack.extend(LocalOp::parents_of(&op));
        }
        // Several local operations can stand for one canonical operation, and they are not
        // alike: a realization of an operation a record dropped stands for what the drop
        // replaced it with, its parents, beside those parents' own realizations. Each is a
        // template for the operation it stands for, and a dropped operation's view and
        // metadata are not its parents': taking it brings the dropped operation back.
        let named_by: HashMap<&LocalOp, &StoreOperation> =
            unmapped.iter().map(|(id, op)| (id, op)).collect();
        let mut candidates = vec![];
        for (local, c) in counterparts {
            let name = self.records.source(local).cloned().or_else(|| {
                let op = named_by.get(local)?;
                OpAttrs(&op.metadata.attributes).canonical_op()
            });
            // A record that renamed an operation kept its original; one that dropped it did
            // not, and what stands for it stands for the image, a different operation.
            let stand_in = match name {
                Some(n) if n != *c && self.canonical.has_operation(&n) => {
                    match (
                        self.canonical.original_id(&n),
                        self.canonical.original_id(c),
                    ) {
                        (Ok(was), Ok(is)) => was != is,
                        _ => true,
                    }
                }
                _ => false,
            };
            candidates.push((local.clone(), c.clone(), stand_in));
        }
        let (genuine, stand_ins) = templates(candidates);
        standing.extend(genuine);
        // Only where no other local operation stands for it: the translation map's, or else
        // the stand-in itself.
        for (c, local) in stand_ins {
            let local = self.local_of(&c).unwrap_or(local);
            standing.entry(c).or_insert(local);
        }
        let mut tops: Vec<CanonicalOp> = standing.keys().cloned().collect();
        for head in heads {
            if let Some(c) = self.canonical_of(head) {
                tops.push(c);
            }
        }
        let mut affected: Vec<CanonicalOp> = canonical.ancestors_until(&tops, |op| {
            !standing.contains_key(op) && !contraction.may_change(canonical, op).unwrap_or(true)
        })?;
        affected.retain(|op| self.local_of(op).is_some() || standing.contains_key(op));
        // Validate and contract tips before their prefixes: asking in parents-first order
        // would rescan each growing prefix to check original identities, quadratically.
        for c in affected.iter().rev() {
            contraction.images(canonical, c)?;
        }
        // Parents first: `ancestors_until` puts them so.
        let mut local_now: HashMap<CanonicalOp, LocalOp> = HashMap::new();
        let mut locals: HashMap<LocalOp, Vec<LocalOp>> = HashMap::new();
        let mut replaced_heads = HashMap::new();
        let putting_back = contraction.dropped().is_empty() && !counterparts.is_empty();
        for c in &affected {
            let Some(template) = standing.get(c).cloned().or_else(|| self.local_of(c)) else {
                continue;
            };
            let images = contraction.images(&self.canonical, c)?;
            if contraction.drops(c) {
                let mut rewritten = vec![];
                for image in &images {
                    rewritten.push(self.local_for(image, &local_now)?);
                }
                locals.insert(template, dedup(rewritten));
                continue;
            }
            let new = images[0].clone();
            let mut op = op_store.read_operation(&template.0).block_on()?;
            let mut parents = vec![];
            for parent in self.canonical.parents(&new)? {
                parents.push(self.local_for(&parent, &local_now)?.0);
            }
            let changed = new != *c
                || (counterparts.contains_key(&template)
                    && OpAttrs(&op.metadata.attributes).canonical().is_none())
                || op.parents != parents
                || OpAttrs(&op.metadata.attributes)
                    .canonical()
                    .is_some_and(|hex| hex != new.0.hex());
            let rewrite = if changed {
                let view = op_store.read_view(&op.view_id).block_on()?;
                let own = self.own_of_view(view.wc_commit_ids, c, &op)?;
                self.record_private_workspaces(&mut op.metadata, own.into_keys(), &new)?;
                op.parents = parents;
                // The translation map is disposable. Without a durable marker, translating
                // this rewrite after cache loss would mint an origin from its new parents.
                // It also prevents jj's local content addressing from coalescing originals.
                OpAttrs(&mut op.metadata.attributes).set_canonical(&new);
                self.write_local_rewrite(
                    &mut op,
                    &template,
                    heads,
                    putting_back,
                    &mut replaced_heads,
                )?
            } else {
                template.clone()
            };
            self.insert_map(rewrite.clone(), new.clone())?;
            local_now.insert(new, rewrite.clone());
            locals.insert(template, vec![rewrite]);
        }
        // Another local operation standing for the same canonical one, as jj's rewrite of an
        // operation and a copy of it a stale workspace brought back do, becomes the same.
        for (local, c) in counterparts {
            if !locals.contains_key(local)
                && let Some(rewritten) = standing.get(c).and_then(|winner| locals.get(winner))
            {
                locals.insert(local.clone(), rewritten.clone());
            }
        }
        // Operations written since that stand for nothing yet, on their parents' rewrites.
        for (id, op) in unmapped {
            if counterparts.contains_key(id) {
                continue;
            }
            let old_parents = LocalOp::parents_of(op);
            let parents = dedup(
                old_parents
                    .iter()
                    .flat_map(|p| locals.get(p).cloned().unwrap_or_else(|| vec![p.clone()])),
            );
            let context = context.filter(|_| parents.as_slice() == [self.root_op_id().clone()]);
            let rewrite = if parents == old_parents && context.is_none() {
                id.clone()
            } else {
                let mut op = op.clone();
                op.parents = parents.into_iter().map(|parent| parent.0).collect();
                if let Some(context) = context {
                    OpAttrs(&mut op.metadata.attributes).set_namespace(context.to_owned());
                }
                self.write_local_rewrite(&mut op, id, heads, putting_back, &mut replaced_heads)?
            };
            locals.insert(id.clone(), vec![rewrite]);
        }
        if !replaced_heads.is_empty() {
            for head in replaced_heads.keys() {
                locals
                    .entry(head.clone())
                    .or_insert_with(|| vec![head.clone()]);
            }
            for images in locals.values_mut() {
                for image in images {
                    if let Some(replacement) = replaced_heads.get(image) {
                        image.clone_from(replacement);
                    }
                }
            }
        }
        Ok(locals)
    }

    /// jj can still have an unlink pending for an old head, even if it has already
    /// disappeared. Give restored heads fresh names when putting history back. Retire
    /// any visible head whose body this would recreate, including a replacement added
    /// before a restart.
    fn write_local_rewrite(
        &self,
        op: &mut StoreOperation,
        source: &LocalOp,
        heads: &[LocalOp],
        putting_back: bool,
        replaced_heads: &mut HashMap<LocalOp, LocalOp>,
    ) -> Result<LocalOp, NodeError> {
        if !putting_back && heads.len() <= 1 {
            return Ok(LocalOp(
                self.loader.op_store().write_operation(op).block_on()?,
            ));
        }
        let mut replaced = vec![];
        let mut id = LocalOp(OperationId::new(blake2b_hash(op).to_vec()));
        if id == *source {
            return Ok(id);
        }
        if (putting_back && heads.contains(source)) || heads.contains(&id) {
            loop {
                OpAttrs(&mut op.metadata.attributes).set_reconciled_from(&source.0, &id.0);
                if heads.contains(&id) {
                    replaced.push(id);
                }
                id = LocalOp(OperationId::new(blake2b_hash(op).to_vec()));
                if !heads.contains(&id) {
                    break;
                }
            }
        }
        let rewrite = LocalOp(self.loader.op_store().write_operation(op).block_on()?);
        replaced_heads.extend(replaced.into_iter().map(|old| (old, rewrite.clone())));
        Ok(rewrite)
    }

    /// The local operation for `canonical`, a node-space operation: one just rewritten, or
    /// the one the translation map has.
    fn local_for(
        &self,
        canonical: &CanonicalOp,
        local_now: &HashMap<CanonicalOp, LocalOp>,
    ) -> Result<LocalOp, NodeError> {
        local_now
            .get(canonical)
            .cloned()
            .or_else(|| self.local_of(canonical))
            .ok_or_else(|| {
                NodeError::NotRealizable(canonical.0.hex(), "its local operation is missing")
            })
    }

    /// Moves the op heads to their rewrites, and to `head` too if given, keeping the maximal
    /// ones: `heads := max(images(heads) ∪ {head})`. `merged`, a merge of some of those, goes
    /// in place of the ones it merges. Returns whether it moved them, as
    /// [`Self::publish_heads`] does.
    pub(super) fn move_heads(
        &mut self,
        heads: &[LocalOp],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
        head: Option<&LocalOp>,
        merged: Option<&LocalOp>,
    ) -> Result<bool, NodeError> {
        let new = self.new_heads(heads, locals, head, merged)?;
        self.publish_heads(heads, locals, &new)
    }

    /// The op heads [`Self::move_heads`] moves `heads` to.
    pub(super) fn new_heads(
        &self,
        heads: &[LocalOp],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
        head: Option<&LocalOp>,
        merged: Option<&LocalOp>,
    ) -> Result<Vec<LocalOp>, NodeError> {
        let mut new = self.moved_heads(heads, locals, head)?;
        if let Some(merged) = merged {
            let parents = LocalOp::parents_of(
                &self
                    .loader
                    .op_store()
                    .read_operation(&merged.0)
                    .block_on()?,
            );
            new.retain(|op| !parents.contains(op));
            new.push(merged.clone());
        }
        Ok(new)
    }

    /// Makes `new` the op heads in place of `heads`, the op heads as read before working out
    /// the move, each of which became what `from` says, if they are still those
    /// ([`Self::replace_heads`]). Returns whether it moved them. Where it didn't, as a `jj`
    /// command or `jj op abandon` changed the op heads meanwhile, the move is left to work
    /// out again from the op heads as they are, and the next look for an abandon does so.
    pub(super) fn publish_heads(
        &mut self,
        heads: &[LocalOp],
        from: &HashMap<LocalOp, Vec<LocalOp>>,
        new: &[LocalOp],
    ) -> Result<bool, NodeError> {
        if self.records.stop == Some(TakingStop::Publishing) {
            // As a crash in jj's update leaves them, its new op heads in.
            self.replace_heads(heads, from, new, false)?;
            self.stop_taking(TakingStop::Publishing)?;
        }
        let moved = self.replace_heads(heads, from, new, true)?;
        if !moved {
            self.abandon.overtaken();
        }
        Ok(moved)
    }

    /// The op heads `heads` moved to their rewrites, with `head` too if given, the maximal
    /// ones: `max(images(heads) ∪ {head})`.
    pub(super) fn moved_heads(
        &self,
        heads: &[LocalOp],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
        head: Option<&LocalOp>,
    ) -> Result<Vec<LocalOp>, NodeError> {
        let mut new: Vec<LocalOp> = dedup(
            heads
                .iter()
                .flat_map(|h| locals.get(h).cloned().unwrap_or_else(|| vec![h.clone()]))
                .chain(head.cloned()),
        );
        // Keep only the maximal ones, by the canonical operations they stand for.
        let canonical: Vec<Option<CanonicalOp>> =
            new.iter().map(|local| self.canonical_of(local)).collect();
        let mut keep = vec![true; new.len()];
        for i in 0..new.len() {
            for j in 0..new.len() {
                if i == j || !keep[j] {
                    continue;
                }
                if let (Some(a), Some(b)) = (&canonical[i], &canonical[j])
                    && a != b
                    && self.canonical.is_ancestor_of(a, b)?
                {
                    keep[i] = false;
                }
            }
        }
        let mut index = 0;
        new.retain(|_| {
            index += 1;
            keep[index - 1]
        });
        Ok(new)
    }

    /// Moves the operation each of this repository's workspaces recorded to its rewrite, as
    /// `locals` or a renaming has it, as jj's own `jj op abandon` moves the workspace it runs
    /// in: otherwise jj takes the working copy for a sibling of the history the next time its
    /// commit changes. Only the record moves; no file changes. A workspace this can't load is
    /// left, and jj's `jj workspace update-stale` moves it.
    pub(in super::super) fn move_workspaces(
        &self,
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> Result<(), NodeError> {
        let mut roots: BTreeSet<PathBuf> = BTreeSet::new();
        let mut names = BTreeSet::new();
        for head in self.local_heads()? {
            let view = self.repo_at(&head)?;
            names.extend(view.view().wc_commit_ids().keys().cloned());
        }
        for name in &names {
            if let Ok(Some(path)) = self.loader.workspace_store().get_workspace_path(name) {
                roots.insert(path);
            }
        }
        // Where `.jj/repo` is a directory, the workspace around it.
        if let Some(root) = self.repo_path.parent().and_then(Path::parent) {
            roots.insert(root.to_owned());
        }
        // Worked out only if a working copy needs it.
        let by_content = std::cell::OnceCell::new();
        for root in roots {
            if let Err(err) = self.move_workspace(&root, locals, &by_content) {
                tracing::warn!(
                    "recording {}'s operation as rewritten: {err}",
                    root.display()
                );
            }
        }
        Ok(())
    }

    /// The rewrites `locals` makes, by the fingerprint of what each rewrites: its content but
    /// for its parents, which jj's own rewrite of an operation keeps. None for a fingerprint
    /// with different rewrites, or one that `locals` drops or splits.
    fn rewrites_by_content(
        &self,
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> HashMap<String, Option<LocalOp>> {
        let op_store = self.loader.op_store();
        let mut by_content: HashMap<String, Option<LocalOp>> = HashMap::new();
        for (old, new) in locals {
            // One that can't be read stands for nothing here.
            let Ok(op) = op_store.read_operation(&old.0).block_on() else {
                continue;
            };
            let rewrite = match new.as_slice() {
                [new] => Some(new.clone()),
                _ => None,
            };
            by_content
                .entry(fingerprint(&op))
                .and_modify(|found| {
                    if *found != rewrite {
                        *found = None;
                    }
                })
                .or_insert(rewrite);
        }
        by_content
    }

    /// The rewrite of `recorded`, an operation a working copy records that `jj op abandon`
    /// rewrote without moving the working copy, as it does one not at an op head, where no
    /// renaming names its rewrite: one not yet published, whose canonical form no record
    /// superseded. jj's rewrite keeps all but the parents, so it is the one operation
    /// `by_content` has with the same fingerprint, if the op heads no longer reach `recorded`.
    /// Left stale, the working copy's next command would merge what the abandon dropped back
    /// in, with `snapshot.auto-update-stale`, and the hub would refuse every push of it.
    fn rewrite_by_content(
        &self,
        recorded: &LocalOp,
        by_content: &HashMap<String, Option<LocalOp>>,
    ) -> Result<Option<LocalOp>, NodeError> {
        let op = match self
            .loader
            .op_store()
            .read_operation(&recorded.0)
            .block_on()
        {
            Ok(op) => op,
            Err(jj_lib::op_store::OpStoreError::ObjectNotFound { .. }) => return Ok(None),
            Err(err) => return Err(err.into()),
        };
        let Some(Some(rewrite)) = by_content.get(&fingerprint(&op)) else {
            return Ok(None);
        };
        // An operation still in the history keeps its working copy.
        let heads = self.local_heads()?;
        let mut stack = heads.clone();
        let mut seen = HashSet::new();
        while let Some(local) = stack.pop() {
            if local == *recorded {
                return Ok(None);
            }
            if !seen.insert(local.clone()) {
                continue;
            }
            let op = self.loader.op_store().read_operation(&local.0).block_on()?;
            stack.extend(LocalOp::parents_of(&op));
        }
        Ok(Some(rewrite.clone()))
    }

    fn move_workspace(
        &self,
        root: &Path,
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
        by_content: &std::cell::OnceCell<HashMap<String, Option<LocalOp>>>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        if !root.join(".jj").join("working_copy").is_dir() {
            return Ok(());
        }
        use jj_lib::workspace::WorkspaceLoaderFactory as _;
        let mut workspace = jj_lib::workspace::DefaultWorkspaceLoaderFactory
            .create(root)?
            .load(
                self.loader.settings(),
                &jj_lib::default_backend_factories::default_backend_factories(),
                &jj_lib::default_backend_factories::default_working_copy_factories(),
            )?;
        let same = |a: &Path, b: &Path| match (a.canonicalize(), b.canonicalize()) {
            (Ok(a), Ok(b)) => a == b,
            _ => false,
        };
        if !same(workspace.repo_path(), &self.repo_path) {
            return Ok(());
        }
        let name = workspace.workspace_name().to_owned();
        // Read under the lock, so that a `jj` command that records another meanwhile isn't
        // moved back.
        let mut locked = workspace.start_working_copy_mutation().block_on()?;
        let recorded = LocalOp(locked.locked_wc().old_operation_id().clone());
        let rewrite = match locals.get(&recorded).map(Vec::as_slice) {
            Some([rewrite]) => Some(rewrite.clone()),
            _ => {
                let now = match self.canonical_of(&recorded) {
                    Some(canonical) => match self.current_ids(&canonical)?.as_slice() {
                        [now] if *now != canonical || self.records.source(&recorded).is_some() => {
                            self.local_of(now)
                        }
                        _ => None,
                    },
                    None => None,
                };
                now.map_or_else(
                    || {
                        let by_content =
                            by_content.get_or_init(|| self.rewrites_by_content(locals));
                        self.rewrite_by_content(&recorded, by_content)
                    },
                    |op| Ok(Some(op)),
                )?
            }
        };
        let Some(rewrite) = rewrite.filter(|rewrite| *rewrite != recorded) else {
            return Ok(());
        };
        let store = self.loader.op_store();
        let old_op = store.read_operation(&recorded.0).block_on()?;
        let old_view = store.read_view(&old_op.view_id).block_on()?;
        let Some(commit) = old_view.wc_commit_ids.get(&name) else {
            return Ok(());
        };
        // A dropped operation can map to an ancestor, even the empty root. That isn't a
        // snapshot basis for these files. Prefer its image only if it preserves the actual
        // working-copy commit; otherwise find a surviving operation that still records it.
        // Never tell jj that the files belong to another commit, or to no workspace at all.
        let mut pending = self.local_heads()?;
        pending.push(rewrite);
        let mut seen = HashSet::new();
        while let Some(candidate) = pending.pop() {
            if !seen.insert(candidate.clone()) {
                continue;
            }
            let op = store.read_operation(&candidate.0).block_on()?;
            let view = store.read_view(&op.view_id).block_on()?;
            if view.wc_commit_ids.get(&name) == Some(commit) {
                locked.finish(candidate.0).block_on()?;
                return Ok(());
            }
            pending.extend(LocalOp::parents_of(&op));
        }
        Ok(())
    }
}

/// The local operation each canonical operation takes as its template, from the `candidates`
/// that stand for it: `(local, canonical, stand_in)`, a stand-in being one that stands for it
/// only as the image of an operation a record dropped. Returns those that are not stand-ins,
/// and the stand-ins, each for an operation that has none of the first; the lowest local id
/// among equals, never an order the caller's map happened to give.
fn templates(
    mut candidates: Vec<(LocalOp, CanonicalOp, bool)>,
) -> (HashMap<CanonicalOp, LocalOp>, HashMap<CanonicalOp, LocalOp>) {
    candidates.sort_by_key(|(local, _, _)| local.0.hex());
    let mut genuine = HashMap::new();
    let mut stand_ins = HashMap::new();
    for (local, c, stand_in) in candidates {
        let into = if stand_in {
            &mut stand_ins
        } else {
            &mut genuine
        };
        into.entry(c).or_insert(local);
    }
    stand_ins.retain(|c, _| !genuine.contains_key(c));
    (genuine, stand_ins)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn local(byte: u8) -> LocalOp {
        LocalOp(OperationId::new(vec![byte; 8]))
    }

    fn canonical(byte: u8) -> CanonicalOp {
        CanonicalOp(OperationId::new(vec![byte; 8]))
    }

    /// A realization of a dropped operation stands for the operation its parents image, beside
    /// that operation's own realization, and never wins, whatever order the map gave them:
    /// taking it brought the dropped operation back, in about half the runs.
    #[test]
    fn a_stand_in_for_a_dropped_operation_is_never_the_template() {
        let entries = [
            (local(1), canonical(9), true),
            (local(2), canonical(9), false),
            (local(3), canonical(9), false),
            (local(4), canonical(8), true),
        ];
        let orders = [
            [0, 1, 2, 3],
            [1, 0, 2, 3],
            [3, 2, 1, 0],
            [2, 3, 0, 1],
            [0, 3, 2, 1],
            [1, 2, 3, 0],
        ];
        for order in orders {
            let (genuine, stand_ins) =
                templates(order.iter().map(|&i| entries[i].clone()).collect());
            assert_eq!(
                genuine,
                HashMap::from([(canonical(9), local(2))]),
                "{order:?}"
            );
            assert_eq!(
                stand_ins,
                HashMap::from([(canonical(8), local(4))]),
                "{order:?}"
            );
        }
    }
}
