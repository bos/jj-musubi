//! Moving the operation each workspace of this repository recorded, where musubi rewrote local
//! operations.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
use std::path::PathBuf;

use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::join::fingerprint;
use crate::op_id::LocalOp;

impl NodeRepo {
    /// Moves the operation each of this repository's workspaces recorded to its rewrite, as
    /// `locals` has it, as jj's own `jj op abandon` moves the workspace it runs
    /// in: otherwise jj takes the working copy for a sibling of the history the next time its
    /// commit changes. Only the record moves; no file changes. A workspace this can't load is
    /// left, and jj's `jj workspace update-stale` moves it.
    pub(super) fn move_workspaces(
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
    /// rewrote without moving the working copy, as it does one not at an op head, where `locals`
    /// doesn't name its rewrite. jj's rewrite keeps all but the parents, so it is the one operation
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
                let by_content = by_content.get_or_init(|| self.rewrites_by_content(locals));
                self.rewrite_by_content(&recorded, by_content)?
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
