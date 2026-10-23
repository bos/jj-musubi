//! Working copies that merges here leave missing, or point at commits other machines
//! abandoned.

use std::collections::BTreeSet;

use jj_lib::backend::CommitId;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::index_err;
use super::is_visible;
use super::view::key_workspace;

impl NodeRepo {
    /// Shows other machines' workspaces in this machine's view again where they went
    /// missing: forgotten here, or dropped when jj merged a forget with concurrent
    /// operations, a removal winning. They are the other machines' own, so this machine's
    /// changes to them never count (see `canonical_view`), and the canonical view still has
    /// them. Returns whether it wrote an operation, which then needs uploading.
    pub fn show_other_workspaces(&mut self) -> Result<bool, NodeError> {
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(repo.op_id())?;
        if canonical == *self.canonical.root_operation_id() {
            return Ok(false);
        }
        let view = self.canonical.read_operation_view(&canonical)?;
        let names = self.local_names(&view);
        let hive_heads: Vec<CommitId> = view.head_ids.iter().cloned().collect();
        let mut tx = repo.start_transaction();
        let mut shown = false;
        for (key, commit) in &view.wc_commit_ids {
            let Some(name) = names.get(key) else {
                continue;
            };
            if self.is_own_key(key) || repo.view().get_wc_commit_id(name).is_some() {
                continue;
            }
            if !is_visible(&repo, commit)? {
                // Forgetting the workspace here hid its commit here, if it was empty, but
                // the hive kept it. Never show a commit the hive hides, though: that would
                // bring back a commit something rewrote. Such a workspace waits for its
                // machine's next operation.
                if !is_ancestor_of_any(&repo, commit, &hive_heads)? {
                    continue;
                }
                let commit = repo.store().get_commit_async(commit).block_on()?;
                tx.repo_mut().add_head(&commit).block_on()?;
            }
            tx.repo_mut()
                .set_wc_commit(name.clone(), commit.clone())
                .map_err(index_err)?;
            shown = true;
        }
        if !shown {
            return Ok(false);
        }
        tx.commit("musubi: show other machines' workspaces")
            .block_on()?;
        Ok(true)
    }

    /// Gives each workspace on this machine whose working-copy commit is no longer visible
    /// a fresh working-copy commit, as jj does when it abandons a working-copy commit
    /// locally. When another machine abandons it, that machine's jj already gave the
    /// workspace a new commit, which arrives with the operation; this covers the rest, such
    /// as an abandon on a machine that had forgotten this machine's workspace. Returns the
    /// workspaces it moved.
    pub fn replace_abandoned_working_copies(&mut self) -> Result<Vec<String>, NodeError> {
        // Merge through `merged_repo`, which exports to `.git`: a bare `load_at_head` would
        // merge without exporting the bookmarks the merge moves.
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(repo.op_id())?;
        let own: BTreeSet<String> = self
            .workspaces_of(&canonical)?
            .into_keys()
            .filter(|key| self.is_own_key(key))
            .map(|key| key_workspace(&key).to_owned())
            .collect();
        let mut abandoned = vec![];
        for (name, wc) in repo.view().wc_commit_ids() {
            // Other machines replace their own.
            if own.contains(name.as_str()) && !is_visible(&repo, wc)? {
                abandoned.push((name.clone(), wc.clone()));
            }
        }
        if abandoned.is_empty() {
            return Ok(vec![]);
        }
        let mut tx = repo.start_transaction();
        let mut moved = vec![];
        for (name, wc) in abandoned {
            // Where jj would have put the new working copy had this happened on this machine:
            // the nearest visible ancestor along first parents, except that an ancestor that
            // was rewritten, not abandoned, is replaced by its rewrite. A rewrite keeps the
            // change id, so it's the change's one visible commit; a change with none was
            // abandoned, and one with several diverged, so neither says where to go.
            let mut parent = repo.store().get_commit_async(&wc).block_on()?;
            while !is_visible(&repo, parent.id())? {
                if parent.id() != &wc
                    && let Some(rewrite) = visible_rewrite(&repo, parent.change_id())?
                {
                    parent = repo.store().get_commit_async(&rewrite).block_on()?;
                    break;
                }
                let Some(first) = parent.parent_ids().first().cloned() else {
                    break;
                };
                parent = repo.store().get_commit_async(&first).block_on()?;
            }
            tx.repo_mut().check_out(name.clone(), &parent).block_on()?;
            moved.push(name.as_str().to_owned());
        }
        let description = format!(
            "musubi: new working copy for {} (abandoned elsewhere)",
            moved.join(", ")
        );
        tx.commit(description).block_on()?;
        Ok(moved)
    }
}

/// Whether `commit` is one of `heads` or an ancestor of one.
fn is_ancestor_of_any(
    repo: &ReadonlyRepo,
    commit: &CommitId,
    heads: &[CommitId],
) -> Result<bool, NodeError> {
    let index = repo.index();
    if !index.has_id(commit).block_on().map_err(index_err)? {
        return Ok(false);
    }
    for head in heads {
        if index.has_id(head).block_on().map_err(index_err)?
            && index
                .is_ancestor(commit, head)
                .block_on()
                .map_err(index_err)?
        {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The visible commit of `change`, if it has exactly one.
fn visible_rewrite(
    repo: &ReadonlyRepo,
    change: &jj_lib::backend::ChangeId,
) -> Result<Option<CommitId>, NodeError> {
    let Some(targets) = repo
        .resolve_change_id(change)
        .block_on()
        .map_err(index_err)?
    else {
        return Ok(None);
    };
    let mut visible = targets.visible_with_offsets().map(|(_, id)| id.clone());
    Ok(match (visible.next(), visible.next()) {
        (Some(only), None) => Some(only),
        _ => None,
    })
}
