//! Working copies that merges here leave missing, or point at commits other machines
//! abandoned.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::slice;

use jj_lib::backend::CommitId;
use jj_lib::commit::Commit;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::rewrite::CommitRewriter;
use jj_lib::transaction::Transaction;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::index_err;
use super::is_visible;
use crate::op_id::LocalOp;

impl NodeRepo {
    /// Shows other machines' workspaces in this machine's view again where they went
    /// missing: forgotten here, or dropped when jj merged a forget with concurrent
    /// operations, a removal winning. They are the other machines' own, so this machine's
    /// changes to them never count (see `canonical_view`), and the canonical view still has
    /// them. Drops other machines' workspaces under names the hive no longer gives them, as
    /// `jj undo` brings back (`names_other_machine`), unless jj's workspace store says this
    /// machine has a working copy for one. Returns whether it wrote an operation, which then
    /// needs uploading.
    pub fn show_other_workspaces(&mut self) -> Result<bool, NodeError> {
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(&LocalOp(repo.op_id().clone()))?;
        if canonical == *self.canonical.root_operation_id() {
            return Ok(false);
        }
        let view = self.canonical.read_operation_view(&canonical)?;
        let known = self.presence(&canonical)?;
        let names = self.local_names(&view, &known)?;
        let machines = self.machines_of(&view, known.known());
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
        let shown_names: BTreeSet<&WorkspaceNameBuf> = names.values().collect();
        let own = self.own_names(&canonical)?;
        let stale: Vec<WorkspaceNameBuf> = repo
            .view()
            .wc_commit_ids()
            .keys()
            .filter(|name| {
                !shown_names.contains(name)
                    && !own.contains(*name)
                    && self.names_other_machine(name, &machines)
                    && !self.may_be_registered(name)
            })
            .cloned()
            .collect();
        for name in &stale {
            tx.repo_mut()
                .remove_workspace(name)
                .block_on()
                .map_err(index_err)?;
            shown = true;
        }
        if !shown {
            return Ok(false);
        }
        tx.repo_mut().rebase_descendants().block_on()?;
        tx.commit("musubi: show other machines' workspaces")
            .block_on()?;
        Ok(true)
    }

    /// Gives each workspace on this machine whose working-copy commit is no longer visible
    /// a fresh working-copy commit, as jj does when it abandons a working-copy commit
    /// locally. When another machine abandons it, that machine's jj already gave the
    /// workspace a new commit, which arrives with the operation; this covers the rest, such
    /// as an abandon on a machine that had forgotten this machine's workspace. A commit that
    /// was rewritten, as one can be while the hive has forgotten this machine and no other
    /// machine sees it as a working copy, is followed to its rewrite instead, as jj would
    /// have moved the workspace. Returns the workspaces it moved.
    ///
    /// While the hive has forgotten this machine, an abandoned working copy stays where it is
    /// rather than get a new commit, which the other machines would see as an empty commit
    /// of no one's: the machine's next `jj` command rewrites it, as a snapshot, say, and that
    /// work shows it again. But no other machine sees it there either, so jj leaves it behind
    /// when another machine rewrites or abandons its parents, and that snapshot would bring
    /// them back. So it is rebased, still hidden, as jj would have rebased it
    /// (`rebase_hidden`).
    pub fn replace_abandoned_working_copies(&mut self) -> Result<Vec<String>, NodeError> {
        self.replace_hidden_working_copies(false)
    }

    /// [`Self::replace_abandoned_working_copies`], giving even a machine the hive has
    /// forgotten new commits if `even_forgotten`, as one that has left.
    pub(super) fn replace_hidden_working_copies(
        &mut self,
        even_forgotten: bool,
    ) -> Result<Vec<String>, NodeError> {
        // Merge through `merged_repo`, which exports to `.git`: a bare `load_at_head` would
        // merge without exporting the bookmarks the merge moves.
        let repo = self.merged_repo()?;
        let canonical = self.canonicalize(&LocalOp(repo.op_id().clone()))?;
        let forgotten =
            !even_forgotten && !self.presence(&canonical)?.is_present(self.machine.key());
        let mut hidden = vec![];
        // Other machines replace their own.
        for (name, wc) in self.own_workspaces(&repo, &canonical)? {
            if !is_visible(&repo, &wc)? {
                hidden.push((name, wc));
            }
        }
        if hidden.is_empty() {
            return Ok(vec![]);
        }
        let mut tx = repo.start_transaction();
        let (mut abandoned, mut rewritten, mut rebased) = (vec![], vec![], vec![]);
        // Each hidden commit rebased, by the commit it was, so that workspaces sharing one
        // share its rebase too, as when jj rebases it.
        let mut rebases: HashMap<CommitId, Option<CommitId>> = HashMap::new();
        for (name, wc) in hidden {
            let wc_commit = repo.store().get_commit_async(&wc).block_on()?;
            if let Some(rewrite) = visible_rewrite(&repo, wc_commit.change_id())? {
                let rewrite = repo.store().get_commit_async(&rewrite).block_on()?;
                tx.repo_mut()
                    .edit(name.clone(), &rewrite)
                    .block_on()
                    .map_err(index_err)?;
                rewritten.push(name.as_str().to_owned());
                continue;
            }
            if forgotten {
                let rebase = match rebases.get(&wc) {
                    Some(rebase) => rebase.clone(),
                    None => {
                        let rebase = rebase_hidden(&repo, &mut tx, wc_commit)?;
                        rebases.insert(wc, rebase.clone());
                        rebase
                    }
                };
                if let Some(commit) = rebase {
                    tx.repo_mut()
                        .set_wc_commit(name.clone(), commit)
                        .map_err(index_err)?;
                    rebased.push(name.as_str().to_owned());
                }
                continue;
            }
            // Where jj would have put the new working copy had this happened on this machine:
            // the nearest visible ancestor along first parents, except that an ancestor that
            // was rewritten, not abandoned, is replaced by its rewrite. A rewrite keeps the
            // change id, so it's the change's one visible commit; a change with none was
            // abandoned, and one with several diverged, so neither says where to go.
            let mut parent = wc_commit;
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
            abandoned.push(name.as_str().to_owned());
        }
        if abandoned.is_empty() && rewritten.is_empty() && rebased.is_empty() {
            return Ok(vec![]);
        }
        let mut description = vec![];
        if !abandoned.is_empty() {
            description.push(format!(
                "new working copy for {} (abandoned elsewhere)",
                abandoned.join(", ")
            ));
        }
        if !rewritten.is_empty() {
            description.push(format!(
                "working copy of {} follows its rewrite elsewhere",
                rewritten.join(", ")
            ));
        }
        if !rebased.is_empty() {
            description.push(format!(
                "working copy of {} rebased, its parents rewritten or abandoned elsewhere",
                rebased.join(", ")
            ));
        }
        tx.commit(format!("musubi: {}", description.join("; ")))
            .block_on()?;
        abandoned.extend(rewritten);
        abandoned.extend(rebased);
        Ok(abandoned)
    }
}

/// The hidden working-copy commit `commit`, of a copy the hive has forgotten, rebased as jj
/// would have rebased it had it seen what other machines did to its parents
/// ([`new_parents`]), and written hidden: neither a head nor recorded as a rewrite, so that
/// the hive hears nothing of it, as of the commit it replaces, until the copy's next work.
/// `None` where its parents are where they were.
fn rebase_hidden(
    repo: &ReadonlyRepo,
    tx: &mut Transaction,
    commit: Commit,
) -> Result<Option<CommitId>, NodeError> {
    let parents = new_parents(repo, commit.parent_ids())?;
    if parents == commit.parent_ids() {
        return Ok(None);
    }
    let rebased = CommitRewriter::new(tx.repo_mut(), commit, parents)
        .rebase()
        .block_on()?
        .detach()
        .write_hidden()
        .block_on()?;
    // jj resolves `@` through the index, which has only the commits transactions add to it.
    tx.repo_mut()
        .index_commits(slice::from_ref(&rebased))
        .block_on()?;
    Ok(Some(rebased.id().clone()))
}

/// The parents jj would rebase a child of `parents` onto, as it does when it merges
/// concurrent operations: a visible parent stays; a hidden one whose change has one visible
/// commit, its rewrite, is replaced by that; and one whose change has none, abandoned, by
/// what its own parents are replaced by. So too one whose change has several, diverged: had jj
/// seen the child, each rewrite would have rebased it, but one child can follow only one, and
/// neither says which.
fn new_parents(repo: &ReadonlyRepo, parents: &[CommitId]) -> Result<Vec<CommitId>, NodeError> {
    let mut new = vec![];
    let mut to_visit: Vec<CommitId> = parents.iter().rev().cloned().collect();
    let mut visited = HashSet::new();
    while let Some(id) = to_visit.pop() {
        if !visited.insert(id.clone()) {
            continue;
        }
        if is_visible(repo, &id)? {
            if !new.contains(&id) {
                new.push(id);
            }
            continue;
        }
        let commit = repo.store().get_commit_async(&id).block_on()?;
        match visible_rewrite(repo, commit.change_id())? {
            Some(rewrite) => to_visit.push(rewrite),
            None => to_visit.extend(commit.parent_ids().iter().rev().cloned()),
        }
    }
    Ok(new)
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
