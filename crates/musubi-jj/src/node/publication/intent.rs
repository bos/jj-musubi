//! Publication intent from immutable jj transaction facts and pinned command renderings.
//!
//! This policy never infers intent from differences against an operation's parents: those
//! parents can be rewritten or collected. Unknown facts keep cleanup conservative.

use std::collections::BTreeSet;
use std::collections::HashSet;

use jj_lib::backend::CommitId;
use jj_lib::op_store::Operation;
use jj_lib::op_store::View;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::content::ContentGraph;
use crate::node::PublicationError;
use crate::op_id::CanonicalOp;

pub const CHECKPOINT_ATTRIBUTE: &str = "musubi.publication-checkpoint";
pub(crate) const INTENT_ATTRIBUTE: &str = "musubi.publication-intent";

/// Cleanup freezes a survivor's source intent before changing its operation parents.
/// The declarations are also predecessor-record roots, not just exemptions from accounting.
pub(crate) fn retained_publication_intent(
    op: &Operation,
) -> Result<Option<BTreeSet<CommitId>>, PublicationError> {
    let Some(text) = op.metadata.attributes.get(INTENT_ATTRIBUTE) else {
        return Ok(None);
    };
    let ids: Vec<String> = serde_json::from_str(text).map_err(PublicationError::MalformedIntent)?;
    let mut roots = BTreeSet::new();
    for id in ids {
        let id = CommitId::try_from_hex(&id).ok_or(PublicationError::InvalidIntentCommit)?;
        if !op
            .commit_predecessors
            .as_ref()
            .is_some_and(|writes| writes.contains_key(&id))
        {
            return Err(PublicationError::UnreferencedIntent);
        }
        roots.insert(id);
    }
    Ok(Some(roots))
}

/// Explicit reference targets retain their history role even when also working-copy tips.
pub(super) fn reference_roots(view: &View) -> BTreeSet<CommitId> {
    let mut roots = BTreeSet::new();
    for target in view
        .local_bookmarks
        .values()
        .chain(view.local_tags.values())
        .chain(view.git_refs.values())
        .chain(view.git_heads.values())
    {
        roots.extend(target.iter().flatten().cloned());
    }
    for remote in view.remote_views.values() {
        for reference in remote.bookmarks.values().chain(remote.tags.values()) {
            roots.extend(reference.target.iter().flatten().cloned());
        }
    }
    roots
}

/// The exact root references in a view, without operation predecessor records.
pub(super) fn view_roots(view: &View) -> BTreeSet<CommitId> {
    let mut roots = reference_roots(view);
    roots.extend(view.head_ids.iter().cloned());
    roots.extend(view.wc_commit_ids.values().cloned());
    roots
}

/// Parse jj's rendered comma-separated symbol list against the view's actual names.
/// Longest matches keep commas and quotes inside a rendered name from becoming separators.
fn named_selections(
    mut names: &str,
    candidates: Vec<(String, BTreeSet<CommitId>)>,
) -> Option<BTreeSet<CommitId>> {
    let mut selected = BTreeSet::new();
    while !names.is_empty() {
        let (name, roots) = candidates
            .iter()
            .filter(|(name, _)| {
                names == name
                    || names
                        .strip_prefix(name.as_str())
                        .is_some_and(|rest| rest.starts_with(", "))
            })
            .max_by_key(|(name, _)| name.len())?;
        selected.extend(roots.iter().cloned());
        names = &names[name.len()..];
        if let Some(rest) = names.strip_prefix(", ") {
            names = rest;
        }
    }
    Some(selected)
}

/// Decode the pinned jj CLI's argument rendering (not POSIX shell quoting).
fn recorded_arg(input: &mut &str) -> Option<String> {
    let mut chars = input.char_indices().peekable();
    let quoted = chars.peek()?.1 == '\'';
    if quoted {
        chars.next();
    }
    let mut value = String::new();
    while let Some((offset, ch)) = chars.next() {
        if quoted && ch == '\\' && chars.peek().is_some_and(|(_, next)| *next == '\'') {
            // jj renders a literal apostrophe and a trailing backslash before the
            // closing delimiter ambiguously. Never guess across that token boundary.
            return None;
        } else if (quoted && ch == '\'') || (!quoted && ch == ' ') {
            let rest = &input[offset + ch.len_utf8()..];
            *input = if quoted && !rest.is_empty() {
                rest.strip_prefix(' ')?
            } else {
                rest
            };
            return Some(value);
        } else {
            if !quoted && !(ch.is_ascii_alphanumeric() || ",-./:@_".contains(ch)) {
                return None;
            }
            value.push(ch);
        }
    }
    if quoted {
        None
    } else {
        *input = "";
        Some(value)
    }
}

/// Whether jj's recorded arguments explicitly invoke Git import, init or clone.
pub fn explicit_git_import(mut args: &str) -> bool {
    if recorded_arg(&mut args).as_deref() != Some("jj") {
        return false;
    }
    let mut git = false;
    while let Some(arg) = recorded_arg(&mut args) {
        let (name, attached) = arg
            .split_once('=')
            .map_or((arg.as_str(), None), |(k, v)| (k, Some(v)));
        if [
            "--repository",
            "-R",
            "--at-operation",
            "--at-op",
            "--color",
            "--config",
            "--config-file",
        ]
        .contains(&name)
        {
            if attached.is_none() && recorded_arg(&mut args).is_none() {
                return false;
            }
        } else if ([
            "--ignore-working-copy",
            "--no-integrate-operation",
            "--ignore-immutable",
            "--debug",
            "--quiet",
            "--no-pager",
        ]
        .contains(&name)
            && attached.is_none())
            || (arg.starts_with("-R") && arg.len() > 2)
        {
            continue;
        } else if !git && arg == "git" {
            git = true;
        } else {
            return git && ["import", "init", "clone"].contains(&arg.as_str());
        }
    }
    false
}

fn recorded_explicit_import(op: &Operation) -> bool {
    op.metadata
        .attributes
        .get("args")
        .is_some_and(|args| explicit_git_import(args))
}

pub(super) fn automatic_git_bookkeeping(op: &Operation) -> bool {
    op.metadata.description == "export git refs"
        || (["import git refs", "import git head"].contains(&op.metadata.description.as_str())
            && !recorded_explicit_import(op))
}

/// Read-only policy access to this copy's joins and native/canonical histories.
pub(super) struct Intent<'a> {
    node: &'a NodeRepo,
}

impl<'a> Intent<'a> {
    pub(super) fn new(node: &'a NodeRepo) -> Self {
        Self { node }
    }

    pub(super) fn facts(
        &self,
        id: &CanonicalOp,
        op: &Operation,
        view: &View,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        if let Some(roots) = retained_publication_intent(op)? {
            return Ok((roots, true));
        }
        if op.metadata.attributes.contains_key(CHECKPOINT_ATTRIBUTE) {
            return Ok((
                op.commit_predecessors
                    .iter()
                    .flatten()
                    .map(|(id, _)| id.clone())
                    .collect(),
                true,
            ));
        }
        if self.node.joins.is_join(id) {
            return self.initial_facts(id);
        }
        self.command(op, view)
    }

    pub(super) fn uncertain(&self, id: &CanonicalOp, op: &Operation) -> Result<bool, NodeError> {
        Ok(!self
            .facts(id, op, &self.node.canonical.read_view(&op.view_id)?)?
            .1)
    }

    pub(super) fn intentional(
        &self,
        id: &CanonicalOp,
        op: &Operation,
        view: &View,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        Ok(self.facts(id, op, view)?.0)
    }

    /// Pre-join native history supplies intrinsic command facts, never a reconstruction
    /// of before/after roles. Missing or unrecognized facts also block destructive cleanup.
    fn initial_facts(&self, join: &CanonicalOp) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        let source = self
            .node
            .local_of(join)
            .ok_or(PublicationError::MissingJoinSource)?;
        let store = self.node.loader.op_store();
        let mut stack = vec![source.0];
        let mut seen = HashSet::new();
        let mut roots = BTreeSet::new();
        let mut known = true;
        while let Some(id) = stack.pop() {
            if !seen.insert(id.clone()) {
                continue;
            }
            let op = store.read_operation(&id).block_on()?;
            stack.extend(op.parents.iter().cloned());
            if let Some(intent) = retained_publication_intent(&op)? {
                roots.extend(intent);
                continue;
            }
            if op.metadata.attributes.contains_key(CHECKPOINT_ATTRIBUTE) {
                roots.extend(
                    op.commit_predecessors
                        .iter()
                        .flatten()
                        .map(|(id, _)| id.clone()),
                );
                continue;
            }
            let view = store.read_view(&op.view_id).block_on()?;
            if let Some(intent) = self.git(&op, &view)? {
                roots.extend(intent);
                continue;
            }
            let (selected, complete) = self.command(&op, &view)?;
            roots.extend(selected);
            known &= complete;
        }
        let view = self.node.canonical.read_operation_view(join)?;
        let required = ContentGraph::new(self.node.loader.store(), &self.node.repo_path)
            .commits(view_roots(&view))?;
        roots.retain(|id| required.contains(id));
        Ok((roots, known))
    }

    #[cfg(test)]
    pub(super) fn initial_intentional(
        &self,
        join: &CanonicalOp,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        Ok(self.initial_facts(join)?.0)
    }

    fn automatic(op: &Operation) -> bool {
        op.metadata.is_snapshot
            || op.metadata.description == "reconcile divergent operations"
            || op.metadata.description.starts_with("musubi:")
    }

    /// Intention must survive arbitrary operation reparenting and native GC. Creation
    /// records and explicit selected revisions do; differences against parent views do not.
    pub(super) fn command(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        if Self::automatic(op) {
            return Ok((BTreeSet::new(), true));
        }
        if automatic_git_bookkeeping(op) {
            return Ok((BTreeSet::new(), false));
        }
        let mut roots = self.recorded_outputs(op, view)?;
        let (selected, known) = self.selections(op, view)?;
        roots.extend(selected);
        Ok((roots, known))
    }

    /// Before stripping private Git refs, establish that every possible selected target is
    /// already covered by actual written outputs. Existing unexplained targets are uncertain;
    /// importing an unrelated ref must not approve an automatically moved bookmark.
    pub(super) fn git(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<Option<BTreeSet<CommitId>>, NodeError> {
        if !["import git refs", "import git head"].contains(&op.metadata.description.as_str())
            || op.metadata.attributes.contains_key(INTENT_ATTRIBUTE)
            || Self::automatic(op)
            || !recorded_explicit_import(op)
        {
            return Ok(None);
        }
        let roots = self.recorded_outputs(op, view)?;
        let covered = ContentGraph::new(self.node.loader.store(), &self.node.repo_path)
            .commits(roots.iter().cloned())?;
        let complete = view
            .git_refs
            .values()
            .chain(view.git_heads.values())
            .flat_map(|target| target.iter().flatten())
            .all(|id| covered.contains(id));
        Ok(complete.then_some(roots))
    }

    /// The pinned jj CLI records full selected commit ids in these command descriptions.
    /// Native fixtures pin those forms; unknown records remain conservative.
    pub(super) fn selections(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        let description = op.metadata.description.as_str();
        let selected = if let Some(id) = description.strip_prefix("edit commit ") {
            Some((id, true))
        } else if description.starts_with("create bookmark ") {
            description
                .rsplit_once(" pointing to commit ")
                .map(|(_, id)| (id, false))
        } else if description.starts_with("point bookmark ") || description.starts_with("set tag ")
        {
            description
                .rsplit_once(" to commit ")
                .map(|(_, id)| (id, false))
        } else {
            None
        };
        if let Some((text, edit)) = selected {
            // `jj diffedit` uses the same description as `jj edit`, but names the old
            // target. Its rewritten output is intentional; the old input gains no exemption.
            if edit
                && CommitId::try_from_hex(text).is_some_and(|id| {
                    op.commit_predecessors
                        .iter()
                        .flatten()
                        .any(|(_, previous)| previous.contains(&id))
                })
            {
                return Ok((BTreeSet::new(), true));
            }
            let id = CommitId::try_from_hex(text).filter(|id| {
                if edit {
                    view.wc_commit_ids.values().any(|tip| tip == id)
                } else {
                    reference_roots(view).contains(id)
                }
            });
            return Ok(match id {
                Some(id) => (BTreeSet::from([id]), true),
                None => (BTreeSet::new(), false),
            });
        }
        if let Some(names) = description.strip_prefix("fetch from git remote(s) ") {
            let candidates = view
                .remote_views
                .iter()
                .map(|(name, remote)| {
                    let roots = remote
                        .bookmarks
                        .values()
                        .chain(remote.tags.values())
                        .flat_map(|reference| reference.target.iter().flatten().cloned())
                        .collect();
                    (name.as_symbol().to_string(), roots)
                })
                .collect();
            return Ok(named_selections(names, candidates)
                .map_or_else(|| (BTreeSet::new(), false), |roots| (roots, true)));
        }
        if description == "fetch from git remote into empty repo" {
            let roots = view
                .remote_views
                .values()
                .flat_map(|remote| remote.bookmarks.values().chain(remote.tags.values()))
                .flat_map(|reference| reference.target.iter().flatten().cloned())
                .collect();
            return Ok((roots, true));
        }
        if ["import git head", "import git refs"].contains(&description) {
            // A complete native import freezes its output roots before private refs
            // disappear. Without that evidence, existing selected targets are uncertain.
            return Ok((BTreeSet::new(), false));
        }
        if description == "export git refs" {
            // jj also retries failed automatic exports under this description. It is
            // not evidence that the user selected its unchanged bookmark targets.
            return Ok((BTreeSet::new(), false));
        }
        for (prefix, tags) in [
            ("track remote bookmark ", false),
            ("track remote tag ", true),
        ] {
            if let Some(names) = description.strip_prefix(prefix) {
                let candidates = view
                    .remote_views
                    .iter()
                    .flat_map(|(remote, refs)| {
                        let refs = if tags { &refs.tags } else { &refs.bookmarks };
                        refs.iter().map(move |(name, reference)| {
                            (
                                name.to_remote_symbol(remote).to_string(),
                                reference.target.iter().flatten().cloned().collect(),
                            )
                        })
                    })
                    .collect();
                return Ok(named_selections(names, candidates)
                    .map_or_else(|| (BTreeSet::new(), false), |roots| (roots, true)));
            }
        }
        let writes_known = op.commit_predecessors.is_some()
            && [
                "commit ",
                "describe ",
                "new empty commit",
                "split ",
                "squash ",
                "rebase ",
                "restore into commit ",
                "revert ",
                "backout ",
                "duplicate ",
                "parallelize ",
                "simplify ",
                "resolve ",
                "Resolve conflicts in commit ",
                "diffedit ",
                "diff edit ",
                "fix ",
                "fixed ",
                "apply fixes",
                "absorb changes into ",
                "arrange revisions",
                "converge ",
                "run: rewrite ",
                "run: nothing changed",
                "track paths",
                "untrack paths",
                "delete paths in commit ",
                "make paths ",
                "edit file ",
                "sign ",
                "unsign ",
                "abandon ",
                "initialize ",
                "create initial working-copy commit",
                "add workspace ",
                "check out git remote's branch: ",
            ]
            .iter()
            .any(|prefix| description.starts_with(prefix));
        let names_only = [
            "delete bookmark ",
            "forget bookmark ",
            "rename bookmark ",
            "untrack remote bookmark ",
            "delete tag ",
            "untrack remote tag ",
            "forget workspace ",
            "forget workspaces ",
            "rename workspace ",
            "Renamed workspace ",
            "add git remote ",
            "remove git remote ",
            "rename git remote ",
            "set git remote ",
        ]
        .iter()
        .any(|prefix| description.starts_with(prefix));
        let root = op.parents.is_empty() && description.is_empty();
        Ok((BTreeSet::new(), writes_known || names_only || root))
    }

    fn recorded_outputs(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        let tips: HashSet<_> = view.wc_commit_ids.values().collect();
        let mut roots: BTreeSet<_> = op
            .commit_predecessors
            .iter()
            .flatten()
            .filter(|(id, previous)| !tips.contains(id) || !previous.is_empty())
            .map(|(id, _)| id.clone())
            .collect();
        // `jj new REV` deliberately chooses REV even when it was already a visible
        // descendant. A partial commit's continuation merely points to its intended output.
        for (id, previous) in op.commit_predecessors.iter().flatten() {
            if previous.is_empty() && tips.contains(id) {
                roots.extend(
                    self.node
                        .loader
                        .store()
                        .get_commit(id)?
                        .parent_ids()
                        .iter()
                        .cloned(),
                );
            }
        }
        Ok(roots)
    }
}
