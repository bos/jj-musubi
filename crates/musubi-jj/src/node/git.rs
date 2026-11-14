//! What a node does only when its backend is git: read the repository's local remotes, and
//! export the jj repository's refs to git when it is colocated.

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;

use gix::refs::transaction::PreviousValue;
use jj_lib::backend::CommitId;
use jj_lib::git::FailedRefExportReason;
use jj_lib::git::GitExportError;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::lock::FileLock;
use jj_lib::lock::FileLockError;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::operation::Operation;
use jj_lib::ref_name::GitRefNameBuf;
use jj_lib::ref_name::RemoteRefSymbol;
use jj_lib::repo::MutableRepo;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::store::Store;
use jj_lib::view::View;
use pollster::FutureExt as _;

use super::NodeError;
use super::git_config::ConfigCache;
use crate::git_command::GitError;
use crate::git_command::GitRepo;
use crate::objects::GitObjects;
use crate::objects::Incompleteness;
use crate::op_id::LocalOp;
use crate::ref_locks;
use crate::remote_url::Remote;
use crate::remote_url::without_credentials;

/// A node's git repository, when its backend is git.
pub(super) struct NodeGit {
    repo: GitRepo,
    colocation: Option<Colocation>,
    config: ConfigCache,
}

/// A colocated repository's git repository is also a working copy's, so every `jj` command
/// there imports and exports its refs, under jj's lock. musubi exports them too, before an
/// operation it publishes becomes an op head.
pub(super) struct Colocation {
    /// jj's lock on importing and exporting refs.
    lock_path: PathBuf,
    /// The git repository's directory.
    git_dir: PathBuf,
    /// The expected values of the conflicted remote bookmarks of the operation exported last,
    /// under its realization's id and its exported copy's, where the next export's walk back
    /// through history ([`expected`]) usually stops.
    expected: Mutex<Expected>,
}

/// Expected values of conflicted remote bookmarks, by operation and git ref.
pub(super) type Expected = HashMap<(LocalOp, GitRefNameBuf), Option<RefTarget>>;

/// The attribute of a fix-up's first operation recording the expected value ([`expected`]) of
/// each conflicted remote bookmark there as the history before the abandon had it, one line
/// each: the git ref, then the value ([`expected_token`]).
pub(super) const EXPECTED_ATTRIBUTE: &str = "musubi.expected";

/// A conflicted remote bookmark's git ref, and its expected value.
type Expectation = (GitRefNameBuf, Option<RefTarget>);

/// Whether the jj repository whose `.jj/repo` directory is `repo_path` is colocated with
/// `git`, its backend's git repository: whether any of git's working trees, the main one or
/// one `git worktree add` made, holds one of its workspaces.
///
/// jj takes a workspace as colocated when git opens a repository at the workspace's root
/// whose common directory is the backend's, and imports and exports refs there in every
/// command; a repository is colocated if any of its workspaces is. Asking from git's side
/// finds every such workspace without a list of them, which jj's workspace store can't give
/// and lacks for workspaces older than it. A `.git` set `core.bare` has no working tree to git,
/// but jj still opens it from the directory it is in, so that directory counts too. This differs
/// from jj's answer only for a working tree moved without `git worktree repair`, where git's
/// record of it is stale.
fn is_colocated(git: &gix::Repository, repo_path: &Path) -> bool {
    use jj_lib::workspace::WorkspaceLoaderFactory as _;
    let Ok(repo_path) = repo_path.canonicalize() else {
        return false;
    };
    let linked = git.worktrees().unwrap_or_else(|err| {
        tracing::warn!("listing git worktrees of {}: {err}", git.path().display());
        Vec::new()
    });
    let beside = (git.path().file_name() == Some(".git".as_ref()))
        .then(|| git.path().parent())
        .flatten();
    let mut roots = git
        .workdir()
        .into_iter()
        .chain(beside)
        .map(Path::to_owned)
        .chain(linked.iter().filter_map(|worktree| worktree.base().ok()));
    roots.any(|root| {
        jj_lib::workspace::DefaultWorkspaceLoaderFactory
            .create(&root)
            .is_ok_and(|loader| {
                loader
                    .repo_path()
                    .canonicalize()
                    .is_ok_and(|path| path == repo_path)
            })
    })
}

impl NodeGit {
    /// The git repository of the jj repository whose `.jj/repo` directory is `repo_path` and
    /// whose store is `store`, if its backend is git, with `executable` the git to run there.
    pub fn open(executable: &Path, repo_path: &Path, store: &Store) -> Option<Self> {
        let backend = jj_lib::git::get_git_backend(store).ok()?;
        let git_path = backend.git_repo_path();
        let colocated = is_colocated(&backend.git_repo(), repo_path);
        Some(Self {
            repo: GitRepo::new(executable, git_path),
            colocation: colocated.then(|| Colocation {
                lock_path: repo_path.join("git_import_export.lock"),
                git_dir: git_path.to_owned(),
                expected: Mutex::default(),
            }),
            config: ConfigCache::default(),
        })
    }

    /// The git this repository runs.
    pub fn executable(&self) -> &Path {
        self.repo.executable()
    }

    pub fn colocation(&self) -> Option<&Colocation> {
        self.colocation.as_ref()
    }

    /// What this repository lacks of its history, if anything: a shallow clone has a
    /// `shallow` file listing its shallow commits, and a partial clone a promisor remote.
    pub fn incompleteness(&self) -> Result<Option<Incompleteness>, GitError> {
        if GitObjects::new(self.repo.executable(), self.repo.git_dir()).is_shallow() {
            return Ok(Some(Incompleteness::Shallow));
        }
        let config = self.config.read(&self.repo)?;
        let partial = config.local().any(|entry| {
            // A boolean with no value is true.
            let value = entry.value.as_deref().unwrap_or("true");
            entry.key == "extensions.partialclone"
                || entry.key.starts_with("remote.")
                    && entry.key.ends_with(".promisor")
                    && !["false", "no", "off", "0", ""]
                        .contains(&value.to_ascii_lowercase().as_str())
        });
        Ok(partial.then_some(Incompleteness::Partial))
    }

    /// Reads this repository's effective remotes as credential-free hints for matching a hive.
    /// Git config is local: this never creates or changes a remote.
    pub fn remotes(&self) -> Result<BTreeMap<String, Remote>, GitError> {
        let config = self.config.read(&self.repo)?;
        let mut remotes: BTreeMap<String, Remote> = BTreeMap::new();
        for entry in &config.entries {
            let Some(value) = entry.value.as_deref() else {
                continue;
            };
            let Some(name) = entry
                .key
                .strip_prefix("remote.")
                .and_then(|s| s.strip_suffix(".url"))
            else {
                continue;
            };
            remotes
                .entry(name.to_owned())
                .or_default()
                .url
                .get_or_insert_with(|| without_credentials(value));
        }
        for line in config.remotes.lines() {
            let Some((name, used)) = line.split_once('\t') else {
                continue;
            };
            let remote = remotes.entry(name.to_owned()).or_default();
            if let Some(used) = used.strip_suffix(" (push)") {
                remote.push_urls.insert(without_credentials(used));
            } else if let Some((used, _)) = used.rsplit_once(" (fetch)") {
                let used = without_credentials(used);
                if remote.url.as_ref() != Some(&used) && remote.expanded_url.is_none() {
                    remote.expanded_url = Some(used);
                }
            }
        }
        Ok(remotes)
    }
}

impl Colocation {
    /// Takes jj's lock on importing and exporting refs.
    pub fn lock(&self) -> Result<FileLock, FileLockError> {
        FileLock::lock(self.lock_path.clone())
    }

    /// Runs jj's `export_refs` on top of a realization and returns the operation that
    /// records the result: the same operation if nothing changed, otherwise a copy with the
    /// updated per-machine fields. `is_join` says whether a local operation is a join point.
    /// `beside` are this machine's op heads concurrent with the realization, whose merge with
    /// it musubi exports next, and publishes in its place. `pending` holds expected values a
    /// fix-up not yet written will record.
    pub fn export_refs(
        &self,
        loader: &RepoLoader,
        realized: &LocalOp,
        is_join: &dyn Fn(&Operation) -> bool,
        beside: &[Operation],
        pending: &Expected,
    ) -> Result<LocalOp, NodeError> {
        #[cfg(test)]
        super::native_contract::emit(super::native_contract::Event::Export(realized.clone()));
        let op = loader.load_operation(&realized.0).block_on()?;
        let repo: Arc<ReadonlyRepo> = loader.load_at(&op).block_on()?;
        let mut tx = repo.start_transaction();
        // Refs that fail to export keep their recorded values, exactly as after a failed
        // export in a local `jj` command; jj's next command imports those git has moved since,
        // and exports the rest again.
        let stats = jj_lib::git::export_refs(tx.repo_mut())?;
        let mut known = self.expected.lock().expect("not poisoned").clone();
        known.extend(
            pending
                .iter()
                .map(|(key, value)| (key.clone(), value.clone())),
        );
        let history = History {
            known: &known,
            roots: std::slice::from_ref(loader.op_store().root_operation_id()),
            is_join,
            parents: &|_| Ok(None),
        };
        let (expected, unwritten) =
            export_conflicted_remote_bookmarks(tx.repo_mut(), &op, &history, beside)?;
        // The next export, this machine's next realization's or a `jj` command's, tries a ref
        // that failed again, so a ref lock left behind would fail it every time.
        let written = |reason: &FailedRefExportReason| {
            matches!(
                reason,
                FailedRefExportReason::FailedToSet(_) | FailedRefExportReason::FailedToDelete(_)
            )
        };
        let bookmarks = stats
            .failed_bookmarks
            .iter()
            .filter(|(_, reason)| written(reason));
        let tags = stats
            .failed_tags
            .iter()
            .filter(|(_, reason)| written(reason));
        let failed: Vec<String> = bookmarks
            .map(|(symbol, _)| {
                if symbol.remote == *REMOTE_NAME_FOR_LOCAL_GIT_REPO {
                    format!("refs/heads/{}", symbol.name.as_str())
                } else {
                    format!(
                        "refs/remotes/{}/{}",
                        symbol.remote.as_str(),
                        symbol.name.as_str()
                    )
                }
            })
            .chain(tags.map(|(symbol, _)| format!("refs/tags/{}", symbol.name.as_str())))
            .chain(unwritten.iter().map(|name| name.as_str().to_owned()))
            .collect();
        if !failed.is_empty() {
            ref_locks::remove_stale_of(&self.git_dir, failed.iter().map(String::as_str));
        }
        let remember = |exported: &LocalOp| {
            let ids = [realized, exported];
            *self.expected.lock().expect("not poisoned") = ids
                .into_iter()
                .flat_map(|id| {
                    expected
                        .iter()
                        .map(|(name, e)| ((id.clone(), name.clone()), e.clone()))
                })
                .collect();
        };
        let view = tx.repo().view().store_view();
        if view == repo.view().store_view() {
            remember(realized);
            #[cfg(test)]
            super::native_contract::emit(super::native_contract::Event::Exported(realized.clone()));
            return Ok(realized.clone());
        }
        let mut store_op = op.store_operation().clone();
        store_op.view_id = loader.op_store().write_view(view).block_on()?;
        let op_store = loader.op_store();
        let exported = LocalOp(op_store.write_operation(&store_op).block_on()?);
        // It refers to the realization's commits, so the realization's index is its index
        // too. Without one, loading the repository there, as merging or the next `jj` command
        // does, would index again every operation since the last one with an index, or for a
        // clone, every commit: none it descends from has one.
        let exported_op = Operation::new(op_store.clone(), exported.0.clone(), store_op);
        if let Err(err) = loader
            .index_store()
            .write_index(repo.readonly_index().start_modification(), &exported_op)
        {
            // Only a cache: jj indexes it when loading the repository there.
            tracing::warn!("indexing the exported operation: {err}");
        }
        remember(&exported);
        #[cfg(test)]
        super::native_contract::emit(super::native_contract::Event::Exported(exported.clone()));
        Ok(exported)
    }
}

/// Writes the expected value of each conflicted remote bookmark ([`expected`]) to this
/// machine's `.git`, which jj's export leaves alone, and records the same value in
/// `git_refs`. Ordinary commands therefore leave the conflict unchanged; a fetch imports its
/// explicit result. After concurrent fetches, the expected value is one conflict side. After
/// a restore, it is the value from before the restore, which the restoring machine kept.
/// The write compares against `.git` itself and replaces only a value the hive knows of:
/// a term of the conflict, absent included, or the record. Any other value was put there by
/// git since, and the next import takes it. An unreadable or unwritable ref is left alone.
/// Nor is a ref written where `.git` holds the value an op head `beside` the realization
/// records and the realization doesn't: that head put it there, as by a fetch, and the merge
/// of the two, exported next, can keep it, which writing for the realization would undo.
/// Returns the expected values, by git ref, and the git refs it failed to write.
fn export_conflicted_remote_bookmarks(
    mut_repo: &mut MutableRepo,
    op: &Operation,
    history: &History<'_>,
    beside: &[Operation],
) -> Result<(Vec<Expectation>, Vec<GitRefNameBuf>), NodeError> {
    let conflicted = conflicted_remote_bookmarks(mut_repo.store(), mut_repo.view(), op, history)?;
    if conflicted.is_empty() {
        return Ok((vec![], vec![]));
    }
    let all = conflicted
        .iter()
        .map(|(name, expected, _)| (name.clone(), expected.clone()))
        .collect();
    let beside = beside
        .iter()
        .map(|op| op.view().block_on())
        .collect::<Result<Vec<_>, _>>()?;
    let git_repo = jj_lib::git::get_git_repo(mut_repo.store()).map_err(GitExportError::from)?;
    let mut unwritten = vec![];
    for (name, expected, terms) in conflicted {
        let Some(expected) = expected else {
            continue;
        };
        let Ok(reference) = git_repo.try_find_reference(name.as_str()) else {
            continue;
        };
        let actual = match &reference {
            Some(reference) => match reference.clone().into_fully_peeled_id() {
                Ok(id) => Some(CommitId::from_bytes(id.detach().as_bytes())),
                Err(_) => continue,
            },
            None => None,
        };
        let recorded = mut_repo.view().get_git_ref(&name);
        let theirs = |view: &View| {
            let other = view.get_git_ref(&name);
            other != recorded && other.is_resolved() && other.as_normal() == actual.as_ref()
        };
        if beside.iter().any(theirs) {
            continue;
        }
        let known = terms.contains(&actual)
            || (recorded.is_resolved() && recorded.as_normal() == actual.as_ref());
        if actual.as_ref() != expected.as_normal() {
            if !known {
                continue;
            }
            let written = match (expected.as_normal(), reference) {
                (Some(new), _) => {
                    let Ok(new) = gix::ObjectId::try_from(new.as_bytes()) else {
                        continue;
                    };
                    let constraint = match &actual {
                        Some(old) => {
                            let Ok(old) = gix::ObjectId::try_from(old.as_bytes()) else {
                                continue;
                            };
                            PreviousValue::MustExistAndMatch(old.into())
                        }
                        None => PreviousValue::MustNotExist,
                    };
                    git_repo
                        .reference(name.as_str(), new, constraint, "export from musubi")
                        .is_ok()
                }
                // The ref goes, as jj's export deletes a ref whose bookmark went: if it still
                // has the value just read.
                (None, Some(reference)) => reference.delete().is_ok(),
                (None, None) => true,
            };
            if !written {
                unwritten.push(name);
                continue;
            }
        }
        if *recorded != expected {
            mut_repo.set_git_ref_target(&name, expected);
        }
    }
    Ok((all, unwritten))
}

type Terms = Vec<Option<CommitId>>;

/// Each conflicted remote bookmark of `view`, the view at `op`, with its git ref, its expected
/// value ([`expected`]) and its target's terms.
fn conflicted_remote_bookmarks(
    store: &Arc<Store>,
    view: &View,
    op: &Operation,
    history: &History<'_>,
) -> Result<Vec<(GitRefNameBuf, Option<RefTarget>, Terms)>, NodeError> {
    view.all_remote_bookmarks()
        .filter(|(symbol, remote_ref)| {
            symbol.remote != REMOTE_NAME_FOR_LOCAL_GIT_REPO
                && symbol.name.as_str() != "HEAD"
                && !remote_ref.target.is_resolved()
        })
        .map(|(symbol, remote_ref)| {
            let name: GitRefNameBuf = format!(
                "refs/remotes/{}/{}",
                symbol.remote.as_str(),
                symbol.name.as_str()
            )
            .into();
            let expected = expected(store, history, op, symbol, &name, &remote_ref.target)?;
            Ok((name, expected, remote_ref.target.iter().cloned().collect()))
        })
        .collect()
}

/// The expected value ([`expected`]) of each conflicted remote bookmark at `op`, by git ref,
/// as `history` has history.
pub(super) fn expected_values(
    store: &Arc<Store>,
    op: &Operation,
    history: &History<'_>,
) -> Result<Vec<(GitRefNameBuf, Option<RefTarget>)>, NodeError> {
    let view = op.view().block_on()?;
    let conflicted = conflicted_remote_bookmarks(store, &view, op, history)?;
    Ok(conflicted
        .into_iter()
        .map(|(name, expected, _)| (name, expected))
        .collect())
}

/// Expected values as [`EXPECTED_ATTRIBUTE`] holds them, if there are any.
pub(super) fn format_expected(values: &[(GitRefNameBuf, Option<RefTarget>)]) -> Option<String> {
    if values.is_empty() {
        return None;
    }
    let mut text = String::new();
    for (name, expected) in values {
        writeln!(
            text,
            "{} {}",
            name.as_str(),
            expected_token(expected.as_ref())
        )
        .expect("writing to a String");
    }
    Some(text)
}

/// An expected value in a word: the commit id, `absent` where the ref should be absent, or
/// `none` where there is none and musubi leaves the ref alone. [`expected`] never makes a
/// conflict one.
pub(super) fn expected_token(expected: Option<&RefTarget>) -> String {
    match expected {
        Some(target) if target.is_absent() => "absent".to_owned(),
        Some(target) => target
            .as_normal()
            .map_or_else(|| "none".to_owned(), CommitId::hex),
        None => "none".to_owned(),
    }
}

/// The expected value [`expected_token`] put in a word, if it is one.
pub(super) fn parse_expected_token(token: &str) -> Option<Option<RefTarget>> {
    match token {
        "absent" => Some(Some(RefTarget::absent())),
        "none" => Some(None),
        hex => CommitId::try_from_hex(hex).map(|id| Some(RefTarget::normal(id))),
    }
}

/// The expected value of git ref `name` that `op`'s [`EXPECTED_ATTRIBUTE`] records, if it
/// records one.
fn recorded(op: &Operation, name: &GitRefNameBuf) -> Option<Option<RefTarget>> {
    recorded_in(op.metadata().attributes.get(EXPECTED_ATTRIBUTE)?, name)
}

/// The expected value of git ref `name` that `text`, as [`EXPECTED_ATTRIBUTE`] holds it,
/// records, if it records one.
fn recorded_in(text: &str, name: &GitRefNameBuf) -> Option<Option<RefTarget>> {
    text.lines().find_map(|line| {
        let (refname, value) = line.split_once(' ')?;
        (refname == name.as_str())
            .then(|| parse_expected_token(value))
            .flatten()
    })
}

/// What [`expected`] knows of history beyond the op store.
pub(super) struct History<'a> {
    /// Expected values already worked out: as the last export remembers them, and as a
    /// fix-up not yet written will record them. By local operation: a walk that `parents`
    /// takes into the canonical store has none.
    pub known: &'a Expected,
    /// The root operations: the op store's, and the canonical store's where the walk goes
    /// there.
    pub roots: &'a [OperationId],
    /// Whether an operation is a join point: a local one, as a canonical one the walk reaches
    /// never is (its join operation is on a root).
    pub is_join: &'a dyn Fn(&Operation) -> bool,
    /// An operation's parents as the walk takes them, where they aren't the op store's.
    pub parents: &'a Parents<'a>,
}

/// An operation's parents as [`expected`]'s walk takes them, or none for the op store's.
pub(super) type Parents<'a> = dyn Fn(&Operation) -> Result<Option<Vec<Operation>>, NodeError> + 'a;

/// The value every machine's `.git` should hold for the conflicted remote bookmark `symbol`,
/// whose git ref is `name` and whose target at `op` is `target`, so that every machine's import
/// resolves it alike: `Refs.lean`'s expected value. It depends only on the history of `op`,
/// which every machine shares. Where a parent has the same target, it is that parent's: the
/// first such parent's, for a merge. Where the only parent has another, as for `jj op restore`
/// of the conflict, it is the parent's target, or if that is a conflict too, its expected
/// value, which the `jj` command that made `op` left in its machine's `.git`, exporting nothing
/// for the conflict. Where a merge made the conflict, it is one of the conflict's sides, the
/// one committed last (then the greatest commit id), or none if no side is present; and so it
/// is at a join, whose history before it only the machine that joined has: a join operation,
/// whose realization's only parent is the root, or the join point it is on that machine. Where
/// `op` is a fix-up's first operation, it is what that records, as the history before the
/// abandon had it (docs/internals/design.md, "The fix-up").
fn expected(
    store: &Arc<Store>,
    history: &History<'_>,
    op: &Operation,
    symbol: RemoteRefSymbol<'_>,
    name: &GitRefNameBuf,
    target: &RefTarget,
) -> Result<Option<RefTarget>, NodeError> {
    let mut op = op.clone();
    let mut target = target.clone();
    loop {
        // Taken for a local operation, which every one here is unless `parents` led the walk
        // into the canonical store, where `known` is empty.
        if let Some(known) = history.known.get(&(LocalOp(op.id().clone()), name.clone())) {
            return Ok(known.clone());
        }
        if let Some(recorded) = recorded(&op, name) {
            return Ok(recorded);
        }
        let mut parents = match (history.parents)(&op)? {
            Some(parents) => parents,
            None => op.parents().block_on()?,
        };
        let joined = (history.is_join)(&op)
            || matches!(parents.as_slice(), [parent] if history.roots.contains(parent.id()));
        if joined {
            return Ok(side(store, &target)?.map(RefTarget::normal));
        }
        let mut targets = Vec::with_capacity(parents.len());
        for parent in &parents {
            let view = parent.view().block_on()?;
            targets.push(view.get_remote_bookmark(symbol).target.clone());
        }
        if let Some(same) = targets.iter().position(|t| *t == target) {
            op = parents.swap_remove(same);
            continue;
        }
        match (parents.pop(), targets.pop()) {
            (Some(parent), Some(parent_target)) if parents.is_empty() => {
                if parent_target.is_resolved() {
                    return Ok(Some(parent_target));
                }
                op = parent;
                target = parent_target;
            }
            _ => return Ok(side(store, &target)?.map(RefTarget::normal)),
        }
    }
}

/// The side of a conflict musubi chooses where a merge made it: the one committed last, then
/// the greatest commit id, the same on every machine; none if no side is present.
fn side(store: &Arc<Store>, target: &RefTarget) -> Result<Option<CommitId>, NodeError> {
    let mut chosen: Option<(i64, CommitId)> = None;
    // A conflict's terms alternate add, remove, add, ...; its sides are the adds.
    for id in target.iter().step_by(2).flatten() {
        let time = store.get_commit(id)?.committer().timestamp.timestamp.0;
        if chosen
            .as_ref()
            .is_none_or(|(best_time, best)| (time, id) > (*best_time, best))
        {
            chosen = Some((time, id.clone()));
        }
    }
    Ok(chosen.map(|(_, id)| id))
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::git_command::git;

    /// What a fix-up records reads back as it was: a commit, a ref that should be absent, and
    /// none, which leaves the ref alone, each told apart.
    #[test]
    fn recorded_expected_values_read_back() {
        let commit = CommitId::from_bytes(&[7; 20]);
        let values: Vec<(GitRefNameBuf, Option<RefTarget>)> = vec![
            (
                "refs/remotes/origin/a".into(),
                Some(RefTarget::normal(commit)),
            ),
            ("refs/remotes/origin/b".into(), Some(RefTarget::absent())),
            ("refs/remotes/origin/c".into(), None),
        ];
        let text = format_expected(&values).unwrap();
        for (name, value) in &values {
            assert_eq!(recorded_in(&text, name), Some(value.clone()), "{name:?}");
        }
        assert_eq!(recorded_in(&text, &"refs/remotes/origin/d".into()), None);
    }

    #[test]
    fn shallow_and_partial_clones_are_incomplete() {
        let dir = tempfile::tempdir().unwrap();
        let run = |args: &[&str]| {
            let output = git(Path::new("git"))
                .current_dir(dir.path())
                .args(args)
                .output()
                .unwrap();
            assert!(output.status.success(), "git {args:?}: {output:?}");
        };
        run(&["init", "--quiet", "--initial-branch=main", "origin"]);
        for n in ["1", "2"] {
            fs::write(dir.path().join("origin/f"), n).unwrap();
            run(&["-C", "origin", "add", "f"]);
            let identity = ["-c", "user.name=t", "-c", "user.email=t@example.com"];
            run(&[
                &identity[..],
                &["-C", "origin", "commit", "--quiet", "-m", n],
            ]
            .concat());
        }
        run(&["-C", "origin", "config", "uploadpack.allowFilter", "true"]);
        // git takes a local path for a local clone, which can be neither shallow nor partial.
        let path = dir
            .path()
            .join("origin")
            .to_string_lossy()
            .replace('\\', "/");
        let url = format!(
            "file://{}{path}",
            if path.starts_with('/') { "" } else { "/" }
        );
        run(&["clone", "--quiet", &url, "full"]);
        run(&["clone", "--quiet", "--depth=1", &url, "shallow"]);
        // Checking files out would need the blobs it left out.
        run(&[
            "clone",
            "--quiet",
            "--no-checkout",
            "--filter=blob:none",
            &url,
            "partial",
        ]);
        let of = |clone: &str| {
            NodeGit {
                repo: GitRepo::new(Path::new("git"), &dir.path().join(clone).join(".git")),
                colocation: None,
                config: ConfigCache::default(),
            }
            .incompleteness()
            .unwrap()
        };
        assert_eq!(of("full"), None);
        assert_eq!(of("shallow"), Some(Incompleteness::Shallow));
        assert_eq!(of("partial"), Some(Incompleteness::Partial));
        // A promisor remote alone, written as git takes a boolean with no value.
        run(&["clone", "--quiet", &url, "promisor"]);
        let config = dir.path().join("promisor/.git/config");
        let text = fs::read_to_string(&config).unwrap();
        fs::write(&config, format!("{text}[remote \"origin\"]\n\tpromisor\n")).unwrap();
        assert_eq!(of("promisor"), Some(Incompleteness::Partial));
    }

    #[test]
    fn remotes_go_as_written_and_as_expanded() {
        let dir = tempfile::tempdir().unwrap();
        let run = |args: &[&str]| {
            let output = git(Path::new("git"))
                .current_dir(dir.path())
                .args(args)
                .output()
                .unwrap();
            assert!(output.status.success(), "git {args:?}: {output:?}");
        };
        run(&["init", "--quiet"]);
        run(&[
            "config",
            "url.https://example.com/.insteadOf",
            "musubi-test:",
        ]);
        run(&[
            "config",
            "url.ssh://example.org/.pushInsteadOf",
            "https://example.org/",
        ]);
        run(&["remote", "add", "aliased", "musubi-test:team/aliased"]);
        let token = "https://bryan:secret@example.net/team/token";
        run(&["remote", "add", "token", token]);
        run(&["remote", "add", "pushes", "https://example.org/team/pushes"]);
        let explicit = "https://example.com/team/explicit";
        run(&["remote", "add", "explicit", explicit]);
        run(&["remote", "set-url", "--push", "explicit", explicit]);
        run(&[
            "config",
            "--add",
            "remote.explicit.pushurl",
            "https://second.example.com/team/explicit",
        ]);
        run(&["remote", "add", "filtered", "musubi-test:team/filtered"]);
        run(&["config", "remote.filtered.partialclonefilter", "blob:none"]);
        let repo = NodeGit {
            repo: GitRepo::new(Path::new("git"), &dir.path().join(".git")),
            colocation: None,
            config: ConfigCache::default(),
        };
        let remotes = repo.remotes().unwrap();
        let urls = |name: &str| {
            let remote = &remotes[name];
            [&remote.url, &remote.expanded_url].map(|url| url.as_deref())
        };
        assert_eq!(
            urls("aliased"),
            [
                Some("musubi-test:team/aliased"),
                Some("https://example.com/team/aliased")
            ]
        );
        assert_eq!(
            urls("token"),
            [Some("https://example.net/team/token"), None]
        );
        assert_eq!(
            urls("pushes"),
            [Some("https://example.org/team/pushes"), None]
        );
        assert_eq!(urls("explicit"), [Some(explicit), None]);
        assert_eq!(
            remotes["explicit"].binding().push,
            [
                "example.com/team/explicit".to_owned(),
                "second.example.com/team/explicit".to_owned()
            ]
            .into()
        );
        assert_eq!(
            urls("filtered"),
            [
                Some("musubi-test:team/filtered"),
                Some("https://example.com/team/filtered")
            ]
        );
        run(&["config", "url.https://tok@example.org/.insteadOf", "tok:"]);
        run(&["remote", "add", "expanded-token", "tok:team/x"]);
        let remote = &repo.remotes().unwrap()["expanded-token"];
        assert_eq!(
            remote.expanded_url.as_deref(),
            Some("https://example.org/team/x")
        );
    }

    /// musubi exports refs to a repository's git repository where jj imports and exports them
    /// in every command: where a workspace is colocated, as jj says. Not to an external git
    /// repository named `.git`, but to the store inside `.jj` once a workspace is a git
    /// worktree of it, and to a `.git` beside `.jj` even if git takes it as bare.
    #[test]
    fn colocated_where_jj_says() {
        let env = musubi_testutil::TestEnv::new();
        let colocated = env.init_repo("colocated");
        // Bare to git, which then sees no working tree, but not to jj.
        let bare = env.init_repo("bare");
        bare.git(&["config", "core.bare", "true"]);
        let internal = env.init_non_colocated_repo("internal");
        let checkout = env.root().join("checkout");
        internal.git(&["init", "--quiet", checkout.to_str().unwrap()]);
        let external = internal.another_copy(&env.root().join("external"));
        internal.jj(&[
            "git",
            "init",
            "--git-repo",
            checkout.join(".git").to_str().unwrap(),
            external.path().to_str().unwrap(),
        ]);
        let worktree = env.init_non_colocated_repo("worktree");
        let linked = env.root().join("linked");
        worktree.jj(&["workspace", "add", "--colocate", linked.to_str().unwrap()]);
        let linked = worktree.another_copy(&linked);
        let colocated_by_jj = |workspace: &musubi_testutil::TestRepo| {
            let status = workspace.jj(&["git", "colocation", "status"]);
            status.contains("is currently colocated")
        };
        let cases = [
            ("colocated", &colocated, vec![&colocated], true),
            ("bare", &bare, vec![&bare], true),
            ("internal", &internal, vec![&internal], false),
            ("external", &external, vec![&external], false),
            ("worktree", &worktree, vec![&worktree, &linked], true),
        ];
        for (case, repo, workspaces, expected) in cases {
            let by_jj = workspaces.into_iter().any(colocated_by_jj);
            assert_eq!(by_jj, expected, "jj, {case}");
            let node = super::super::NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
            assert_eq!(node.colocation().is_some(), expected, "musubi, {case}");
        }
    }
}

#[cfg(test)]
#[path = "git_expected_tests.rs"]
mod expected_tests;

#[cfg(test)]
impl Colocation {
    pub(in crate::node) fn native_expected(&self) -> Expected {
        self.expected.lock().expect("not poisoned").clone()
    }
}
