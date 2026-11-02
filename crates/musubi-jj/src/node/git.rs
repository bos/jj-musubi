//! What a node does only when its backend is git: share the repository's git remotes, and
//! export its refs to `.git` when it is colocated.

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
use crate::hive_settings::Remote;
use crate::hive_settings::repository;
use crate::hive_settings::same_repository;
use crate::objects::GitObjects;
use crate::objects::Incompleteness;
use crate::op_id::LocalOp;
use crate::ref_locks;
use crate::remote_url::without_credentials;

/// A node's git repository, when its backend is git.
pub(super) struct NodeGit {
    repo: GitRepo,
    colocation: Option<Colocation>,
    config: ConfigCache,
}

/// A colocated repository's git repository is a working copy's `.git`, so every `jj`
/// command imports and exports its refs, under jj's lock. musubi exports them too, before an
/// operation it publishes becomes an op head.
pub(super) struct Colocation {
    /// jj's lock on importing and exporting refs.
    lock_path: PathBuf,
    /// The `.git` directory.
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

impl NodeGit {
    /// The git repository of the jj repository whose `.jj/repo` directory is `repo_path` and
    /// whose store is `store`, if its backend is git, with `executable` the git to run there.
    pub fn open(executable: &Path, repo_path: &Path, store: &Store) -> Option<Self> {
        let git_path = jj_lib::git::get_git_backend(store).ok()?.git_repo_path();
        let colocated = git_path.file_name().is_some_and(|name| name == ".git")
            && !git_path.starts_with(repo_path.join("store"));
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

    /// This repository's own git config file.
    pub fn config_path(&self) -> PathBuf {
        self.repo.git_dir().join("config")
    }

    /// The remotes in this repository's own git config, with their URLs as written and,
    /// where this machine's `url.<base>.insteadOf` rules change them, as git expands them,
    /// since another machine needn't have the same rules. Unless `share_credentials`, the
    /// URLs go [without the credentials](without_credentials) an http(s) URL may carry.
    pub fn remotes(&self, share_credentials: bool) -> Result<BTreeMap<String, Remote>, GitError> {
        let config = self.config.read(&self.repo)?;
        let mut remotes: BTreeMap<String, Remote> = BTreeMap::new();
        for entry in config.own() {
            let Some(value) = entry.value.as_deref() else {
                continue;
            };
            let Some((name, variable)) = entry
                .key
                .strip_prefix("remote.")
                .and_then(|rest| rest.rsplit_once('.'))
            else {
                continue;
            };
            let remote = remotes.entry(name.to_owned()).or_default();
            // The first of several, which git fetches from.
            match variable {
                "url" => _ = remote.url.get_or_insert_with(|| value.to_owned()),
                "pushurl" => _ = remote.push_url.get_or_insert_with(|| value.to_owned()),
                _ => {}
            }
        }
        // Each remote's URLs as git uses them: its first URL, followed by a partial clone's
        // filter, then where it pushes. Only a push URL in the config is expanded; where
        // `pushInsteadOf` sends pushes is this machine's own business, as aliases are.
        let mut used: BTreeMap<&str, (Option<&str>, Option<&str>)> = BTreeMap::new();
        for line in config.remotes.lines() {
            let Some((name, url)) = line.split_once('\t') else {
                continue;
            };
            let (fetch, push) = used.entry(name).or_default();
            if let Some(url) = url.strip_suffix(" (push)") {
                push.get_or_insert(url);
            } else if let Some((url, _)) = url.rsplit_once(" (fetch)") {
                fetch.get_or_insert(url);
            }
        }
        let shared = |url: &str| {
            if share_credentials {
                url.to_owned()
            } else {
                without_credentials(url)
            }
        };
        // An expansion only of a URL in this repository's config, and only where it differs
        // as shared.
        let expansion = |written: &Option<String>, used: Option<&str>| {
            let written = written.as_deref()?;
            let used = shared(used?);
            (used != shared(written)).then_some(used)
        };
        for (name, remote) in &mut remotes {
            if let Some(&(fetch, push)) = used.get(name.as_str()) {
                remote.expanded_url = expansion(&remote.url, fetch);
                remote.expanded_push_url = expansion(&remote.push_url, push);
            }
            for url in [&mut remote.url, &mut remote.push_url]
                .into_iter()
                .flatten()
            {
                *url = shared(url);
            }
        }
        Ok(remotes)
    }

    /// How this machine writes a URL another machine wrote as `written` and expanded to
    /// `expanded`: as written where this machine's git expands it to the same repository, so
    /// that an alias they share stays one, even where its rule holds a token, and otherwise
    /// as expanded.
    fn spelling(&self, written: Option<&str>, expanded: Option<&str>) -> Option<String> {
        let (Some(written), Some(expanded)) = (written, expanded) else {
            return written.map(str::to_owned);
        };
        let same = self
            .repo
            .run(&["ls-remote", "--get-url", "--", written], None)
            .is_ok_and(|here| {
                repository(String::from_utf8_lossy(&here).trim_end()) == repository(expanded)
            });
        Some(if same { written } else { expanded }.to_owned())
    }

    /// Changes this repository's git remotes from `from` to `to`, as `git remote` does:
    /// renaming a remote moves its remote-tracking refs, and removing one deletes them.
    pub fn change_remotes(
        &self,
        from: &BTreeMap<String, Remote>,
        to: &BTreeMap<String, Remote>,
    ) -> Result<(), GitError> {
        let mut removed: Vec<&String> = from.keys().filter(|n| !to.contains_key(*n)).collect();
        for (name, remote) in to {
            match from.get(name) {
                Some(old) if old == remote => continue,
                Some(_) => {}
                None => {
                    // The same remote under a new name is a rename.
                    if let Some(position) = removed.iter().position(|old| from[*old] == *remote) {
                        let old = removed.remove(position);
                        self.repo.run(&["remote", "rename", old, name], None)?;
                        continue;
                    }
                    let url = self.spelling(remote.url.as_deref(), remote.expanded_url.as_deref());
                    let given = url.as_deref().unwrap_or_default();
                    self.repo.run(&["remote", "add", "--", name, given], None)?;
                    if url.is_none() {
                        // git adds it with an empty URL; it has none.
                        let key = format!("remote.{name}.url");
                        self.repo
                            .run(&["config", "--local", "--unset-all", &key], None)?;
                    }
                    // Its URL set, only a push URL, if it has one, is still to set: one naming
                    // the URL's repository too, if that is how it was written.
                    let push = self.spelling(
                        remote.push_url.as_deref(),
                        remote.expanded_push_url.as_deref(),
                    );
                    if let Some(push) = push {
                        let key = format!("remote.{name}.pushurl");
                        self.repo.run(&["config", "--local", &key, &push], None)?;
                    }
                    continue;
                }
            }
            self.set_remote_urls(name, from.get(name), remote)?;
        }
        for name in removed {
            self.repo.run(&["remote", "remove", name], None)?;
        }
        Ok(())
    }

    /// Points remote `name`, which `old` describes as this repository has it, where `remote`
    /// says. A URL that already names the repository `remote`'s does is left as this
    /// machine spells it (see [`Remote`]'s equality), and a push URL is removed once it no
    /// longer names where pushes should go.
    fn set_remote_urls(
        &self,
        name: &str,
        old: Option<&Remote>,
        remote: &Remote,
    ) -> Result<(), GitError> {
        let set = |variable: &str, value: Option<&str>| -> Result<(), GitError> {
            let key = format!("remote.{name}.{variable}");
            match value {
                Some(value) => self.repo.run(&["config", "--local", &key, value], None)?,
                // Unsetting a variable that isn't set fails; that's fine.
                None => self
                    .repo
                    .run(&["config", "--local", "--unset-all", &key], None)
                    .unwrap_or_default(),
            };
            Ok(())
        };
        let mut now = old.cloned().unwrap_or_default();
        if old.is_none() || !same_repository(&now.url_repositories(), &remote.url_repositories()) {
            let url = self.spelling(remote.url.as_deref(), remote.expanded_url.as_deref());
            set("url", url.as_deref())?;
            now.url.clone_from(&remote.url);
            now.expanded_url.clone_from(&remote.expanded_url);
        }
        if old.is_none() || !same_repository(&now.push_repositories(), &remote.push_repositories())
        {
            let push = self.spelling(
                remote.push_url.as_deref(),
                remote.expanded_push_url.as_deref(),
            );
            set("pushurl", push.as_deref())?;
        }
        Ok(())
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
        let op = loader.load_operation(&realized.0).block_on()?;
        let repo: Arc<ReadonlyRepo> = loader.load_at(&op).block_on()?;
        let mut tx = repo.start_transaction();
        // Refs that fail to export keep their recorded values, exactly as after a failed
        // export in a local `jj` command; jj's next import reconciles them.
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
        Ok(exported)
    }
}

/// Writes the expected value of each conflicted remote bookmark ([`expected`]) to this
/// machine's `.git`, which jj's export leaves alone. Every `jj` command imports
/// `refs/remotes/<remote>/<name>` and resolves a conflicted remote bookmark to what it finds
/// there, so every machine must find the same, or their imports merge to a value none of them
/// had (docs/internals/races.md, "Remotes"). After concurrent fetches, a machine that made
/// neither fetch still has an older one, and one that made a fetch has its own side. After
/// `jj op restore` of a conflict, the machine that restored it exported nothing for it, so
/// has the value from before the restore, which the others must keep too. So the write
/// compares against what `.git` holds, not jj's record of it, and replaces any value the hive
/// already knows of: a term of the conflict, absent included, or the record. That includes a
/// `git fetch` that happens to match a term; the next fetch after the conflict resolves
/// corrects it. Any other value, absent included, was put there by git since, and the import
/// takes it, as it would without musubi. A ref that can't be read or written is left alone, as
/// jj's export leaves a failed ref (Refs.lean, `exportConflicted`). Nor is a ref written where
/// `.git` holds the value an op head `beside` the realization records and the realization
/// doesn't: that head put it there, as by a fetch, and the merge of the two, exported next and
/// published in the realization's place, can keep it, which a write for the realization alone
/// would undo.
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
        run(&["remote", "add", "filtered", "musubi-test:team/filtered"]);
        run(&["config", "remote.filtered.partialclonefilter", "blob:none"]);
        let repo = NodeGit {
            repo: GitRepo::new(Path::new("git"), &dir.path().join(".git")),
            colocation: None,
            config: ConfigCache::default(),
        };
        let remotes = repo.remotes(false).unwrap();
        let urls = |name: &str| {
            let remote = &remotes[name];
            [
                &remote.url,
                &remote.expanded_url,
                &remote.push_url,
                &remote.expanded_push_url,
            ]
            .map(|url| url.as_deref())
        };
        let aliased = [
            "musubi-test:team/aliased",
            "https://example.com/team/aliased",
        ];
        assert_eq!(
            urls("aliased"),
            [Some(aliased[0]), Some(aliased[1]), None, None]
        );
        let stripped = "https://example.net/team/token";
        assert_eq!(urls("token"), [Some(stripped), None, None, None]);
        // Where pushes go through `pushInsteadOf` is this machine's own business.
        let pushes = "https://example.org/team/pushes";
        assert_eq!(urls("pushes"), [Some(pushes), None, None, None]);
        assert_eq!(
            urls("explicit"),
            [Some(explicit), None, Some(explicit), None]
        );
        let filtered = [
            "musubi-test:team/filtered",
            "https://example.com/team/filtered",
        ];
        assert_eq!(
            urls("filtered"),
            [Some(filtered[0]), Some(filtered[1]), None, None]
        );
        let shared = repo.remotes(true).unwrap();
        assert_eq!(shared["token"].url.as_deref(), Some(token));

        // Another machine's alias is kept where this one expands it the same way.
        let spelling = |written, expanded| repo.spelling(Some(written), Some(expanded));
        assert_eq!(
            spelling(aliased[0], aliased[1]).as_deref(),
            Some(aliased[0])
        );
        let theirs = ["theirs:team/x", "https://example.com/team/x"];
        assert_eq!(spelling(theirs[0], theirs[1]).as_deref(), Some(theirs[1]));
        // An alias whose rule holds a token, which the other machine's expansion lacks.
        run(&["config", "url.https://tok@example.org/.insteadOf", "tok:"]);
        let token = ["tok:team/x", "https://example.org/team/x"];
        assert_eq!(spelling(token[0], token[1]).as_deref(), Some(token[0]));
        // Not git's option, but an alias.
        run(&["config", "url.https://example.com/.insteadOf", "-x:"]);
        assert_eq!(
            spelling("-x:team/x", theirs[1]).as_deref(),
            Some("-x:team/x")
        );
    }
}

#[cfg(test)]
#[path = "git_expected_tests.rs"]
mod expected_tests;
