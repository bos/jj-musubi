//! What a node does only when its backend is git: share the repository's git remotes, and
//! export its refs to `.git` when it is colocated.

use std::collections::BTreeMap;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use gix::refs::transaction::PreviousValue;
use jj_lib::backend::CommitId;
use jj_lib::git::GitExportError;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::lock::FileLock;
use jj_lib::lock::FileLockError;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;
use jj_lib::operation::Operation;
use jj_lib::ref_name::GitRefNameBuf;
use jj_lib::repo::MutableRepo;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::store::Store;
use pollster::FutureExt as _;

use super::NodeError;
use crate::git_command::GitError;
use crate::git_command::GitRepo;
use crate::hive_settings::Remote;
use crate::hive_settings::repository;
use crate::hive_settings::same_repository;
use crate::objects::GitObjects;
use crate::objects::Incompleteness;
use crate::objects::ObjectError;
use crate::remote_url::without_credentials;

/// A node's git repository, when its backend is git.
pub(super) struct NodeGit {
    repo: GitRepo,
    colocation: Option<Colocation>,
}

/// A colocated repository's git repository is a working copy's `.git`, so every `jj`
/// command imports and exports its refs, under jj's lock. musubi exports them too, before an
/// operation it publishes becomes an op head.
pub(super) struct Colocation {
    /// jj's lock on importing and exporting refs.
    lock_path: PathBuf,
}

impl NodeGit {
    /// The git repository of the jj repository whose `.jj/repo` directory is `repo_path` and
    /// whose store is `store`, if its backend is git.
    pub fn open(repo_path: &Path, store: &Store) -> Option<Self> {
        let git_path = jj_lib::git::get_git_backend(store).ok()?.git_repo_path();
        let colocated = git_path.file_name().is_some_and(|name| name == ".git")
            && !git_path.starts_with(repo_path.join("store"));
        Some(Self {
            repo: GitRepo::new(git_path),
            colocation: colocated.then(|| Colocation {
                lock_path: repo_path.join("git_import_export.lock"),
            }),
        })
    }

    pub fn colocation(&self) -> Option<&Colocation> {
        self.colocation.as_ref()
    }

    /// What this repository lacks of its history, if anything.
    pub fn incompleteness(&self) -> Result<Option<Incompleteness>, ObjectError> {
        GitObjects::new(self.repo.git_dir()).incompleteness()
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
        let output = self.repo.run(&["config", "--local", "--list"], None)?;
        let mut remotes: BTreeMap<String, Remote> = BTreeMap::new();
        for line in String::from_utf8_lossy(&output).lines() {
            let Some((key, value)) = line.split_once('=') else {
                continue;
            };
            let Some((name, variable)) = key
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
        let output = self.repo.run(&["remote", "-v"], None)?;
        let output = String::from_utf8_lossy(&output);
        let mut used: BTreeMap<&str, (Option<&str>, Option<&str>)> = BTreeMap::new();
        for line in output.lines() {
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
    fn spelling(
        &self,
        written: Option<&str>,
        expanded: Option<&str>,
    ) -> Result<Option<String>, GitError> {
        let (Some(written), Some(expanded)) = (written, expanded) else {
            return Ok(written.map(str::to_owned));
        };
        let same = self
            .repo
            .run(&["ls-remote", "--get-url", "--", written], None)
            .is_ok_and(|here| {
                repository(String::from_utf8_lossy(&here).trim_end()) == repository(expanded)
            });
        Ok(Some(if same { written } else { expanded }.to_owned()))
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
                    let url =
                        self.spelling(remote.url.as_deref(), remote.expanded_url.as_deref())?;
                    self.repo.run(
                        &["remote", "add", "--", name, &url.unwrap_or_default()],
                        None,
                    )?;
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
            let url = self.spelling(remote.url.as_deref(), remote.expanded_url.as_deref())?;
            set("url", url.as_deref())?;
            now.url.clone_from(&remote.url);
            now.expanded_url.clone_from(&remote.expanded_url);
        }
        if old.is_none() || !same_repository(&now.push_repositories(), &remote.push_repositories())
        {
            let push = self.spelling(
                remote.push_url.as_deref(),
                remote.expanded_push_url.as_deref(),
            )?;
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
    /// updated per-machine fields.
    pub fn export_refs(
        &self,
        loader: &RepoLoader,
        realized: &OperationId,
    ) -> Result<OperationId, NodeError> {
        let op = loader.load_operation(realized).block_on()?;
        let repo: Arc<ReadonlyRepo> = loader.load_at(&op).block_on()?;
        let mut tx = repo.start_transaction();
        // Refs that fail to export keep their recorded values, exactly as after a failed
        // export in a local `jj` command; jj's next import reconciles them.
        let _stats = jj_lib::git::export_refs(tx.repo_mut())?;
        export_conflicted_remote_bookmarks(tx.repo_mut())?;
        let view = tx.repo().view().store_view();
        if view == repo.view().store_view() {
            return Ok(realized.clone());
        }
        let mut store_op = op.store_operation().clone();
        store_op.view_id = loader.op_store().write_view(view).block_on()?;
        let op_store = loader.op_store();
        let exported = op_store.write_operation(&store_op).block_on()?;
        // It refers to the realization's commits, so the realization's index is its index
        // too. Without one, loading the repository there, as merging or the next `jj` command
        // does, would index again every operation since the last one with an index, or for a
        // clone, every commit: none it descends from has one.
        let exported_op = Operation::new(op_store.clone(), exported.clone(), store_op);
        if let Err(err) = loader
            .index_store()
            .write_index(repo.readonly_index().start_modification(), &exported_op)
        {
            // Only a cache: jj indexes it when loading the repository there.
            tracing::warn!("indexing the exported operation: {err}");
        }
        Ok(exported)
    }
}

/// Writes one side of each conflicted remote bookmark to this machine's `.git`, which jj's
/// export leaves alone. Every `jj` command imports `refs/remotes/<remote>/<name>` and resolves
/// a conflicted remote bookmark to what it finds there. On one machine that is its latest
/// fetch, one of the sides. Here a machine that made neither fetch still has an older one,
/// and its import would replicate that, losing both sides (docs/races.md, "Remotes"). Every
/// machine writes the same side, the one committed last (then the greatest commit id), so
/// their imports agree: one machine importing anything else would merge with the others'
/// imports back to an older value. So the write compares against what `.git` holds, not jj's
/// record of it, and replaces any value the hive already knows of: a term of the conflict,
/// absent included, or the record. That includes a `git fetch` that happens to match a term;
/// the next fetch after the conflict resolves corrects it. Any other value, absent included,
/// was put there by git since, and the import takes it, as it would without musubi. A ref
/// that can't be read or written is left alone, as jj's export leaves a failed ref.
fn export_conflicted_remote_bookmarks(mut_repo: &mut MutableRepo) -> Result<(), NodeError> {
    type Terms = Vec<Option<CommitId>>;
    let conflicted: Vec<(GitRefNameBuf, Terms)> = mut_repo
        .view()
        .all_remote_bookmarks()
        .filter(|(symbol, remote_ref)| {
            symbol.remote != REMOTE_NAME_FOR_LOCAL_GIT_REPO
                && symbol.name.as_str() != "HEAD"
                && !remote_ref.target.is_resolved()
        })
        .map(|(symbol, remote_ref)| {
            let name = format!(
                "refs/remotes/{}/{}",
                symbol.remote.as_str(),
                symbol.name.as_str()
            );
            (name.into(), remote_ref.target.iter().cloned().collect())
        })
        .collect();
    if conflicted.is_empty() {
        return Ok(());
    }
    let git_repo = jj_lib::git::get_git_repo(mut_repo.store()).map_err(GitExportError::from)?;
    for (name, terms) in conflicted {
        let mut chosen: Option<(i64, CommitId)> = None;
        // A conflict's terms alternate add, remove, add, ...; its sides are the adds.
        for id in terms.iter().step_by(2).flatten() {
            let time = mut_repo
                .store()
                .get_commit(id)?
                .committer()
                .timestamp
                .timestamp
                .0;
            if chosen
                .as_ref()
                .is_none_or(|(best_time, best)| (time, id) > (*best_time, best))
            {
                chosen = Some((time, id.clone()));
            }
        }
        let Some((_, side)) = chosen else {
            continue;
        };
        let actual = match git_repo.try_find_reference(name.as_str()) {
            Ok(Some(reference)) => match reference.into_fully_peeled_id() {
                Ok(id) => Some(CommitId::from_bytes(id.detach().as_bytes())),
                Err(_) => continue,
            },
            Ok(None) => None,
            Err(_) => continue,
        };
        let recorded = mut_repo.view().get_git_ref(&name);
        let known = terms.contains(&actual)
            || (recorded.is_resolved() && recorded.as_normal() == actual.as_ref());
        if actual.as_ref() != Some(&side) {
            if !known {
                continue;
            }
            let Ok(new) = gix::ObjectId::try_from(side.as_bytes()) else {
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
            if git_repo
                .reference(name.as_str(), new, constraint, "export from musubi")
                .is_err()
            {
                continue;
            }
        }
        if recorded.as_normal() != Some(&side) {
            mut_repo.set_git_ref_target(&name, RefTarget::normal(side));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::git_command::git;

    #[test]
    fn remotes_go_as_written_and_as_expanded() {
        let dir = tempfile::tempdir().unwrap();
        let run = |args: &[&str]| {
            let output = git().current_dir(dir.path()).args(args).output().unwrap();
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
            repo: GitRepo::new(&dir.path().join(".git")),
            colocation: None,
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
        let spelling = |written, expanded| repo.spelling(Some(written), Some(expanded)).unwrap();
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
