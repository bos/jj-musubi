//! A copy doesn't sync while one of its own workspaces has a `/` in its name: other machines'
//! workspaces show here as `beta/x`, so a name of that form is never this machine's own (see
//! "Which workspaces are this machine's own" in docs/internals/design.md).

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt;
use std::path::Path;
use std::path::PathBuf;
use std::sync::PoisonError;
use std::time::SystemTime;

use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::RepoLoader;
use jj_lib::settings::UserSettings;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::view::is_publishable;
use crate::op_id::LocalOp;

/// A repository's own workspaces whose names have a `/`, by name, each with the directory jj's
/// workspace store records for it. Never empty.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlashedWorkspaces {
    dirs: BTreeMap<String, PathBuf>,
}

impl SlashedWorkspaces {
    /// Each workspace's name and directory, by name.
    pub fn workspaces(&self) -> impl Iterator<Item = (&str, &Path)> {
        self.dirs
            .iter()
            .map(|(name, path)| (name.as_str(), path.as_path()))
    }
}

impl fmt::Display for SlashedWorkspaces {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names: Vec<&String> = self.dirs.keys().collect();
        match names.as_slice() {
            [name] => write!(
                f,
                "this repository can't sync while its workspace {name} has a \"/\" in its name"
            ),
            several => write!(
                f,
                "this repository can't sync while its workspaces {} have a \"/\" in their names",
                and_list(several)
            ),
        }
    }
}

/// `items` as a list in words: `a`, `a and b`, `a, b and c`.
fn and_list(items: impl IntoIterator<Item = impl fmt::Display>) -> String {
    let items: Vec<String> = items.into_iter().map(|item| item.to_string()).collect();
    match items.split_last() {
        None => String::new(),
        Some((last, [])) => last.clone(),
        Some((last, rest)) => format!("{} and {last}", rest.join(", ")),
    }
}

/// The own workspaces of the repository whose `.jj/repo` directory is `repo_path` whose names
/// have a `/`, if it has any, read without opening it as a copy, as before it joins a hive.
pub fn slashed_workspaces(
    repo_path: &Path,
    settings: &UserSettings,
) -> Result<Option<SlashedWorkspaces>, NodeError> {
    let loader =
        RepoLoader::init_from_file_system(settings, repo_path, &default_backend_factories())?;
    let heads = loader.op_heads_store().get_op_heads().block_on()?;
    let store = loader.workspace_store();
    slashed_at(
        &loader,
        heads.iter().map(|head| LocalOp(head.clone())),
        |name| store.get_workspace_path(name).ok().flatten(),
    )
}

/// The workspaces in the views of op heads `heads` whose names have a `/` and that jj's
/// workspace store records a directory for, as `recorded` says, whether the directory is there
/// or not, as on a disk not mounted. jj records one from `jj workspace add` on and moves it
/// with `jj workspace rename`. It never records one for another machine's workspace, which has
/// no working copy here. `jj workspace forget` leaves the record, but jj ignores it once the
/// name has left the view, and so does this.
fn slashed_at(
    loader: &RepoLoader,
    heads: impl IntoIterator<Item = LocalOp>,
    recorded: impl Fn(&WorkspaceName) -> Option<PathBuf>,
) -> Result<Option<SlashedWorkspaces>, NodeError> {
    let op_store = loader.op_store();
    let mut found = BTreeMap::new();
    for head in heads {
        let op = op_store.read_operation(&head.0).block_on()?;
        let view = op_store.read_view(&op.view_id).block_on()?;
        for name in view.wc_commit_ids.keys() {
            if is_publishable(name) || found.contains_key(name.as_str()) {
                continue;
            }
            if let Some(path) = recorded(name) {
                found.insert(name.as_str().to_owned(), path);
            }
        }
    }
    Ok((!found.is_empty()).then_some(SlashedWorkspaces { dirs: found }))
}

/// The modification time and length of jj's workspace store's file, which every change to
/// the store rewrites, if it can be read.
pub(super) type StoreStamp = Option<(Option<SystemTime>, u64)>;

/// The directories jj's workspace store recorded for the names asked about, while its file
/// has the same [`StoreStamp`]: each lookup reads and decodes the whole file.
#[derive(Default)]
pub(super) struct Records {
    stamp: StoreStamp,
    paths: HashMap<WorkspaceNameBuf, Option<PathBuf>>,
}

/// What [`NodeRepo::slashed_workspaces`] last found, with the op heads, sorted, it found it at.
pub(super) type SlashedMemo = Option<(Vec<LocalOp>, Option<SlashedWorkspaces>)>;

impl NodeRepo {
    /// The stamp of jj's workspace store's file now.
    fn store_stamp(&self) -> StoreStamp {
        let metadata =
            std::fs::metadata(self.repo_path.join("workspace_store").join("index")).ok()?;
        Some((metadata.modified().ok(), metadata.len()))
    }

    /// The directory jj's workspace store records for `name`, if any, remembered while the
    /// store's file is unchanged.
    fn recorded_directory(&self, name: &WorkspaceName, stamp: &StoreStamp) -> Option<PathBuf> {
        let lookup = || {
            self.loader
                .workspace_store()
                .get_workspace_path(name)
                .ok()
                .flatten()
        };
        if stamp.is_none() {
            return lookup();
        }
        let mut records = self
            .names
            .records
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if records.stamp != *stamp {
            *records = Records {
                stamp: *stamp,
                paths: HashMap::new(),
            };
        }
        records
            .paths
            .entry(name.to_owned())
            .or_insert_with(lookup)
            .clone()
    }

    /// This copy's own workspaces whose names have a `/`, as of its op heads now, if it has
    /// any (`slashed_at`). The same for the same op heads, so worked out once for them. `jj
    /// workspace add` writes an operation with the name in the view before it records the
    /// directory: worked out between the two, the answer misses the workspace until the op
    /// heads change, as they do a moment later, when it writes a second operation, which moves
    /// the workspace to its commit (races.md, "Workspaces").
    pub fn slashed_workspaces(&self) -> Result<Option<SlashedWorkspaces>, NodeError> {
        let mut heads = self.local_heads()?;
        heads.sort();
        let mut memo = self
            .names
            .slashed
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some((at, slashed)) = &*memo
            && *at == heads
        {
            return Ok(slashed.clone());
        }
        let stamp = self.store_stamp();
        let slashed = slashed_at(&self.loader, heads.iter().cloned(), |name| {
            self.recorded_directory(name, &stamp)
        })?;
        *memo = Some((heads, slashed.clone()));
        Ok(slashed)
    }

    /// Refuses to go on while this copy has an own workspace whose name has a `/`
    /// ([`Self::slashed_workspaces`]): nothing is canonicalized, realized beside it or shown
    /// again until it is renamed.
    pub fn refuse_slashed_workspaces(&self) -> Result<(), NodeError> {
        match self.slashed_workspaces()? {
            Some(slashed) => Err(NodeError::SlashedWorkspaces(slashed)),
            None => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use musubi_testutil::TestEnv;

    use super::*;

    /// A workspace with a `/` in its name counts in any op head, as from two `jj` commands at
    /// once, but not once `jj workspace forget` has dropped it from the view, though jj keeps
    /// its directory then.
    #[test]
    fn finds_workspaces_with_a_slash_in_every_op_head() {
        let env = TestEnv::new();
        let repo = env.init_repo("alpha");
        let base = repo.jj(&["op", "log", "--no-graph", "-n1", "-T", "id"]);
        let dir = |name: &str| env.root().join(name);
        let add = |at: &[&str], name: &str, path: &str| {
            let path = dir(path);
            let mut args = at.to_vec();
            args.extend(["workspace", "add", "--name", name, path.to_str().unwrap()]);
            repo.jj(&args);
        };
        add(&[], "a/x", "ax");
        add(&[], "gone/z", "gz");
        repo.jj(&["workspace", "forget", "gone/z"]);
        add(&["--at-op", base.trim()], "b/y", "by");
        let found = slashed_workspaces(&repo.repo_path(), &repo.settings())
            .unwrap()
            .unwrap();
        let found: Vec<(String, PathBuf)> = found
            .workspaces()
            .map(|(name, path)| (name.to_owned(), path.canonicalize().unwrap()))
            .collect();
        assert_eq!(
            found,
            [
                ("a/x".to_owned(), dir("ax").canonicalize().unwrap()),
                ("b/y".to_owned(), dir("by").canonicalize().unwrap()),
            ]
        );
    }

    #[test]
    fn says_which_workspaces_have_a_slash() {
        let some = |names: &[&str]| SlashedWorkspaces {
            dirs: names
                .iter()
                .map(|name| ((*name).to_owned(), PathBuf::from("/x")))
                .collect(),
        };
        assert_eq!(
            some(&["feat/x"]).to_string(),
            "this repository can't sync while its workspace feat/x has a \"/\" in its name"
        );
        assert_eq!(
            some(&["c/z", "a/x", "b/y"]).to_string(),
            "this repository can't sync while its workspaces a/x, b/y and c/z have a \"/\" in \
             their names"
        );
    }
}
