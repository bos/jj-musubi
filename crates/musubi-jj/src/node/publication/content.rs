//! Required commit/tree/file closures and exact content sizes, independent of intent policy.
//!
//! Every raw tree side is walked, including directory sides of conflicts. Both command
//! intent and budget accounting use this object-store view of reachable content.

use std::collections::BTreeSet;
use std::collections::HashSet;
use std::path::Path;
use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::backend::FileId;
use jj_lib::backend::SymlinkId;
use jj_lib::backend::TreeId;
use jj_lib::backend::TreeValue;
use jj_lib::repo_path::RepoPathBuf;
use jj_lib::store::Store;
use pollster::FutureExt as _;

use super::NodeError;

#[derive(Default)]
pub(super) struct Closure {
    commits: HashSet<CommitId>,
    trees: HashSet<(RepoPathBuf, TreeId)>,
    files: HashSet<ContentId>,
    versions: BTreeSet<FileVersion>,
}

impl Closure {
    pub(super) fn contains_content(&self, id: &ContentId) -> bool {
        self.files.contains(id)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct FileVersion {
    pub(super) path: RepoPathBuf,
    pub(super) id: ContentId,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum ContentId {
    File(FileId),
    Symlink(SymlinkId),
    Submodule(CommitId),
}

/// Object access used by both intent classification and exact publication accounting.
pub(super) struct ContentGraph<'a> {
    store: &'a Arc<Store>,
    repo_path: &'a Path,
}

impl<'a> ContentGraph<'a> {
    pub(super) fn new(store: &'a Arc<Store>, repo_path: &'a Path) -> Self {
        Self { store, repo_path }
    }

    pub(super) fn commits(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        let mut pending: Vec<_> = roots.into_iter().collect();
        let mut seen = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if seen.insert(id.clone()) {
                pending.extend(self.store.get_commit(&id)?.parent_ids().iter().cloned());
            }
        }
        Ok(seen)
    }

    pub(super) fn extend(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
        into: &mut Closure,
        skip: &Closure,
    ) -> Result<(), NodeError> {
        self.walk(roots, &mut into.commits, &mut into.trees, &[skip], |file| {
            into.files.insert(file.id.clone());
            into.versions.insert(file);
        })
    }

    /// Walks all raw tree sides, including a directory side of a file/directory conflict.
    /// MergedTree::entries deliberately does not descend those directories. Each commit and
    /// path/tree pair outside `skip` is visited once, recording it in the supplied sets.
    fn walk(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
        seen_commits: &mut HashSet<CommitId>,
        seen_trees: &mut HashSet<(RepoPathBuf, TreeId)>,
        skip: &[&Closure],
        mut visit: impl FnMut(FileVersion),
    ) -> Result<(), NodeError> {
        let store = self.store;
        let mut commits: Vec<_> = roots.into_iter().collect();
        while let Some(id) = commits.pop() {
            if skip.iter().any(|known| known.commits.contains(&id))
                || !seen_commits.insert(id.clone())
            {
                continue;
            }
            let commit = store.get_commit(&id)?;
            commits.extend(commit.parent_ids().iter().cloned());
            let mut trees: Vec<_> = commit
                .tree_ids()
                .iter()
                .map(|id| (RepoPathBuf::root(), id.clone()))
                .collect();
            while let Some((path, id)) = trees.pop() {
                let key = (path.clone(), id.clone());
                if skip.iter().any(|known| known.trees.contains(&key)) || !seen_trees.insert(key) {
                    continue;
                }
                let tree = store.get_tree(path.clone(), &id).block_on()?;
                for entry in tree.entries_non_recursive() {
                    let path = path.join(entry.name());
                    let id = match entry.value() {
                        TreeValue::File { id, .. } => ContentId::File(id.clone()),
                        TreeValue::Symlink(id) => ContentId::Symlink(id.clone()),
                        TreeValue::GitSubmodule(id) => ContentId::Submodule(id.clone()),
                        TreeValue::Tree(id) => {
                            trees.push((path, id.clone()));
                            continue;
                        }
                    };
                    visit(FileVersion { path, id });
                }
            }
        }
        Ok(())
    }

    pub(super) fn files(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
        known: &Closure,
        intentional: &Closure,
    ) -> Result<BTreeSet<FileVersion>, NodeError> {
        let mut files = BTreeSet::new();
        self.walk(
            roots,
            &mut HashSet::new(),
            &mut HashSet::new(),
            &[known, intentional],
            |file| {
                if !known.versions.contains(&file) && !intentional.versions.contains(&file) {
                    files.insert(file);
                }
            },
        )?;
        Ok(files)
    }

    pub(super) fn content_bytes(&self, file: &FileVersion) -> Result<u64, NodeError> {
        match &file.id {
            ContentId::File(id) => {
                let mut reader = self.store.read_file(&file.path, id).block_on()?;
                futures::io::copy(&mut reader, &mut futures::io::sink())
                    .block_on()
                    .map_err(|source| NodeError::Io {
                        path: self.repo_path.to_path_buf(),
                        source,
                    })
            }
            ContentId::Symlink(id) => {
                Ok(self.store.read_symlink(&file.path, id).block_on()?.len() as u64)
            }
            ContentId::Submodule(_) => Ok(0),
        }
    }
}
