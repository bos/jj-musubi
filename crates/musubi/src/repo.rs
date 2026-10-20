//! Locating and opening the repository a command runs in.

use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use musubi_jj::node::NodeRepo;

use crate::settings;

/// A jj workspace and the repository it belongs to.
pub struct Located {
    /// The workspace root (the directory containing `.jj`).
    pub workspace_root: PathBuf,
    /// The `.jj/repo` directory, following a secondary workspace's pointer to it.
    pub repo_path: PathBuf,
}

impl Located {
    /// Finds the workspace containing `start`.
    pub fn find(start: &Path) -> anyhow::Result<Self> {
        let start = start.canonicalize()?;
        let workspace_root = start
            .ancestors()
            .find(|dir| dir.join(".jj").is_dir())
            .with_context(|| format!("{start:?} is not in a jj workspace"))?
            .to_owned();
        let repo = workspace_root.join(".jj/repo");
        // A secondary workspace's `.jj/repo` is a file holding the repository's path.
        let repo_path = if repo.is_file() {
            let target = PathBuf::from(std::fs::read_to_string(&repo)?.trim());
            if target.is_absolute() {
                target
            } else {
                workspace_root.join(".jj").join(target)
            }
        } else {
            repo
        };
        Ok(Self {
            workspace_root,
            repo_path: repo_path.canonicalize()?,
        })
    }

    pub fn open(&self) -> anyhow::Result<NodeRepo> {
        let settings = settings::load(&self.workspace_root, &self.repo_path)?;
        Ok(NodeRepo::open(&self.repo_path, &settings)?)
    }
}
