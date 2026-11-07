//! Locating and opening the repository a command runs in.

use std::io::Write as _;
use std::path::Component;
use std::path::Path;
use std::path::PathBuf;

use std::time::Duration;

use anyhow::Context as _;
use musubi_jj::node::NodeRepo;
use musubi_jj::workspaces::Machine;

use crate::block_on;
use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::UserState;
use crate::control;
use crate::copy;
use crate::daemon;
use crate::settings;
use crate::socket::Socket;
use crate::ui::Ui;

/// A jj workspace and the repository it belongs to.
#[derive(Clone)]
pub struct Located {
    /// The workspace root (the directory containing `.jj`).
    pub workspace_root: PathBuf,
    /// The `.jj/repo` directory, following a secondary workspace's pointer to it.
    pub repo_path: PathBuf,
}

impl Located {
    /// Finds the workspace containing `start`.
    pub fn find(start: &Path) -> anyhow::Result<Self> {
        Self::search(start)?.with_context(|| format!("{start:?} is not in a jj workspace"))
    }

    /// Finds the workspace containing `start`: `None` if no workspace does, and an error if
    /// one does but its repository can't be reached, as when a secondary workspace's main
    /// one has moved.
    pub fn search(start: &Path) -> anyhow::Result<Option<Self>> {
        let start = start.canonicalize()?;
        let Some(workspace_root) = start
            .ancestors()
            .find(|dir| dir.join(".jj").is_dir())
            .map(Path::to_owned)
        else {
            return Ok(None);
        };
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
        // As one line, as jj says it.
        let repo_path = repo_path.canonicalize().map_err(|err| {
            anyhow::anyhow!(
                "can't reach this workspace's repository, {}: {err}",
                lexically_normal(&repo_path).display()
            )
        })?;
        Ok(Some(Self {
            workspace_root,
            repo_path,
        }))
    }

    /// The directory of the workspace the repository was made in, which holds its `.jj/repo`,
    /// from whichever of its workspaces it was found: what the daemon knows a copy by, since
    /// the repository goes with it, where another workspace can be forgotten and deleted. The
    /// workspace found, if the repository's isn't where it should be.
    pub fn repository_root(&self) -> PathBuf {
        let root = self.repo_path.parent().and_then(Path::parent);
        match root {
            Some(root) if copy::same_directory(&root.join(".jj/repo"), &self.repo_path) => {
                root.to_owned()
            }
            _ => self.workspace_root.clone(),
        }
    }

    /// Opens the repository, which must have a machine key: only a join makes one
    /// ([`crate::copy`], R6), and opening makes nothing, a jj config id included.
    pub fn open(&self) -> anyhow::Result<NodeRepo> {
        let settings = settings::load(&self.workspace_root, &self.repo_path)?;
        self.open_with_settings(&settings)
    }

    /// Opens with settings already loaded, keeping a running handle's randomness across
    /// config reloads so that seeded change ids aren't generated again.
    pub fn open_with_settings(
        &self,
        settings: &jj_lib::settings::UserSettings,
    ) -> anyhow::Result<NodeRepo> {
        let machine = NodeRepo::machine_of(&self.repo_path)?
            .context("this repository is not part of a hive")?;
        self.open_as(settings, machine)
    }

    /// Opens the repository as `machine`'s, storing no key, for joining as it.
    pub fn open_as(
        &self,
        settings: &jj_lib::settings::UserSettings,
        machine: Machine,
    ) -> anyhow::Result<NodeRepo> {
        let repo_config = settings::existing_repo_config_path(&self.repo_path)?;
        Ok(NodeRepo::open_as(&self.repo_path, settings, machine)?.with_repo_config(repo_config))
    }
}

/// `path` with its `.`, `..` and trailing `/` taken out by its words alone, without looking at
/// what is there, as for a path that doesn't exist.
pub fn lexically_normal(path: &Path) -> PathBuf {
    let mut normal = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir
                if matches!(normal.components().next_back(), Some(Component::Normal(_))) =>
            {
                normal.pop();
            }
            component => normal.push(component),
        }
    }
    normal
}

/// The repository at `start`, its record and its entry, if it is the copy of its key here
/// ([`copy`]); else fails, saying what it is. A copy whose entry is at a path that no longer
/// holds it moved here: its entry follows it, and the daemon serves it here.
pub fn the_copy(
    ui: &Ui,
    start: &Path,
    socket: &Socket,
) -> anyhow::Result<(Located, HiveConfig, Entry)> {
    let located = Located::find(start)?;
    copy::check_owner(&located.repo_path)?;
    let found = copy::Found::resolve(&located)?;
    let state = UserState::load()?;
    let entry = found.key.as_deref().and_then(|key| state.entry(key));
    let standing = copy::standing_of(&located, &found, entry);
    let (copy::Standing::Copy, Some(record), Some(entry)) = (standing, &found.record, entry) else {
        anyhow::bail!(
            "{}",
            copy::not_the_copy(standing, found.record.as_ref(), entry)
        );
    };
    let entry = follow_move(ui, &located, entry, socket)?;
    Ok((located, record.clone(), entry))
}

/// Moves `entry` to `located`, the copy it names, if its path no longer holds it, and has
/// the daemon serve it there. Returns the entry as it is now.
pub fn follow_move(
    ui: &Ui,
    located: &Located,
    entry: &Entry,
    socket: &Socket,
) -> anyhow::Result<Entry> {
    let root = located.repository_root();
    if entry.path == root || copy::holds(entry, &entry.path) {
        return Ok(entry.clone());
    }
    let moved = Entry {
        path: root,
        ..entry.clone()
    };
    // Unless the daemon, or another command, changed it first, which may have made another
    // repository the copy.
    anyhow::ensure!(
        UserState::move_entry(entry, moved.path.clone())?,
        "this machine's record of this repository changed meanwhile; run the command again"
    );
    // Not with what the command prints, as `musubi list -T` prints only its lines.
    writeln!(
        ui.stderr(),
        "This repository moved here from {}; it syncs from here now",
        entry.path.display()
    )?;
    // The daemon starts serving it here at once, and syncs in its own time: the command
    // needn't wait for that.
    block_on(async {
        if let Some(client) = daemon::running(socket).await? {
            client
                .add(control::context(Duration::from_secs(2)), moved.key.clone())
                .await
                .ok();
        }
        Ok::<_, anyhow::Error>(())
    })?;
    Ok(moved)
}
