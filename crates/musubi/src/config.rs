//! What musubi records, and what the user sets.
//!
//! - Each node keeps its hive membership in `.jj/repo/musubi/hive.toml`, beside the
//!   repository it describes, so moving or copying the repository keeps it consistent.
//! - `state.toml` in the user's musubi state directory (see [`state_dir`]) lists the
//!   repositories the daemon serves, and the hub this machine saved as its default. musubi
//!   writes it; it is the source of truth: the daemon reads it when it starts, and commands
//!   that change it tell a running daemon.
//! - What the user sets lives in jj's user config, under `musubi.` (see [`Settings`]).

use std::fs;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use etcetera::BaseStrategy as _;
use jj_lib::config::ConfigGetResultExt as _;
use serde::Deserialize;
use serde::Serialize;
use uuid::Uuid;

/// A node's membership in a hive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiveConfig {
    pub hive: Uuid,
    /// The hive's name as `musubi list` last heard it from the hub, or as it was when this
    /// repository joined, for showing while the hub is out of reach.
    #[serde(default)]
    pub name: Option<String>,
    /// The hub: an ssh destination (see [`crate::ssh`]), or on the hub's machine, its
    /// directory.
    pub hub: String,
    /// This node's name, used in status output.
    pub node: String,
}

impl HiveConfig {
    pub fn path(repo_path: &Path) -> PathBuf {
        repo_path.join("musubi/hive.toml")
    }

    pub fn load(repo_path: &Path) -> anyhow::Result<Option<Self>> {
        let path = Self::path(repo_path);
        match fs::read_to_string(&path) {
            Ok(text) => Ok(Some(
                toml::from_str(&text).with_context(|| format!("{path:?}"))?,
            )),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(err) => Err(err).with_context(|| format!("reading {path:?}")),
        }
    }

    pub fn save(&self, repo_path: &Path) -> anyhow::Result<()> {
        let dir = repo_path.join("musubi");
        fs::create_dir_all(&dir)?;
        write_private(&dir.join("hive.toml"), toml::to_string(self)?.as_bytes())
    }

    /// The subject the hub serves requests on.
    pub fn rpc_subject(&self) -> String {
        musubi_sync::wire::rpc_subject(&self.hive.to_string())
    }

    /// The subject the hub announces new canonical heads on.
    pub fn head_subject(&self) -> String {
        musubi_sync::wire::head_subject(&self.hive.to_string())
    }

    /// The name to show for the hive.
    pub fn display_name(&self) -> String {
        self.name.clone().unwrap_or_else(|| self.hive.to_string())
    }
}

/// What musubi keeps for itself, in `state.toml`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct UserState {
    /// The hub this machine saved as its default: the first one joined, or on the hub's own
    /// machine, that hub.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hub: Option<String>,
    /// The workspace roots of the repositories the daemon serves.
    #[serde(default)]
    pub repos: Vec<PathBuf>,
}

/// What the user sets for musubi in jj's config. These are a machine's, not a repository's,
/// so they come from the user's config alone.
#[derive(Clone, Debug, Default)]
pub struct Settings {
    /// `musubi.hub`: the hub to use when a command isn't given `--hub`, in place of the one
    /// this machine saved.
    pub hub: Option<String>,
    /// `musubi.daemon.log`: what the daemon logs, as a filter in `RUST_LOG`'s syntax;
    /// `--log` and `RUST_LOG` take its place when given.
    pub daemon_log: Option<String>,
    /// `musubi.daemon.socket`: where the daemon's control socket is, in place of the usual
    /// place.
    pub daemon_socket: Option<String>,
}

impl Settings {
    pub fn load() -> anyhow::Result<Self> {
        let config = crate::settings::user_config()?;
        let get = |name: &'static str| config.get::<String>(name).optional();
        Ok(Self {
            hub: get("musubi.hub")?.map(|hub| expand_home(&hub)),
            daemon_log: get("musubi.daemon.log")?,
            daemon_socket: get("musubi.daemon.socket")?,
        })
    }
}

/// A hub's directory written from the home directory, as `~/musubi-hub`, made absolute. An
/// ssh destination never starts so.
fn expand_home(hub: &str) -> String {
    match (hub.strip_prefix("~/"), etcetera::home_dir()) {
        (Some(rest), Ok(home)) => home.join(rest).display().to_string(),
        _ => hub.to_owned(),
    }
}

/// Writes `path` so that only its owner can read it, and so that a reader finds either the
/// old contents or the new ones.
pub fn write_private(path: &Path, contents: &[u8]) -> anyhow::Result<()> {
    // On Unix, readable only by its owner, as the temporary file `replace` writes through is.
    musubi_jj::files::replace(path, contents).with_context(|| format!("writing {path:?}"))
}

/// Where musubi keeps `state.toml`, logs, and locks: `$XDG_STATE_HOME/musubi`
/// (`~/.local/state/musubi`), `%APPDATA%\musubi` on Windows, which has no state directory of
/// its own, or `$MUSUBI_STATE_DIR`.
pub fn state_dir() -> anyhow::Result<PathBuf> {
    if let Some(dir) = std::env::var_os("MUSUBI_STATE_DIR") {
        return Ok(PathBuf::from(dir));
    }
    let strategy = etcetera::choose_base_strategy()
        .context("cannot locate a state directory; set MUSUBI_STATE_DIR")?;
    let base = strategy.state_dir().unwrap_or_else(|| strategy.data_dir());
    Ok(base.join("musubi"))
}

/// Where a daemon started in the background, or at login, logs.
pub fn daemon_log() -> anyhow::Result<PathBuf> {
    Ok(state_dir()?.join("daemon.log"))
}

impl UserState {
    pub fn path() -> anyhow::Result<PathBuf> {
        Ok(state_dir()?.join("state.toml"))
    }

    pub fn load() -> anyhow::Result<Self> {
        let path = Self::path()?;
        match fs::read_to_string(&path) {
            Ok(text) => Ok(toml::from_str(&text).with_context(|| format!("{path:?}"))?),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(Self::default()),
            Err(err) => Err(err).with_context(|| format!("reading {path:?}")),
        }
    }

    fn save(&self) -> anyhow::Result<()> {
        let path = Self::path()?;
        if let Some(dir) = path.parent() {
            fs::create_dir_all(dir)?;
        }
        write_private(&path, toml::to_string(self)?.as_bytes())
    }

    /// Changes the saved state, holding a lock meanwhile so that two commands changing it
    /// at once (two joins, say) don't lose either's change.
    pub fn update(change: impl FnOnce(&mut Self)) -> anyhow::Result<Self> {
        let _lock = crate::lock::lock(&state_dir()?.join("state.lock"))?;
        let mut state = Self::load()?;
        let before = state.clone();
        change(&mut state);
        if state != before {
            state.save()?;
        }
        Ok(state)
    }

    /// Adds a repository workspace root, if not already listed.
    pub fn add_repo(workspace_root: &Path) -> anyhow::Result<()> {
        let root = workspace_root.canonicalize()?;
        Self::update(|state| {
            if !state.repos.contains(&root) {
                state.repos.push(root);
            }
        })?;
        Ok(())
    }

    pub fn remove_repo(workspace_root: &Path) -> anyhow::Result<()> {
        Self::update(|state| state.repos.retain(|repo| repo != workspace_root))?;
        Ok(())
    }

    /// Saves `hub` as this machine's default hub, unless it saved one before. Returns whether
    /// that made it the default, as it does unless `musubi.hub` names another.
    pub fn save_default_hub(hub: &str) -> anyhow::Result<bool> {
        let mut saved = false;
        Self::update(|state| {
            if state.hub.is_none() {
                state.hub = Some(hub.to_owned());
                saved = true;
            }
        })?;
        Ok(saved && Settings::load()?.hub.is_none())
    }

    /// The hub to use when a command isn't given `--hub`: `musubi.hub` in jj's config, or
    /// else the one saved.
    pub fn default_hub(&self) -> anyhow::Result<Option<String>> {
        Ok(Settings::load()?.hub.or_else(|| self.hub.clone()))
    }

    /// The hub to use: `given`, or the default.
    pub fn hub(given: Option<&str>) -> anyhow::Result<String> {
        match given {
            Some(hub) => Ok(crate::hub::absolute(hub)),
            None => Self::load()?.default_hub()?.context(
                "no hub given; pass --hub <host>, as `musubi hub` prints (the first join saves \
                 it as the default, and musubi.hub in jj's config chooses one)",
            ),
        }
    }

    /// Every hub this machine knows of, `default` first, given its copies' hives.
    pub fn known_hubs<'a>(
        default: Option<String>,
        hives: impl IntoIterator<Item = &'a HiveConfig>,
    ) -> Vec<String> {
        let mut hubs: Vec<String> = default.into_iter().collect();
        for hive in hives {
            if !hubs.contains(&hive.hub) {
                hubs.push(hive.hub.clone());
            }
        }
        hubs
    }
}

#[cfg(all(test, unix))]
mod tests {
    use std::os::unix::fs::PermissionsExt as _;

    use super::*;

    #[test]
    fn private_files_are_owner_only() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("state.toml");
        // Replacing a file other users could read leaves one they can't.
        fs::write(&path, "old").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        write_private(&path, b"new").unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "new");
        let mode = fs::metadata(&path).unwrap().permissions().mode();
        assert_eq!(mode & 0o777, 0o600);
    }
}
