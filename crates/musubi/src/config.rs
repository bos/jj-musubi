//! musubi's own configuration.
//!
//! - Each node keeps its hive membership in `.jj/repo/musubi/hive.toml`, beside the
//!   repository it describes, so moving or copying the repository keeps it consistent.
//! - `config.toml` in the user's musubi config directory (`$XDG_CONFIG_HOME/musubi`, or
//!   `%APPDATA%\musubi` on Windows, or `$MUSUBI_CONFIG_DIR`) lists the repositories the
//!   daemon serves, and holds the user's default hub and daemon settings. It is the source
//!   of truth: the daemon reads it when it starts, and commands that change it tell a
//!   running daemon.

use std::fs;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use etcetera::BaseStrategy as _;
use serde::Deserialize;
use serde::Serialize;
use uuid::Uuid;

/// A node's membership in a hive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiveConfig {
    pub hive: Uuid,
    /// The hive's name when this repository joined, for showing while the hub is out of
    /// reach.
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

/// The user's `config.toml`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct UserConfig {
    /// The hub to use when a command isn't given `--hub`: the first one joined, or on the
    /// hub's own machine, that hub.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hub: Option<String>,
    #[serde(default, skip_serializing_if = "DaemonSettings::is_default")]
    pub daemon: DaemonSettings,
    /// The workspace roots of the repositories the daemon serves.
    #[serde(default)]
    pub repos: Vec<PathBuf>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DaemonSettings {
    /// Where the daemon's control socket is, in place of the usual place.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub socket: Option<String>,
    /// What the daemon logs, as a filter in `RUST_LOG`'s syntax; `--log` and `RUST_LOG`
    /// take its place when given.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub log: Option<String>,
}

impl DaemonSettings {
    fn is_default(&self) -> bool {
        *self == Self::default()
    }
}

/// Writes `path` so that only its owner can read it, and so that a reader finds either the
/// old contents or the new ones.
pub fn write_private(path: &Path, contents: &[u8]) -> anyhow::Result<()> {
    // On Unix, readable only by its owner, as the temporary file `replace` writes through is.
    musubi_jj::files::replace(path, contents).with_context(|| format!("writing {path:?}"))
}

/// The user's musubi config directory.
pub fn config_dir() -> anyhow::Result<PathBuf> {
    if let Some(dir) = std::env::var_os("MUSUBI_CONFIG_DIR") {
        return Ok(PathBuf::from(dir));
    }
    // Where jj keeps its own: `$XDG_CONFIG_HOME` or `~/.config` on Unix and macOS,
    // `%APPDATA%` on Windows.
    let base = etcetera::choose_base_strategy()
        .map(|strategy| strategy.config_dir())
        .context("cannot locate a config directory; set MUSUBI_CONFIG_DIR")?;
    Ok(base.join("musubi"))
}

/// Where musubi keeps logs and locks: `$XDG_STATE_HOME/musubi` (`~/.local/state/musubi`),
/// `%LOCALAPPDATA%\musubi` on Windows, or `$MUSUBI_CONFIG_DIR`.
pub fn state_dir() -> anyhow::Result<PathBuf> {
    if let Some(dir) = std::env::var_os("MUSUBI_CONFIG_DIR") {
        return Ok(PathBuf::from(dir));
    }
    let strategy = etcetera::choose_base_strategy()
        .context("cannot locate a state directory; set MUSUBI_CONFIG_DIR")?;
    let base = strategy.state_dir().unwrap_or_else(|| strategy.data_dir());
    Ok(base.join("musubi"))
}

/// Where a daemon started in the background, or at login, logs.
pub fn daemon_log() -> anyhow::Result<PathBuf> {
    Ok(state_dir()?.join("daemon.log"))
}

impl UserConfig {
    pub fn path() -> anyhow::Result<PathBuf> {
        Ok(config_dir()?.join("config.toml"))
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

    /// Changes the saved config, holding a lock meanwhile so that two commands changing it
    /// at once (two joins, say) don't lose either's change.
    pub fn update(change: impl FnOnce(&mut Self)) -> anyhow::Result<Self> {
        let _lock = crate::lock::lock(&config_dir()?.join("config.lock"))?;
        let mut config = Self::load()?;
        let before = config.clone();
        change(&mut config);
        if config != before {
            config.save()?;
        }
        Ok(config)
    }

    /// Adds a repository workspace root, if not already listed.
    pub fn add_repo(workspace_root: &Path) -> anyhow::Result<()> {
        let root = workspace_root.canonicalize()?;
        Self::update(|config| {
            if !config.repos.contains(&root) {
                config.repos.push(root);
            }
        })?;
        Ok(())
    }

    pub fn remove_repo(workspace_root: &Path) -> anyhow::Result<()> {
        Self::update(|config| config.repos.retain(|repo| repo != workspace_root))?;
        Ok(())
    }

    /// The hub to use: `given`, or the saved default.
    pub fn hub(given: Option<&str>) -> anyhow::Result<String> {
        match given {
            Some(hub) => Ok(crate::hub::absolute(hub)),
            None => Self::load()?.hub.context(
                "no hub given; pass --hub <host>, as `musubi hub` prints (the first join saves \
                 it as the default)",
            ),
        }
    }
}

#[cfg(all(test, unix))]
mod tests {
    use std::os::unix::fs::PermissionsExt as _;

    use super::*;

    #[test]
    fn private_files_are_owner_only() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("config.toml");
        // Replacing a file other users could read leaves one they can't.
        fs::write(&path, "old").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        write_private(&path, b"new").unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "new");
        let mode = fs::metadata(&path).unwrap().permissions().mode();
        assert_eq!(mode & 0o777, 0o600);
    }
}
