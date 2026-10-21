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
    /// The NATS server the hub listens on.
    pub nats_url: String,
    /// Prefix of the NATS subjects for this hive.
    #[serde(default = "default_subject_prefix")]
    pub subject_prefix: String,
    /// This node's name, used in status output.
    pub node: String,
}

pub fn default_subject_prefix() -> String {
    "musubi".to_owned()
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
        let path = dir.join("hive.toml");
        fs::write(&path, toml::to_string(self)?).with_context(|| format!("writing {path:?}"))
    }

    /// The subject the hub serves requests on.
    pub fn rpc_subject(&self) -> String {
        format!("{}.{}.rpc", self.subject_prefix, self.hive)
    }

    /// The subject the hub announces new canonical heads on.
    pub fn head_subject(&self) -> String {
        format!("{}.{}.head", self.subject_prefix, self.hive)
    }

    /// The name to show for the hive.
    pub fn display_name(&self) -> String {
        self.name.clone().unwrap_or_else(|| self.hive.to_string())
    }
}

/// The user's `config.toml`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct UserConfig {
    /// The hub to use when a command isn't given `--nats`: the first one joined.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub nats: Option<String>,
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
}

impl DaemonSettings {
    fn is_default(&self) -> bool {
        *self == Self::default()
    }
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
        // Atomically, so that a reader never sees half of it.
        let dir = path.parent().context("config path has no directory")?;
        let tmp = tempfile::NamedTempFile::new_in(dir)?;
        fs::write(tmp.path(), toml::to_string(self)?)?;
        tmp.persist(&path)
            .map_err(|err| err.error)
            .with_context(|| format!("writing {path:?}"))?;
        Ok(())
    }

    /// Changes the saved config.
    pub fn update(change: impl FnOnce(&mut Self)) -> anyhow::Result<Self> {
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
    pub fn nats(given: Option<&str>) -> anyhow::Result<String> {
        match given {
            Some(url) => Ok(url.to_owned()),
            None => Self::load()?.nats.context(
                "no hub given; pass --nats <url>, the URL `musubi hub` prints (the first join \
                 saves it as the default)",
            ),
        }
    }
}
