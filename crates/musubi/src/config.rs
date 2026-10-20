//! musubi's own configuration.
//!
//! - Each node keeps its hive membership in `.jj/repo/musubi/hive.toml`, beside the
//!   repository it describes, so moving or copying the repository keeps it consistent.
//! - The daemon reads the list of repositories to serve from `config.toml` in the user's
//!   musubi config directory (`$XDG_CONFIG_HOME/musubi` or the platform equivalent).

use std::fs;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use serde::Deserialize;
use serde::Serialize;
use uuid::Uuid;

/// A node's membership in a hive.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiveConfig {
    pub hive: Uuid,
    /// The NATS server the hub listens on.
    pub nats_url: String,
    /// Prefix of the NATS subjects for this hive.
    #[serde(default = "default_subject_prefix")]
    pub subject_prefix: String,
    /// This node's name, used in status output.
    pub node: String,
}

fn default_subject_prefix() -> String {
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
}

/// The repositories the daemon serves.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DaemonConfig {
    #[serde(default)]
    pub repos: Vec<PathBuf>,
}

impl DaemonConfig {
    pub fn path() -> anyhow::Result<PathBuf> {
        if let Some(dir) = std::env::var_os("MUSUBI_CONFIG_DIR") {
            return Ok(PathBuf::from(dir).join("config.toml"));
        }
        let base = std::env::var_os("XDG_CONFIG_HOME")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".config")))
            .context("cannot locate a config directory; set MUSUBI_CONFIG_DIR")?;
        Ok(base.join("musubi/config.toml"))
    }

    pub fn load() -> anyhow::Result<Self> {
        let path = Self::path()?;
        match fs::read_to_string(&path) {
            Ok(text) => Ok(toml::from_str(&text).with_context(|| format!("{path:?}"))?),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(Self::default()),
            Err(err) => Err(err).with_context(|| format!("reading {path:?}")),
        }
    }

    /// Adds a repository workspace root, if not already listed.
    pub fn add_repo(workspace_root: &Path) -> anyhow::Result<()> {
        let path = Self::path()?;
        let mut config = Self::load()?;
        let root = workspace_root.canonicalize()?;
        if !config.repos.contains(&root) {
            config.repos.push(root);
            if let Some(dir) = path.parent() {
                fs::create_dir_all(dir)?;
            }
            fs::write(&path, toml::to_string(&config)?)?;
        }
        Ok(())
    }
}
