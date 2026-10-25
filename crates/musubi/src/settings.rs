//! jj settings, loaded exactly as the `jj` CLI loads them.
//!
//! musubi writes operations and, when merging, commits on the user's behalf, so it must use
//! the same identity, hostname, and signing configuration as `jj` itself, including the
//! repo's config and conditional scopes. Its own settings live in jj's config too, under
//! `musubi.` (see [`crate::config::Settings`]).

use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use jj_cli::config::ConfigEnv;
use jj_cli::config::RawConfig;
use jj_cli::config::config_from_environment;
use jj_cli::config::default_config_layers;
use jj_cli::ui::Ui;
use jj_lib::config::StackedConfig;
use jj_lib::settings::UserSettings;

/// jj's config outside any repository: its defaults, the system's and the user's config, and
/// what the environment sets.
fn base() -> anyhow::Result<(ConfigEnv, RawConfig)> {
    let env = ConfigEnv::from_environment();
    let mut raw = config_from_environment(default_config_layers());
    env.reload_system_config(&mut raw)
        .context("loading system config")?;
    env.reload_user_config(&mut raw)
        .context("loading user config")?;
    Ok((env, raw))
}

/// jj's config as `jj` sees it outside any repository, where musubi reads the settings that
/// are a machine's rather than a repository's.
pub fn user_config() -> anyhow::Result<StackedConfig> {
    let (env, raw) = base()?;
    env.resolve_config(&raw).context("resolving config")
}

/// Loads settings for the repository at `repo_path` (its `.jj/repo` directory), as seen
/// from the workspace at `workspace_root`: the system's and the user's config, the
/// repository's, and the workspace's.
pub fn load(workspace_root: &Path, repo_path: &Path) -> anyhow::Result<UserSettings> {
    let ui = Ui::null();
    let (mut env, mut raw) = base()?;
    env.reset_repo_path(repo_path);
    env.reload_repo_config(&ui, &mut raw)
        .map_err(|err| anyhow::anyhow!("loading repo config: {err:?}"))?;
    env.reset_workspace_path(workspace_root);
    env.reload_workspace_config(&ui, &mut raw)
        .map_err(|err| anyhow::anyhow!("loading workspace config: {err:?}"))?;
    let config = env.resolve_config(&raw).context("resolving config")?;
    UserSettings::from_config_and_home_dir(config, env.home_dir().map(ToOwned::to_owned))
        .context("reading settings")
}

/// jj's repo config file for the repository at `repo_path`, where jj keeps it, outside the
/// repository. Like `jj config set --repo`, gives the repository a config id if it has none.
pub fn repo_config_path(repo_path: &Path) -> anyhow::Result<Option<PathBuf>> {
    let ui = Ui::null();
    let mut env = ConfigEnv::from_environment();
    env.reset_repo_path(repo_path);
    env.repo_config_path(&ui)
        .map_err(|err| anyhow::anyhow!("finding the repo config: {err:?}"))
}

/// [`repo_config_path`], but `None` for a repository without a config id, which only joining
/// gives it.
pub fn existing_repo_config_path(repo_path: &Path) -> anyhow::Result<Option<PathBuf>> {
    if !repo_path.join("config-id").exists() {
        return Ok(None);
    }
    repo_config_path(repo_path)
}

/// The `.jj/repo` directory jj last saw the repository with `config_id` at: jj records it
/// for each repository it opens, under the user's jj config directory, and when it finds a
/// repository moved, records where it went.
pub fn path_of_config_id(config_id: &str) -> Option<PathBuf> {
    let dir = ConfigEnv::from_environment()
        .repo_configs_root_dir()?
        .join(config_id);
    let metadata = jj_lib::secure_config::read_metadata(&dir).ok()?;
    Some(
        jj_lib::secure_config::metadata_path(&metadata)
            .ok()??
            .to_owned(),
    )
}
