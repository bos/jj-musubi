//! jj settings for a repository, loaded exactly as the `jj` CLI loads them.
//!
//! musubi writes operations and, when merging, commits on the user's behalf, so it must use
//! the same identity, hostname, and signing configuration as `jj` itself, including the
//! repo's config and conditional scopes.

use std::path::Path;

use anyhow::Context as _;
use jj_cli::config::ConfigEnv;
use jj_cli::config::config_from_environment;
use jj_cli::config::default_config_layers;
use jj_cli::ui::Ui;
use jj_lib::settings::UserSettings;

/// Loads settings for the repository at `repo_path` (its `.jj/repo` directory), as seen
/// from the workspace at `workspace_root`.
pub fn load(workspace_root: &Path, repo_path: &Path) -> anyhow::Result<UserSettings> {
    let ui = Ui::null();
    let mut env = ConfigEnv::from_environment();
    let mut raw = config_from_environment(default_config_layers());
    env.reload_user_config(&mut raw)
        .context("loading user config")?;
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
