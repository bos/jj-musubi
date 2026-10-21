//! jj settings for a repository, loaded exactly as the `jj` CLI loads them.
//!
//! musubi writes operations and, when merging, commits on the user's behalf, so it must use
//! the same identity, hostname, and signing configuration as `jj` itself, including the
//! repo's config and conditional scopes.

use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use jj_cli::config::ConfigEnv;
use jj_cli::config::config_from_environment;
use jj_cli::config::default_config_layers;
use jj_cli::ui::Ui;
use jj_lib::config::ConfigFile;
use jj_lib::config::ConfigSource;
use jj_lib::settings::UserSettings;

/// The jj setting that has the next `jj` command update a working copy another machine left
/// stale (docs/design.md).
const AUTO_UPDATE_STALE: &str = "snapshot.auto-update-stale";

/// Loads settings for the repository at `repo_path` (its `.jj/repo` directory), as seen
/// from the workspace at `workspace_root`.
pub fn load(workspace_root: &Path, repo_path: &Path) -> anyhow::Result<UserSettings> {
    load_layers(repo_path, Some(workspace_root))
}

/// Loads the user's and the repository's config, and the workspace's if given.
fn load_layers(repo_path: &Path, workspace_root: Option<&Path>) -> anyhow::Result<UserSettings> {
    let ui = Ui::null();
    let mut env = ConfigEnv::from_environment();
    let mut raw = config_from_environment(default_config_layers());
    env.reload_user_config(&mut raw)
        .context("loading user config")?;
    env.reset_repo_path(repo_path);
    env.reload_repo_config(&ui, &mut raw)
        .map_err(|err| anyhow::anyhow!("loading repo config: {err:?}"))?;
    if let Some(workspace_root) = workspace_root {
        env.reset_workspace_path(workspace_root);
        env.reload_workspace_config(&ui, &mut raw)
            .map_err(|err| anyhow::anyhow!("loading workspace config: {err:?}"))?;
    }
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

/// Turns on `snapshot.auto-update-stale` in the repository's repo config, unless the user's
/// or the repo's config already has it on. Another machine rewriting this one's
/// working-copy commit leaves it stale, which in a hive is routine, so without it every such
/// rewrite stops the next `jj` command. Every workspace of the repository goes stale that
/// way, so one workspace's own config decides nothing. Returns whether it turned it on.
pub fn enable_auto_update_stale(repo_path: &Path) -> anyhow::Result<bool> {
    if load_layers(repo_path, None)?.get_bool(AUTO_UPDATE_STALE)? {
        return Ok(false);
    }
    let Some(path) = repo_config_path(repo_path)? else {
        return Ok(false);
    };
    let mut file = ConfigFile::load_or_empty(ConfigSource::Repo, &path)
        .with_context(|| format!("loading {}", path.display()))?;
    file.set_value(AUTO_UPDATE_STALE, true)
        .with_context(|| format!("setting {AUTO_UPDATE_STALE} in {}", path.display()))?;
    file.save()
        .with_context(|| format!("saving {}", path.display()))?;
    Ok(true)
}
