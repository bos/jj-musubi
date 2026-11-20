//! Records a jj snapshot without importing Git refs or checking out files.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use anyhow::Context as _;
use jj_cli::cli_util::load_fileset_aliases;
use jj_cli::cli_util::load_revset_aliases;
use jj_cli::config::ConfigEnv;
use jj_cli::ui::Ui;
use jj_frontend::workspace_env::WorkspaceEnvironment;
use jj_frontend::workspace_env::WorkspaceEnvironmentDiagnostics;
use jj_lib::backend::CommitId;
use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::default_backend_factories::default_working_copy_factories;
use jj_lib::file_util::FileIdentity;
use jj_lib::fileset;
use jj_lib::fileset::FilesetDiagnostics;
use jj_lib::fsmonitor::FsmonitorSettings;
use jj_lib::git;
use jj_lib::gitignore::GitIgnoreFile;
use jj_lib::local_working_copy::LockedLocalWorkingCopy;
use jj_lib::lock::FileLock;
use jj_lib::matchers::NothingMatcher;
use jj_lib::op_store::RefTarget;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::repo::Repo as _;
use jj_lib::repo_path::RepoPath;
use jj_lib::revset::RevsetExpression;
use jj_lib::settings::HumanByteSize;
use jj_lib::settings::UserSettings;
use jj_lib::working_copy::SnapshotOptions;
use jj_lib::working_copy::WorkingCopyFreshness;
use jj_lib::workspace::DefaultWorkspaceLoaderFactory;
use jj_lib::workspace::WorkspaceLoaderFactory as _;
use pollster::FutureExt as _;

const WATCHMAN_WAIT: Duration = Duration::from_secs(15);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Outcome {
    Changed,
    Unchanged,
    Deferred(&'static str),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ScanKind {
    Incremental,
    Full,
}

/// Opens and scans one registered working copy. Run this on a blocking worker.
pub(crate) fn snapshot(
    repo_path: &Path,
    workspace_root: &Path,
    workspace_name: &WorkspaceName,
    settings: &UserSettings,
    kind: ScanKind,
) -> anyhow::Result<Outcome> {
    let watchman = match FsmonitorSettings::from_settings(settings)? {
        FsmonitorSettings::Watchman(config) if config.register_trigger => {
            return Ok(Outcome::Deferred(
                "jj's Watchman snapshot trigger is enabled",
            ));
        }
        FsmonitorSettings::Watchman(_) => true,
        _ => false,
    };
    if !watchman {
        return snapshot_async(
            repo_path,
            workspace_root,
            workspace_name,
            settings,
            kind,
            false,
        )
        .block_on();
    }

    // The daemon stops polling the copy's runtime before it joins blocking workers.
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    let result = runtime.block_on(snapshot_async(
        repo_path,
        workspace_root,
        workspace_name,
        settings,
        kind,
        true,
    ));
    if !result
        .as_ref()
        .is_err_and(|err| err.is::<tokio::time::error::Elapsed>())
    {
        return result;
    }
    drop(runtime);
    tracing::warn!("snapshot with Watchman timed out; scanning the working copy directly");
    let mut config = settings.config().clone();
    let mut layer = ConfigLayer::empty(ConfigSource::CommandArg);
    layer.set_value("fsmonitor.backend", "none")?;
    config.add_layer(layer);
    let settings = settings.with_new_config(config)?;
    snapshot_async(
        repo_path,
        workspace_root,
        workspace_name,
        &settings,
        ScanKind::Full,
        false,
    )
    .block_on()
}

async fn snapshot_async(
    repo_path: &Path,
    workspace_root: &Path,
    workspace_name: &WorkspaceName,
    settings: &UserSettings,
    kind: ScanKind,
    watchman: bool,
) -> anyhow::Result<Outcome> {
    let repo_path = repo_path.canonicalize()?;
    let workspace_root = workspace_root.canonicalize()?;
    let metadata_dir = workspace_root.join(".jj");
    let paths = [
        (
            &workspace_root,
            FileIdentity::from_symlink_path(&workspace_root)?,
        ),
        (
            &metadata_dir,
            FileIdentity::from_symlink_path(&metadata_dir)?,
        ),
        (&repo_path, FileIdentity::from_symlink_path(&repo_path)?),
    ];
    let workspace = DefaultWorkspaceLoaderFactory.create(&workspace_root)?;
    if !crate::copy::same_directory(workspace.repo_path(), &repo_path) {
        return Ok(Outcome::Deferred("workspace points to another repository"));
    }
    let mut workspace = workspace.load(
        settings,
        &default_backend_factories(),
        &default_working_copy_factories(),
    )?;
    if workspace.workspace_name() != workspace_name {
        return Ok(Outcome::Deferred("workspace name changed"));
    }
    let loader = workspace.repo_loader().clone();
    let ui = Ui::null();
    let env = WorkspaceEnvironment::new(
        &mut WorkspaceEnvironmentDiagnostics::new(),
        &workspace,
        &workspace_root,
        Arc::default(),
        load_fileset_aliases(&ui, settings.config())
            .map_err(|err| anyhow::Error::msg(err.error))?,
        load_revset_aliases(&ui, settings.config()).map_err(|err| anyhow::Error::msg(err.error))?,
    )?;
    let git_backend = git::get_git_backend(loader.store()).ok();
    let (git_repo, _git_lock) = if env.working_copy_shared_with_git() {
        let Some(lock) = FileLock::try_lock(repo_path.join("git_import_export.lock"))? else {
            return Ok(Outcome::Deferred("jj is using the repository"));
        };
        let backend = git_backend.context("opening the workspace's Git repository")?;
        (
            Some(backend.open_git_repo_at_workdir(&workspace_root)?),
            Some(lock),
        )
    } else {
        (None, None)
    };

    let recorded = workspace.working_copy().operation_id().clone();
    let mut working_copy = workspace.start_working_copy_mutation().await?;
    // A rename saves the name and its operation together. If something moved the
    // working copy since we checked its name, retry with the newly recorded identity.
    if working_copy.locked_wc().old_operation_id() != &recorded {
        return Ok(Outcome::Deferred(
            "working copy changed before the snapshot",
        ));
    }
    let op_heads = loader.op_heads_store();
    let heads = op_heads.get_op_heads().await?;
    let [head] = heads.as_slice() else {
        return Ok(Outcome::Deferred(
            "repository has multiple operations at its head",
        ));
    };
    // Loading at head can merge divergent operations. Limit this command to a snapshot
    // based on a current working copy.
    let op = loader.load_operation(head).await?;
    let repo = loader.load_at(&op).await?;
    let Some(commit_id) = repo.view().get_wc_commit_id(workspace_name) else {
        return Ok(Outcome::Deferred("workspace was removed"));
    };
    let commit = repo.store().get_commit_async(commit_id).await?;
    if WorkingCopyFreshness::check_stale(working_copy.locked_wc(), &commit, &repo).await?
        != WorkingCopyFreshness::Fresh
    {
        return Ok(Outcome::Deferred("working copy is stale"));
    }
    let prior_git_head = repo.view().git_head(workspace_name);
    let git_safe = || {
        git_repo
            .as_ref()
            .map_or(Ok(None), |git_repo| git_deferred(git_repo, prior_git_head))
    };
    if let Some(reason) = git_safe()? {
        return Ok(Outcome::Deferred(reason));
    }

    let auto_track = settings.get_string("snapshot.auto-track")?;
    let matcher = fileset::parse(
        &mut FilesetDiagnostics::new(),
        &auto_track,
        &env.fileset_parse_context_for_config(),
    )?
    .to_matcher();
    let HumanByteSize(max_new_file_size) =
        settings.get_value_with("snapshot.max-new-file-size", TryInto::try_into)?;
    let options = SnapshotOptions {
        base_ignores: git_ignores(&workspace_root, git_backend)?,
        progress: None,
        start_tracking_matcher: matcher.as_ref(),
        force_tracking_matcher: &NothingMatcher,
        max_new_file_size: if max_new_file_size == 0 {
            u64::MAX
        } else {
            max_new_file_size
        },
    };
    let locked = working_copy.locked_wc();
    if kind == ScanKind::Full && watchman {
        // A query without a clock makes jj scan the whole tree and supplies a new clock
        // for the next snapshot. Disabling the monitor would discard the shared clock.
        locked
            .downcast_mut::<LockedLocalWorkingCopy>()
            .context("Watchman requires a local-disk working copy")?
            .reset_watchman()?;
    }
    let snapshot = locked.snapshot(&options);
    // This is still before publication. On timeout drop the locked tree state and
    // reopen the workspace for the full scan.
    let (tree, _) = if watchman {
        tokio::time::timeout(WATCHMAN_WAIT, snapshot).await??
    } else {
        snapshot.await?
    };

    let (outcome, snapshot) = if tree.tree_ids_and_labels() == commit.tree().tree_ids_and_labels() {
        (Outcome::Unchanged, None)
    } else {
        let immutable = env
            .resolve_immutable_expression(repo.as_ref(), false)?
            .intersection(&RevsetExpression::commit(commit_id.clone()))
            .evaluate(repo.as_ref())?;
        let mut tx = repo.start_transaction();
        tx.set_is_snapshot(true);
        tx.set_workspace_name(workspace_name);
        let tx_repo = tx.repo_mut();
        let new_commit = if immutable.is_empty().await? {
            tx_repo
                .rewrite_commit(&commit)
                .set_tree(tree)
                .write()
                .await?
        } else {
            tx_repo
                .new_commit(vec![commit_id.clone()], tree)
                .write()
                .await?
        };
        tx_repo.set_wc_commit(workspace_name.to_owned(), new_commit.id().clone())?;
        tx_repo.rebase_descendants().await?;
        let snapshot = tx.write("snapshot working copy").await?.leave_unpublished();
        (Outcome::Changed, Some(snapshot))
    };

    let _heads_lock = op_heads.lock().await?;
    if op_heads.get_op_heads().await? != heads {
        return Ok(Outcome::Deferred("repository changed during the snapshot"));
    }
    if let Some(reason) = git_safe()? {
        return Ok(Outcome::Deferred(reason));
    }
    // The locks protect jj's state, not a directory replaced by a filesystem move.
    // In particular, a replacement can look like an empty linked Git worktree to the scan.
    if paths.iter().any(|(path, expected)| {
        !FileIdentity::from_symlink_path(path)
            .as_ref()
            .is_ok_and(|current| current == expected)
    }) {
        return Ok(Outcome::Deferred(
            "workspace or repository moved during the snapshot",
        ));
    }
    let current = if let Some(snapshot) = &snapshot {
        // As in jj, publish before recording the checkout state. If interrupted after
        // publication, the snapshot is available and jj can recover the stale metadata.
        op_heads
            .update_op_heads(snapshot.operation().parent_ids(), snapshot.op_id())
            .await?;
        snapshot.op_id()
    } else {
        head
    };
    working_copy.finish(current.clone()).await?;
    Ok(outcome)
}

fn git_deferred(
    git_repo: &gix::Repository,
    recorded: &RefTarget,
) -> anyhow::Result<Option<&'static str>> {
    if git_repo.state().is_some() || git_repo.path().join("index.lock").try_exists()? {
        return Ok(Some("Git operation in progress"));
    }
    let head = git_repo
        .head()?
        .try_into_peeled_id()?
        .map(|id| CommitId::from_bytes(id.as_bytes()));
    Ok((recorded.as_resolved() != Some(&head)).then_some("Git HEAD changed"))
}

/// The base ignore files jj applies before reading the working copy's own .gitignore files.
fn git_ignores(
    workspace_root: &Path,
    git_backend: Option<&jj_lib::git_backend::GitBackend>,
) -> anyhow::Result<Arc<GitIgnoreFile>> {
    let excludes_file = |config: &gix::config::File| {
        if let Some(value) = config.string("core.excludesFile") {
            let home = ConfigEnv::from_environment();
            let value = std::str::from_utf8(&value).ok()?;
            return Some(
                workspace_root.join(jj_lib::file_util::expand_home_path(value, home.home_dir())),
            );
        }
        let home = std::env::var_os("XDG_CONFIG_HOME")
            .filter(|value| !value.is_empty())
            .map(PathBuf::from)
            .or_else(|| etcetera::home_dir().ok().map(|path| path.join(".config")))?;
        Some(home.join("git").join("ignore"))
    };
    let mut ignores = GitIgnoreFile::empty();
    let global = if let Some(backend) = git_backend {
        excludes_file(&backend.git_repo().config_snapshot())
    } else {
        gix::config::File::from_globals()
            .ok()
            .and_then(|config| excludes_file(&config))
    };
    if let Some(path) = global {
        ignores = ignores
            .chain_with_file(RepoPath::root(), path.clone())
            .with_context(|| format!("reading Git excludes {}", path.display()))?;
    }
    if let Some(backend) = git_backend {
        ignores = ignores.chain_with_file(
            RepoPath::root(),
            backend.git_repo_path().join("info").join("exclude"),
        )?;
    }
    Ok(ignores)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use jj_cli::config::default_config_layers;
    use musubi_testutil::TestEnv;
    use musubi_testutil::TestRepo;

    use super::*;

    fn snapshot_settings(repo: &TestRepo) -> UserSettings {
        let settings = repo.settings();
        let mut config = settings.config().clone();
        config.extend_layers(default_config_layers());
        settings.with_new_config(config).unwrap()
    }

    #[test]
    fn snapshots_colocated_edits_and_leaves_git_and_idle_history_alone() {
        let env = TestEnv::new();
        let repo = env.init_repo("laptop");
        let settings = snapshot_settings(&repo);
        let scan = || {
            snapshot(
                &repo.repo_path(),
                repo.path(),
                WorkspaceName::new(repo.machine()),
                &settings,
                ScanKind::Full,
            )
            .unwrap()
        };
        let op = || {
            repo.jj(&[
                "--ignore-working-copy",
                "op",
                "log",
                "-n1",
                "--no-graph",
                "-T",
                "id",
            ])
        };
        let dir = repo.path();
        repo.git(&["config", "core.excludesFile", ".git/info/exclude"]);
        repo.write_file(".git/info/exclude", "ignored\n");
        repo.write_file("file", "original\n");
        repo.jj(&["commit", "-m", "add file"]);
        repo.write_file("file", "modified\n");
        repo.jj(&["bookmark", "create", "-r", "@", "topic"]);
        repo.jj(&["commit", "-m", "modify file"]);
        repo.jj(&["status"]);
        let before = op();
        repo.write_file("ignored", "scratch\n");
        assert_eq!(scan(), Outcome::Unchanged);
        assert_eq!(op(), before);

        // A Git ref import here would abandon the second commit and change the file.
        let original = repo.git(&["rev-parse", "topic^"]);
        repo.git(&["update-ref", "refs/heads/topic", original.trim()]);
        repo.write_file("agent", "saved\n");
        assert_eq!(scan(), Outcome::Changed);
        assert_eq!(fs::read_to_string(dir.join("file")).unwrap(), "modified\n");
        assert_eq!(repo.git(&["rev-parse", "topic"]), original);
        assert_eq!(
            repo.jj(&["--ignore-working-copy", "file", "show", "agent"]),
            "saved\n"
        );
        let captured = op();
        assert_ne!(captured, before);
        assert_eq!(scan(), Outcome::Unchanged);
        assert_eq!(op(), captured);

        // Git now puts another commit on disk, without jj having imported the move.
        repo.git(&["checkout", "--detach", original.trim()]);
        assert_eq!(scan(), Outcome::Deferred("Git HEAD changed"));
        assert_eq!(op(), captured);
        assert_eq!(fs::read_to_string(dir.join("file")).unwrap(), "original\n");
        assert_eq!(fs::read_to_string(dir.join("agent")).unwrap(), "saved\n");
    }

    #[test]
    #[cfg(unix)]
    fn replacing_a_workspace_during_a_snapshot_leaves_the_operation_unpublished() {
        use std::thread;
        use std::time::Duration;
        use std::time::Instant;

        let env = TestEnv::new();
        let repo = env.init_repo("laptop");
        repo.write_file("original", "committed\n");
        repo.jj(&["commit", "-m", "start"]);
        let root = env.root().join("secondary");
        repo.jj(&["workspace", "add", root.to_str().unwrap()]);
        let secondary = env.repo_handle_at("laptop", &root);
        secondary.jj(&["status"]);
        secondary.write_file("agent", "saved\n");

        let settings = snapshot_settings(&repo);
        let workspace = DefaultWorkspaceLoaderFactory
            .create(&root)
            .unwrap()
            .load(
                &settings,
                &default_backend_factories(),
                &default_working_copy_factories(),
            )
            .unwrap();
        let repo_path = repo.repo_path();
        let heads = workspace.repo_loader().op_heads_store();
        let before = heads.get_op_heads().block_on().unwrap();
        let operations = repo_path.join("op_store/operations");
        let operation_count = || fs::read_dir(&operations).unwrap().count();
        let count = operation_count();
        let moved = env.root().join("moved");
        thread::scope(|scope| {
            // Stop publication after the scan writes its operation into the shared repo.
            let lock = heads.lock().block_on().unwrap();
            let scan = scope.spawn(|| {
                snapshot(
                    &repo_path,
                    &root,
                    WorkspaceName::new("secondary"),
                    &settings,
                    ScanKind::Full,
                )
            });
            let deadline = Instant::now() + Duration::from_secs(10);
            while operation_count() == count && !scan.is_finished() && Instant::now() < deadline {
                thread::sleep(Duration::from_millis(2));
            }
            if operation_count() == count {
                drop(lock);
                panic!("snapshot did not reach publication: {:?}", scan.join());
            }
            fs::rename(&root, &moved).unwrap();
            fs::create_dir(&root).unwrap();
            drop(lock);
            assert_eq!(
                scan.join().unwrap().unwrap(),
                Outcome::Deferred("workspace or repository moved during the snapshot")
            );
        });
        assert_eq!(heads.get_op_heads().block_on().unwrap(), before);
        assert_eq!(fs::read_to_string(moved.join("agent")).unwrap(), "saved\n");
    }

    #[test]
    fn defers_when_jjs_watchman_snapshot_trigger_is_enabled() {
        let env = TestEnv::new();
        let repo = env.init_repo("laptop");
        let settings = snapshot_settings(&repo);
        let mut config = settings.config().clone();
        config.add_layer(
            ConfigLayer::parse(
                ConfigSource::CommandArg,
                "fsmonitor.backend = 'watchman'\nfsmonitor.watchman.register-snapshot-trigger = true\n",
            )
            .unwrap(),
        );
        let settings = settings.with_new_config(config).unwrap();
        assert_eq!(
            snapshot(
                &repo.repo_path(),
                repo.path(),
                WorkspaceName::new(repo.machine()),
                &settings,
                ScanKind::Full,
            )
            .unwrap(),
            Outcome::Deferred("jj's Watchman snapshot trigger is enabled"),
        );
    }
}
