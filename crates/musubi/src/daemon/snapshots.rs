//! Snapshot scheduling for the local workspaces of one copy. The hub and filesystem
//! notifications can each be unavailable; a local timer still scans the workspaces.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Duration;

use anyhow::Context as _;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::default_backend_factories::default_working_copy_factories;
use jj_lib::ref_name::WorkspaceName;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::settings::UserSettings;
use jj_lib::workspace::DefaultWorkspaceLoaderFactory;
use jj_lib::workspace::Workspace;
use jj_lib::workspace::WorkspaceLoaderFactory as _;
use notify::RecursiveMode;
use notify::Watcher as _;
use tokio::sync::Notify;
use tokio::sync::oneshot;
use tokio::time::Instant;

use super::status::SharedStatus;
use crate::config::Entry;
use crate::config::UserState;
use crate::config::auto_snapshot;
use crate::copy;
use crate::repo::Located;
use crate::snapshot::Outcome;
use crate::snapshot::ScanKind;

const EDIT_DELAY: Duration = Duration::from_secs(5);
const SCAN_INTERVAL: Duration = Duration::from_secs(3 * 60);

pub(super) async fn serve(key: &str, status: &SharedStatus) {
    let mut schedule = Snapshots {
        changed: Arc::default(),
        workspaces: BTreeMap::new(),
        discovery_issues: BTreeMap::new(),
    };
    let mut copy = None;
    let mut rediscover = Instant::now();
    loop {
        if rediscover <= Instant::now() {
            let key = key.to_owned();
            match tokio::task::spawn_blocking(move || discover(&key)).await {
                Ok(Ok(Some(found))) => {
                    if copy.as_ref() != Some(&found.copy) {
                        schedule.workspaces.clear();
                    }
                    copy = Some(found.copy);
                    schedule.update(found.workspaces, found.issues);
                }
                Ok(Ok(None)) => return,
                Ok(Err(err)) => {
                    tracing::debug!("looking for workspaces to snapshot: {err:#}");
                    copy = None;
                    schedule.update(BTreeMap::new(), BTreeMap::new());
                }
                Err(err) => {
                    tracing::warn!("looking for workspaces to snapshot: {err}");
                    copy = None;
                    schedule.update(BTreeMap::new(), BTreeMap::new());
                }
            }
            schedule.report(status);
            rediscover = Instant::now() + SCAN_INTERVAL;
        }

        let next = schedule.next_workspace();
        if let Some((name, deadline)) = next.as_ref()
            && let Some(copy) = &copy
            && *deadline <= Instant::now()
        {
            let copy = copy.clone();
            schedule
                .scan(name, move |root, name, kind| {
                    scan(&copy, &root, &name, kind)
                })
                .await;
            schedule.report(status);
            continue;
        }
        let deadline = next.map_or(rediscover, |(_, deadline)| rediscover.min(deadline));
        tokio::select! {
            () = tokio::time::sleep_until(deadline) => {}
            () = schedule.changed.notified() => {}
        }
    }
}

struct Snapshots {
    changed: Arc<Notify>,
    workspaces: BTreeMap<WorkspaceNameBuf, Watched>,
    discovery_issues: BTreeMap<String, String>,
}

impl Snapshots {
    fn update(
        &mut self,
        paths: BTreeMap<WorkspaceNameBuf, PathBuf>,
        issues: BTreeMap<String, String>,
    ) {
        self.workspaces
            .retain(|name, workspace| paths.get(name) == Some(&workspace.root));
        for (name, root) in paths {
            self.workspaces.entry(name).or_insert_with(|| Watched {
                root,
                timing: Schedule::new(Instant::now()),
                events: Arc::default(),
                watcher: None,
                arming: None,
                rebuild: false,
                issue: None,
            });
        }
        self.discovery_issues = issues;
    }

    fn next_workspace(&mut self) -> Option<(WorkspaceNameBuf, Instant)> {
        self.workspaces
            .iter_mut()
            .map(|(name, workspace)| {
                workspace.install_watch();
                workspace.receive_events();
                (name, workspace.timing.deadline())
            })
            .min_by_key(|(_, deadline)| *deadline)
            .map(|(name, deadline)| (name.clone(), deadline))
    }

    async fn scan(
        &mut self,
        name: &WorkspaceName,
        take_snapshot: impl FnOnce(
            PathBuf,
            WorkspaceNameBuf,
            ScanKind,
        ) -> anyhow::Result<Option<Outcome>>
        + Send
        + 'static,
    ) {
        let Some(workspace) = self.workspaces.get_mut(name) else {
            return;
        };
        let started = Instant::now();
        let (notified, kind) = workspace.timing.begin_scan(started);
        if workspace.watcher.is_none() || workspace.rebuild {
            workspace.arm(&self.changed);
        }
        let root = workspace.root.clone();
        let name_owned = name.to_owned();
        let result =
            tokio::task::spawn_blocking(move || take_snapshot(root, name_owned, kind)).await;
        workspace.timing.scanned(kind, started, Instant::now());
        match result {
            Ok(Ok(Some(Outcome::Changed))) => {
                workspace.issue = None;
                tracing::debug!(workspace = %name.as_str(), "snapshotted working copy");
                if !notified && workspace.watcher.is_some() {
                    workspace.arm(&self.changed);
                }
            }
            Ok(Ok(Some(Outcome::Unchanged))) => workspace.issue = None,
            Ok(Ok(Some(Outcome::Deferred(reason)))) => workspace.issue = Some(reason.to_owned()),
            Ok(Ok(None)) => {
                self.workspaces.remove(name);
            }
            Ok(Err(err)) => {
                tracing::warn!(workspace = %name.as_str(), "couldn't snapshot working copy: {err:#}");
                workspace.issue = Some("couldn't read or record the snapshot".to_owned());
            }
            Err(err) => {
                tracing::warn!(workspace = %name.as_str(), "couldn't snapshot working copy: {err}");
                workspace.issue = Some("snapshot scan stopped unexpectedly".to_owned());
            }
        }
    }

    fn report(&self, status: &SharedStatus) {
        let mut issues = self.discovery_issues.clone();
        issues.extend(self.workspaces.iter().filter_map(|(name, workspace)| {
            Some((name.as_str().to_owned(), workspace.issue.clone()?))
        }));
        status.set_snapshot_issues(issues);
    }
}

struct Watched {
    root: PathBuf,
    timing: Schedule,
    events: Arc<Mutex<Events>>,
    watcher: Option<notify::RecommendedWatcher>,
    arming: Option<oneshot::Receiver<notify::Result<notify::RecommendedWatcher>>>,
    rebuild: bool,
    issue: Option<String>,
}

impl Watched {
    fn receive_events(&mut self) {
        let mut events = self.events.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(event) = events.pending.take() {
            self.timing.notify(event.first);
            self.rebuild |= event.rescan;
        }
        events.armed = self.timing.event_deadline.is_some();
    }

    fn arm(&mut self, changed: &Arc<Notify>) {
        if self.arming.is_some() {
            return;
        }
        let root = self.root.clone();
        let changed = changed.clone();
        let events = self.events.clone();
        let old_watch = self.watcher.take();
        let (sender, receiver) = oneshot::channel();
        drop(tokio::task::spawn_blocking(move || {
            // A crawl to register watches must not hold up the snapshot timer.
            // Drop old registrations before requesting new ones against the same kernel limit.
            drop(old_watch);
            let result = watch(root, changed.clone(), events);
            sender.send(result).ok();
            changed.notify_one();
        }));
        self.arming = Some(receiver);
        self.rebuild = false;
    }

    fn install_watch(&mut self) {
        let Some(arming) = &mut self.arming else {
            return;
        };
        let result = arming.try_recv();
        match result {
            Ok(Ok(watcher)) => self.watcher = Some(watcher),
            Ok(Err(err)) => {
                tracing::debug!(path = %self.root.display(), "couldn't watch files: {err:#}");
                self.rebuild = true;
            }
            Err(oneshot::error::TryRecvError::Empty) => return,
            Err(err @ oneshot::error::TryRecvError::Closed) => {
                tracing::warn!(path = %self.root.display(), "couldn't watch files: {err}");
                self.rebuild = true;
            }
        }
        self.arming = None;
    }
}

struct Schedule {
    event_deadline: Option<Instant>,
    fallback: Instant,
    earliest: Instant,
}

impl Schedule {
    fn new(now: Instant) -> Self {
        Self {
            event_deadline: None,
            fallback: now,
            earliest: now,
        }
    }

    fn notify(&mut self, now: Instant) {
        self.event_deadline.get_or_insert(now + EDIT_DELAY);
    }

    fn deadline(&self) -> Instant {
        self.event_deadline
            .map_or(self.fallback, |deadline| deadline.min(self.fallback))
            .max(self.earliest)
    }

    /// Consume current events before the scan. The watcher can queue another batch during it.
    fn begin_scan(&mut self, now: Instant) -> (bool, ScanKind) {
        let kind = if self.fallback <= now {
            ScanKind::Full
        } else {
            ScanKind::Incremental
        };
        (self.event_deadline.take().is_some(), kind)
    }

    fn scanned(&mut self, kind: ScanKind, started: Instant, finished: Instant) {
        if kind == ScanKind::Full {
            self.fallback = finished + SCAN_INTERVAL;
        }
        // Give foreground work a turn when edits arrive throughout a long scan.
        self.earliest = finished + (finished - started).min(SCAN_INTERVAL);
    }
}

struct EventBatch {
    first: Instant,
    rescan: bool,
}

#[derive(Default)]
struct Events {
    pending: Option<EventBatch>,
    /// A timer already wakes the scheduler. Queue events without waking it again.
    armed: bool,
}

fn watch(
    root: PathBuf,
    changed: Arc<Notify>,
    events: Arc<Mutex<Events>>,
) -> notify::Result<notify::RecommendedWatcher> {
    let watched = root.clone();
    let mut watcher = notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
        let rescan = match event {
            Ok(event) if event.need_rescan() => true,
            Ok(event) if useful(&watched, &event) => rescan_directories(&event),
            Ok(_) => return,
            Err(_) => true,
        };
        let mut events = events.lock().unwrap_or_else(PoisonError::into_inner);
        // One slot per workspace, regardless of how many files a build touches.
        if let Some(batch) = &mut events.pending {
            batch.rescan |= rescan;
        } else {
            events.pending = Some(EventBatch {
                first: Instant::now(),
                rescan,
            });
            if !events.armed {
                changed.notify_one();
            }
        }
    })?;
    watch_tree(&mut watcher, &root)?;
    Ok(watcher)
}

fn useful(root: &Path, event: &notify::Event) -> bool {
    !event.kind.is_access()
        && (event.paths.is_empty()
            || event.paths.iter().any(|path| {
                path.strip_prefix(root).is_ok_and(|relative| {
                    !relative.iter().any(|name| name == ".jj" || name == ".git")
                })
            }))
}

#[cfg(not(target_os = "linux"))]
fn watch_tree(watcher: &mut notify::RecommendedWatcher, root: &Path) -> notify::Result<()> {
    watcher.watch(root, RecursiveMode::Recursive)
}

#[cfg(not(target_os = "linux"))]
fn rescan_directories(_event: &notify::Event) -> bool {
    false
}

#[cfg(target_os = "linux")]
fn rescan_directories(event: &notify::Event) -> bool {
    use notify::EventKind;
    use notify::event::CreateKind;
    use notify::event::ModifyKind;

    matches!(event.kind, EventKind::Create(CreateKind::Folder))
        || matches!(event.kind, EventKind::Modify(ModifyKind::Name(_)))
            && event.paths.iter().any(|path| path.is_dir())
        || event
            .paths
            .iter()
            .any(|path| path.file_name().is_some_and(|name| name == ".gitignore"))
}

/// inotify needs a watch per directory. Avoid large ignored build trees, and bound each
/// workspace's kernel registrations and the amount of work spent finding them. The timer
/// covers edits in portions of the tree without a watch, including tracked files in an
/// ignored directory.
#[cfg(target_os = "linux")]
fn watch_tree(watcher: &mut notify::RecommendedWatcher, root: &Path) -> notify::Result<()> {
    use jj_lib::gitignore::GitIgnoreFile;
    use jj_lib::repo_path::RepoPath;

    const MAX_DIRECTORIES: usize = 2048;
    const MAX_ENTRIES: usize = 50_000;
    let mut dirs = vec![(root.to_owned(), GitIgnoreFile::empty())];
    let mut found = 1;
    let mut budget = MAX_ENTRIES;
    while let Some((dir, parent_ignores)) = dirs.pop() {
        if let Err(err) = watcher.watch(&dir, RecursiveMode::NonRecursive) {
            if dir != root && !dir.exists() {
                continue;
            }
            return Err(err);
        }
        if found >= MAX_DIRECTORIES || budget == 0 {
            continue;
        }
        let Some(relative) = dir.strip_prefix(root).ok().and_then(Path::to_str) else {
            continue;
        };
        let Ok(prefix) = RepoPath::from_internal_string(relative) else {
            continue;
        };
        let ignore_path = dir.join(".gitignore");
        let ignores = if ignore_path
            .symlink_metadata()
            .is_ok_and(|m| m.is_file() && m.len() <= 1024 * 1024)
        {
            parent_ignores
                .chain_with_file(prefix, ignore_path)
                .unwrap_or(parent_ignores)
        } else {
            parent_ignores
        };
        let Ok(entries) = dir.read_dir() else {
            continue;
        };
        for entry in entries.take(budget) {
            budget -= 1;
            let Ok(entry) = entry else { continue };
            let name = entry.file_name();
            if name == ".jj" || name == ".git" || !entry.file_type().is_ok_and(|ty| ty.is_dir()) {
                continue;
            }
            let path = entry.path();
            if path
                .strip_prefix(root)
                .ok()
                .and_then(Path::to_str)
                .and_then(|relative| RepoPath::from_internal_string(relative).ok())
                .is_some_and(|relative| ignores.matches_dir(relative))
                || path.join(".jj").exists()
                || path.join(".git").exists()
            {
                continue;
            }
            dirs.push((path, ignores.clone()));
            found += 1;
            if found >= MAX_DIRECTORIES {
                break;
            }
        }
    }
    Ok(())
}

#[derive(Clone, PartialEq, Eq)]
struct Copy {
    entry: Entry,
    repo_path: PathBuf,
}

struct Inventory {
    copy: Copy,
    workspaces: BTreeMap<WorkspaceNameBuf, PathBuf>,
    issues: BTreeMap<String, String>,
}

fn discover(key: &str) -> anyhow::Result<Option<Inventory>> {
    let state = UserState::load()?;
    let Some(entry) = state.entry(key) else {
        return Ok(None);
    };
    let root = copy::whereabouts(entry).context("the copy is unavailable")?;
    let located = Located::find(&root)?;
    copy::check_owner(&located.repo_path)?;
    let copy = Copy {
        entry: entry.clone(),
        repo_path: located.repo_path.clone(),
    };
    // A broken workspace config mustn't prevent discovery of its siblings.
    let root_settings = crate::settings::load_repo(&located.repo_path)?;
    let primary = load_workspace(&located.workspace_root, &root_settings)?;
    let loader = primary.repo_loader();
    // Reading the views directly allows discovery without merging divergent operation heads.
    let names = crate::block_on(async {
        let mut names = BTreeSet::new();
        for head in loader.op_heads_store().get_op_heads().await? {
            let operation = loader.op_store().read_operation(&head).await?;
            let view = loader.op_store().read_view(&operation.view_id).await?;
            names.extend(view.wc_commit_ids.into_keys());
        }
        Ok(names)
    })?;

    let mut inventory = Inventory {
        copy,
        workspaces: BTreeMap::new(),
        issues: BTreeMap::new(),
    };
    let enabled_by_default = auto_snapshot(&root_settings).unwrap_or(false);
    let mut paths = BTreeMap::new();
    for name in &names {
        let label = name.as_str();
        let path = if name == primary.workspace_name() {
            Some(located.workspace_root.clone())
        } else {
            match loader.workspace_store().get_workspace_path(name) {
                Ok(path) => path,
                Err(err) => {
                    tracing::debug!(workspace = %label, "reading workspace location: {err:#}");
                    if enabled_by_default {
                        inventory.issues.insert(
                            label.to_owned(),
                            "can't read the workspace location".to_owned(),
                        );
                    }
                    continue;
                }
            }
        };
        if let Some(path) = path {
            paths.insert(name.clone(), path);
        }
    }
    // The main workspace and colocated Git worktrees can supply missing or stale paths.
    // Verify jj's workspace identity before using one of these paths.
    let mut candidates = located
        .repo_path
        .parent()
        .and_then(Path::parent)
        .map(Path::to_owned)
        .into_iter()
        .collect::<Vec<_>>();
    if let Ok(backend) = jj_lib::git::get_git_backend(loader.store())
        && let Ok(worktrees) = backend.git_repo().worktrees()
    {
        candidates.extend(worktrees.iter().filter_map(|worktree| worktree.base().ok()));
    }
    for path in candidates {
        if paths.values().any(|known| *known == path) {
            continue;
        }
        let Ok(workspace) = load_workspace(&path, &root_settings) else {
            continue;
        };
        let name = workspace.workspace_name();
        if names.contains(name)
            && copy::same_directory(workspace.repo_path(), &located.repo_path)
            && paths.get(name).is_none_or(|registered| {
                !load_workspace(registered, &root_settings).is_ok_and(|workspace| {
                    workspace.workspace_name() == name
                        && copy::same_directory(workspace.repo_path(), &located.repo_path)
                })
            })
        {
            paths.insert(name.to_owned(), path);
        }
    }
    for (name, path) in paths {
        add_workspace(&mut inventory, &name, &path, enabled_by_default);
    }
    Ok(Some(inventory))
}

fn load_workspace(path: &Path, settings: &UserSettings) -> anyhow::Result<Workspace> {
    Ok(DefaultWorkspaceLoaderFactory.create(path)?.load(
        settings,
        &default_backend_factories(),
        &default_working_copy_factories(),
    )?)
}

fn add_workspace(
    inventory: &mut Inventory,
    name: &WorkspaceName,
    path: &Path,
    enabled_by_default: bool,
) {
    let label = name.as_str();
    match DefaultWorkspaceLoaderFactory.create(path) {
        Ok(loader) if copy::same_directory(loader.repo_path(), &inventory.copy.repo_path) => {
            let root = loader.workspace_root().to_owned();
            match crate::settings::load(&root, &inventory.copy.repo_path)
                .and_then(|s| auto_snapshot(&s))
            {
                Ok(true) => {
                    inventory.workspaces.insert(name.to_owned(), root);
                }
                Ok(false) => {}
                Err(err) => {
                    tracing::warn!(workspace = %label, "reading automatic snapshot setting: {err:#}");
                    inventory.issues.insert(
                        label.to_owned(),
                        "can't read the automatic snapshot setting".to_owned(),
                    );
                    return;
                }
            }
            inventory.issues.remove(label);
        }
        _ if enabled_by_default => {
            inventory.issues.insert(
                label.to_owned(),
                "workspace directory is unavailable".to_owned(),
            );
        }
        _ => {}
    }
}

/// Checks current membership and settings again before a snapshot, since discovery may be
/// several minutes old. The snapshot itself checks the workspace name under jj's lock.
fn scan(
    copy: &Copy,
    root: &Path,
    name: &WorkspaceName,
    kind: ScanKind,
) -> anyhow::Result<Option<Outcome>> {
    let state = UserState::load()?;
    let Some(entry) = state
        .entry(&copy.entry.key)
        .filter(|entry| entry.config_id == copy.entry.config_id && entry.hive == copy.entry.hive)
    else {
        return Ok(None);
    };
    if !copy::whereabouts(entry)
        .and_then(|root| Located::find(&root).ok())
        .is_some_and(|located| copy::same_directory(&located.repo_path, &copy.repo_path))
    {
        return Ok(None);
    }
    copy::check_owner(&copy.repo_path)?;
    let settings = crate::settings::load(root, &copy.repo_path)
        .context("can't read the workspace's settings")?;
    if !auto_snapshot(&settings).context("can't read the automatic snapshot setting")? {
        return Ok(None);
    }
    Ok(Some(crate::snapshot::snapshot(
        &copy.repo_path,
        root,
        name,
        &settings,
        kind,
    )?))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::Snapshots;
    use super::{EDIT_DELAY, SCAN_INTERVAL, Schedule};
    use crate::snapshot::ScanKind;
    use jj_lib::ref_name::WorkspaceNameBuf;
    use tokio::time::Instant;

    #[test]
    fn first_edit_arms_scan_and_silence_cannot_disarm_the_fallback() {
        let started = Instant::now();
        let mut timing = Schedule::new(started);
        assert_eq!(timing.deadline(), started);
        assert_eq!(timing.begin_scan(started), (false, ScanKind::Full));
        timing.scanned(ScanKind::Full, started, started);
        assert_eq!(timing.deadline(), started + SCAN_INTERVAL);

        let first_edit = started + EDIT_DELAY;
        timing.notify(first_edit);
        timing.notify(first_edit + EDIT_DELAY / 2);
        assert_eq!(timing.deadline(), first_edit + EDIT_DELAY);
        assert_eq!(
            timing.begin_scan(first_edit + EDIT_DELAY),
            (true, ScanKind::Incremental)
        );
        let finished = first_edit + EDIT_DELAY * 2;
        timing.scanned(ScanKind::Incremental, first_edit + EDIT_DELAY, finished);

        // The watcher can go silent for good. The next scan needs no event, and an edit
        // just before it cannot defer it by another batch interval.
        let fallback = started + SCAN_INTERVAL;
        assert_eq!(timing.deadline(), fallback);
        timing.notify(fallback - EDIT_DELAY / 2);
        assert_eq!(timing.deadline(), fallback);
        assert_eq!(timing.begin_scan(fallback), (true, ScanKind::Full));
    }

    #[test]
    fn an_edit_during_a_long_scan_schedules_a_later_pass() {
        let started = Instant::now();
        let mut timing = Schedule::new(started);
        let duration = EDIT_DELAY * 3;
        let finished = started + duration;
        timing.scanned(ScanKind::Full, started, finished);
        timing.notify(started + EDIT_DELAY);
        assert_eq!(timing.deadline(), finished + duration);
    }

    /// A real colocated workspace's final edit reaches jj even after losing its watcher.
    #[tokio::test(start_paused = true)]
    async fn scans_and_records_a_final_edit_after_the_watcher_goes_silent() {
        let env = musubi_testutil::TestEnv::new();
        let repo = env.init_repo("work");
        let name = WorkspaceNameBuf::from("work");
        let mut snapshots = Snapshots {
            changed: Default::default(),
            workspaces: BTreeMap::new(),
            discovery_issues: BTreeMap::new(),
        };
        snapshots.update(
            BTreeMap::from([(name.clone(), repo.path().to_owned())]),
            BTreeMap::new(),
        );
        let take_snapshot = || {
            let repo_path = repo.repo_path();
            let settings = repo.settings();
            let mut config = settings.config().clone();
            config.extend_layers(jj_cli::config::default_config_layers());
            let settings = settings.with_new_config(config).unwrap();
            move |root: std::path::PathBuf, name: WorkspaceNameBuf, kind| {
                crate::snapshot::snapshot(&repo_path, &root, &name, &settings, kind).map(Some)
            }
        };
        let head = || repo.jj(&["--ignore-working-copy", "op", "log", "-n1", "-T", "id"]);
        let before = head();
        snapshots.scan(&name, take_snapshot()).await;
        assert_eq!(head(), before, "an idle scan writes no operation");

        let workspace = snapshots.workspaces.get_mut(&name).unwrap();
        workspace.watcher = None;
        if let Some(arming) = workspace.arming.take() {
            drop(arming.await);
        }
        // Leave a watcher installed that can never report an edit. A native watch may
        // finish delivering an old event as it shuts down, so disconnect its slot too.
        workspace.watcher =
            Some(notify::recommended_watcher(|_: notify::Result<notify::Event>| {}).unwrap());
        workspace.events = Default::default();
        repo.write_file("new-directory/file", "the agent's final edit\n");
        let (_, deadline) = snapshots.next_workspace().unwrap();
        assert_eq!(deadline, Instant::now() + SCAN_INTERVAL);
        tokio::time::advance(SCAN_INTERVAL).await;
        let (due, deadline) = snapshots.next_workspace().unwrap();
        assert!(deadline <= Instant::now());
        snapshots.scan(&due, take_snapshot()).await;
        assert!(snapshots.workspaces.get(&name).unwrap().arming.is_some());
        assert_ne!(head(), before);
        assert_eq!(
            repo.jj(&[
                "--ignore-working-copy",
                "file",
                "show",
                "new-directory/file"
            ]),
            "the agent's final edit\n",
        );
    }
}
