//! Notices new local operations by watching `.jj/repo/op_heads/heads`, a repository moved by
//! watching where jj records its path, and the daemon's socket deleted by watching its
//! directory.
//!
//! Every jj operation, from any process, ends by adding a file there, so a file added to that
//! directory is the earliest moment a new operation is visible. Notifications are only
//! hints: the daemon also polls, and filesystem events can be dropped or coalesced.

use std::path::Path;

use anyhow::Context as _;
use notify::RecursiveMode;
use notify::Watcher as _;
use tokio::sync::mpsc;

/// A directory watched for changes: files added to it, or one file in it going.
pub struct Watcher {
    _watcher: notify::RecommendedWatcher,
    events: mpsc::UnboundedReceiver<()>,
}

impl Watcher {
    /// Watches for new operations in the repository at `repo_path` (its `.jj/repo`).
    pub fn op_heads(repo_path: &Path) -> anyhow::Result<Self> {
        Self::watch(&repo_path.join("op_heads/heads"), |event| {
            news(event, false)
        })
    }

    /// Watches where jj records the path of the repository whose config lives in
    /// `config_dir` ([`crate::settings::config_id_dir`]). jj rewrites the record the first
    /// time it runs in a repository after a move, which on macOS, whose events follow paths,
    /// the op heads watch, still on the old path, doesn't see. jj writes the record to a
    /// file of its own, then renames it into place, so the rename is news too: the file's
    /// creation may wake the daemon before the record says anything new.
    pub fn moves(config_dir: &Path) -> anyhow::Result<Self> {
        Self::watch(config_dir, move |event| news(event, true))
    }

    /// Watches for the file at `path` going, as a temp cleaner deletes the daemon's socket, by
    /// watching its directory, where other files' events are ignored. The directory going,
    /// removed or moved aside, takes the file with it.
    pub fn removal(path: &Path) -> anyhow::Result<Self> {
        let dir = path.parent().context("a file at the root")?;
        let name = path
            .file_name()
            .context("a path with no file name")?
            .to_owned();
        // As given, and as macOS's FSEvents reports it, with symbolic links resolved.
        let mut dirs = vec![dir.to_owned()];
        dirs.extend(dir.canonicalize().ok().filter(|real| real != dir));
        Self::watch(dir, move |event| gone(event, &dirs, &name))
    }

    fn watch(
        dir: &Path,
        wanted: impl Fn(&notify::Event) -> bool + Send + 'static,
    ) -> anyhow::Result<Self> {
        let (sender, events) = mpsc::unbounded_channel();
        let mut watcher =
            notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
                if event.is_ok_and(|event| wanted(&event)) {
                    // The daemon stopped listening; nothing to notify.
                    sender.send(()).ok();
                }
            })
            .context("creating filesystem watcher")?;
        watcher
            .watch(dir, RecursiveMode::NonRecursive)
            .with_context(|| format!("watching {dir:?}"))?;
        Ok(Self {
            _watcher: watcher,
            events,
        })
    }

    /// Waits for the next change, then swallows any already-queued ones: one look covers
    /// them all.
    pub async fn changed(&mut self) {
        if self.events.recv().await.is_none() {
            std::future::pending::<()>().await;
        }
        while self.events.try_recv().is_ok() {}
    }
}

/// [`Watcher::changed`] for `watcher`, or never, without one.
pub async fn changed(watcher: Option<&mut Watcher>) {
    match watcher {
        Some(watcher) => watcher.changed().await,
        None => std::future::pending().await,
    }
}

/// Whether `event` in a watched directory is news: a file added, or renamed into place if
/// `renames`, that is still there. inotify reports reads too, and every sync reads the
/// directory. Files removed, as jj removes heads an operation replaces, are also what `rm -rf`
/// of the repository looks like, which a sync would race, writing into what it deletes; and
/// macOS's FSEvents reports a file's flags together, so the removal of a file soon after it
/// was added, as when `rm -rf` deletes a head just written, comes as its creation too. A
/// backend that can't say what happened is believed.
fn news(event: &notify::Event, renames: bool) -> bool {
    use notify::EventKind;
    let added = match event.kind {
        EventKind::Create(_) | EventKind::Any | EventKind::Other => true,
        EventKind::Modify(notify::event::ModifyKind::Name(_)) => renames,
        _ => false,
    };
    added && (event.paths.is_empty() || event.paths.iter().any(|path| path.exists()))
}

/// Whether `event` in the watched directory, spelled as in `dirs`, may be the file `name`
/// going: removed, or renamed away, or the directory itself removed or moved aside. The file's
/// name, not its whole path, tells it from the directory's others, since macOS's FSEvents
/// reports paths with symbolic links resolved, as `/private/var` for `/var`. A backend that
/// can't say what happened, or to what, is believed.
fn gone(event: &notify::Event, dirs: &[std::path::PathBuf], name: &std::ffi::OsStr) -> bool {
    use notify::EventKind;
    let removal = matches!(
        event.kind,
        EventKind::Remove(_)
            | EventKind::Modify(notify::event::ModifyKind::Name(_))
            | EventKind::Any
            | EventKind::Other
    );
    removal
        && (event.paths.is_empty()
            || event
                .paths
                .iter()
                .any(|path| path.file_name() == Some(name) || dirs.iter().any(|dir| dir == path)))
}

#[cfg(test)]
mod tests {
    use notify::Event;
    use notify::EventKind;
    use notify::event::CreateKind;
    use notify::event::ModifyKind;
    use notify::event::RemoveKind;
    use notify::event::RenameMode;

    use super::*;

    /// A file added is news while it is there, and not once removed, as FSEvents reports the
    /// removal of a file just added; a removal never is, and a rename only where asked for.
    #[test]
    fn only_files_added_and_still_there_are_news() {
        let dir = tempfile::tempdir().unwrap();
        let here = dir.path().join("here");
        std::fs::write(&here, "").unwrap();
        let gone = dir.path().join("gone");
        let event = |kind, path: &Path| Event::new(kind).add_path(path.to_owned());
        let created = EventKind::Create(CreateKind::File);
        assert!(news(&event(created, &here), false));
        assert!(!news(&event(created, &gone), false));
        assert!(!news(
            &event(EventKind::Remove(RemoveKind::File), &here),
            false
        ));
        let renamed = EventKind::Modify(ModifyKind::Name(RenameMode::To));
        assert!(news(&event(renamed, &here), true));
        assert!(!news(&event(renamed, &here), false));
        assert!(!news(&event(renamed, &gone), true));
        assert!(news(&Event::new(EventKind::Any), false));
    }

    /// The removal of the watched file, or its rename away, may be its going, as may the
    /// directory's own; another file's isn't, nor the file's creation, as the daemon makes its
    /// socket again.
    #[test]
    fn only_the_file_or_its_directory_removed_may_be_gone() {
        let name = std::ffi::OsStr::new("daemon.sock");
        let dirs = [Path::new("/x").to_owned()];
        let event = |kind, path: &str| Event::new(kind).add_path(Path::new("/x").join(path));
        let removed = EventKind::Remove(RemoveKind::Any);
        assert!(gone(&event(removed, "daemon.sock"), &dirs, name));
        assert!(!gone(&event(removed, "daemon.log"), &dirs, name));
        let renamed = EventKind::Modify(ModifyKind::Name(RenameMode::From));
        assert!(gone(&event(renamed, "daemon.sock"), &dirs, name));
        let created = EventKind::Create(CreateKind::Any);
        assert!(!gone(&event(created, "daemon.sock"), &dirs, name));
        assert!(gone(&Event::new(EventKind::Any), &dirs, name));
        let dir = |kind| Event::new(kind).add_path(Path::new("/x").to_owned());
        assert!(gone(
            &dir(EventKind::Remove(RemoveKind::Folder)),
            &dirs,
            name
        ));
        assert!(gone(
            &dir(EventKind::Modify(ModifyKind::Name(RenameMode::Any))),
            &dirs,
            name
        ));
    }

    /// A file deleted in the watched directory is reported, so the daemon notices its socket
    /// gone without waiting for its next look.
    #[tokio::test]
    async fn a_removal_is_reported() {
        let dir = musubi_testutil::tempdir();
        let path = dir.path().join("daemon.sock");
        std::fs::write(&path, "").unwrap();
        let mut watcher = Watcher::removal(&path).unwrap();
        std::fs::write(dir.path().join("daemon.log"), "").unwrap();
        std::fs::remove_file(&path).unwrap();
        tokio::time::timeout(std::time::Duration::from_secs(60), watcher.changed())
            .await
            .expect("no event for the removal");
    }

    /// The directory moved aside, with the socket in it, is reported too.
    ///
    /// Not on Windows: `ReadDirectoryChangesW` reports what happens to the entries of the
    /// watched directory, not to the directory itself, so renaming it away is no event there;
    /// and when the directory is deleted, notify ends the watch without one. The daemon
    /// never relies on it: there its socket is a named pipe, which has no watch
    /// (`watch_socket`) and can't be deleted, so only the periodic look matters.
    #[cfg(not(windows))]
    #[tokio::test]
    async fn a_directory_moved_aside_is_reported() {
        let dir = musubi_testutil::tempdir();
        let path = dir.path().join("daemon.sock");
        std::fs::write(&path, "").unwrap();
        let mut watcher = Watcher::removal(&path).unwrap();
        std::fs::rename(dir.path(), dir.path().with_extension("aside")).unwrap();
        let moved =
            tokio::time::timeout(std::time::Duration::from_secs(60), watcher.changed()).await;
        std::fs::rename(dir.path().with_extension("aside"), dir.path()).unwrap();
        moved.expect("no event for the directory moved aside");
    }
}
