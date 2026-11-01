//! Notices new local operations by watching `.jj/repo/op_heads/heads`, and a repository
//! moved by watching where jj records its path.
//!
//! Every jj operation, from any process, ends by adding a file there, so a file added to that
//! directory is the earliest moment a new operation is visible. Notifications are only
//! hints: the daemon also polls, and filesystem events can be dropped or coalesced.

use std::path::Path;

use anyhow::Context as _;
use notify::RecursiveMode;
use notify::Watcher as _;
use tokio::sync::mpsc;

/// A directory watched for files added to it.
pub struct Watcher {
    _watcher: notify::RecommendedWatcher,
    events: mpsc::UnboundedReceiver<()>,
}

impl Watcher {
    /// Watches for new operations in the repository at `repo_path` (its `.jj/repo`).
    pub fn op_heads(repo_path: &Path) -> anyhow::Result<Self> {
        Self::watch(&repo_path.join("op_heads/heads"), false)
    }

    /// Watches where jj records the path of the repository whose config lives in
    /// `config_dir` ([`crate::settings::config_id_dir`]). jj rewrites the record the first
    /// time it runs in a repository after a move, which on macOS, whose events follow paths,
    /// the op heads watch, still on the old path, doesn't see. jj writes the record to a
    /// file of its own, then renames it into place, so the rename is news too: the file's
    /// creation may wake the daemon before the record says anything new.
    pub fn moves(config_dir: &Path) -> anyhow::Result<Self> {
        Self::watch(config_dir, true)
    }

    fn watch(dir: &Path, renames: bool) -> anyhow::Result<Self> {
        let (sender, events) = mpsc::unbounded_channel();
        let mut watcher =
            notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
                if event.is_ok_and(|event| news(&event, renames)) {
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
}
