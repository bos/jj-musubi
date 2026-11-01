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
                // Only a file added, or renamed into place where that's asked for, is news:
                // inotify reports reads too, and every sync reads the directory; and files
                // removed, as jj removes heads an operation replaces, are also what `rm -rf`
                // of the repository looks like, which a sync would race, writing into what it
                // deletes. A backend that can't say what happened is believed.
                if let Ok(event) = event
                    && (matches!(
                        event.kind,
                        notify::EventKind::Create(_)
                            | notify::EventKind::Any
                            | notify::EventKind::Other
                    ) || renames
                        && matches!(
                            event.kind,
                            notify::EventKind::Modify(notify::event::ModifyKind::Name(_))
                        ))
                {
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
