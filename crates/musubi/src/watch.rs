//! Notices new local operations by watching `.jj/repo/op_heads/heads`.
//!
//! Every jj operation, from any process, ends by adding a file there, so a change in that
//! directory is the earliest moment a new operation is visible. Notifications are only
//! hints: the daemon also polls, and filesystem events can be dropped or coalesced.

use std::path::Path;

use anyhow::Context as _;
use notify::RecursiveMode;
use notify::Watcher as _;
use tokio::sync::mpsc;

pub struct OpHeadsWatcher {
    _watcher: notify::RecommendedWatcher,
    events: mpsc::UnboundedReceiver<()>,
}

impl OpHeadsWatcher {
    pub fn new(repo_path: &Path) -> anyhow::Result<Self> {
        let (sender, events) = mpsc::unbounded_channel();
        let mut watcher =
            notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
                if event.is_ok() {
                    // The daemon stopped listening; nothing to notify.
                    sender.send(()).ok();
                }
            })
            .context("creating filesystem watcher")?;
        let heads = repo_path.join("op_heads/heads");
        watcher
            .watch(&heads, RecursiveMode::NonRecursive)
            .with_context(|| format!("watching {heads:?}"))?;
        Ok(Self {
            _watcher: watcher,
            events,
        })
    }

    /// Waits for the next change, then swallows any already-queued ones: one look at the op
    /// heads covers them all.
    pub async fn changed(&mut self) {
        if self.events.recv().await.is_none() {
            std::future::pending::<()>().await;
        }
        while self.events.try_recv().is_ok() {}
    }
}
