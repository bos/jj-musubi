//! The per-user daemon, syncing every registered copy and optionally snapshotting its workspaces.
//!
//! `process` owns daemon discovery and process lifetime; `server` owns control requests and
//! the worker registry. Each `worker` owns one copy's sync thread, while `status` owns its
//! shared, persisted result. `sync` shares setup with foreground syncs, and `connections`
//! coalesces connections to hubs across copies.

mod connections;
mod process;
mod server;
mod snapshots;
mod status;
mod sync;
mod worker;

pub use process::Running;
#[cfg(windows)]
pub use process::detach;
pub use process::ensure;
pub use process::install;
pub use process::run;
pub use process::running;
pub use process::stop;
pub use process::trim_log;
pub use process::uninstall;
pub use process::unreachable;
pub use status::Status;
pub use status::now;
pub use sync::leave_hive;
pub use sync::leave_reset_hive;
pub use sync::record_reset;
pub use sync::sync_once;

/// Why the daemon syncs nothing for an entry: its path doesn't hold the copy it names, and
/// jj hasn't seen the copy anywhere else.
#[derive(Debug)]
pub struct Suspended(String);

impl std::fmt::Display for Suspended {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "suspended: {}", self.0)
    }
}

impl std::error::Error for Suspended {}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::ffi::OsStr;
    use std::fs;
    use std::path::Path;
    use std::time::Duration;

    use tokio::sync::mpsc;
    use tokio::sync::oneshot;

    use super::process::LOG_LIMIT;
    use super::process::isolate;
    use super::trim_log;
    use super::worker::Command;
    use super::worker::pause;

    /// Backoff expires at its deadline, but a sync or losing the command sender wakes it
    /// early. Time here is Tokio's paused clock, shared with the production wait.
    #[tokio::test(start_paused = true)]
    async fn retry_wait_expires_or_answers_commands() {
        let delay = Duration::from_secs(60);
        let (commands, mut received) = mpsc::unbounded_channel();
        let mut waiting = vec![];
        {
            let wait = pause(delay, &mut received, &mut waiting);
            tokio::pin!(wait);
            assert!(futures::poll!(&mut wait).is_pending());
            tokio::time::advance(delay - Duration::from_millis(1)).await;
            assert!(futures::poll!(&mut wait).is_pending());
            tokio::time::advance(Duration::from_millis(1)).await;
            assert!(matches!(
                futures::poll!(&mut wait),
                std::task::Poll::Ready(false)
            ));
        }
        let now = tokio::time::Instant::now();
        let (reply, mut answer) = oneshot::channel();
        {
            let wait = pause(delay, &mut received, &mut waiting);
            tokio::pin!(wait);
            assert!(futures::poll!(&mut wait).is_pending());
            commands.send(Command::Sync(reply)).unwrap();
            assert!(!wait.await);
        }
        assert_eq!(tokio::time::Instant::now(), now);
        assert_eq!(waiting.len(), 1);
        waiting
            .pop()
            .unwrap()
            .send(Err("retrying".to_owned()))
            .unwrap();
        assert_eq!(answer.try_recv().unwrap().unwrap_err(), "retrying");
        let wait = pause(delay, &mut received, &mut waiting);
        tokio::pin!(wait);
        assert!(futures::poll!(&mut wait).is_pending());
        drop(commands);
        assert!(wait.await);
        assert_eq!(tokio::time::Instant::now(), now);
    }

    /// A large log starts over, in place, so that a daemon launchd started, which writes to
    /// it through its own handle, goes on logging to it.
    #[test]
    fn a_large_log_starts_over_in_place() {
        use std::io::Write as _;
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("daemon.log");
        let mut appending = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .unwrap();
        appending.write_all(b"small\n").unwrap();
        trim_log(&path);
        assert_eq!(fs::metadata(&path).unwrap().len(), 6);
        appending
            .write_all(&vec![b'x'; usize::try_from(LOG_LIMIT).unwrap()])
            .unwrap();
        trim_log(&path);
        appending.write_all(b"after\n").unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "after\n");
    }

    #[test]
    fn a_started_daemon_takes_nothing_of_where_it_was_started() {
        let mut command = std::process::Command::new("musubi");
        isolate(&mut command, Some(Path::new("/state/ssh-agent")));
        let envs: BTreeMap<&OsStr, Option<&OsStr>> = command.get_envs().collect();
        for name in musubi_jj::git_command::REPOSITORY_ENV {
            assert_eq!(envs.get(OsStr::new(name)), Some(&None), "{name}");
        }
        assert_eq!(
            envs.get(OsStr::new("SSH_AUTH_SOCK")),
            Some(&Some(OsStr::new("/state/ssh-agent")))
        );
    }
}
