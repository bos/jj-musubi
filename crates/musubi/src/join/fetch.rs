//! A best-effort upstream fetch must not keep an otherwise completed join waiting forever.

use std::io;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::time::Duration;

use process_wrap::tokio::ChildWrapper;
use process_wrap::tokio::CommandWrap;
use process_wrap::tokio::KillOnDrop;
use tokio::sync::Notify;

type Active = Arc<Mutex<Option<Arc<Notify>>>>;
static INTERRUPTS: OnceLock<Result<Active, ctrlc::Error>> = OnceLock::new();

/// Tokio leaves its signal handler installed after a short-lived runtime ends. Keep a
/// process-wide handler for this command instead: cancel and reap the active fetch, then
/// retain ordinary interruption behavior during the rest of the join (notably its sync).
struct Cancellation {
    active: Active,
    notify: Arc<Notify>,
}

impl Cancellation {
    fn register() -> io::Result<Self> {
        let active = INTERRUPTS
            .get_or_init(|| {
                let active: Active = Arc::default();
                let signal = active.clone();
                ctrlc::set_handler(move || {
                    let active = signal
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                    if let Some(notify) = &*active {
                        // Repeated interrupts must not exit before the first one's cleanup.
                        notify.notify_one();
                    } else {
                        std::process::exit(130);
                    }
                })?;
                Ok(active)
            })
            .as_ref()
            .map_err(|err| io::Error::other(err.to_string()))?
            .clone();
        let notify = Arc::new(Notify::new());
        let mut slot = active
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if slot.is_some() {
            return Err(io::Error::other(
                "an automatic upstream fetch is already running",
            ));
        }
        *slot = Some(notify.clone());
        drop(slot);
        Ok(Self { active, notify })
    }
}

impl Drop for Cancellation {
    fn drop(&mut self) {
        self.active
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take();
    }
}

/// Keep jj and its Git/SSH descendants together, including when a wait is interrupted.
struct FetchChild {
    child: Box<dyn ChildWrapper>,
    running: bool,
}

impl Drop for FetchChild {
    fn drop(&mut self) {
        if self.running {
            self.child.start_kill().ok();
        }
    }
}

/// Fetch without interactive input or captured pipes that a stalled descendant can hold
/// open. Timeout and cancellation terminate the process group (Unix) or job (Windows), then
/// reap the direct child before the caller syncs any completed repository effects.
pub(super) async fn run(mut command: Command, limit: Duration) -> io::Result<ExitStatus> {
    command
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .env("GIT_TERMINAL_PROMPT", "0");
    let mut command = CommandWrap::from(tokio::process::Command::from(command));
    command.wrap(KillOnDrop);
    #[cfg(unix)]
    command.wrap(process_wrap::tokio::ProcessGroup::leader());
    #[cfg(windows)]
    command.wrap(process_wrap::tokio::JobObject);
    // Declared first so unwinding stops the child before clearing its cancellation state.
    let cancellation = Cancellation::register()?;
    let mut child = FetchChild {
        child: command.spawn()?,
        running: true,
    };
    let waited = tokio::select! {
        status = tokio::time::timeout(limit, child.child.wait()) => Some(status),
        _ = cancellation.notify.notified() => None,
    };
    match waited {
        Some(Ok(status)) => {
            child.running = status.is_err();
            status
        }
        stopped => {
            // A process can exit between the timeout and kill. Reap it in that case too.
            let killed = child.child.start_kill();
            let reaped = child.child.wait().await;
            child.running = reaped.is_err();
            reaped?;
            if let Err(err) = killed {
                // The process group can disappear before the kill, while the direct child
                // is still ours to reap. Keep an interrupt classified as an interrupt.
                #[cfg(unix)]
                let already_gone =
                    err.raw_os_error() == Some(rustix::io::Errno::SRCH.raw_os_error());
                #[cfg(not(unix))]
                let already_gone = false;
                if !already_gone {
                    return Err(err);
                }
            }
            let kind = if stopped.is_none() {
                io::ErrorKind::Interrupted
            } else {
                io::ErrorKind::TimedOut
            };
            Err(io::Error::new(kind, "upstream fetch stopped"))
        }
    }
}

#[cfg(test)]
mod tests;
