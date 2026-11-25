//! A best-effort upstream fetch must not keep an otherwise completed join waiting forever.

use std::io;
use std::process::Command;
use std::process::ExitStatus;
use std::process::Stdio;
use std::time::Duration;

use process_wrap::tokio::ChildWrapper;
use process_wrap::tokio::CommandWrap;
use process_wrap::tokio::KillOnDrop;

use crate::interrupt::Interrupts;

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
    // Caught for the fetch alone: an interrupt during the rest of the join ends it as usual.
    let interrupts = Interrupts::catch()?;
    let mut child = FetchChild {
        child: command.spawn()?,
        running: true,
    };
    let waited = tokio::select! {
        status = tokio::time::timeout(limit, child.child.wait()) => Some(status),
        () = interrupts.next() => None,
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
