//! Interrupts (^C, and on Unix SIGTERM and SIGHUP, as a closed terminal sends) during the
//! parts of a command that stop cleanly when asked, rather than dying where they are.

use std::io;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::OnceLock;

use tokio::sync::Notify;

type Active = Arc<Mutex<Option<Arc<Notify>>>>;
static INTERRUPTS: OnceLock<Result<Active, ctrlc::Error>> = OnceLock::new();

/// Interrupts caught until dropped. Tokio leaves its signal handler installed after a
/// short-lived runtime ends, so a handler for the whole process takes them instead: it
/// tells the one `Interrupts` caught at the time, if any, and otherwise exits at once, as the
/// signal would, with the status a shell gives a command ^C ended.
pub struct Interrupts {
    active: Active,
    notify: Arc<Notify>,
}

impl Interrupts {
    /// Catches interrupts from now until dropped. Fails if they are caught already.
    pub fn catch() -> io::Result<Self> {
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
            return Err(io::Error::other("interrupts are caught already"));
        }
        *slot = Some(notify.clone());
        drop(slot);
        Ok(Self { active, notify })
    }

    /// Waits for an interrupt, returning at once for one that came since the last.
    pub async fn next(&self) {
        self.notify.notified().await;
    }
}

impl Drop for Interrupts {
    fn drop(&mut self) {
        self.active
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take();
    }
}
