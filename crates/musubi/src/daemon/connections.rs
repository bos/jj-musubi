//! Sharing hub connections among copies and coalescing concurrent connection attempts.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::Weak;
use std::time::Duration;

use futures::FutureExt as _;
use futures::future::BoxFuture;
use futures::future::Shared;
use musubi_sync::remote::OpenConnection;
use musubi_transport::stream::WhileDisconnected;

use super::REQUEST_TIMEOUT;
use crate::hub::Connection;

/// How long a copy waits to open a connection of its own for a large transfer, before it
/// moves the transfer on the connection it shares.
const OWN_CONNECTION_TIMEOUT: Duration = Duration::from_secs(10);

/// The daemon's connections to hubs: one to each, which every copy it serves there shares,
/// rather than one, and an ssh, a copy. Each runs on the runtime that made the registry, the
/// daemon's own, which outlives the copies', and ends once no copy holds it.
pub(super) struct Hubs {
    runtime: tokio::runtime::Handle,
    hubs: Arc<Mutex<HashMap<String, HubConnection>>>,
    /// Whether a copy opens another connection for a large transfer
    /// (`musubi.daemon.connections`).
    own_connections: bool,
}

/// A hub's connection while a copy holds it, and the attempt to connect while one is under
/// way, which copies that ask meanwhile wait for rather than connecting too.
#[derive(Default)]
struct HubConnection {
    connection: Weak<Connection>,
    connecting: Option<Connecting>,
}

type Connecting = Shared<BoxFuture<'static, Result<Arc<Connection>, String>>>;

/// Records how an attempt to connect ended, however it ends, panicking included: what it
/// made, and that it is over, so that the next copy to ask connects afresh.
struct Attempted {
    hubs: Arc<Mutex<HashMap<String, HubConnection>>>,
    hub: String,
    connection: Weak<Connection>,
}

impl Attempted {
    fn made(&mut self, connection: &Arc<Connection>) {
        self.connection = Arc::downgrade(connection);
    }
}

impl Drop for Attempted {
    fn drop(&mut self) {
        let mut hubs = self.hubs.lock().unwrap_or_else(PoisonError::into_inner);
        let entry = hubs.entry(std::mem::take(&mut self.hub)).or_default();
        entry.connecting = None;
        entry.connection = std::mem::take(&mut self.connection);
    }
}

impl Hubs {
    pub(super) fn new(runtime: tokio::runtime::Handle, own_connections: bool) -> Self {
        Self {
            runtime,
            hubs: Arc::default(),
            own_connections,
        }
    }

    /// Opens a connection of a copy's own to `hub`, for a large transfer, unless the daemon
    /// is to reach each hub over one. It runs on the copy's runtime, which the transfer
    /// keeps busy, and ends with the transfer.
    pub(super) fn own_connections(&self, hub: &str) -> Option<OpenConnection> {
        let hub = hub.to_owned();
        self.own_connections.then(|| -> OpenConnection {
            Arc::new(move || {
                let hub = hub.clone();
                async move {
                    let next = WhileDisconnected::NextAttempt;
                    Ok(crate::hub::connect_with(&hub, OWN_CONNECTION_TIMEOUT, next)
                        .await?
                        .transport)
                }
                .boxed()
            })
        })
    }

    /// The connection to `hub`, connecting if no copy holds one. An attempt that fails
    /// fails every copy that waited for it.
    pub(super) async fn connect(&self, hub: &str) -> anyhow::Result<Arc<Connection>> {
        let attempt = {
            let mut hubs = self.hubs.lock().unwrap_or_else(PoisonError::into_inner);
            let entry = hubs.entry(hub.to_owned()).or_default();
            if let Some(connection) = entry.connection.upgrade() {
                return Ok(connection);
            }
            entry
                .connecting
                .get_or_insert_with(|| self.attempt(hub))
                .clone()
        };
        attempt.await.map_err(anyhow::Error::msg)
    }

    /// Connects to `hub` on the daemon's runtime, and records the connection as it ends,
    /// for copies that ask afterwards: so that only the copies that waited hold what it
    /// made, which ends once none does.
    fn attempt(&self, hub: &str) -> Connecting {
        let mut ended = Attempted {
            hubs: self.hubs.clone(),
            hub: hub.to_owned(),
            connection: Weak::new(),
        };
        let task = self.runtime.spawn(async move {
            // A copy's sync fails once the connection is lost and connecting again fails,
            // rather than waiting out its timeouts, so that the copy says why at once and
            // waits for the hub itself.
            let next = WhileDisconnected::NextAttempt;
            let connected = crate::hub::connect_with(&ended.hub, REQUEST_TIMEOUT, next)
                .await
                .map(Arc::new)
                .map_err(|err| format!("{err:#}"));
            if let Ok(connection) = &connected {
                ended.made(connection);
            }
            connected
        });
        async move {
            task.await
                .unwrap_or_else(|err| Err(format!("connecting to the hub: {err}")))
        }
        .boxed()
        .shared()
    }
}
