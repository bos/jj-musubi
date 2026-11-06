//! Polling hubs and the daemon while retaining connections between refreshes.

use std::collections::HashMap;
use std::time::Duration;

use musubi_hub::activity::HubActivity;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use tokio::time::Instant;

use crate::config::UserState;
use crate::control;
use crate::daemon;
use crate::hub;
use crate::socket::Socket;

/// The default hub, and the hubs of this machine's copies.
pub(super) fn known_hubs() -> anyhow::Result<Vec<String>> {
    let state = UserState::load()?;
    Ok(UserState::known_hubs(
        state.default_hub()?,
        &state.memberships(),
    ))
}

/// What every hub, and this machine's daemon, said at one refresh.
pub(super) struct Sample {
    pub(super) hubs: Vec<HubSample>,
    /// The number of repositories the daemon serves, if it is running.
    pub(super) daemon: Result<Option<usize>, String>,
    /// Whether this machine has copies, which need the daemon. A hub's machine may have none.
    pub(super) copies: bool,
}

/// What a hub said, and when it said it.
pub(super) struct HubSample {
    pub(super) hub: String,
    pub(super) at: Instant,
    pub(super) activity: Result<HubActivity, String>,
}

/// How long to wait before connecting again to a hub it couldn't connect to, rather than
/// wait for it at every refresh.
const RECONNECT: Duration = Duration::from_secs(30);

/// Where it is with a hub.
enum Link {
    Connected(hub::Connection),
    /// It couldn't connect, at this time, for this reason.
    Failed(Instant, String),
}

/// Asks the hubs, keeping a connection to each that it reached.
pub(super) struct Sampler {
    hubs: Vec<String>,
    socket: Result<Socket, String>,
    links: HashMap<String, Link>,
}

impl Sampler {
    pub(super) fn new(hubs: Vec<String>, socket: Result<Socket, String>) -> Self {
        Self {
            hubs,
            socket,
            links: HashMap::new(),
        }
    }

    /// Asks every hub at once, so that one slow to answer holds up only itself.
    pub(super) async fn sample(&mut self) -> Sample {
        let asks = self.hubs.iter().map(|hub| {
            let link = self.links.remove(hub);
            async move {
                let (link, activity) = ask(hub, link).await;
                let at = Instant::now();
                (
                    link,
                    HubSample {
                        hub: hub.clone(),
                        at,
                        activity,
                    },
                )
            }
        });
        let asked = futures::future::join_all(asks).await;
        let mut hubs = vec![];
        for (link, sample) in asked {
            self.links.insert(sample.hub.clone(), link);
            hubs.push(sample);
        }
        let daemon = match &self.socket {
            Ok(socket) => serving(socket).await,
            Err(err) => Err(err.clone()),
        };
        // Read again each time, since a copy may join or leave while it watches.
        let copies = UserState::load().map_or(true, |state| !state.copies.is_empty());
        Sample {
            hubs,
            daemon,
            copies,
        }
    }
}

/// The activity of `hub`, connecting to it first if need be and it's time to try again.
async fn ask(hub: &str, link: Option<Link>) -> (Link, Result<HubActivity, String>) {
    let connection = match link {
        Some(Link::Connected(connection)) => connection,
        Some(Link::Failed(at, why)) if at.elapsed() < RECONNECT => {
            return (Link::Failed(at, why.clone()), Err(why));
        }
        _ => {
            // Over ssh, through a ProxyCommand, connecting takes a while.
            let limit = Duration::from_secs(if hub::is_local(hub) { 3 } else { 15 });
            match hub::connect(hub, limit).await {
                Ok(connection) => connection,
                Err(err) => {
                    let why = format!("{err:#}");
                    return (Link::Failed(Instant::now(), why.clone()), Err(why));
                }
            }
        }
    };
    let activity = activity(&connection, hub)
        .await
        .map_err(|err| format!("{err:#}"));
    (Link::Connected(connection), activity)
}

async fn activity(connection: &hub::Connection, hub: &str) -> anyhow::Result<HubActivity> {
    // Once connected, the transport connects again by itself; until it has, say why not.
    if !connection.transport.connected()
        && let Some(why) = connection.out_of_reach().await
    {
        anyhow::bail!("{why}");
    }
    let limit = Duration::from_secs(10);
    match hub::ask_within(connection, hub, HubWideRequest::Activity, limit).await? {
        HubWideReply::Activity(activity) => Ok(activity),
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    }
}

/// How many repositories this machine's daemon serves, or `None` if it isn't running.
async fn serving(socket: &Socket) -> Result<Option<usize>, String> {
    let client = match daemon::running(socket).await {
        Ok(Some(client)) => client,
        Ok(None) => return Ok(None),
        Err(err) => return Err(format!("{err:#}")),
    };
    match client
        .status(control::context(Duration::from_secs(5)))
        .await
    {
        Ok(repos) => Ok(Some(repos.len())),
        Err(err) => Err(format!("{err}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A failed connection is reused until exactly the reconnect deadline, then tried
    /// again. The absolute path confines that attempt to a missing local hub.
    #[tokio::test(start_paused = true)]
    async fn a_failed_hub_is_retried_at_the_deadline() {
        let dir = musubi_testutil::tempdir();
        let hub = dir.path().join("missing").to_str().unwrap().to_owned();
        let started = Instant::now();
        let mut link = Some(Link::Failed(started, "cached failure".to_owned()));
        for advance in [Duration::ZERO, RECONNECT - Duration::from_millis(1)] {
            tokio::time::advance(advance).await;
            let (next, activity) = ask(&hub, link).await;
            assert_eq!(activity.unwrap_err(), "cached failure");
            assert!(matches!(&next, Link::Failed(at, _) if *at == started));
            link = Some(next);
        }
        tokio::time::advance(Duration::from_millis(1)).await;
        let (next, activity) = ask(&hub, link).await;
        assert_ne!(activity.unwrap_err(), "cached failure");
        assert!(matches!(next, Link::Failed(at, _) if at == started + RECONNECT));
    }
}
