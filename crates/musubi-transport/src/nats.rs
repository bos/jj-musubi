//! NATS transport, using core NATS (no JetStream): the hub is the durable store.

use std::time::Duration;

use async_trait::async_trait;
use bytes::Bytes;
use futures::StreamExt as _;
use tokio::sync::mpsc;

use crate::Message;
use crate::Subscription;
use crate::Transport;
use crate::TransportError;
use crate::check_size;

const PING_INTERVAL: Duration = Duration::from_secs(10);
const CONNECTION_TIMEOUT: Duration = Duration::from_secs(30);

pub struct NatsTransport {
    client: async_nats::Client,
}

impl NatsTransport {
    /// Connects to `url`, retrying until the server answers, and reconnecting automatically
    /// afterwards. Credentials in the URL authenticate: `nats://<token>@host:port` with a
    /// token, `nats://<user>:<password>@host:port` with a user and password.
    pub async fn connect(url: &str) -> Result<Self, TransportError> {
        let other = |err: &dyn std::fmt::Display| TransportError::Other(err.to_string());
        let (url, credentials) = split_credentials(url);
        let options = match credentials {
            Credentials::None => async_nats::ConnectOptions::new(),
            Credentials::Token(token) => async_nats::ConnectOptions::with_token(token),
            Credentials::User(user, password) => {
                async_nats::ConnectOptions::with_user_and_password(user, password)
            }
        };
        let client = options
            .retry_on_initial_connect()
            // Notices a connection that died while the machine slept within seconds of
            // waking, rather than minutes.
            .ping_interval(PING_INTERVAL)
            // Connecting covers the server's INFO, which over ssh (see musubi's `ssh`) waits
            // for an ssh login, through a tunnel's ProxyCommand perhaps.
            .connection_timeout(CONNECTION_TIMEOUT)
            .connect(url.as_str())
            .await
            .map_err(|err| other(&err))?;
        // With retries, `connect` returns before the server's INFO (and so its payload
        // limit) has arrived; a flush round-trips to the server.
        client.flush().await.map_err(|err| other(&err))?;
        Ok(Self { client })
    }

    pub fn from_client(client: async_nats::Client) -> Self {
        Self { client }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Credentials {
    None,
    Token(String),
    User(String, String),
}

/// Takes the credentials out of a NATS URL. async-nats ignores them there.
fn split_credentials(url: &str) -> (String, Credentials) {
    let Some((scheme, rest)) = url.split_once("://") else {
        return (url.to_owned(), Credentials::None);
    };
    let authority_end = rest.find('/').unwrap_or(rest.len());
    let Some(at) = rest[..authority_end].rfind('@') else {
        return (url.to_owned(), Credentials::None);
    };
    let (userinfo, host) = (&rest[..at], &rest[at + 1..]);
    let credentials = match userinfo.split_once(':') {
        Some((user, password)) => Credentials::User(user.to_owned(), password.to_owned()),
        None => Credentials::Token(userinfo.to_owned()),
    };
    (format!("{scheme}://{host}"), credentials)
}

#[async_trait]
impl Transport for NatsTransport {
    fn max_payload(&self) -> usize {
        self.client.server_info().max_payload
    }

    async fn publish(&self, subject: &str, payload: Bytes) -> Result<(), TransportError> {
        check_size(&payload, self.max_payload())?;
        self.client
            .publish(subject.to_owned(), payload)
            .await
            .map_err(|err| TransportError::Other(err.to_string()))
    }

    async fn subscribe(&self, subject: &str) -> Result<Subscription, TransportError> {
        let mut subscriber = self
            .client
            .subscribe(subject.to_owned())
            .await
            .map_err(|err| TransportError::Other(err.to_string()))?;
        let (sender, receiver) = mpsc::unbounded_channel();
        tokio::spawn(async move {
            while let Some(message) = subscriber.next().await {
                let message = Message {
                    subject: message.subject.to_string(),
                    payload: message.payload,
                    reply: message.reply.map(|reply| reply.to_string()),
                };
                if sender.send(message).is_err() {
                    break;
                }
            }
        });
        Ok(Subscription::new(receiver))
    }

    async fn request(
        &self,
        subject: &str,
        payload: Bytes,
        timeout: Duration,
    ) -> Result<Bytes, TransportError> {
        check_size(&payload, self.max_payload())?;
        let request = async_nats::Request::new()
            .payload(payload)
            .timeout(Some(timeout));
        match self.client.send_request(subject.to_owned(), request).await {
            Ok(message) => Ok(message.payload),
            Err(err) => Err(match err.kind() {
                async_nats::RequestErrorKind::TimedOut => TransportError::Timeout,
                async_nats::RequestErrorKind::NoResponders => {
                    TransportError::NoResponders(subject.to_owned())
                }
                _ => TransportError::Other(err.to_string()),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn credentials_come_out_of_the_url() {
        assert_eq!(
            split_credentials("nats://s3cret@hub.local:4222"),
            (
                "nats://hub.local:4222".to_owned(),
                Credentials::Token("s3cret".to_owned())
            )
        );
        assert_eq!(
            split_credentials("tls://me:pw@hub.local:4222"),
            (
                "tls://hub.local:4222".to_owned(),
                Credentials::User("me".to_owned(), "pw".to_owned())
            )
        );
        assert_eq!(
            split_credentials("nats://hub.local:4222"),
            ("nats://hub.local:4222".to_owned(), Credentials::None)
        );
        assert_eq!(
            split_credentials("hub.local:4222"),
            ("hub.local:4222".to_owned(), Credentials::None)
        );
    }
}
