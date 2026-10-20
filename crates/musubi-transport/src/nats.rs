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

pub struct NatsTransport {
    client: async_nats::Client,
}

impl NatsTransport {
    /// Connects to `url`, retrying until the server answers, and reconnecting automatically
    /// afterwards.
    pub async fn connect(url: &str) -> Result<Self, TransportError> {
        let other = |err: &dyn std::fmt::Display| TransportError::Other(err.to_string());
        let client = async_nats::ConnectOptions::new()
            .retry_on_initial_connect()
            .connect(url)
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
