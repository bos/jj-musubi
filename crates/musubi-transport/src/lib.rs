//! Message transports for jj-musubi.
//!
//! musubi needs very little from a transport: publish to a subject, subscribe to a subject,
//! and request/reply with a timeout, all with payloads up to a size limit the transport
//! reports. Delivery is best-effort; the protocol tolerates lost, duplicated, and reordered
//! messages (see docs/protocol.md).

use std::time::Duration;

use async_trait::async_trait;
use bytes::Bytes;
use thiserror::Error;
use tokio::sync::mpsc;

mod memory;
mod nats;

pub use memory::Faults;
pub use memory::MemoryNetwork;
pub use memory::MemoryTransport;
pub use nats::NatsTransport;

#[derive(Debug, Error)]
pub enum TransportError {
    #[error("request timed out")]
    Timeout,
    #[error("no responders for {0}")]
    NoResponders(String),
    #[error("payload of {size} bytes exceeds the limit of {limit}")]
    PayloadTooLarge { size: usize, limit: usize },
    #[error("disconnected")]
    Disconnected,
    #[error("transport error: {0}")]
    Other(String),
}

/// A message delivered to a subscriber.
#[derive(Clone, Debug)]
pub struct Message {
    pub subject: String,
    pub payload: Bytes,
    /// Where to publish a reply, for requests.
    pub reply: Option<String>,
}

/// Messages arriving on a subscription. The stream ends when the transport shuts down.
pub struct Subscription {
    receiver: mpsc::UnboundedReceiver<Message>,
}

impl Subscription {
    pub(crate) fn new(receiver: mpsc::UnboundedReceiver<Message>) -> Self {
        Self { receiver }
    }

    pub async fn next(&mut self) -> Option<Message> {
        self.receiver.recv().await
    }
}

#[async_trait]
pub trait Transport: Send + Sync {
    /// The largest payload the transport accepts.
    fn max_payload(&self) -> usize;

    async fn publish(&self, subject: &str, payload: Bytes) -> Result<(), TransportError>;

    /// Subscribes to `subject`, which may hold NATS wildcards: `*` matches one token, and a
    /// final `>` one or more.
    async fn subscribe(&self, subject: &str) -> Result<Subscription, TransportError>;

    /// Publishes `payload` with a fresh reply subject and waits for the first reply.
    async fn request(
        &self,
        subject: &str,
        payload: Bytes,
        timeout: Duration,
    ) -> Result<Bytes, TransportError>;
}

/// Whether `subject` matches the subscription `pattern`, as NATS matches them.
pub fn subject_matches(pattern: &str, subject: &str) -> bool {
    let mut pattern = pattern.split('.');
    let mut subject = subject.split('.');
    loop {
        match (pattern.next(), subject.next()) {
            (Some(">"), Some(_)) => return true,
            (Some("*"), Some(_)) => {}
            (Some(p), Some(s)) if p == s => {}
            (None, None) => return true,
            _ => return false,
        }
    }
}

pub(crate) fn check_size(payload: &Bytes, limit: usize) -> Result<(), TransportError> {
    if payload.len() > limit {
        Err(TransportError::PayloadTooLarge {
            size: payload.len(),
            limit,
        })
    } else {
        Ok(())
    }
}
