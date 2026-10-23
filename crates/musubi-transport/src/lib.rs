//! Message transports for jj-musubi.
//!
//! Internal to jj-musubi, with no stable API.
//!
//! musubi needs very little from a transport: publish to a subject, subscribe to a subject,
//! and request/reply with a timeout, all with payloads up to a size limit the transport
//! reports. Delivery is best-effort; the protocol tolerates lost, duplicated, and reordered
//! messages (see docs/internals/protocol.md).

use std::time::Duration;

use async_trait::async_trait;
use bytes::Bytes;
use thiserror::Error;
use tokio::sync::mpsc;
use tokio::sync::watch;

mod memory;
pub mod stream;

pub use memory::Faults;
pub use memory::MemoryNetwork;
pub use memory::MemoryTransport;
pub use stream::StreamTransport;

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

/// A transport's reconnections, each time it connects again after losing its connection,
/// when announcements made meanwhile may have been missed.
pub struct Reconnections {
    receiver: Option<watch::Receiver<u64>>,
}

impl Reconnections {
    /// For a transport that never loses its connection.
    pub fn never() -> Self {
        Self { receiver: None }
    }

    /// Counts reconnections from now on: a counter the transport increments on each.
    pub(crate) fn watching(mut receiver: watch::Receiver<u64>) -> Self {
        receiver.borrow_and_update();
        Self {
            receiver: Some(receiver),
        }
    }

    /// Forgets reconnections so far, as when starting a sync, which covers them.
    pub fn seen(&mut self) {
        if let Some(receiver) = &mut self.receiver {
            receiver.borrow_and_update();
        }
    }

    /// Waits for the next reconnection.
    pub async fn next(&mut self) {
        if let Some(receiver) = &mut self.receiver
            && receiver.changed().await.is_ok()
        {
            return;
        }
        // The transport is gone, or never reconnects.
        std::future::pending::<()>().await;
    }
}

#[async_trait]
pub trait Transport: Send + Sync {
    /// Its reconnections from now on.
    fn reconnections(&self) -> Reconnections {
        Reconnections::never()
    }

    /// Whether it has a connection now. One that never loses it always has.
    fn connected(&self) -> bool {
        true
    }

    /// The largest payload the transport accepts.
    fn max_payload(&self) -> usize;

    async fn publish(&self, subject: &str, payload: Bytes) -> Result<(), TransportError>;

    /// Subscribes to `subject`, which may hold wildcards: `*` matches one token, and a final
    /// `>` one or more.
    async fn subscribe(&self, subject: &str) -> Result<Subscription, TransportError>;

    /// Publishes `payload` with a fresh reply subject and waits for the first reply.
    async fn request(
        &self,
        subject: &str,
        payload: Bytes,
        timeout: Duration,
    ) -> Result<Bytes, TransportError>;
}

/// Whether `subject` matches the subscription `pattern`, wildcards and all.
pub(crate) fn subject_matches(pattern: &str, subject: &str) -> bool {
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
