//! An in-process network with fault injection, for tests.
//!
//! Subjects match exactly; there are no wildcards. Faults are drawn from a seeded generator,
//! so a failing run can be replayed from its seed.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;
use std::time::Duration;

use async_trait::async_trait;
use bytes::Bytes;
use tokio::sync::mpsc;

use crate::Message;
use crate::Subscription;
use crate::Transport;
use crate::TransportError;
use crate::check_size;

/// Per-message fault probabilities, in parts per million.
#[derive(Clone, Copy, Debug, Default)]
pub struct Faults {
    pub drop_ppm: u32,
    pub duplicate_ppm: u32,
    /// Chance that a message is held back by up to `max_delay`, reordering it with later
    /// ones.
    pub delay_ppm: u32,
    pub max_delay: Duration,
}

struct Subscriber {
    client: u64,
    sender: mpsc::UnboundedSender<Message>,
}

struct State {
    subscriptions: HashMap<String, Vec<Subscriber>>,
    partitioned: HashMap<u64, bool>,
    faults: Faults,
    rng: u64,
}

impl State {
    /// xorshift64*: deterministic for a given seed, which is all tests need.
    fn next_ppm(&mut self) -> u32 {
        self.rng ^= self.rng >> 12;
        self.rng ^= self.rng << 25;
        self.rng ^= self.rng >> 27;
        (self.rng.wrapping_mul(0x2545_f491_4f6c_dd1d) >> 32) as u32 % 1_000_000
    }
}

/// The shared medium that [`MemoryTransport`]s connect to.
#[derive(Clone)]
pub struct MemoryNetwork {
    state: Arc<Mutex<State>>,
    next_id: Arc<AtomicU64>,
    max_payload: usize,
}

impl MemoryNetwork {
    pub fn new(seed: u64, max_payload: usize) -> Self {
        Self {
            state: Arc::new(Mutex::new(State {
                subscriptions: HashMap::new(),
                partitioned: HashMap::new(),
                faults: Faults::default(),
                rng: seed | 1,
            })),
            next_id: Arc::new(AtomicU64::new(1)),
            max_payload,
        }
    }

    pub fn set_faults(&self, faults: Faults) {
        self.state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .faults = faults;
    }

    pub fn connect(&self) -> MemoryTransport {
        MemoryTransport {
            network: self.clone(),
            client: self.next_id.fetch_add(1, Ordering::Relaxed),
        }
    }

    /// Cuts a client off: nothing it sends is delivered, and nothing reaches it.
    pub fn partition(&self, transport: &MemoryTransport) {
        self.state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .partitioned
            .insert(transport.client, true);
    }

    pub fn heal(&self, transport: &MemoryTransport) {
        self.state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .partitioned
            .remove(&transport.client);
    }

    fn deliver(&self, from: u64, message: Message) -> Result<(), TransportError> {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        if state.partitioned.contains_key(&from) {
            return Err(TransportError::Disconnected);
        }
        let faults = state.faults;
        let targets: Vec<mpsc::UnboundedSender<Message>> = state
            .subscriptions
            .get(&message.subject)
            .into_iter()
            .flatten()
            .filter(|sub| !state.partitioned.contains_key(&sub.client))
            .map(|sub| sub.sender.clone())
            .collect();
        for target in targets {
            if state.next_ppm() < faults.drop_ppm {
                continue;
            }
            let copies = if state.next_ppm() < faults.duplicate_ppm {
                2
            } else {
                1
            };
            for _ in 0..copies {
                if state.next_ppm() < faults.delay_ppm && !faults.max_delay.is_zero() {
                    let delay = faults.max_delay.mul_f64(f64::from(state.next_ppm()) / 1e6);
                    let (target, message) = (target.clone(), message.clone());
                    tokio::spawn(async move {
                        tokio::time::sleep(delay).await;
                        // A receiver that has gone away just misses the message.
                        target.send(message).ok();
                    });
                } else {
                    target.send(message.clone()).ok();
                }
            }
        }
        Ok(())
    }

    fn has_subscribers(&self, subject: &str) -> bool {
        let state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        state
            .subscriptions
            .get(subject)
            .is_some_and(|subs| subs.iter().any(|sub| !sub.sender.is_closed()))
    }
}

/// One client's connection to a [`MemoryNetwork`].
#[derive(Clone)]
pub struct MemoryTransport {
    network: MemoryNetwork,
    client: u64,
}

#[async_trait]
impl Transport for MemoryTransport {
    fn max_payload(&self) -> usize {
        self.network.max_payload
    }

    async fn publish(&self, subject: &str, payload: Bytes) -> Result<(), TransportError> {
        check_size(&payload, self.network.max_payload)?;
        let message = Message {
            subject: subject.to_owned(),
            payload,
            reply: None,
        };
        self.network.deliver(self.client, message)
    }

    async fn subscribe(&self, subject: &str) -> Result<Subscription, TransportError> {
        let (sender, receiver) = mpsc::unbounded_channel();
        let mut state = self
            .network
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let subs = state.subscriptions.entry(subject.to_owned()).or_default();
        subs.retain(|sub| !sub.sender.is_closed());
        subs.push(Subscriber {
            client: self.client,
            sender,
        });
        Ok(Subscription::new(receiver))
    }

    async fn request(
        &self,
        subject: &str,
        payload: Bytes,
        timeout: Duration,
    ) -> Result<Bytes, TransportError> {
        check_size(&payload, self.network.max_payload)?;
        if !self.network.has_subscribers(subject) {
            return Err(TransportError::NoResponders(subject.to_owned()));
        }
        let inbox = format!(
            "_INBOX.{}.{}",
            self.client,
            self.network.next_id.fetch_add(1, Ordering::Relaxed)
        );
        let mut replies = self.subscribe(&inbox).await?;
        let message = Message {
            subject: subject.to_owned(),
            payload,
            reply: Some(inbox.clone()),
        };
        self.network.deliver(self.client, message)?;
        let reply = tokio::time::timeout(timeout, replies.next()).await;
        self.network
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .subscriptions
            .remove(&inbox);
        match reply {
            Ok(Some(message)) => Ok(message.payload),
            Ok(None) => Err(TransportError::Disconnected),
            Err(_) => Err(TransportError::Timeout),
        }
    }
}
