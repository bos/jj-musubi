//! A transport over a byte stream: a local socket, or ssh's standard input and output.
//!
//! A hub serves each connection with [`serve`], relaying what the other side sends through a
//! transport of its own, which reaches the hub's service. [`StreamTransport`] is the other
//! side, opening a new connection through its [`Connector`] whenever one ends.
//!
//! The hub first sends [`GREETING`], the protocol's name and version, followed by the largest
//! payload it takes, as a big-endian `u32`, and the client answers with the same greeting.
//! Over ssh, the hub's machine can print something first, as some shells' startup files do
//! even for a command: the client passes over up to [`MAX_BEFORE_GREETING`] bytes of it, as
//! Mercurial's ssh client passes over noise, and greets only after the hub has, so that none
//! of what runs there before the hub can read the greeting. Each frame after that is its
//! length as a big-endian `u32`, a kind, and its fields: integers are big-endian `u64`s,
//! strings a big-endian `u16` length and UTF-8, and a payload whatever is left.
//!
//! - From the client: `SUB sid subject`, `PUB subject payload`, and
//!   `REQ id timeout-ms subject payload`.
//! - From the hub: `MSG sid subject reply payload` for a subscription, the reply empty when
//!   there is none, and `REPLY id payload` or `FAIL id code message` for a request.
//!
//! A frame cut off by the connection ending is never delivered.

mod frame;
mod greeting;
mod server;

use std::collections::HashMap;
use std::io;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Duration;

use async_trait::async_trait;
use bytes::Bytes;
use tokio::io::AsyncRead;
use tokio::io::AsyncReadExt as _;
use tokio::io::AsyncWrite;
use tokio::io::AsyncWriteExt as _;
use tokio::io::BufReader;
use tokio::sync::Notify;
use tokio::sync::mpsc;
use tokio::sync::mpsc::error::TrySendError;
use tokio::sync::oneshot;
use tokio::sync::watch;
use tokio::time::Instant;

use self::frame::FRAME_OVERHEAD;
use self::frame::Frame;
use self::frame::NO_RESPONDERS;
use self::frame::TIMED_OUT;
use self::frame::invalid;
use self::frame::read_frame;
use self::frame::write_frames;
use self::greeting::GREETING_TIMEOUT;

pub use self::greeting::GREETING;
pub use self::greeting::MAX_BEFORE_GREETING;
pub use self::greeting::PLAUSIBLE_PAYLOADS;
pub use self::greeting::await_greeting;
pub use self::server::serve;

#[cfg(any(fuzzing, test))]
pub use self::frame::fuzzing;

use crate::Message;
use crate::Reconnections;
use crate::Subscription;
use crate::Transport;
use crate::TransportError;
use crate::check_size;

/// The longest wait between attempts to connect.
const MAX_RETRY_DELAY: Duration = Duration::from_secs(4);

/// How long to wait before connecting again to a hub that answered but can't be talked to,
/// which only another hub, started meanwhile, would change.
const INCOMPATIBLE_RETRY_DELAY: Duration = Duration::from_secs(60);

/// How many frames may wait to be written to a connection: few are large, since replies are
/// only as many as the client's requests in flight. A connection with this many waiting,
/// whose other side has stopped reading, as one that vanished without a word has, is ended.
const MAX_QUEUED: usize = 1024;

/// Per-connection admission limits, checked on both sides. Client subscription slots stay
/// in use until disconnect, since there is no unsubscribe frame; request slots end with the call.
const MAX_SUBSCRIPTIONS: usize = 1024;
const MAX_REQUESTS: usize = 1024;

fn check_subject(subject: &str) -> Result<(), TransportError> {
    if subject.is_empty() || subject.len() > usize::from(u16::MAX) {
        return Err(TransportError::Other(format!(
            "a subject of {} bytes",
            subject.len()
        )));
    }
    Ok(())
}

/// The reading half of a connection.
pub type Reader = Box<dyn AsyncRead + Send + Unpin>;

/// The writing half of a connection.
pub type Writer = Box<dyn AsyncWrite + Send + Unpin>;

/// Opens connections to a hub for a [`StreamTransport`]: each one a new ssh, say.
#[async_trait]
pub trait Connector: Send + Sync {
    async fn connect(&self) -> io::Result<(Reader, Writer)>;

    /// Hears why the connection it opened last was given up on before the hub greeted: what
    /// answered isn't a hub to talk to, which it may know no better.
    fn not_hub(&self, _why: &io::Error) {}
}

/// A connection to a hub over the streams a [`Connector`] opens, opening another whenever
/// one ends. Requests in flight when a connection ends fail with
/// [`TransportError::Disconnected`], those made while there is none do as
/// [`WhileDisconnected`] says, and subscriptions carry on over each new connection, missing
/// what was published in between.
pub struct StreamTransport {
    shared: Arc<Shared>,
    task: tokio::task::JoinHandle<()>,
}

impl Drop for StreamTransport {
    fn drop(&mut self) {
        self.task.abort();
    }
}

/// What a request made while a [`StreamTransport`] has no connection does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WhileDisconnected {
    /// Waits for the next connection, up to its timeout: for a command, which a link that
    /// drops and comes back within moments shouldn't fail.
    Wait,
    /// Waits for the next attempt to connect, failing with [`TransportError::Disconnected`]
    /// if it fails: for a caller that says why the hub is out of reach and waits for it
    /// itself, as the daemon does, rather than wait for the timeout of each request.
    NextAttempt,
}

struct Shared {
    while_disconnected: WhileDisconnected,
    /// How many attempts to connect have failed.
    failed_attempts: watch::Sender<u64>,
    state: Mutex<State>,
    /// Whether there is a connection now.
    connected: watch::Sender<bool>,
    /// How many times it has connected again after losing its connection.
    reconnected: watch::Sender<u64>,
}

struct State {
    /// Where frames for the connection go, while there is one.
    out: Option<mpsc::Sender<Vec<u8>>>,
    /// Ends the connection, when it falls too far behind.
    stalled: Arc<Notify>,
    max_payload: usize,
    next_id: u64,
    /// Its subscriptions on the hub, by id: one for each subject, which the subscriptions
    /// made to it share. Nothing unsubscribes on the hub, so one that nobody reads any more
    /// stays until the connection ends, for a subscription to the same subject to take up.
    subscriptions: HashMap<u64, Subscribed>,
    /// Requests awaiting replies on this connection, with their subjects.
    pending: HashMap<u64, (String, oneshot::Sender<Result<Bytes, TransportError>>)>,
}

/// A registered call owns its inbox only while someone is waiting, including when the
/// request future is dropped before a reply or timeout.
struct PendingCall<'a> {
    shared: &'a Shared,
    id: u64,
}

impl Drop for PendingCall<'_> {
    fn drop(&mut self) {
        self.shared.lock().pending.remove(&self.id);
    }
}

/// A subscription on the hub, to `subject`.
struct Subscribed {
    subject: String,
    /// Where its messages go: one for each subscription made to the subject.
    to: Vec<mpsc::UnboundedSender<Message>>,
}

impl State {
    /// Queues a frame for the connection. One too far behind to take it is ended, and the
    /// next one subscribes again to everything.
    fn send(&self, frame: Vec<u8>) -> Result<(), TransportError> {
        let out = self.out.as_ref().ok_or(TransportError::Disconnected)?;
        out.try_send(frame).map_err(|err| {
            if matches!(err, TrySendError::Full(_)) {
                self.stalled.notify_one();
            }
            TransportError::Disconnected
        })
    }
}

impl Shared {
    fn lock(&self) -> std::sync::MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Takes on a new connection, which ends when `stalled` is notified, subscribing again to
    /// everything still subscribed to. Returns the frames to write to it.
    fn attach(&self, stalled: Arc<Notify>, max_payload: usize) -> mpsc::Receiver<Vec<u8>> {
        let mut state = self.lock();
        // Only what is still read: the last connection's took the rest with it.
        state.subscriptions.retain(|_, subscribed| {
            subscribed.to.retain(|to| !to.is_closed());
            !subscribed.to.is_empty()
        });
        // Sized under the same lock as the frames below, with room for every one of them, so
        // none is dropped and a subscription never silently goes without its messages.
        let (out, frames) = mpsc::channel(MAX_QUEUED + state.subscriptions.len());
        for (&sid, subscribed) in &state.subscriptions {
            let subject = subscribed.subject.clone();
            let sent = out.try_send(Frame::Sub { sid, subject }.encode());
            debug_assert!(sent.is_ok(), "a new connection has room to subscribe again");
        }
        state.out = Some(out);
        state.stalled = stalled;
        state.max_payload = max_payload;
        drop(state);
        self.connected.send_replace(true);
        frames
    }

    /// Lets go of a connection that ended: requests made on it will get no reply.
    fn detach(&self) {
        let pending = {
            let mut state = self.lock();
            state.out = None;
            std::mem::take(&mut state.pending)
        };
        self.connected.send_replace(false);
        for (_, reply) in pending.into_values() {
            reply.send(Err(TransportError::Disconnected)).ok();
        }
    }

    fn receive(&self, frame: Frame) -> io::Result<()> {
        let mut state = self.lock();
        match frame {
            Frame::Msg {
                sid,
                subject,
                reply,
                payload,
            } => {
                let message = Message {
                    subject,
                    payload,
                    reply,
                    deadline: None,
                };
                if let Some(subscribed) = state.subscriptions.get_mut(&sid) {
                    subscribed.to.retain(|to| to.send(message.clone()).is_ok());
                }
            }
            Frame::Reply { id, payload } => {
                if let Some((_, reply)) = state.pending.remove(&id) {
                    reply.send(Ok(payload)).ok();
                }
            }
            Frame::Fail { id, code, message } => {
                if let Some((subject, reply)) = state.pending.remove(&id) {
                    let err = match code {
                        TIMED_OUT => TransportError::Timeout,
                        NO_RESPONDERS => TransportError::NoResponders(subject),
                        _ => TransportError::Other(message),
                    };
                    reply.send(Err(err)).ok();
                }
            }
            frame => {
                return Err(invalid(format!(
                    "the hub sent a client's frame, {}",
                    frame.kind()
                )));
            }
        }
        Ok(())
    }
}

impl StreamTransport {
    /// Connects through `connector`, trying again until a hub answers, and connecting again
    /// whenever a connection ends. Fails at once if what answers isn't a musubi hub, or
    /// speaks another version of the protocol.
    pub async fn connect(connector: Arc<dyn Connector>) -> Result<Self, TransportError> {
        Self::connect_with(connector, WhileDisconnected::Wait).await
    }

    /// [`StreamTransport::connect`], with requests made while there is no connection doing
    /// as `while_disconnected` says.
    pub async fn connect_with(
        connector: Arc<dyn Connector>,
        while_disconnected: WhileDisconnected,
    ) -> Result<Self, TransportError> {
        let shared = Arc::new(Shared {
            while_disconnected,
            failed_attempts: watch::channel(0).0,
            state: Mutex::new(State {
                out: None,
                stalled: Arc::new(Notify::new()),
                max_payload: 0,
                next_id: 1,
                subscriptions: HashMap::new(),
                pending: HashMap::new(),
            }),
            connected: watch::channel(false).0,
            reconnected: watch::channel(0).0,
        });
        let (first, answered) = oneshot::channel();
        // Dropping the transport stops the task, as when the caller gives up waiting here.
        let transport = Self {
            task: tokio::spawn(run(shared.clone(), connector, first)),
            shared,
        };
        match answered.await {
            Ok(Ok(())) => Ok(transport),
            Ok(Err(err)) => Err(err),
            Err(_) => Err(TransportError::Disconnected),
        }
    }
}

/// Keeps connecting, and serves each connection until it ends. `first` hears how the first
/// connection that worked, or couldn't work, went.
async fn run(
    shared: Arc<Shared>,
    connector: Arc<dyn Connector>,
    first: oneshot::Sender<Result<(), TransportError>>,
) {
    let mut first = Some(first);
    let mut failures = 0;
    loop {
        match open(connector.as_ref()).await {
            Ok((reader, writer, max_payload)) => {
                failures = 0;
                let stalled = Arc::new(Notify::new());
                let frames = shared.attach(stalled.clone(), max_payload);
                match first.take() {
                    Some(first) => {
                        first.send(Ok(())).ok();
                    }
                    None => shared.reconnected.send_modify(|n| *n += 1),
                }
                let ended = tokio::select! {
                    result = receive(&shared, reader, max_payload) => result,
                    result = write_frames(writer, frames) => result,
                    () = stalled.notified() => Err(io::Error::other(format!(
                        "it fell {MAX_QUEUED} frames behind"
                    ))),
                };
                shared.detach();
                match ended {
                    Ok(()) => tracing::debug!("the hub closed the connection"),
                    Err(err) => tracing::debug!("lost the connection to the hub: {err}"),
                }
            }
            // The other side not speaking the protocol: trying again won't help, not soon.
            Err(err) if err.kind() == io::ErrorKind::InvalidData => {
                shared.failed_attempts.send_modify(|n| *n += 1);
                if let Some(first) = first.take() {
                    first.send(Err(TransportError::Other(err.to_string()))).ok();
                    return;
                }
                tracing::warn!("cannot talk to the hub: {err}");
                tokio::time::sleep(INCOMPATIBLE_RETRY_DELAY).await;
                continue;
            }
            Err(err) => {
                failures += 1;
                shared.failed_attempts.send_modify(|n| *n += 1);
                tracing::debug!("could not connect to the hub: {err}");
            }
        }
        tokio::time::sleep(retry_delay(failures)).await;
    }
}

/// How long to wait before connecting again: a moment after a connection ends, and longer
/// after each attempt that fails, up to [`MAX_RETRY_DELAY`].
fn retry_delay(failures: u32) -> Duration {
    Duration::from_millis(250)
        .saturating_mul(1 << failures.min(8))
        .min(MAX_RETRY_DELAY)
}

/// Opens a connection and waits for the hub's greeting, returning the largest payload it
/// takes; then greets it.
async fn open(connector: &dyn Connector) -> io::Result<(BufReader<Reader>, Writer, usize)> {
    let (reader, mut writer) = connector.connect().await?;
    let mut reader = BufReader::new(reader);
    let greeted = async {
        await_greeting(&mut reader).await?;
        let max_payload = reader.read_u32().await? as usize;
        if !PLAUSIBLE_PAYLOADS.contains(&max_payload) {
            return Err(invalid(format!(
                "what answered is not a musubi hub: it offered messages of up to \
                 {max_payload} bytes"
            )));
        }
        Ok(max_payload)
    };
    let max_payload = match tokio::time::timeout(GREETING_TIMEOUT, greeted).await {
        Ok(Ok(max_payload)) => max_payload,
        Ok(Err(err)) => {
            if err.kind() == io::ErrorKind::InvalidData {
                connector.not_hub(&err);
            }
            return Err(err);
        }
        Err(_) => {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "the hub did not answer",
            ));
        }
    };
    // Only now: what runs on the hub's machine before the hub could read it.
    writer.write_all(GREETING).await?;
    writer.flush().await?;
    Ok((reader, writer, max_payload))
}

async fn receive(
    shared: &Shared,
    mut reader: BufReader<Reader>,
    max_payload: usize,
) -> io::Result<()> {
    while let Some(frame) = read_frame(&mut reader, max_payload + FRAME_OVERHEAD).await? {
        shared.receive(frame)?;
    }
    Ok(())
}

#[async_trait]
impl Transport for StreamTransport {
    fn reconnections(&self) -> Reconnections {
        Reconnections::watching(self.shared.reconnected.subscribe())
    }

    fn connected(&self) -> bool {
        *self.shared.connected.borrow()
    }

    fn max_payload(&self) -> usize {
        self.shared.lock().max_payload
    }

    async fn publish(&self, subject: &str, payload: Bytes) -> Result<(), TransportError> {
        check_subject(subject)?;
        check_size(&payload, self.max_payload())?;
        let subject = subject.to_owned();
        let frame = Frame::Pub { subject, payload }.encode();
        self.shared.lock().send(frame)
    }

    async fn subscribe(&self, subject: &str) -> Result<Subscription, TransportError> {
        check_subject(subject)?;
        let (sender, receiver) = mpsc::unbounded_channel();
        let mut state = self.shared.lock();
        // On the hub already, perhaps for a subscription that has ended.
        if let Some(subscribed) = state
            .subscriptions
            .values_mut()
            .find(|subscribed| subscribed.subject == subject)
        {
            subscribed.to.retain(|to| !to.is_closed());
            subscribed.to.push(sender);
            return Ok(Subscription::new(receiver));
        }
        if state.subscriptions.len() >= MAX_SUBSCRIPTIONS {
            return Err(TransportError::Other(format!(
                "this connection already has {MAX_SUBSCRIPTIONS} subscriptions"
            )));
        }
        let sid = state.next_id;
        state.next_id += 1;
        // Without a connection now, or with one too far behind to take it, the next one
        // subscribes.
        let frame = Frame::Sub {
            sid,
            subject: subject.to_owned(),
        };
        state.send(frame.encode()).ok();
        state.subscriptions.insert(
            sid,
            Subscribed {
                subject: subject.to_owned(),
                to: vec![sender],
            },
        );
        Ok(Subscription::new(receiver))
    }

    async fn request(
        &self,
        subject: &str,
        payload: Bytes,
        timeout: Duration,
    ) -> Result<Bytes, TransportError> {
        check_subject(subject)?;
        check_size(&payload, self.max_payload())?;
        let deadline = Instant::now() + timeout;
        let mut connected = self.shared.connected.subscribe();
        // Before looking for a connection: an attempt that fails meanwhile counts.
        let mut failed_attempts = self.shared.failed_attempts.subscribe();
        let (id, replied) = loop {
            {
                let mut state = self.shared.lock();
                if state.out.is_some() {
                    if state.pending.len() >= MAX_REQUESTS {
                        return Err(TransportError::Other(format!(
                            "this connection already has {MAX_REQUESTS} requests in flight"
                        )));
                    }
                    let id = state.next_id;
                    state.next_id += 1;
                    let (reply, replied) = oneshot::channel();
                    state.pending.insert(id, (subject.to_owned(), reply));
                    let frame = Frame::Req {
                        id,
                        timeout: deadline.saturating_duration_since(Instant::now()),
                        subject: subject.to_owned(),
                        payload: payload.clone(),
                    };
                    if let Err(err) = state.send(frame.encode()) {
                        state.pending.remove(&id);
                        return Err(err);
                    }
                    break (id, replied);
                }
            }
            // No connection now: wait for the next, as long as the timeout allows, or as
            // long as the next attempt to make one.
            let attempt_failed = async {
                match self.shared.while_disconnected {
                    WhileDisconnected::Wait => std::future::pending().await,
                    WhileDisconnected::NextAttempt => failed_attempts.changed().await,
                }
            };
            let waited = tokio::time::timeout_at(deadline, async {
                // A connection made since counts for more than an attempt that failed before
                // it.
                tokio::select! {
                    biased;
                    changed = connected.changed() => changed.is_ok(),
                    _ = attempt_failed => false,
                }
            });
            match waited.await {
                Ok(true) => {}
                Ok(false) => return Err(TransportError::Disconnected),
                Err(_) => return Err(TransportError::Timeout),
            }
        };
        let _pending = PendingCall {
            shared: &self.shared,
            id,
        };
        match tokio::time::timeout_at(deadline, replied).await {
            Ok(Ok(result)) => result,
            Ok(Err(_)) => Err(TransportError::Disconnected),
            Err(_) => Err(TransportError::Timeout),
        }
    }
}

#[cfg(test)]
mod io_tests;

#[cfg(test)]
mod tests {
    use super::frame::OTHER;
    use super::*;

    fn empty_shared(next_id: u64) -> Shared {
        Shared {
            while_disconnected: WhileDisconnected::Wait,
            failed_attempts: watch::channel(0).0,
            state: Mutex::new(State {
                out: None,
                stalled: Arc::new(Notify::new()),
                max_payload: 1024,
                next_id,
                subscriptions: HashMap::new(),
                pending: HashMap::new(),
            }),
            connected: watch::channel(false).0,
            reconnected: watch::channel(0).0,
        }
    }

    /// A connection made with a full subscription table takes a subscription frame for
    /// every subject and still has its own room for `MAX_QUEUED` more.
    #[test]
    fn attach_resubscribes_a_full_table() {
        let shared = empty_shared(1);
        let mut held = vec![];
        for sid in 1..=MAX_SUBSCRIPTIONS as u64 {
            let (sender, receiver) = mpsc::unbounded_channel();
            held.push(receiver);
            let subscribed = Subscribed {
                subject: format!("musubi.test.{sid}"),
                to: vec![sender],
            };
            shared.lock().subscriptions.insert(sid, subscribed);
        }
        let mut frames = shared.attach(Arc::new(Notify::new()), 1024);
        let out = shared.lock().out.clone().unwrap();
        assert_eq!(out.capacity(), MAX_QUEUED);
        let mut sids = vec![];
        while let Ok(encoded) = frames.try_recv() {
            match Frame::decode(Bytes::from(encoded[4..].to_vec())).unwrap() {
                Frame::Sub { sid, subject } => {
                    assert_eq!(subject, format!("musubi.test.{sid}"));
                    sids.push(sid);
                }
                other => panic!("{other:?}"),
            }
        }
        sids.sort_unstable();
        assert_eq!(sids, (1..=MAX_SUBSCRIPTIONS as u64).collect::<Vec<_>>());
    }

    /// Service-side reply inboxes can discard duplicates before they become stream frames.
    /// Deliver frames here, in a fixed order, to pin the client's own correlation rule.
    #[test]
    fn replies_only_complete_the_matching_pending_call_once() {
        use serde_json::json;

        let shared = empty_shared(4);
        let (abandoned, canceled) = oneshot::channel();
        shared.lock().pending.insert(1, ("rpc".into(), abandoned));
        drop(canceled);
        let (fresh, mut completed) = oneshot::channel();
        shared.lock().pending.insert(2, ("rpc".into(), fresh));
        let (current, mut waiting) = oneshot::channel();
        shared.lock().pending.insert(3, ("rpc".into(), current));
        let mut oracle = crate::oracle::Oracle::spawn();
        let mut model = json!({"op": "retryInbox", "action": "finish",
            "next": 4, "pending": [1, 2, 3], "cut": 3});
        let mut finish = |id, payload| {
            model["id"] = json!(id);
            let expected = oracle.call(&model);
            assert_eq!(expected["ok"], true, "{expected}");
            let matched = shared.lock().pending.contains_key(&id);
            shared.receive(Frame::Reply { id, payload }).unwrap();
            assert_eq!(expected["matched"], matched);
            let mut live: Vec<_> = shared.lock().pending.keys().copied().collect();
            live.sort_unstable();
            assert_eq!(expected["pending"], json!(live));
            assert_eq!(expected["next"], shared.lock().next_id);
            model["pending"] = expected["pending"].clone();
        };
        finish(2, Bytes::from_static(b"fresh"));
        assert_eq!(completed.try_recv().unwrap().unwrap(), "fresh");
        for id in [1, 2, 1, 999] {
            finish(id, Bytes::from_static(b"obsolete"));
            assert!(matches!(
                waiting.try_recv(),
                Err(oneshot::error::TryRecvError::Empty)
            ));
        }
        finish(3, Bytes::from_static(b"current"));
        assert_eq!(waiting.try_recv().unwrap().unwrap(), "current");
        assert!(shared.lock().pending.is_empty());
    }

    /// A failed call consumes its id as a successful one does, preserving the peer's reason
    /// and the original subject. Unknown or duplicate failures cannot finish another call.
    #[test]
    fn failure_frames_preserve_the_reason_and_only_complete_the_matching_call() {
        for code in [TIMED_OUT, NO_RESPONDERS, OTHER, 255] {
            let shared = empty_shared(9);
            let (reply, mut failed) = oneshot::channel();
            shared.lock().pending.insert(7, ("rpc".into(), reply));
            let (reply, mut waiting) = oneshot::channel();
            shared.lock().pending.insert(8, ("other".into(), reply));
            let failure = |id| Frame::Fail {
                id,
                code,
                message: "peer failure".into(),
            };
            shared.receive(failure(999)).unwrap();
            assert!(matches!(
                failed.try_recv(),
                Err(oneshot::error::TryRecvError::Empty)
            ));
            shared.receive(failure(7)).unwrap();
            let error = failed.try_recv().unwrap().unwrap_err();
            match code {
                TIMED_OUT => assert!(matches!(error, TransportError::Timeout), "{error:?}"),
                NO_RESPONDERS => assert!(
                    matches!(&error, TransportError::NoResponders(subject) if subject == "rpc"),
                    "{error:?}"
                ),
                _ => assert!(
                    matches!(&error, TransportError::Other(message) if message == "peer failure"),
                    "{error:?}"
                ),
            }
            shared.receive(failure(7)).unwrap();
            assert!(matches!(
                waiting.try_recv(),
                Err(oneshot::error::TryRecvError::Empty)
            ));
            shared
                .receive(Frame::Reply {
                    id: 8,
                    payload: Bytes::from_static(b"current"),
                })
                .unwrap();
            assert_eq!(waiting.try_recv().unwrap().unwrap(), "current");
            assert!(shared.lock().pending.is_empty());
        }
    }
}
