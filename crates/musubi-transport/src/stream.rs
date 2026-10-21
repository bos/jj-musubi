//! A transport over a byte stream: a local socket, or ssh's standard input and output.
//!
//! A hub serves each connection with [`serve`], relaying what the other side sends through a
//! transport of its own, which reaches the hub's service. [`StreamTransport`] is the other
//! side, opening a new connection through its [`Connector`] whenever one ends.
//!
//! Each side first sends [`GREETING`], the protocol's name and version, and the hub follows
//! it with the largest payload it takes, as a big-endian `u32`. Each frame after that is its
//! length as a big-endian `u32`, a kind, and its fields: integers are big-endian `u64`s,
//! strings a big-endian `u16` length and UTF-8, and a payload whatever is left.
//!
//! - From the client: `SUB sid subject`, `PUB subject payload`, and
//!   `REQ id timeout-ms subject payload`.
//! - From the hub: `MSG sid subject reply payload` for a subscription, the reply empty when
//!   there is none, and `REPLY id payload` or `FAIL id code message` for a request.
//!
//! A frame cut off by the connection ending is never delivered.

use std::collections::HashMap;
use std::io;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Duration;

use async_trait::async_trait;
use bytes::Buf as _;
use bytes::Bytes;
use tokio::io::AsyncRead;
use tokio::io::AsyncReadExt as _;
use tokio::io::AsyncWrite;
use tokio::io::AsyncWriteExt as _;
use tokio::io::BufReader;
use tokio::io::BufWriter;
use tokio::sync::mpsc;
use tokio::sync::oneshot;
use tokio::sync::watch;
use tokio::task::JoinSet;
use tokio::time::Instant;

use crate::Message;
use crate::Reconnections;
use crate::Subscription;
use crate::Transport;
use crate::TransportError;
use crate::check_size;

/// What each side sends first: the protocol's name and version.
pub const GREETING: &[u8; 8] = b"musubi1\n";

/// How long the other side may take to greet, which over ssh includes logging in, through a
/// tunnel's ProxyCommand perhaps.
const GREETING_TIMEOUT: Duration = Duration::from_secs(30);

/// The longest wait between attempts to connect.
const MAX_RETRY_DELAY: Duration = Duration::from_secs(4);

/// The longest a request relayed for a client may take, whatever the client asked for.
const MAX_REQUEST_TIMEOUT: Duration = Duration::from_secs(3600);

/// Room in a frame for everything but its payload: two strings and a few integers.
const FRAME_OVERHEAD: usize = 2 * (2 + u16::MAX as usize) + 32;

const SUB: u8 = 1;
const PUB: u8 = 2;
const REQ: u8 = 3;
const MSG: u8 = 4;
const REPLY: u8 = 5;
const FAIL: u8 = 6;

/// Why a request failed, in a `FAIL` frame.
const TIMED_OUT: u8 = 1;
const NO_RESPONDERS: u8 = 2;
const OTHER: u8 = 3;

#[derive(Debug, PartialEq, Eq)]
enum Frame {
    Sub {
        sid: u64,
        subject: String,
    },
    Pub {
        subject: String,
        payload: Bytes,
    },
    Req {
        id: u64,
        timeout: Duration,
        subject: String,
        payload: Bytes,
    },
    Msg {
        sid: u64,
        subject: String,
        reply: Option<String>,
        payload: Bytes,
    },
    Reply {
        id: u64,
        payload: Bytes,
    },
    Fail {
        id: u64,
        code: u8,
        message: String,
    },
}

impl Frame {
    fn kind(&self) -> &'static str {
        match self {
            Self::Sub { .. } => "SUB",
            Self::Pub { .. } => "PUB",
            Self::Req { .. } => "REQ",
            Self::Msg { .. } => "MSG",
            Self::Reply { .. } => "REPLY",
            Self::Fail { .. } => "FAIL",
        }
    }

    /// The frame, with its length in front.
    fn encode(&self) -> Vec<u8> {
        let mut out = vec![0; 4];
        let payload = match self {
            Self::Sub { sid, subject } => {
                out.push(SUB);
                put_u64(&mut out, *sid);
                put_str(&mut out, subject);
                None
            }
            Self::Pub { subject, payload } => {
                out.push(PUB);
                put_str(&mut out, subject);
                Some(payload)
            }
            Self::Req {
                id,
                timeout,
                subject,
                payload,
            } => {
                out.push(REQ);
                put_u64(&mut out, *id);
                put_u64(
                    &mut out,
                    u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX),
                );
                put_str(&mut out, subject);
                Some(payload)
            }
            Self::Msg {
                sid,
                subject,
                reply,
                payload,
            } => {
                out.push(MSG);
                put_u64(&mut out, *sid);
                put_str(&mut out, subject);
                put_str(&mut out, reply.as_deref().unwrap_or_default());
                Some(payload)
            }
            Self::Reply { id, payload } => {
                out.push(REPLY);
                put_u64(&mut out, *id);
                Some(payload)
            }
            Self::Fail { id, code, message } => {
                out.push(FAIL);
                put_u64(&mut out, *id);
                out.push(*code);
                put_str(&mut out, message);
                None
            }
        };
        if let Some(payload) = payload {
            out.extend_from_slice(payload);
        }
        let len = u32::try_from(out.len() - 4).unwrap_or(u32::MAX);
        out[..4].copy_from_slice(&len.to_be_bytes());
        out
    }

    /// Reads a frame's body, everything after its length.
    fn decode(mut body: Bytes) -> io::Result<Self> {
        Ok(match take_u8(&mut body)? {
            SUB => {
                let sid = take_u64(&mut body)?;
                let subject = take_str(&mut body)?;
                Self::Sub { sid, subject }
            }
            PUB => {
                let subject = take_str(&mut body)?;
                Self::Pub {
                    subject,
                    payload: body,
                }
            }
            REQ => {
                let id = take_u64(&mut body)?;
                let timeout = Duration::from_millis(take_u64(&mut body)?);
                let subject = take_str(&mut body)?;
                Self::Req {
                    id,
                    timeout,
                    subject,
                    payload: body,
                }
            }
            MSG => {
                let sid = take_u64(&mut body)?;
                let subject = take_str(&mut body)?;
                let reply = take_str(&mut body)?;
                Self::Msg {
                    sid,
                    subject,
                    reply: (!reply.is_empty()).then_some(reply),
                    payload: body,
                }
            }
            REPLY => {
                let id = take_u64(&mut body)?;
                Self::Reply { id, payload: body }
            }
            FAIL => {
                let id = take_u64(&mut body)?;
                let code = take_u8(&mut body)?;
                let message = take_str(&mut body)?;
                Self::Fail { id, code, message }
            }
            kind => return Err(invalid(format!("a frame of unknown kind {kind}"))),
        })
    }
}

fn put_u64(out: &mut Vec<u8>, n: u64) {
    out.extend_from_slice(&n.to_be_bytes());
}

fn put_str(out: &mut Vec<u8>, s: &str) {
    // Subjects are checked before they get this far; only an error's message can be longer.
    let s = &s[..s.floor_char_boundary(usize::from(u16::MAX))];
    out.extend_from_slice(&u16::try_from(s.len()).unwrap_or(u16::MAX).to_be_bytes());
    out.extend_from_slice(s.as_bytes());
}

fn take_u8(body: &mut Bytes) -> io::Result<u8> {
    if body.is_empty() {
        return Err(cut_short());
    }
    Ok(body.get_u8())
}

fn take_u64(body: &mut Bytes) -> io::Result<u64> {
    if body.len() < 8 {
        return Err(cut_short());
    }
    Ok(body.get_u64())
}

fn take_str(body: &mut Bytes) -> io::Result<String> {
    if body.len() < 2 {
        return Err(cut_short());
    }
    let len = usize::from(body.get_u16());
    if body.len() < len {
        return Err(cut_short());
    }
    String::from_utf8(body.split_to(len).to_vec()).map_err(|_| invalid("a string that isn't UTF-8"))
}

fn cut_short() -> io::Error {
    invalid("a frame cut short")
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

/// Reads the next frame, or `None` at the end of the stream. A frame longer than `limit`
/// is an error.
async fn read_frame(
    reader: &mut (impl AsyncRead + Unpin),
    limit: usize,
) -> io::Result<Option<Frame>> {
    let len = match reader.read_u32().await {
        Ok(len) => len as usize,
        Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
        Err(err) => return Err(err),
    };
    if len > limit {
        return Err(invalid(format!(
            "a frame of {len} bytes, more than the {limit} allowed"
        )));
    }
    let mut body = vec![0; len];
    reader.read_exact(&mut body).await?;
    Frame::decode(Bytes::from(body)).map(Some)
}

/// Writes encoded frames as they come, until there are no more.
async fn write_frames(
    writer: impl AsyncWrite + Unpin,
    mut frames: mpsc::UnboundedReceiver<Vec<u8>>,
) -> io::Result<()> {
    let mut writer = BufWriter::new(writer);
    while let Some(frame) = frames.recv().await {
        writer.write_all(&frame).await?;
        while let Ok(frame) = frames.try_recv() {
            writer.write_all(&frame).await?;
        }
        writer.flush().await?;
    }
    writer.shutdown().await
}

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
}

/// A connection to a hub over the streams a [`Connector`] opens, opening another whenever
/// one ends. Requests in flight when a connection ends fail with
/// [`TransportError::Disconnected`], those made while there is none wait for the next, up
/// to their timeout, and subscriptions carry on over each new connection, missing what was
/// published in between.
pub struct StreamTransport {
    shared: Arc<Shared>,
    task: tokio::task::JoinHandle<()>,
}

impl Drop for StreamTransport {
    fn drop(&mut self) {
        self.task.abort();
    }
}

struct Shared {
    state: Mutex<State>,
    /// Whether there is a connection now.
    connected: watch::Sender<bool>,
    /// How many times it has connected again after losing its connection.
    reconnected: watch::Sender<u64>,
}

struct State {
    /// Where frames for the connection go, while there is one.
    out: Option<mpsc::UnboundedSender<Vec<u8>>>,
    max_payload: usize,
    next_id: u64,
    subscriptions: HashMap<u64, (String, mpsc::UnboundedSender<Message>)>,
    /// Requests awaiting replies on this connection, with their subjects.
    pending: HashMap<u64, (String, oneshot::Sender<Result<Bytes, TransportError>>)>,
}

impl Shared {
    fn lock(&self) -> std::sync::MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Takes on a new connection, which carries the frames sent to `out`, subscribing again
    /// to everything still subscribed to.
    fn attach(&self, out: mpsc::UnboundedSender<Vec<u8>>, max_payload: usize) {
        let mut state = self.lock();
        state
            .subscriptions
            .retain(|_, (_, sender)| !sender.is_closed());
        for (&sid, (subject, _)) in &state.subscriptions {
            let subject = subject.clone();
            out.send(Frame::Sub { sid, subject }.encode()).ok();
        }
        state.out = Some(out);
        state.max_payload = max_payload;
        drop(state);
        self.connected.send_replace(true);
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
                };
                if let Some((_, sender)) = state.subscriptions.get(&sid)
                    && sender.send(message).is_err()
                {
                    // Nobody reads the subscription any more.
                    state.subscriptions.remove(&sid);
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
        let shared = Arc::new(Shared {
            state: Mutex::new(State {
                out: None,
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
                let (out, frames) = mpsc::unbounded_channel();
                shared.attach(out, max_payload);
                match first.take() {
                    Some(first) => {
                        first.send(Ok(())).ok();
                    }
                    None => shared.reconnected.send_modify(|n| *n += 1),
                }
                let ended = tokio::select! {
                    result = receive(&shared, reader, max_payload) => result,
                    result = write_frames(writer, frames) => result,
                };
                shared.detach();
                match ended {
                    Ok(()) => tracing::debug!("the hub closed the connection"),
                    Err(err) => tracing::debug!("lost the connection to the hub: {err}"),
                }
            }
            Err(err) => {
                // The other side not speaking the protocol: trying again won't help.
                if err.kind() == io::ErrorKind::InvalidData
                    && let Some(first) = first.take()
                {
                    first.send(Err(TransportError::Other(err.to_string()))).ok();
                    return;
                }
                failures += 1;
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

/// Opens a connection and greets the hub, returning the largest payload it takes.
async fn open(connector: &dyn Connector) -> io::Result<(Reader, Writer, usize)> {
    let (mut reader, mut writer) = connector.connect().await?;
    writer.write_all(GREETING).await?;
    writer.flush().await?;
    let greeted = async {
        let mut greeting = [0; GREETING.len()];
        reader.read_exact(&mut greeting).await?;
        if &greeting != GREETING {
            return Err(invalid(if greeting.starts_with(b"musubi") {
                "the hub speaks another version of musubi's protocol"
            } else {
                "what answered is not a musubi hub"
            }));
        }
        reader.read_u32().await
    };
    let max_payload = tokio::time::timeout(GREETING_TIMEOUT, greeted)
        .await
        .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "the hub did not answer"))??;
    Ok((reader, writer, max_payload as usize))
}

async fn receive(shared: &Shared, reader: Reader, max_payload: usize) -> io::Result<()> {
    let mut reader = BufReader::new(reader);
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

    fn max_payload(&self) -> usize {
        self.shared.lock().max_payload
    }

    async fn publish(&self, subject: &str, payload: Bytes) -> Result<(), TransportError> {
        check_subject(subject)?;
        check_size(&payload, self.max_payload())?;
        let subject = subject.to_owned();
        let frame = Frame::Pub { subject, payload }.encode();
        let state = self.shared.lock();
        let out = state.out.as_ref().ok_or(TransportError::Disconnected)?;
        out.send(frame).map_err(|_| TransportError::Disconnected)
    }

    async fn subscribe(&self, subject: &str) -> Result<Subscription, TransportError> {
        check_subject(subject)?;
        let (sender, receiver) = mpsc::unbounded_channel();
        let mut state = self.shared.lock();
        let sid = state.next_id;
        state.next_id += 1;
        // Without a connection now, the next one subscribes.
        if let Some(out) = &state.out {
            let subject = subject.to_owned();
            out.send(Frame::Sub { sid, subject }.encode()).ok();
        }
        state
            .subscriptions
            .insert(sid, (subject.to_owned(), sender));
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
        let (id, replied) = loop {
            {
                let mut state = self.shared.lock();
                if let Some(out) = state.out.clone() {
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
                    // If the connection is ending, ending it fails the request.
                    out.send(frame.encode()).ok();
                    break (id, replied);
                }
            }
            // No connection now: wait for the next, as long as the timeout allows.
            match tokio::time::timeout_at(deadline, connected.changed()).await {
                Ok(Ok(())) => {}
                Ok(Err(_)) => return Err(TransportError::Disconnected),
                Err(_) => return Err(TransportError::Timeout),
            }
        };
        match tokio::time::timeout_at(deadline, replied).await {
            Ok(Ok(result)) => result,
            Ok(Err(_)) => Err(TransportError::Disconnected),
            Err(_) => {
                self.shared.lock().pending.remove(&id);
                Err(TransportError::Timeout)
            }
        }
    }
}

/// Serves one connection to the hub, relaying what the other side sends through
/// `transport`, which reaches the hub's service, until either side closes it. Requests are
/// relayed as they come, without waiting for earlier ones' replies.
pub async fn serve(
    transport: Arc<dyn Transport>,
    reader: impl AsyncRead + Send + Unpin,
    mut writer: impl AsyncWrite + Send + Unpin,
) -> io::Result<()> {
    let limit = transport.max_payload();
    writer.write_all(GREETING).await?;
    writer
        .write_u32(u32::try_from(limit).unwrap_or(u32::MAX))
        .await?;
    writer.flush().await?;
    let mut reader = BufReader::new(reader);
    let mut greeting = [0; GREETING.len()];
    tokio::time::timeout(GREETING_TIMEOUT, reader.read_exact(&mut greeting))
        .await
        .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "the client did not greet"))??;
    if &greeting != GREETING {
        return Err(invalid(
            "what connected is not a musubi client, or speaks another version of its protocol",
        ));
    }
    let (out, frames) = mpsc::unbounded_channel();
    // Subscriptions and requests in progress, which end with the connection.
    let mut tasks = JoinSet::new();
    let relay = async {
        while let Some(frame) = read_frame(&mut reader, limit + FRAME_OVERHEAD).await? {
            while tasks.try_join_next().is_some() {}
            match frame {
                Frame::Sub { sid, subject } => {
                    let mut subscription = transport
                        .subscribe(&subject)
                        .await
                        .map_err(io::Error::other)?;
                    let out = out.clone();
                    tasks.spawn(async move {
                        while let Some(message) = subscription.next().await {
                            let frame = Frame::Msg {
                                sid,
                                subject: message.subject,
                                reply: message.reply,
                                payload: message.payload,
                            };
                            if out.send(frame.encode()).is_err() {
                                break;
                            }
                        }
                    });
                }
                // Delivery is best effort: what can't be published is lost, as on the way.
                Frame::Pub { subject, payload } => {
                    transport.publish(&subject, payload).await.ok();
                }
                Frame::Req {
                    id,
                    timeout,
                    subject,
                    payload,
                } => {
                    let (transport, out) = (transport.clone(), out.clone());
                    tasks.spawn(async move {
                        let timeout = timeout.min(MAX_REQUEST_TIMEOUT);
                        let frame = match transport.request(&subject, payload, timeout).await {
                            Ok(payload) => Frame::Reply { id, payload },
                            Err(err) => failure(id, err),
                        };
                        out.send(frame.encode()).ok();
                    });
                }
                frame => {
                    return Err(invalid(format!(
                        "a client sent the hub's frame, {}",
                        frame.kind()
                    )));
                }
            }
        }
        Ok(())
    };
    tokio::select! {
        result = relay => result,
        result = write_frames(writer, frames) => result,
    }
}

fn failure(id: u64, err: TransportError) -> Frame {
    let (code, message) = match err {
        TransportError::Timeout => (TIMED_OUT, String::new()),
        TransportError::NoResponders(_) => (NO_RESPONDERS, String::new()),
        err => (OTHER, err.to_string()),
    };
    Frame::Fail { id, code, message }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trip(frame: Frame) {
        let encoded = frame.encode();
        let len = u32::from_be_bytes([encoded[0], encoded[1], encoded[2], encoded[3]]);
        assert_eq!(len as usize, encoded.len() - 4);
        let decoded = Frame::decode(Bytes::from(encoded[4..].to_vec())).unwrap();
        assert_eq!(decoded, frame);
    }

    #[test]
    fn frames_round_trip() {
        round_trip(Frame::Sub {
            sid: 7,
            subject: "musubi.*.rpc".into(),
        });
        round_trip(Frame::Pub {
            subject: "musubi.hive.head".into(),
            payload: Bytes::from_static(b"head"),
        });
        round_trip(Frame::Req {
            id: u64::MAX,
            timeout: Duration::from_millis(1500),
            subject: "musubi.hive.rpc".into(),
            payload: Bytes::new(),
        });
        round_trip(Frame::Msg {
            sid: 1,
            subject: "musubi.hive.rpc".into(),
            reply: Some("_INBOX.1.2".into()),
            payload: Bytes::from_static(b"request"),
        });
        round_trip(Frame::Msg {
            sid: 1,
            subject: "musubi.hive.head".into(),
            reply: None,
            payload: Bytes::new(),
        });
        round_trip(Frame::Reply {
            id: 3,
            payload: Bytes::from_static(b"reply"),
        });
        round_trip(Frame::Fail {
            id: 4,
            code: OTHER,
            message: "it went wrong".into(),
        });
    }

    #[test]
    fn long_messages_are_cut_to_fit() {
        let message = "é".repeat(40_000);
        let encoded = Frame::Fail {
            id: 1,
            code: OTHER,
            message,
        }
        .encode();
        let Frame::Fail { message, .. } =
            Frame::decode(Bytes::from(encoded[4..].to_vec())).unwrap()
        else {
            panic!("not a FAIL");
        };
        assert_eq!(message.len(), 65534);
    }

    #[test]
    fn malformed_frames_are_errors() {
        let mut encoded = Frame::Sub {
            sid: 7,
            subject: "subject".into(),
        }
        .encode();
        encoded.pop();
        let err = Frame::decode(Bytes::from(encoded[4..].to_vec())).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        let err = Frame::decode(Bytes::from_static(&[99])).unwrap_err();
        assert!(err.to_string().contains("unknown kind 99"), "{err}");
        let err = Frame::decode(Bytes::from_static(&[
            SUB, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0xff,
        ]))
        .unwrap_err();
        assert!(err.to_string().contains("UTF-8"), "{err}");
    }

    #[tokio::test]
    async fn frames_over_the_limit_are_refused() {
        let frame = Frame::Reply {
            id: 1,
            payload: Bytes::from(vec![0; 100]),
        }
        .encode();
        let err = read_frame(&mut frame.as_slice(), 50).await.unwrap_err();
        assert!(
            err.to_string().contains("more than the 50 allowed"),
            "{err}"
        );
        // A frame the stream ends partway through is never delivered.
        let err = read_frame(&mut &frame[..50], 200).await.unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);
        assert!(read_frame(&mut &[][..], 200).await.unwrap().is_none());
    }
}
