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

use std::collections::HashMap;
use std::io;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Duration;

use async_trait::async_trait;
use bytes::Buf as _;
use bytes::Bytes;
use tokio::io::AsyncBufRead;
use tokio::io::AsyncBufReadExt as _;
use tokio::io::AsyncRead;
use tokio::io::AsyncReadExt as _;
use tokio::io::AsyncWrite;
use tokio::io::AsyncWriteExt as _;
use tokio::io::BufReader;
use tokio::io::BufWriter;
use tokio::sync::Notify;
use tokio::sync::mpsc;
use tokio::sync::mpsc::error::TrySendError;
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

/// What each side sends first: the protocol's name and version, after a NUL. A NUL is never
/// part of text, so a banner passes for the greeting, as one naming a host `musubi1` would
/// without it, only by printing it on purpose.
pub const GREETING: &[u8; 9] = b"\0musubi1\n";

/// The payload limits a hub may offer: what it says outside this is more likely to be noise
/// than a hub.
const PLAUSIBLE_PAYLOADS: std::ops::RangeInclusive<usize> = 1024..=64 << 20;

/// The most the hub's machine may print before the hub greets: a banner of ASCII art, say,
/// that a shell's startup files print for every shell.
pub const MAX_BEFORE_GREETING: usize = 64 * 1024;

/// How long the other side may take to greet, which over ssh includes logging in, through a
/// tunnel's ProxyCommand perhaps.
const GREETING_TIMEOUT: Duration = Duration::from_secs(30);

/// The longest wait between attempts to connect.
const MAX_RETRY_DELAY: Duration = Duration::from_secs(4);

/// How long to wait before connecting again to a hub that answered but can't be talked to,
/// which only another hub, started meanwhile, would change.
const INCOMPATIBLE_RETRY_DELAY: Duration = Duration::from_secs(60);

/// How many frames may wait to be written to a connection: few are large, since replies are
/// only as many as the client's requests in flight. A connection with this many waiting,
/// whose other side has stopped reading, as one that vanished without a word has, is ended.
const MAX_QUEUED: usize = 1024;

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
    mut frames: mpsc::Receiver<Vec<u8>>,
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

    /// Hears why the connection it opened last was given up on before the hub greeted: what
    /// answered isn't a hub to talk to, which it may know no better.
    fn not_hub(&self, _why: &io::Error) {}
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
    out: Option<mpsc::Sender<Vec<u8>>>,
    /// Ends the connection, when it falls too far behind.
    stalled: Arc<Notify>,
    max_payload: usize,
    next_id: u64,
    subscriptions: HashMap<u64, (String, mpsc::UnboundedSender<Message>)>,
    /// Requests awaiting replies on this connection, with their subjects.
    pending: HashMap<u64, (String, oneshot::Sender<Result<Bytes, TransportError>>)>,
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

    /// Takes on a new connection, which carries the frames sent to `out` and ends when
    /// `stalled` is notified, subscribing again to everything still subscribed to.
    fn attach(&self, out: mpsc::Sender<Vec<u8>>, stalled: Arc<Notify>, max_payload: usize) {
        let mut state = self.lock();
        state
            .subscriptions
            .retain(|_, (_, sender)| !sender.is_closed());
        for (&sid, (subject, _)) in &state.subscriptions {
            let subject = subject.clone();
            out.try_send(Frame::Sub { sid, subject }.encode()).ok();
        }
        state.out = Some(out);
        state.stalled = stalled;
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
                // Room for subscribing again to everything, too.
                let room = MAX_QUEUED + shared.lock().subscriptions.len();
                let (out, frames) = mpsc::channel(room);
                let stalled = Arc::new(Notify::new());
                shared.attach(out, stalled.clone(), max_payload);
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

/// Reads through the hub's greeting, passing over up to [`MAX_BEFORE_GREETING`] bytes of
/// whatever comes before it. Fails with [`io::ErrorKind::InvalidData`] if what answers is
/// not a hub, or speaks another version of the protocol.
pub async fn await_greeting(reader: &mut (impl AsyncBufRead + Unpin)) -> io::Result<()> {
    let mut before = Vec::new();
    loop {
        let room = MAX_BEFORE_GREETING.saturating_sub(before.len()) + GREETING.len();
        let mut line = Vec::new();
        let n = (&mut *reader)
            .take(room as u64)
            .read_until(b'\n', &mut line)
            .await?;
        // Whatever came before on the same line, as when the last thing printed has no
        // newline, is more of the same.
        if line.ends_with(GREETING) {
            return Ok(());
        }
        if is_other_greeting(&line) {
            return Err(invalid(
                "the hub speaks another version of musubi's protocol",
            ));
        }
        if n == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "the connection ended before the hub answered",
            ));
        }
        before.extend_from_slice(&line);
        if before.len() > MAX_BEFORE_GREETING {
            let said = String::from_utf8_lossy(&before);
            let first = said.lines().map(str::trim).find(|line| !line.is_empty());
            let first: String = first.unwrap_or_default().chars().take(80).collect();
            return Err(invalid(format!(
                "what answered is not a musubi hub: it said {first:?}"
            )));
        }
    }
}

/// Whether `line` ends as another version's greeting would, `\0musubi<digits>\n`.
fn is_other_greeting(line: &[u8]) -> bool {
    let Some(line) = line.strip_suffix(b"\n") else {
        return false;
    };
    let digits = line.iter().rev().take_while(|b| b.is_ascii_digit()).count();
    digits > 0 && line[..line.len() - digits].ends_with(b"\0musubi")
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
        let sid = state.next_id;
        state.next_id += 1;
        // Without a connection now, or with one too far behind to take it, the next one
        // subscribes.
        let frame = Frame::Sub {
            sid,
            subject: subject.to_owned(),
        };
        state.send(frame.encode()).ok();
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
                if state.out.is_some() {
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
    let (out, frames) = mpsc::channel(MAX_QUEUED);
    let stopped_reading = Arc::new(Notify::new());
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
                    let (out, stopped_reading) = (out.clone(), stopped_reading.clone());
                    tasks.spawn(async move {
                        while let Some(message) = subscription.next().await {
                            let frame = Frame::Msg {
                                sid,
                                subject: message.subject,
                                reply: message.reply,
                                payload: message.payload,
                            };
                            if !queue(&out, &stopped_reading, &frame) {
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
                    let stopped_reading = stopped_reading.clone();
                    tasks.spawn(async move {
                        let timeout = timeout.min(MAX_REQUEST_TIMEOUT);
                        let frame = match transport.request(&subject, payload, timeout).await {
                            Ok(payload) => Frame::Reply { id, payload },
                            Err(err) => failure(id, err),
                        };
                        queue(&out, &stopped_reading, &frame);
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
        () = stopped_reading.notified() => Err(io::Error::other(format!(
            "the client fell {MAX_QUEUED} frames behind; it may have vanished"
        ))),
    }
}

/// Queues `frame` for the client, returning whether the connection carries on: it doesn't
/// once it has closed, or once too many frames wait for the client.
fn queue(out: &mpsc::Sender<Vec<u8>>, stopped_reading: &Notify, frame: &Frame) -> bool {
    match out.try_send(frame.encode()) {
        Ok(()) => true,
        Err(TrySendError::Full(_)) => {
            stopped_reading.notify_one();
            false
        }
        Err(TrySendError::Closed(_)) => false,
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

/// Entry points for fuzz/, which reach frames without making them public. Tests build them
/// too, so that they're checked and linted with everything else.
#[cfg(any(fuzzing, test))]
pub mod fuzzing {
    use bytes::Bytes;

    use super::Frame;
    use super::read_frame;

    /// Reads frames from `stream` until it ends or one is malformed, checking that each
    /// encodes to a frame that reads back as the same one.
    pub async fn frames(mut stream: &[u8], limit: usize) {
        while let Ok(Some(frame)) = read_frame(&mut stream, limit).await {
            let encoded = frame.encode();
            let len = u32::from_be_bytes([encoded[0], encoded[1], encoded[2], encoded[3]]);
            assert_eq!(len as usize, encoded.len() - 4);
            let decoded = Frame::decode(Bytes::from(encoded[4..].to_vec()));
            assert_eq!(decoded.ok(), Some(frame));
        }
    }
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
    async fn noise_before_the_greeting_is_passed_over() {
        // On a host named as if it were the greeting, too.
        let goat = b"\x1b[1;33m      _))\n     > *\\     _~\n  Welcome to musubi1\n\x1b[0m\
                     Last login: never";
        let stream = [&goat[..], GREETING, b"rest"].concat();
        let mut reader = BufReader::new(stream.as_slice());
        await_greeting(&mut reader).await.unwrap();
        let mut rest = Vec::new();
        reader.read_to_end(&mut rest).await.unwrap();
        assert_eq!(rest, b"rest");
    }

    #[tokio::test]
    async fn too_much_noise_and_other_versions_are_refused() {
        let noise = "baa\n".repeat(MAX_BEFORE_GREETING);
        let stream = [noise.as_bytes(), GREETING].concat();
        let err = await_greeting(&mut BufReader::new(stream.as_slice()))
            .await
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(err.to_string().contains("it said \"baa\""), "{err}");
        // Noise with no newline in it at all.
        let stream = [&vec![b'x'; 2 * MAX_BEFORE_GREETING][..], GREETING].concat();
        let err = await_greeting(&mut BufReader::new(stream.as_slice()))
            .await
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        let err = await_greeting(&mut BufReader::new(&b"motd\n\0musubi2\n"[..]))
            .await
            .unwrap_err();
        assert!(err.to_string().contains("another version"), "{err}");
        let err = await_greeting(&mut BufReader::new(&b"motd\n"[..]))
            .await
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);
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
