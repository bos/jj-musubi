//! The daemon's control socket: how commands reach the one daemon each user runs.
//!
//! JSON messages over a local socket: a Unix domain socket, or a named pipe on Windows, with
//! the framing, greeting and request timeouts that the hub's connections have
//! ([`musubi_transport::stream`]). The socket is, in order of preference, `--socket`,
//! `$MUSUBI_SOCKET`, `musubi.daemon.socket` in jj's config, or else:
//!
//! - `$MUSUBI_STATE_DIR/daemon.sock` when that is set (a pipe named after the directory on
//!   Windows);
//! - Linux: `$XDG_RUNTIME_DIR/musubi/daemon.sock`, or `/tmp/musubi-<uid>/daemon.sock`;
//! - macOS: `$TMPDIR/musubi/daemon.sock`;
//! - Windows: `\\.\pipe\musubi-<user>`.
//!
//! Only the user may reach the daemon (see [`crate::socket`]).
//!
//! A socket chosen by a setting must be absolute, or start with `~/`, so that commands run
//! anywhere find the same daemon. Without one, commands use the socket that this machine's
//! daemon, if one runs, says it listens on, wherever they run: its usual place depends on
//! the environment, which differs under cron, `sudo -u`, or in a container.
//!
//! A lock file in the state directory keeps a second daemon from starting there, whatever its
//! socket ([`crate::daemon::Running`]); the daemon holding it removes any socket a crashed one
//! left behind. (Not beside the socket: temp cleaners would delete it there.)
//!
//! # Protocol
//!
//! A command connects, and the daemon greets it as a hub greets a machine. The command sends
//! [`Request`]s on one subject, `SUBJECT`, and the daemon answers each with a [`Response`].
//! Both travel as JSON, in an object that names first the [`VERSION`] of the build that sent
//! it, as the hub's `Envelope` does: `{"control": "0.47.0/control-6", "body": ...}`. A message
//! of another build is never read past that name, so builds tell each other apart whatever
//! else changed, and none may change how that is written. The one request every build obeys
//! is [`Request::Stop`], written `"Stop"`, so that `musubi daemon restart` works across
//! builds.
//!
//! A daemon writes its [`VERSION`] beside its process id ([`crate::daemon::Running`]), so a
//! command knows at once that the daemon is of another build, without connecting. One from
//! before this protocol, which spoke tarpc, wrote none, and never greets. Either fails with
//! [`OtherBuild`], which says "another build", or "an earlier build" for one that named none.
//! The command that reports it says how to restart the daemon, or for one from before this
//! protocol, that it is to be ended by hand. A daemon that doesn't greet within `HANDSHAKE` is
//! only [`Unresponsive`], as a busy one is: the pid file is what tells it from one of another
//! build.
//!
//! # Timeouts
//!
//! Each call says how long it waits for the answer, as each tarpc request's deadline did.
//! `add` and `sync` return once the copy has synced, so commands wait [`SYNC_LIMIT`] for
//! them, an hour, as they did before. The transport waits no longer than that for a request
//! whatever the caller asks, so it never cuts one off before its caller would. A connection
//! has no timeout of its own, and one that is idle stays open. The daemon drops a request only
//! when its deadline passes, as tarpc's server did. A command that gives up sooner, or goes
//! away, leaves its request running to the end: it is the same work that the next command
//! would ask for, and `add` finishes what it started whatever happens to its caller.

use std::io;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::task::Context;
use std::task::Poll;
use std::time::Duration;
use std::time::Instant;

use anyhow::Context as _;
use async_trait::async_trait;
use bytes::Bytes;
use interprocess::local_socket::tokio::Stream;
use musubi_sync::progress::Activity;
use musubi_transport::MemoryNetwork;
use musubi_transport::MemoryTransport;
use musubi_transport::Message;
use musubi_transport::StreamTransport;
use musubi_transport::Transport;
use musubi_transport::TransportError;
use musubi_transport::stream::Connector;
use musubi_transport::stream::Reader;
use musubi_transport::stream::WhileDisconnected;
use musubi_transport::stream::Writer;
use serde::Deserialize;
use serde::Serialize;
use serde::de::DeserializeOwned;
use tokio::io::AsyncRead;
use tokio::io::ReadBuf;
use tokio::sync::Notify;

use crate::config;
use crate::config::Settings;
use crate::daemon::Status;
use crate::socket::Socket;
use crate::socket::fnv;
use crate::socket::uid;

/// Changes whenever the control protocol does, or how commands find the daemon (its lock and
/// the file beside it), so that a command and a daemon from different builds notice each
/// other.
pub const VERSION: &str = concat!(env!("CARGO_PKG_VERSION"), "/control-6");

/// The subject of every request to the daemon.
const SUBJECT: &str = "musubi.daemon.rpc";

/// The largest message either side sends: what tarpc's codec took.
const MAX_PAYLOAD: usize = 8 << 20;

/// How long a command waits for a daemon to greet it before giving up on it. A daemon of this
/// protocol greets as soon as it accepts the connection, in milliseconds, over a socket on the
/// same machine: two seconds is long enough for one that is busy, and short enough not to be
/// felt by a command that has found one that never greets.
const HANDSHAKE: Duration = Duration::from_secs(2);

/// How long to wait for `add` and `sync`, which return only once the copy has synced. The
/// transport waits no longer for a request, whatever it is asked.
pub const SYNC_LIMIT: Duration = Duration::from_secs(3600);

/// What one repository's sync reached: the hub's head.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Synced {
    pub seq: u64,
    pub head: String,
}

/// One repository the daemon serves.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RepoStatus {
    /// The copy's machine key.
    pub key: String,
    pub status: Status,
}

/// What a command asks of the daemon. Each is answered with the [`Response`] of its name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Request {
    /// The daemon's [`VERSION`].
    Version,
    /// Starts serving a repository now, starting over if it serves it already, and returns
    /// once it has synced (or failed to: it keeps trying).
    /// The copy is the one state.toml's entry for its machine key names.
    Add {
        key: String,
    },
    /// Stops serving a copy, by its machine key.
    Remove {
        key: String,
    },
    /// Syncs a copy the daemon serves now, by its machine key.
    Sync {
        key: String,
    },
    /// What a copy's sync is doing, by its machine key, if the daemon serves it.
    Progress {
        key: String,
    },
    Status,
    /// Stops the daemon.
    Stop,
}

/// What the daemon answers.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Response {
    Version(String),
    Add(Result<Synced, String>),
    Remove(Result<(), String>),
    Sync(Result<Synced, String>),
    Progress(Option<Activity>),
    Status(Vec<RepoStatus>),
    Stop,
    /// The daemon couldn't take the request at all, as for one it couldn't read.
    Error(String),
}

/// The daemon of another build, or something else that doesn't speak this protocol: told
/// apart from a daemon of this build by the [`VERSION`] its pid file or its answers name, or
/// by a greeting that isn't this transport's. Not by being slow to greet ([`Unresponsive`]).
#[derive(Debug)]
pub struct OtherBuild(
    /// The daemon's [`VERSION`], if it said.
    pub Option<String>,
);

/// The release a [`VERSION`] is of, without the tag after it that changes with the protocol,
/// which users have no use for.
fn release(version: &str) -> &str {
    version
        .split_once('/')
        .map_or(version, |(release, _)| release)
}

impl std::fmt::Display for OtherBuild {
    /// Names the daemon's release only if it isn't this one, since a build of the same release
    /// may differ all the same.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ours = env!("CARGO_PKG_VERSION");
        match self
            .0
            .as_deref()
            .map(release)
            .filter(|theirs| *theirs != ours)
        {
            Some(theirs) => write!(
                f,
                "the running daemon is musubi {theirs}, but this is {ours}"
            ),
            // One that names no build predates the protocol: its pid file says none, or it
            // doesn't greet as this transport's daemons do.
            None if self.0.is_none() => {
                write!(f, "the running daemon is from an earlier build of musubi")
            }
            None => write!(f, "the running daemon is from another build of musubi"),
        }
    }
}

impl std::error::Error for OtherBuild {}

/// A daemon that took the connection, but didn't greet, or answer, in time: busy, say. It is
/// not known to be of another build.
#[derive(Debug)]
pub struct Unresponsive;

impl std::fmt::Display for Unresponsive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "the daemon did not answer in time")
    }
}

impl std::error::Error for Unresponsive {}

/// What a message is wrapped in.
#[derive(Serialize)]
struct Sealed<'a, T> {
    control: &'a str,
    body: &'a T,
}

/// The start of a message, the same in every build.
#[derive(Deserialize)]
struct Header {
    control: String,
}

#[derive(Deserialize)]
struct Opened<T> {
    body: T,
}

/// `body`, as a message from the build `version`.
fn seal_as<T: Serialize>(version: &str, body: &T) -> anyhow::Result<Bytes> {
    let sealed = Sealed {
        control: version,
        body,
    };
    Ok(serde_json::to_vec(&sealed)?.into())
}

fn seal<T: Serialize>(body: &T) -> anyhow::Result<Bytes> {
    seal_as(VERSION, body)
}

/// The body of a message, if it is from this build: [`OtherBuild`] if it is from another, or
/// isn't a message of the protocol at all.
fn open<T: DeserializeOwned>(bytes: &[u8]) -> anyhow::Result<T> {
    let Ok(header) = serde_json::from_slice::<Header>(bytes) else {
        return Err(OtherBuild(None).into());
    };
    if header.control != VERSION {
        return Err(OtherBuild(Some(header.control)).into());
    }
    let opened: Opened<T> = serde_json::from_slice(bytes).context("couldn't read the message")?;
    Ok(opened.body)
}

/// A client's request as the daemon reads it: the request, or what to answer instead. A
/// request from another build is refused, but for [`Request::Stop`], which every build obeys.
fn read_request(bytes: &[u8]) -> Result<Request, Response> {
    let err = match open(bytes) {
        Ok(request) => return Ok(request),
        Err(err) => err,
    };
    Err(Response::Error(match err.downcast_ref::<OtherBuild>() {
        Some(OtherBuild(Some(_))) => {
            let stop = serde_json::from_slice::<Opened<String>>(bytes)
                .is_ok_and(|opened| opened.body == "Stop");
            if stop {
                return Ok(Request::Stop);
            }
            // As the command will say of it. (The answer is sealed with this build's version,
            // so a command of another build reads it as that, and never sees this text.)
            OtherBuild(Some(VERSION.to_owned())).to_string()
        }
        Some(OtherBuild(None)) => "the daemon couldn't read the request".to_owned(),
        None => {
            tracing::debug!("a request that couldn't be read: {err:#}");
            "the daemon couldn't read the request".to_owned()
        }
    }))
}

/// Answers the requests that arrive on the control socket's connections, each with what
/// `answer` makes of it, and returns what [`serve`] relays the connections to.
pub async fn service<A, F>(answer: A) -> anyhow::Result<Arc<dyn Transport>>
where
    A: Fn(Request) -> F + Send + Sync + 'static,
    F: Future<Output = Response> + Send + 'static,
{
    let network = MemoryNetwork::new(0, MAX_PAYLOAD);
    let service = Arc::new(network.connect());
    let mut requests = service.subscribe(SUBJECT).await?;
    let answer = Arc::new(answer);
    tokio::spawn(async move {
        while let Some(request) = requests.next().await {
            let (service, answer) = (service.clone(), answer.clone());
            // Each on a task of its own: a sync takes as long as it takes.
            tokio::spawn(async move { respond(&service, &*answer, request).await });
        }
    });
    Ok(Arc::new(network.connect()))
}

/// Answers one request, unless whoever sent it has given up waiting by the time it is done.
async fn respond<A, F>(service: &MemoryTransport, answer: &A, request: Message)
where
    A: Fn(Request) -> F,
    F: Future<Output = Response>,
{
    let Some(inbox) = request.reply.clone() else {
        return;
    };
    let answered = async {
        match read_request(&request.payload) {
            Ok(asked) => answer(asked).await,
            Err(refusal) => refusal,
        }
    };
    let response = match request.deadline {
        Some(deadline) => {
            let left = deadline.saturating_duration_since(Instant::now());
            match tokio::time::timeout(left, answered).await {
                Ok(response) => response,
                Err(_) => return,
            }
        }
        None => answered.await,
    };
    let failed = |why: String| seal(&Response::Error(why)).unwrap_or_default();
    let payload = match seal(&response) {
        Ok(payload) if payload.len() <= MAX_PAYLOAD => payload,
        Ok(_) => failed("the daemon's answer is too large to send".to_owned()),
        Err(err) => {
            tracing::debug!("an answer that couldn't be written: {err:#}");
            failed("the daemon couldn't write its answer".to_owned())
        }
    };
    if let Err(err) = service.publish(&inbox, payload).await {
        tracing::debug!("answering a command: {err}");
    }
}

/// Serves one connection to the control socket, through the transport [`service`] returned,
/// until either side closes it.
pub async fn serve(transport: Arc<dyn Transport>, stream: Stream) {
    let (reader, writer) = tokio::io::split(stream);
    if let Err(err) = musubi_transport::stream::serve(transport, reader, writer).await {
        tracing::debug!("a connection to the control socket ended: {err}");
    }
}

/// A connection to the daemon's control socket: the daemon's operations, as calls that each
/// say how long to wait for the answer. Connects again whenever the daemon closes the
/// connection; a call that finds it gone fails.
#[derive(Clone)]
pub struct ControlClient {
    transport: Arc<StreamTransport>,
}

impl ControlClient {
    /// Connects through `connector`. Fails with [`Unresponsive`] if what answers doesn't greet
    /// within [`HANDSHAKE`], which a busy daemon of this build may not, and with [`OtherBuild`]
    /// if its greeting isn't a musubi hub's of this transport. Returns `None`, as for no
    /// daemon, if the connection ends before the daemon has said anything: as one stopping, or
    /// starting over, closes it, which isn't one of another build.
    async fn over(connector: Arc<dyn Connector>) -> anyhow::Result<Option<Self>> {
        let closed = Arc::new(Notify::new());
        let connector = Arc::new(Watched {
            connector,
            closed: closed.clone(),
        });
        let connecting = StreamTransport::connect_with(connector, WhileDisconnected::NextAttempt);
        // Not the transport's own attempts, which retry after a pause.
        tokio::select! {
            () = closed.notified() => {
                tracing::debug!("the daemon closed the connection before it greeted");
                Ok(None)
            }
            connected = tokio::time::timeout(HANDSHAKE, connecting) => match connected {
                Ok(Ok(transport)) => Ok(Some(Self {
                    transport: Arc::new(transport),
                })),
                // Greeted as no daemon of this build does: the one way the transport gives up
                // on a connection before the timeout.
                Ok(Err(TransportError::Other(err))) => {
                    tracing::debug!("not a daemon of this build: {err}");
                    Err(OtherBuild(None).into())
                }
                Ok(Err(err)) => {
                    tracing::debug!("the daemon's connection failed before it greeted: {err}");
                    Err(Unresponsive.into())
                }
                Err(_) => {
                    tracing::debug!("the daemon did not greet within {HANDSHAKE:?}");
                    Err(Unresponsive.into())
                }
            },
        }
    }

    async fn call(&self, request: Request, limit: Duration) -> anyhow::Result<Response> {
        let reply = self
            .transport
            .request(SUBJECT, seal(&request)?, limit)
            .await
            .map_err(|err| match err {
                TransportError::Timeout => anyhow::Error::from(Unresponsive),
                TransportError::Disconnected => {
                    anyhow::anyhow!("lost the connection to the daemon")
                }
                err => anyhow::anyhow!("asking the daemon: {err}"),
            })?;
        let response = open::<Response>(&reply).map_err(|err| {
            if err.is::<OtherBuild>() {
                return err;
            }
            tracing::debug!("an answer that couldn't be read: {err:#}");
            anyhow::anyhow!("the daemon's answer couldn't be read")
        })?;
        match response {
            // Each says what went wrong in a line of its own.
            Response::Error(message) => anyhow::bail!("{message}"),
            response => Ok(response),
        }
    }

    /// Fails if the daemon is of another build, whose [`VERSION`] every answer names.
    pub async fn check(&self, limit: Duration) -> anyhow::Result<()> {
        match self.call(Request::Version, limit).await? {
            Response::Version(_) => Ok(()),
            other => Err(unexpected(&other)),
        }
    }

    /// [`Request::Add`], waiting `limit` for it ([`SYNC_LIMIT`], for a sync that takes long).
    pub async fn add(
        &self,
        key: String,
        limit: Duration,
    ) -> anyhow::Result<Result<Synced, String>> {
        match self.call(Request::Add { key }, limit).await? {
            Response::Add(result) => Ok(result),
            other => Err(unexpected(&other)),
        }
    }

    /// [`Request::Remove`].
    pub async fn remove(&self, key: String, limit: Duration) -> anyhow::Result<Result<(), String>> {
        match self.call(Request::Remove { key }, limit).await? {
            Response::Remove(result) => Ok(result),
            other => Err(unexpected(&other)),
        }
    }

    /// [`Request::Sync`], waiting `limit` for it ([`SYNC_LIMIT`], for a sync that takes long).
    pub async fn sync(
        &self,
        key: String,
        limit: Duration,
    ) -> anyhow::Result<Result<Synced, String>> {
        match self.call(Request::Sync { key }, limit).await? {
            Response::Sync(result) => Ok(result),
            other => Err(unexpected(&other)),
        }
    }

    /// [`Request::Progress`].
    pub async fn progress(&self, key: String, limit: Duration) -> anyhow::Result<Option<Activity>> {
        match self.call(Request::Progress { key }, limit).await? {
            Response::Progress(activity) => Ok(activity),
            other => Err(unexpected(&other)),
        }
    }

    /// [`Request::Status`].
    pub async fn status(&self, limit: Duration) -> anyhow::Result<Vec<RepoStatus>> {
        match self.call(Request::Status, limit).await? {
            Response::Status(statuses) => Ok(statuses),
            other => Err(unexpected(&other)),
        }
    }

    /// [`Request::Stop`], which a daemon of any build obeys. It may be gone before it answers.
    pub async fn stop(&self, limit: Duration) -> anyhow::Result<()> {
        match self.call(Request::Stop, limit).await {
            // Answered as another build's, which stops all the same.
            Err(err) if err.is::<OtherBuild>() => Ok(()),
            Ok(Response::Stop) => Ok(()),
            Ok(other) => Err(unexpected(&other)),
            Err(err) => Err(err),
        }
    }
}

fn unexpected(response: &Response) -> anyhow::Error {
    tracing::debug!("an answer to another request: {response:?}");
    anyhow::anyhow!("the daemon answered another request")
}

/// What a [`ControlClient`] connects through: `connector`'s connections, each of which says
/// when it ends before the daemon on it has sent anything, and so before it could greet.
struct Watched {
    connector: Arc<dyn Connector>,
    closed: Arc<Notify>,
}

#[async_trait]
impl Connector for Watched {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        let (reader, writer) = self.connector.connect().await?;
        let reader = Silent {
            reader,
            heard: false,
            closed: self.closed.clone(),
        };
        Ok((Box::new(reader), writer))
    }

    fn not_hub(&self, why: &io::Error) {
        self.connector.not_hub(why);
    }
}

/// A reader that notifies `closed` if it ends, or fails, before it has read anything.
struct Silent {
    reader: Reader,
    heard: bool,
    closed: Arc<Notify>,
}

impl AsyncRead for Silent {
    fn poll_read(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let before = buf.filled().len();
        let polled = Pin::new(&mut self.reader).poll_read(cx, buf);
        if !self.heard && !matches!(polled, Poll::Pending) {
            if matches!(polled, Poll::Ready(Ok(()))) && buf.filled().len() > before {
                self.heard = true;
            } else {
                self.closed.notify_one();
            }
        }
        polled
    }
}

/// Opens connections to the daemon on `socket`, for a [`ControlClient`].
struct Dial {
    socket: Socket,
    /// The first connection, opened to see that a daemon is there.
    first: Mutex<Option<Stream>>,
}

#[async_trait]
impl Connector for Dial {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        let first = self
            .first
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        let stream = match first {
            Some(stream) => stream,
            None => self
                .socket
                .connect_stream()
                .await
                .map_err(io::Error::other)?
                .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "no daemon listens"))?,
        };
        let (reader, writer) = tokio::io::split(stream);
        Ok((Box::new(reader), Box::new(writer)))
    }
}

impl Socket {
    /// The socket to use, given `--socket` (or `MUSUBI_SOCKET`, which clap reads for it).
    pub fn locate(given: Option<&str>) -> anyhow::Result<Self> {
        let chosen = match given {
            Some(socket) => Some(socket.to_owned()),
            None => match std::env::var("MUSUBI_SOCKET") {
                Ok(socket) if !socket.is_empty() => Some(socket),
                _ => Settings::load()?.daemon_socket,
            },
        };
        let socket = match chosen {
            Some(socket) => Self::chosen(&socket)?,
            // Where this machine's daemon listens, if it runs: started where the usual place
            // is another, as from cron, or after `sudo -u`, without `XDG_RUNTIME_DIR`.
            None => match crate::daemon::Running::find()?.and_then(|running| running.socket) {
                Some(socket) => socket,
                None => Self::usual()?,
            },
        };
        socket.check()?;
        Ok(socket)
    }

    /// The socket a user chose: a path, absolute or starting with `~/`, the same from
    /// every directory; or on Windows, a pipe's name.
    fn chosen(socket: &str) -> anyhow::Result<Self> {
        let named = Self::named(socket);
        let Self::Path(path) = &named else {
            return Ok(named);
        };
        if let Some(rest) = socket.strip_prefix("~/") {
            let home = etcetera::home_dir().context("no home directory to put the socket in")?;
            return Ok(Self::Path(home.join(rest)));
        }
        anyhow::ensure!(
            path.is_absolute(),
            "the daemon's socket {socket} is a relative path; give an absolute one, or one starting \
             with ~/"
        );
        Ok(named)
    }

    fn usual() -> anyhow::Result<Self> {
        if std::env::var_os("MUSUBI_STATE_DIR").is_some() {
            let dir = config::state_dir()?;
            return Ok(if cfg!(windows) {
                Self::Pipe(format!(
                    "musubi-{:016x}",
                    fnv(dir.to_string_lossy().as_bytes())
                ))
            } else {
                Self::Path(dir.join("daemon.sock"))
            });
        }
        if cfg!(windows) {
            let user = std::env::var("USERNAME").unwrap_or_else(|_| "user".to_owned());
            return Ok(Self::Pipe(format!("musubi-{user}")));
        }
        let runtime = if cfg!(target_os = "macos") {
            std::env::var_os("TMPDIR")
        } else {
            std::env::var_os("XDG_RUNTIME_DIR")
        };
        let dir = match runtime {
            Some(dir) if !dir.is_empty() => PathBuf::from(dir).join("musubi"),
            _ => std::env::temp_dir().join(format!("musubi-{}", uid()?)),
        };
        Ok(Self::Path(dir.join("daemon.sock")))
    }

    /// Unix sockets' paths are limited to what fits in `sockaddr_un`.
    fn check(&self) -> anyhow::Result<()> {
        if let Some(over) = self.too_long() {
            anyhow::bail!(
                "the daemon's socket path {self} is {over} bytes too long; set a shorter one with \
                 MUSUBI_SOCKET or musubi.daemon.socket"
            );
        }
        Ok(())
    }

    /// Connects to a running daemon, or returns `None` if there is none, or the one that
    /// listens closes the connection before it greets, as when it stops. Fails with
    /// [`OtherBuild`] if what listens doesn't greet as a daemon of this protocol does. It
    /// takes a call to learn whether it is of this build ([`ControlClient::check`]).
    pub async fn connect(&self) -> anyhow::Result<Option<ControlClient>> {
        let Some(stream) = self.connect_stream().await? else {
            return Ok(None);
        };
        let dial = Dial {
            socket: self.clone(),
            first: Mutex::new(Some(stream)),
        };
        ControlClient::over(Arc::new(dial)).await
    }
}

#[cfg(test)]
mod tests {
    use tokio::io::DuplexStream;
    use tokio::time::Instant as TokioInstant;

    use super::*;

    /// What another build calls itself, in the messages it sends.
    const ELSEWHERE: &str = "0.0.1/control-1";

    /// A build of this release, from before the protocol last changed.
    const EARLIER: &str = concat!(env!("CARGO_PKG_VERSION"), "/control-0");

    const ANOTHER: &str = "the running daemon is from another build of musubi";

    /// What a command says of a daemon that names no build.
    const EARLIER_BUILD: &str = "the running daemon is from an earlier build of musubi";

    /// A connector with one connection, which is all a test makes.
    struct Once(Mutex<Option<DuplexStream>>);

    #[async_trait]
    impl Connector for Once {
        async fn connect(&self) -> io::Result<(Reader, Writer)> {
            let stream = (self.0.lock().unwrap().take()).ok_or_else(|| io::Error::other("used"))?;
            let (reader, writer) = tokio::io::split(stream);
            Ok((Box::new(reader), Box::new(writer)))
        }
    }

    /// Serves a connection through `transport`, and returns a connector for the other end.
    fn connect_to(transport: Arc<dyn Transport>) -> Arc<dyn Connector> {
        let (near, far) = tokio::io::duplex(64 * 1024);
        tokio::spawn(async move {
            let (reader, writer) = tokio::io::split(far);
            musubi_transport::stream::serve(transport, reader, writer)
                .await
                .ok();
        });
        Arc::new(Once(Mutex::new(Some(near))))
    }

    async fn client_of<A, F>(answer: A) -> ControlClient
    where
        A: Fn(Request) -> F + Send + Sync + 'static,
        F: Future<Output = Response> + Send + 'static,
    {
        let transport = service(answer).await.unwrap();
        ControlClient::over(connect_to(transport))
            .await
            .unwrap()
            .unwrap()
    }

    /// A service that answers every request as the build `version` would, whatever it says.
    async fn build_of(version: &'static str) -> Arc<dyn Transport> {
        let network = MemoryNetwork::new(0, MAX_PAYLOAD);
        let service = network.connect();
        let mut requests = service.subscribe(SUBJECT).await.unwrap();
        tokio::spawn(async move {
            while let Some(request) = requests.next().await {
                let answer = seal_as(version, &Response::Version(version.to_owned())).unwrap();
                service
                    .publish(&request.reply.unwrap(), answer)
                    .await
                    .unwrap();
            }
        });
        Arc::new(network.connect())
    }

    const SECOND: Duration = Duration::from_secs(1);

    /// Each operation reaches the daemon as itself, and its answer comes back as its own.
    #[tokio::test]
    async fn every_operation_gets_its_own_answer() {
        let client = client_of(|request| async move {
            match request {
                Request::Version => Response::Version(VERSION.to_owned()),
                Request::Add { key } => Response::Add(Ok(Synced { seq: 7, head: key })),
                Request::Remove { key } => Response::Remove(Err(key)),
                Request::Sync { key } => Response::Sync(Err(key)),
                Request::Progress { .. } => Response::Progress(Some(Activity::default())),
                Request::Status => Response::Status(vec![RepoStatus {
                    key: "k".to_owned(),
                    status: Status::default(),
                }]),
                Request::Stop => Response::Stop,
            }
        })
        .await;
        client.check(SECOND).await.unwrap();
        let added = client.add("a".to_owned(), SECOND).await.unwrap().unwrap();
        assert_eq!((added.seq, added.head.as_str()), (7, "a"));
        assert_eq!(
            client.remove("r".to_owned(), SECOND).await.unwrap(),
            Err("r".to_owned())
        );
        assert_eq!(
            client
                .sync("s".to_owned(), SECOND)
                .await
                .unwrap()
                .unwrap_err(),
            "s"
        );
        assert_eq!(
            client.progress("p".to_owned(), SECOND).await.unwrap(),
            Some(Activity::default())
        );
        let statuses = client.status(SECOND).await.unwrap();
        assert_eq!(statuses.len(), 1);
        assert_eq!(statuses[0].key, "k");
        client.stop(SECOND).await.unwrap();
    }

    /// A copy's first sync takes as long as it takes: as with tarpc's deadline, a command
    /// gives up on it after an hour, and not sooner for anything in the transport.
    #[tokio::test(start_paused = true)]
    async fn add_and_sync_wait_as_long_as_the_commands_limit() {
        let client = client_of(|request| async move {
            let (Request::Add { key } | Request::Sync { key }) = request else {
                return Response::Stop;
            };
            // Under the limit, or over it, as the key says.
            let wait = if key == "slow" { 3601 } else { 3599 };
            tokio::time::sleep(Duration::from_secs(wait)).await;
            Response::Add(Ok(Synced { seq: 1, head: key }))
        })
        .await;
        let started = TokioInstant::now();
        client
            .add("fast".to_owned(), SYNC_LIMIT)
            .await
            .unwrap()
            .unwrap();
        assert_eq!(started.elapsed(), Duration::from_secs(3599));
        let err = client.add("slow".to_owned(), SYNC_LIMIT).await.unwrap_err();
        assert_eq!(err.to_string(), "the daemon did not answer in time");
        assert_eq!(started.elapsed(), Duration::from_secs(3599) + SYNC_LIMIT);
        // The connection waited out both without ending: it still answers.
        client
            .add("fast".to_owned(), SYNC_LIMIT)
            .await
            .unwrap()
            .unwrap();
    }

    /// A call's own limit holds, whatever the daemon is doing.
    #[tokio::test(start_paused = true)]
    async fn a_call_gives_up_after_its_limit() {
        let client = client_of(|_| async {
            std::future::pending::<()>().await;
            Response::Stop
        })
        .await;
        let started = TokioInstant::now();
        let err = client.status(Duration::from_secs(10)).await.unwrap_err();
        assert_eq!(err.to_string(), "the daemon did not answer in time");
        assert_eq!(started.elapsed(), Duration::from_secs(10));
    }

    /// A daemon of another build says which, in every answer; the command names the release if
    /// it is another, and never the tag that follows it.
    #[tokio::test]
    async fn a_daemon_of_another_build_is_named() {
        let client = ControlClient::over(connect_to(build_of(ELSEWHERE).await))
            .await
            .unwrap()
            .unwrap();
        let err = client.check(SECOND).await.unwrap_err();
        assert!(matches!(
            err.downcast_ref::<OtherBuild>(),
            Some(OtherBuild(Some(version))) if version == ELSEWHERE
        ));
        assert_eq!(
            err.to_string(),
            format!(
                "the running daemon is musubi 0.0.1, but this is {}",
                env!("CARGO_PKG_VERSION")
            )
        );
        // Stopping it is all that works across builds, and doesn't fail for the mismatch.
        client.stop(SECOND).await.unwrap();
        assert!(client.status(SECOND).await.is_err());
    }

    /// A build of the same release that speaks another protocol is no other release, to a user.
    #[tokio::test]
    async fn a_build_of_this_release_is_not_named_by_release() {
        let client = ControlClient::over(connect_to(build_of(EARLIER).await))
            .await
            .unwrap()
            .unwrap();
        let err = client.check(SECOND).await.unwrap_err();
        assert_eq!(err.to_string(), ANOTHER);
        for other in [OtherBuild(None), OtherBuild(Some(EARLIER.to_owned()))] {
            let said = other.to_string();
            assert!(!said.contains("control") && !said.contains(';'), "{said}");
        }
    }

    /// A daemon that doesn't greet is not waited for longer than `HANDSHAKE`, and isn't taken
    /// for one of another build, which only its pid file or its answers can show: a busy one
    /// greets late. It is said not to have answered in time, as for any call.
    #[tokio::test(start_paused = true)]
    async fn a_daemon_slow_to_greet_is_not_another_build() {
        // Silent, and open: as a daemon too busy to greet is.
        let (near, _far) = tokio::io::duplex(1024);
        let started = TokioInstant::now();
        let err = ControlClient::over(Arc::new(Once(Mutex::new(Some(near)))))
            .await
            .err()
            .unwrap();
        assert_eq!(started.elapsed(), HANDSHAKE);
        assert!(err.is::<Unresponsive>() && !err.is::<OtherBuild>());
        assert_eq!(err.to_string(), "the daemon did not answer in time");
    }

    /// What greets as no musubi daemon does, but not for being slow, is of another build.
    #[tokio::test(start_paused = true)]
    async fn a_greeting_of_another_kind_is_another_build() {
        let (near, mut far) = tokio::io::duplex(1024);
        tokio::spawn(async move {
            use tokio::io::AsyncWriteExt as _;
            // What a hub of another version of the transport greets with.
            far.write_all(b"\0musubi99\n").await.unwrap();
            std::future::pending::<()>().await;
        });
        let err = ControlClient::over(Arc::new(Once(Mutex::new(Some(near)))))
            .await
            .err()
            .unwrap();
        assert!(matches!(
            err.downcast_ref::<OtherBuild>(),
            Some(OtherBuild(None))
        ));
        assert_eq!(err.to_string(), EARLIER_BUILD);
    }

    /// A daemon that closes the connection before it greets is stopping, or starting over,
    /// not of another build: there is none to talk to, at once, and not after the wait for a
    /// greeting.
    #[tokio::test(start_paused = true)]
    async fn a_daemon_that_closes_before_it_greets_is_none() {
        let (near, far) = tokio::io::duplex(1024);
        drop(far);
        let started = TokioInstant::now();
        let client = ControlClient::over(Arc::new(Once(Mutex::new(Some(near)))))
            .await
            .unwrap();
        assert!(client.is_none());
        assert_eq!(started.elapsed(), Duration::ZERO);
    }

    /// A request of another build is refused as another build's, in an answer that names this
    /// daemon's build, as the build that sent it reads it as the daemon of another.
    #[tokio::test]
    async fn a_refusal_of_another_build_says_to_restart() {
        let transport = service(|_| async { Response::Stop }).await.unwrap();
        let request = seal_as(ELSEWHERE, &Request::Status).unwrap();
        let reply = transport.request(SUBJECT, request, SECOND).await.unwrap();
        assert_eq!(
            serde_json::from_slice::<Header>(&reply).unwrap().control,
            VERSION
        );
        assert!(matches!(
            open::<Response>(&reply).unwrap(),
            Response::Error(why) if why == ANOTHER
        ));
    }

    /// Whatever arrives on the socket is a request, or an error: never a panic, and nothing
    /// from another build but `Stop`, which every build obeys.
    #[test]
    fn requests_are_read_by_version_only() {
        let sealed = |version: &str, request: Request| seal_as(version, &request).unwrap();
        let refusal = |bytes: &[u8]| match read_request(bytes) {
            Err(Response::Error(why)) => why,
            other => panic!("{other:?}"),
        };
        assert!(matches!(
            read_request(&sealed(VERSION, Request::Status)),
            Ok(Request::Status)
        ));
        assert!(matches!(
            read_request(&sealed(ELSEWHERE, Request::Stop)),
            Ok(Request::Stop)
        ));
        let another = ANOTHER;
        assert_eq!(refusal(&sealed(ELSEWHERE, Request::Status)), another);
        // As a build that wrote its requests another way would: only its version is read.
        let other = br#"{"control":"0.0.1/control-1","body":{"Frobnicate":[1,2,3]}}"#;
        assert_eq!(refusal(other), another);
        let ours = format!(r#"{{"control":"{VERSION}","body":{{"Frobnicate":[1,2,3]}}}}"#);
        assert_eq!(
            refusal(ours.as_bytes()),
            "the daemon couldn't read the request"
        );
        for garbage in [
            &b""[..],
            b"{",
            b"null",
            b"\0musubi1\n",
            br#"{"control":5,"body":"Stop"}"#,
            br#"{"body":"Stop"}"#,
            b"\xff\xfe",
        ] {
            assert_eq!(
                refusal(garbage),
                "the daemon couldn't read the request",
                "{}",
                String::from_utf8_lossy(garbage)
            );
        }
    }

    /// An answer too large for the transport is an error to the command, not a wait for it
    /// to give up.
    #[tokio::test]
    async fn an_answer_too_large_to_send_is_an_error() {
        let client = client_of(|_| async { Response::Add(Err("x".repeat(MAX_PAYLOAD))) }).await;
        let err = client.add("k".to_owned(), SECOND).await.unwrap_err();
        assert_eq!(err.to_string(), "the daemon's answer is too large to send");
    }
}
