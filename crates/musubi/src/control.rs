//! The daemon's control socket: how commands reach the one daemon each user runs.
//!
//! tarpc, with JSON messages, over a local socket: a Unix domain socket, or a named pipe
//! on Windows. The socket is, in order of preference, `--socket`, `$MUSUBI_SOCKET`,
//! `musubi.daemon.socket` in jj's config, or else:
//!
//! - `$MUSUBI_STATE_DIR/daemon.sock` when that is set (a pipe named after the directory on
//!   Windows);
//! - Linux: `$XDG_RUNTIME_DIR/musubi/daemon.sock`, or `/tmp/musubi-<uid>/daemon.sock`;
//! - macOS: `$TMPDIR/musubi/daemon.sock`;
//! - Windows: `\\.\pipe\musubi-<user>`.
//!
//! Only the user may reach the daemon (see [`crate::socket`]).
//!
//! A lock file in the state directory, named after the socket, keeps a second daemon from
//! starting; the daemon holding it removes any socket a crashed one left behind. (Not beside
//! the socket: temp cleaners would delete it there.)

use std::path::PathBuf;
use std::time::Duration;
use std::time::Instant;

use anyhow::Context as _;
use interprocess::local_socket::tokio::Stream;
use serde::Deserialize;
use serde::Serialize;
use tarpc::serde_transport;
use tarpc::tokio_serde::formats::Json;
use tarpc::tokio_util::codec::LengthDelimitedCodec;

use crate::config;
use crate::config::Settings;
use crate::daemon::Status;
use crate::socket::Socket;
use crate::socket::fnv;
use crate::socket::uid;

/// Changes whenever the control service does, so that a command and a daemon from
/// different builds notice each other.
pub const VERSION: &str = concat!(env!("CARGO_PKG_VERSION"), "/control-1");

/// What a successful sync reached: the hub's head.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Synced {
    pub seq: u64,
    pub head: String,
}

/// One repository the daemon serves.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RepoStatus {
    pub workspace: PathBuf,
    pub status: Status,
}

#[tarpc::service]
pub trait Control {
    /// The daemon's [`VERSION`].
    async fn version() -> String;
    /// Starts serving a repository now, and returns once it has synced (or failed to: it
    /// keeps trying).
    async fn add(workspace: PathBuf) -> Result<Synced, String>;
    /// Stops serving a repository.
    async fn remove(workspace: PathBuf) -> Result<(), String>;
    /// Syncs a repository the daemon serves now.
    async fn sync(workspace: PathBuf) -> Result<Synced, String>;
    async fn status() -> Vec<RepoStatus>;
    /// Stops the daemon.
    async fn stop();
}

impl Socket {
    /// The socket to use, given `--socket`.
    pub fn locate(given: Option<&str>) -> anyhow::Result<Self> {
        let chosen = match given {
            Some(socket) => Some(socket.to_owned()),
            None => match std::env::var("MUSUBI_SOCKET") {
                Ok(socket) if !socket.is_empty() => Some(socket),
                _ => Settings::load()?.daemon_socket,
            },
        };
        let socket = match chosen {
            Some(socket) => Self::named(&socket),
            None => Self::usual()?,
        };
        socket.check()?;
        Ok(socket)
    }

    fn usual() -> anyhow::Result<Self> {
        if let Some(dir) = std::env::var_os("MUSUBI_STATE_DIR") {
            let dir = PathBuf::from(dir);
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
                "the daemon's socket path {self} is {over} bytes longer than this system allows; \
                 choose a shorter one with MUSUBI_SOCKET or musubi.daemon.socket in jj's config"
            );
        }
        Ok(())
    }

    /// The lock file a daemon holds while it serves this socket.
    pub fn lock_path(&self) -> anyhow::Result<PathBuf> {
        let name = format!("daemon-{:016x}.lock", fnv(self.to_string().as_bytes()));
        Ok(config::state_dir()?.join(name))
    }

    /// Whether a daemon holds this socket's lock.
    pub fn is_locked(&self) -> anyhow::Result<bool> {
        let path = self.lock_path()?;
        let file = match std::fs::OpenOptions::new().write(true).open(&path) {
            Ok(file) => file,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(false),
            Err(err) => return Err(err).with_context(|| format!("opening {path:?}")),
        };
        Ok(matches!(
            file.try_lock(),
            Err(std::fs::TryLockError::WouldBlock)
        ))
    }

    /// Connects to a running daemon, or returns `None` if there is none.
    pub async fn connect(&self) -> anyhow::Result<Option<ControlClient>> {
        Ok(self.connect_stream().await?.map(client))
    }
}

/// A transport for the control service over a connected stream.
pub fn transport<Item, SinkItem>(
    stream: Stream,
) -> serde_transport::Transport<Stream, Item, SinkItem, Json<Item, SinkItem>>
where
    Item: for<'de> Deserialize<'de>,
    SinkItem: Serialize,
{
    let framed = LengthDelimitedCodec::builder().new_framed(stream);
    serde_transport::new(framed, Json::default())
}

fn client(stream: Stream) -> ControlClient {
    ControlClient::new(tarpc::client::Config::default(), transport(stream)).spawn()
}

/// A request context that waits as long as `limit`: syncs can take a while.
pub fn context(limit: Duration) -> tarpc::context::Context {
    let mut context = tarpc::context::current();
    context.deadline = Instant::now() + limit;
    context
}
