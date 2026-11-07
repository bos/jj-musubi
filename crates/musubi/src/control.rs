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
//! A socket chosen by a setting must be absolute, or start with `~/`, so that commands run
//! anywhere find the same daemon. Without one, commands use the socket that this machine's
//! daemon, if one runs, says it listens on, wherever they run: its usual place depends on
//! the environment, which differs under cron, `sudo -u`, or in a container.
//!
//! A lock file in the state directory keeps a second daemon from starting there, whatever its
//! socket ([`crate::daemon::Running`]); the daemon holding it removes any socket a crashed one
//! left behind. (Not beside the socket: temp cleaners would delete it there.)

use std::path::PathBuf;
use std::time::Duration;
use std::time::Instant;

use anyhow::Context as _;
use interprocess::local_socket::tokio::Stream;
use musubi_sync::progress::Activity;
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

/// Changes whenever the control service does, or how commands find the daemon (its lock and
/// the file beside it), so that a command and a daemon from different builds notice each
/// other.
pub const VERSION: &str = concat!(env!("CARGO_PKG_VERSION"), "/control-4");

/// What a successful sync reached: the hub's head.
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

#[tarpc::service]
pub trait Control {
    /// The daemon's [`VERSION`].
    async fn version() -> String;
    /// Starts serving a repository now, starting over if it serves it already, and returns
    /// once it has synced (or failed to: it keeps trying).
    /// The copy is the one state.toml's entry for its machine key names.
    async fn add(key: String) -> Result<Synced, String>;
    /// Stops serving a copy, by its machine key.
    async fn remove(key: String) -> Result<(), String>;
    /// Syncs a copy the daemon serves now, by its machine key.
    async fn sync(key: String) -> Result<Synced, String>;
    /// What a copy's sync is doing, by its machine key, if the daemon serves it.
    async fn progress(key: String) -> Option<Activity>;
    async fn status() -> Vec<RepoStatus>;
    /// Stops the daemon.
    async fn stop();
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
