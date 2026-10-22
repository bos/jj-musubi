//! Local sockets that only their owner can reach: a Unix domain socket, or a named pipe on
//! Windows. The daemon's control socket is one (see [`crate::control`]). So is the socket a
//! hub listens on, in its directory, which `musubi hub connect` relays to and commands on
//! the hub's machine connect to.
//!
//! A Unix socket's directory must belong to the user and be writable by no one else, or
//! nothing listens there and nothing connects, as tmux and ssh-agent check theirs, so that
//! nobody else can put a socket of their own in its place. A named pipe admits only its
//! owner, and is created as the pipe's first instance, so it can't be listened on if
//! someone else has taken the name.

use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::Context as _;
use interprocess::local_socket::GenericFilePath;
use interprocess::local_socket::ListenerOptions;
use interprocess::local_socket::tokio::Listener;
use interprocess::local_socket::tokio::Stream;
use interprocess::local_socket::tokio::prelude::*;

/// Where a local socket is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Socket {
    Path(PathBuf),
    /// A Windows named pipe, `\\.\pipe\<name>`.
    Pipe(String),
}

impl std::fmt::Display for Socket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Path(path) => write!(f, "{}", path.display()),
            Self::Pipe(name) => write!(f, r"\\.\pipe\{name}"),
        }
    }
}

impl Socket {
    /// The socket written as `socket`: a path, or on Windows, a pipe's name.
    pub fn named(socket: &str) -> Self {
        if cfg!(windows) {
            let name = socket.strip_prefix(r"\\.\pipe\").unwrap_or(socket);
            Self::Pipe(name.to_owned())
        } else {
            Self::Path(PathBuf::from(socket))
        }
    }

    /// The socket the hub serving `dir`, an absolute path, listens on: in the directory
    /// itself, where no temp cleaner, or the end of a login, removes it.
    pub fn hub(dir: &Path) -> Self {
        if cfg!(windows) {
            // However the directory is spelled: its case, a mapped drive, and the rest.
            let dir = std::fs::canonicalize(dir).unwrap_or_else(|_| dir.to_owned());
            let hash = fnv(dir.to_string_lossy().as_bytes());
            Self::Pipe(format!("musubi-hub-{hash:016x}"))
        } else {
            Self::Path(dir.join("run/hub.sock"))
        }
    }

    /// How much longer a Unix socket's path is than fits in `sockaddr_un`, if it is.
    pub fn too_long(&self) -> Option<usize> {
        let Self::Path(path) = self else {
            return None;
        };
        let limit = if cfg!(target_os = "linux") { 107 } else { 103 };
        path.as_os_str()
            .len()
            .checked_sub(limit)
            .filter(|&over| over > 0)
    }

    fn name(&self) -> std::io::Result<interprocess::local_socket::Name<'static>> {
        match self {
            Self::Path(path) => path.clone().to_fs_name::<GenericFilePath>(),
            Self::Pipe(name) => format!(r"\\.\pipe\{name}").to_fs_name::<GenericFilePath>(),
        }
    }

    /// Binds the socket. The caller holds a lock that keeps anyone else listening here, so
    /// any socket file is one left behind by a process that died.
    pub fn listen(&self) -> anyhow::Result<Listener> {
        if let Self::Path(path) = self {
            if let Some(dir) = path.parent() {
                create_private_dir(dir)?;
                check_private_dir(dir)?;
            }
            match std::fs::remove_file(path) {
                Ok(()) => tracing::info!("removed a stale socket {}", path.display()),
                Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
                Err(err) => return Err(err).with_context(|| format!("removing {path:?}")),
            }
        }
        let options = ListenerOptions::new().name(self.name()?);
        #[cfg(windows)]
        let options = {
            use interprocess::os::windows::local_socket::ListenerOptionsExt as _;
            use interprocess::os::windows::security_descriptor::SecurityDescriptor;
            // Full access for the pipe's owner and the system, and no one else.
            let sddl = widestring::u16cstr!("D:P(A;;GA;;;OW)(A;;GA;;;SY)");
            options.security_descriptor(SecurityDescriptor::deserialize(sddl)?)
        };
        options
            .create_tokio()
            .with_context(|| format!("listening on {self}"))
    }

    /// Connects to what listens on the socket, or returns `None` if nothing does.
    pub async fn connect_stream(&self) -> anyhow::Result<Option<Stream>> {
        if let Self::Path(path) = self
            && let Some(dir) = path.parent()
            && dir.exists()
        {
            check_private_dir(dir)?;
        }
        match Stream::connect(self.name()?).await {
            Ok(stream) => Ok(Some(stream)),
            Err(err)
                if matches!(
                    err.kind(),
                    std::io::ErrorKind::NotFound | std::io::ErrorKind::ConnectionRefused
                ) =>
            {
                Ok(None)
            }
            Err(err) => Err(err).with_context(|| format!("connecting to {self}")),
        }
    }
}

/// The next connection to `listener`. One that can't be accepted, as when the process is
/// out of file descriptors, is logged, and the next tried a moment later: at once, the
/// same failure would spin.
pub async fn accept(listener: &Listener) -> Stream {
    loop {
        match listener.accept().await {
            Ok(stream) => return stream,
            Err(err) => {
                tracing::warn!("accepting a connection: {err}");
                tokio::time::sleep(Duration::from_millis(100)).await;
            }
        }
    }
}

#[cfg(unix)]
fn create_private_dir(dir: &Path) -> anyhow::Result<()> {
    use std::os::unix::fs::DirBuilderExt as _;
    std::fs::DirBuilder::new()
        .recursive(true)
        .mode(0o700)
        .create(dir)
        .with_context(|| format!("creating {dir:?}"))
}

/// Fails unless `dir` is a directory, not a symbolic link, that belongs to this user and
/// that no one else can write to.
#[cfg(unix)]
fn check_private_dir(dir: &Path) -> anyhow::Result<()> {
    use std::os::unix::fs::MetadataExt as _;
    let metadata = std::fs::symlink_metadata(dir).with_context(|| format!("checking {dir:?}"))?;
    let uid = uid()?;
    anyhow::ensure!(
        metadata.is_dir() && metadata.uid() == uid && metadata.mode() & 0o022 == 0,
        "{} is not a private directory of this user's (it must be owned by uid {uid}, not a \
         symbolic link, and writable by no one else), so its sockets can't be trusted; remove \
         it, or for the daemon's socket, choose another place with MUSUBI_SOCKET",
        dir.display()
    );
    Ok(())
}

#[cfg(not(unix))]
fn check_private_dir(_: &Path) -> anyhow::Result<()> {
    Ok(())
}

#[cfg(not(unix))]
fn create_private_dir(dir: &Path) -> anyhow::Result<()> {
    std::fs::create_dir_all(dir).with_context(|| format!("creating {dir:?}"))
}

#[cfg(unix)]
pub fn uid() -> anyhow::Result<u32> {
    use std::os::unix::fs::MetadataExt as _;
    // This process's own entry is owned by its user (Linux), and so is a file it creates.
    if let Ok(metadata) = std::fs::metadata("/proc/self") {
        return Ok(metadata.uid());
    }
    let probe = tempfile::NamedTempFile::new()?;
    Ok(probe.as_file().metadata()?.uid())
}

#[cfg(not(unix))]
pub fn uid() -> anyhow::Result<u32> {
    Ok(0)
}

/// FNV-1a, for naming a socket or pipe after a directory.
pub fn fnv(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |hash, &byte| {
        (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
    })
}

#[cfg(all(test, unix))]
mod tests {
    use std::os::unix::fs::PermissionsExt as _;

    use super::*;

    #[test]
    fn sockets_live_only_in_private_directories() {
        let root = tempfile::tempdir().unwrap();
        let dir = root.path().join("musubi");
        create_private_dir(&dir).unwrap();
        check_private_dir(&dir).unwrap();
        // Writable by others: someone else could swap in a socket of their own.
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o777)).unwrap();
        assert!(check_private_dir(&dir).is_err());
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        // A symbolic link could point anywhere.
        let link = root.path().join("link");
        std::os::unix::fs::symlink(&dir, &link).unwrap();
        assert!(check_private_dir(&link).is_err());
    }
}
