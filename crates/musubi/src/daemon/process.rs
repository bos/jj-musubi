//! Discovering, starting and stopping this machine's daemon process.
//!
//! The process holds its ownership lock through worker shutdown and socket removal. The
//! control server runs under that lock; upgrades restart only after it and the runtime drop.

use std::fs;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::Context as _;

use crate::agent;
use crate::backoff::Backoff;
use crate::config;
use crate::control;
use crate::control::ControlClient;
use crate::login;
use crate::socket::Socket;
use crate::ui::Ui;

/// How large the daemon's log grows before a daemon starting starts it over.
pub(super) const LOG_LIMIT: u64 = 10 << 20;

/// Starts the daemon's (or the hub's) log at `path` over if it has grown large: whether a
/// command started this daemon or launchd did at login, which never would. In place, since
/// whatever started it holds it open to append to: one deleted would take the rest of the log
/// with it.
pub fn trim_log(path: &Path) {
    if fs::metadata(path).is_ok_and(|m| m.len() > LOG_LIMIT)
        && let Ok(file) = fs::OpenOptions::new().write(true).open(path)
    {
        file.set_len(0).ok();
    }
}

/// This machine's daemon, while it runs: it holds a lock on the state directory, whatever
/// socket it listens on, so that only one serves the copies listed there, and beside it says
/// which process it is, where, and where it listens.
pub struct Running {
    pub pid: Option<String>,
    /// `None` for a moment as it starts.
    pub socket: Option<Socket>,
    /// Which processes its pid is among ([`processes`]).
    among: Option<String>,
}

impl Running {
    fn lock_path() -> anyhow::Result<PathBuf> {
        Ok(config::state_dir()?.join("daemon.lock"))
    }

    /// Its process id, its socket, and which processes the id is among, a line each. Not in
    /// the lock file itself, which Windows doesn't let others read while it is locked.
    fn info_path() -> anyhow::Result<PathBuf> {
        Ok(config::state_dir()?.join("daemon.pid"))
    }

    /// This machine's daemon, if one runs. Looking takes a shared lock for a moment, which
    /// others looking at once share, and which a daemon starting at that moment waits out.
    pub fn find() -> anyhow::Result<Option<Self>> {
        let path = Self::lock_path()?;
        let file = match fs::OpenOptions::new().write(true).open(&path) {
            Ok(file) => file,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(err) => return Err(err).with_context(|| format!("opening {path:?}")),
        };
        if !matches!(file.try_lock_shared(), Err(fs::TryLockError::WouldBlock)) {
            return Ok(None);
        }
        let info = fs::read_to_string(Self::info_path()?).unwrap_or_default();
        let mut lines = info.lines().map(str::trim);
        let mut next = || {
            lines
                .next()
                .filter(|line| !line.is_empty())
                .map(str::to_owned)
        };
        Ok(Some(Self {
            pid: next(),
            socket: next().as_deref().map(Socket::named),
            among: next(),
        }))
    }

    /// Takes the lock for a daemon starting, waiting out commands looking for one.
    fn lock() -> anyhow::Result<Option<crate::lock::Lock>> {
        let path = Self::lock_path()?;
        for _ in 0..20 {
            if let Some(lock) = crate::lock::try_lock(&path)? {
                return Ok(Some(lock));
            }
            if Self::find()?.and_then(|running| running.pid).is_some() {
                break;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        Ok(None)
    }

    /// Whether it listens somewhere other than `socket`.
    fn elsewhere(&self, socket: &Socket) -> Option<&Socket> {
        self.socket.as_ref().filter(|theirs| *theirs != socket)
    }

    /// Why no other daemon can start on `socket`.
    fn refusal(&self, socket: &Socket) -> anyhow::Error {
        match self.elsewhere(socket) {
            Some(theirs) => anyhow::anyhow!(
                "this machine's daemon already runs, listening on {theirs}, not {socket}"
            ),
            None => anyhow::anyhow!("this machine's daemon already runs, listening on {socket}"),
        }
    }

    /// Why a command can't reach it on `socket`, its own: as for a moment after a temp
    /// cleaner deletes the socket, until the daemon notices and listens again.
    fn unreachable(&self, socket: &Socket) -> anyhow::Error {
        let pid = self.pid.as_deref().unwrap_or("unknown");
        crate::ui::with_hint(
            anyhow::anyhow!("this machine's daemon (pid {pid}) isn't listening on {socket}"),
            self.remedy(),
        )
    }

    /// Whether this process can stop it when it isn't listening: not from a container
    /// sharing the state directory with a daemon outside it, nor on Windows.
    fn stoppable(&self) -> bool {
        cfg!(unix) && self.among.as_deref() == Some(processes().as_str())
    }

    /// What gets a daemon that isn't listening going again.
    fn remedy(&self) -> &'static str {
        if self.stoppable() {
            "`musubi daemon restart` restarts it."
        } else {
            "Stop it where it runs, then start it again."
        }
    }
}

/// Which processes this one's id is among: on Linux, its pid namespace, which a container has
/// of its own, though it may share the state directory, and so see the lock of a daemon it
/// can't signal. Elsewhere, every process on the machine.
fn processes() -> String {
    fs::read_link("/proc/self/ns/pid")
        .map(|ns| ns.display().to_string())
        .unwrap_or_else(|_| "machine".to_owned())
}

/// What `musubi list` and `musubi status` say of this machine's daemon if it runs, but isn't
/// listening on its socket, which is `socket` unless a service manager chose another.
pub fn unreachable(socket: &Socket) -> Option<String> {
    let running = Running::find().ok()??;
    let pid = running.pid.as_deref().unwrap_or("unknown");
    let socket = running.socket.as_ref().unwrap_or(socket);
    Some(if running.stoppable() {
        format!(
            "running (pid {pid}), but not listening on {socket}; restart it with `musubi daemon \
             restart`"
        )
    } else {
        format!("running (pid {pid}) elsewhere, not listening on {socket}; stop it where it runs")
    })
}

/// Runs the daemon until it is stopped or interrupted.
pub fn run(socket: &Socket) -> anyhow::Result<()> {
    config::create_state_dir()?;
    let lock_path = Running::lock_path()?;
    let Some(lock) = Running::lock()? else {
        return Err(match Running::find()? {
            Some(running) => running.refusal(socket),
            None => anyhow::anyhow!("this machine's daemon already runs"),
        });
    };
    // At once, so that what a daemon that died left there is soon replaced.
    let info_path = Running::info_path()?;
    fs::write(
        &info_path,
        format!("{}\n{socket}\n{}\n", std::process::id(), processes()),
    )?;
    if let Ok(log) = config::daemon_log() {
        trim_log(&log);
    }
    crate::upgrade::started();
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    let result = runtime.block_on(super::server::listen(socket, &lock_path));
    fs::remove_file(&info_path).ok();
    drop(lock);
    drop(runtime);
    match result? {
        Some(exe) => crate::upgrade::restart(exe),
        None => Ok(()),
    }
}

/// Where a service manager runs this machine's daemon on another socket, which the service's
/// environment decides, not the command's, that one; where something else does, an error
/// saying so, rather than `None`, which would have a command go around the daemon.
pub async fn running(socket: &Socket) -> anyhow::Result<Option<ControlClient>> {
    if let Some(client) = running_on(socket).await? {
        return Ok(Some(client));
    }
    let Some(running) = Running::find()? else {
        return Ok(None);
    };
    match running.elsewhere(socket) {
        Some(theirs) if login::managed() => running_on(theirs).await,
        Some(_) => Err(running.refusal(socket)),
        None => Ok(None),
    }
}

/// A daemon that speaks this build's control protocol on `socket`, if there is one.
async fn running_on(socket: &Socket) -> anyhow::Result<Option<ControlClient>> {
    let Some(client) = socket.connect().await? else {
        return Ok(None);
    };
    let version = client
        .version(control::context(Duration::from_secs(10)))
        .await
        .context("asking the daemon its version")?;
    anyhow::ensure!(
        version == control::VERSION,
        "the running daemon is musubi {version}, but this is {}; restart it with `musubi \
         daemon restart`",
        control::VERSION
    );
    Ok(Some(client))
}

/// The running daemon, starting one in the background if there is none.
pub async fn ensure(socket: &Socket) -> anyhow::Result<ControlClient> {
    if let Some(client) = running(socket).await? {
        return Ok(client);
    }
    // One running already on this socket, which this can't reach, stops any other starting:
    // it listens again once it notices its socket is gone. (On another, `running` refuses.)
    let already = Running::find()?;
    // Where a service manager runs the daemon, it starts it, so that there is only one.
    let (mut child, log) = if already.is_some() {
        (None, String::new())
    } else if login::managed() {
        login::start()?;
        (None, login::log_hint(login::Service::Daemon))
    } else {
        let (child, log) = spawn(socket)?;
        (Some(child), log.display().to_string())
    };
    let deadline = std::time::Instant::now() + Duration::from_secs(20);
    // A child that exits may have lost a race with another command's daemon, which is as
    // good: keep looking for one until the deadline.
    let mut exited = None;
    let mut pause = Backoff::new(FIRST_POLL, LAST_POLL);
    loop {
        if let Some(client) = running(socket).await? {
            return Ok(client);
        }
        if exited.is_none()
            && let Some(child) = &mut child
        {
            exited = child.try_wait()?;
        }
        if std::time::Instant::now() >= deadline {
            if let Some(running) = &already {
                return Err(running.unreachable(socket));
            }
            let Some(status) = exited else {
                anyhow::bail!("the daemon did not start listening on {socket}; see {log}");
            };
            let tail = fs::read_to_string(&log).unwrap_or_default();
            let tail: Vec<&str> = tail.lines().rev().take(5).collect();
            let tail: Vec<&str> = tail.into_iter().rev().collect();
            anyhow::bail!(
                "the daemon exited ({status}) before it was ready; from {log}:\n{}",
                tail.join("\n")
            );
        }
        tokio::time::sleep(pause.next()).await;
    }
}

/// How long to wait before looking again for a daemon starting or stopping, at first and at
/// most: one is ready in a few milliseconds, which a fixed 50 would add to every command
/// that starts it.
const FIRST_POLL: Duration = Duration::from_millis(2);
const LAST_POLL: Duration = Duration::from_millis(50);

/// Starts `musubi daemon` in the background, detached from this terminal, logging to the
/// state directory.
fn spawn(socket: &Socket) -> anyhow::Result<(std::process::Child, PathBuf)> {
    let state = config::create_state_dir()?;
    let log = config::daemon_log()?;
    let file = fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&log)
        .with_context(|| format!("opening {log:?}"))?;
    let socket = match socket {
        Socket::Path(path) => Socket::Path(std::path::absolute(path)?),
        Socket::Pipe(_) => socket.clone(),
    };
    let mut command = std::process::Command::new(std::env::current_exe()?);
    command
        .args(["daemon", "--socket", &socket.to_string()])
        // Not the directory of the command that starts it, often a repository it serves,
        // which may be deleted or moved: gix needs the current directory whenever it opens
        // a repository, any repository. So the paths it is given are absolute.
        .current_dir(&state)
        .stdin(std::process::Stdio::null())
        .stdout(file.try_clone()?)
        .stderr(file);
    if std::env::var_os("MUSUBI_STATE_DIR").is_some() {
        command.env("MUSUBI_STATE_DIR", &state);
    }
    // Now that the state directory exists.
    if let Err(err) = agent::refresh() {
        tracing::debug!("not pointing the daemon at this ssh agent: {err:#}");
    }
    isolate(&mut command, agent::link()?.as_deref());
    detach(&mut command);
    let child = command.spawn().context("starting the daemon")?;
    Ok((child, log))
}

/// What a daemon takes from the command that starts it, which it outlives, serving every
/// repository on the machine: not git's variables naming the command's repository, as a git
/// hook has, and not the command's ssh agent, but `agent_link`, which commands keep pointed
/// at a live one ([`agent`]).
pub(super) fn isolate(command: &mut std::process::Command, agent_link: Option<&Path>) {
    musubi_jj::git_command::without_repository_env(command);
    if let Some(link) = agent_link {
        command.env("SSH_AUTH_SOCK", link);
    }
}

#[cfg(unix)]
fn detach(command: &mut std::process::Command) {
    use std::os::unix::process::CommandExt as _;
    // Its own process group, so that ^C in this terminal doesn't reach it.
    command.process_group(0);
}

#[cfg(windows)]
pub fn detach(command: &mut std::process::Command) {
    use std::os::windows::process::CommandExt as _;
    const DETACHED_PROCESS: u32 = 0x0000_0008;
    const CREATE_NEW_PROCESS_GROUP: u32 = 0x0000_0200;
    command.creation_flags(DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP);
}

/// `musubi daemon install`: has the service manager start the daemon at login.
pub async fn install(ui: &Ui, socket: &Socket) -> anyhow::Result<()> {
    // The service manager starts the daemon from now on, so stop one started otherwise; and
    // start it again if the service manager can't.
    let stopped = stop(socket).await?;
    let described = match login::install(login::Service::Daemon, None) {
        Ok(described) => described,
        Err(err) => {
            if stopped && let Err(again) = ensure(socket).await {
                writeln!(ui.warning(), "Couldn't start the daemon again: {again:#}")?;
            }
            return Err(err);
        }
    };
    ensure(socket).await?;
    writeln!(
        ui.stdout(),
        "The daemon starts at login from now on, through {described}."
    )?;
    if cfg!(target_os = "linux") {
        writeln!(
            ui.hint(),
            "To keep it running while you're logged out, as on a server: `loginctl \
             enable-linger`"
        )?;
    }
    Ok(())
}

/// `musubi daemon uninstall`: stops the daemon starting at login, and stops it.
pub async fn uninstall(ui: &Ui, socket: &Socket) -> anyhow::Result<()> {
    let was = login::uninstall(login::Service::Daemon)?;
    let stopped = stop(socket).await?;
    if was {
        writeln!(
            ui.stdout(),
            "The daemon no longer starts at login, and is stopped."
        )?;
    } else if stopped {
        writeln!(
            ui.stdout(),
            "Stopped the daemon. It wasn't set to start at login."
        )?;
    } else {
        writeln!(ui.stdout(), "The daemon wasn't set to start at login.")?;
    }
    Ok(())
}

/// Stops this machine's daemon, if it runs, and waits for it to go. Returns whether one was
/// running. One not listening on `socket`, as after its socket was deleted, is stopped all
/// the same: asked on the socket it listens on, or else signalled; or else, as for a daemon
/// starting, asked once it listens.
pub async fn stop(socket: &Socket) -> anyhow::Result<bool> {
    let deadline = std::time::Instant::now() + Duration::from_secs(30);
    let mut pause = Backoff::new(FIRST_POLL, LAST_POLL);
    loop {
        let running = Running::find()?;
        let mut client = socket.connect().await?;
        if client.is_none()
            && let Some(theirs) = running
                .as_ref()
                .and_then(|running| running.elsewhere(socket))
        {
            client = theirs.connect().await.unwrap_or(None);
        }
        if let Some(client) = client {
            // The daemon may be gone before its reply arrives.
            client
                .stop(control::context(Duration::from_secs(10)))
                .await
                .ok();
            break;
        }
        let Some(running) = running else {
            return Ok(false);
        };
        if terminate(&running)? {
            break;
        }
        if std::time::Instant::now() >= deadline {
            let pid = running.pid.as_deref().unwrap_or("unknown");
            anyhow::bail!(
                "this machine's daemon (pid {pid}) isn't listening on {socket}, and can't be \
                 stopped from here"
            );
        }
        tokio::time::sleep(pause.next()).await;
    }
    wait_until_stopped(socket).await?;
    Ok(true)
}

/// Stops a daemon that can't be reached on its socket as ^C stops one in a terminal, if its
/// pid is among this process's, and says whether it did.
#[cfg(unix)]
fn terminate(running: &Running) -> anyhow::Result<bool> {
    use rustix::process::Pid;
    use rustix::process::Signal;
    let Some(pid) = running
        .pid
        .as_deref()
        .and_then(|pid| pid.parse().ok())
        .and_then(Pid::from_raw)
        .filter(|_| running.stoppable())
    else {
        return Ok(false);
    };
    match rustix::process::kill_process(pid, Signal::TERM) {
        Ok(()) | Err(rustix::io::Errno::SRCH) => Ok(true),
        Err(err) => Err(err).context("stopping the daemon"),
    }
}

/// A named pipe lasts as long as the daemon listening on it, so a daemon that runs but isn't
/// listening is starting or stopping.
#[cfg(not(unix))]
fn terminate(_: &Running) -> anyhow::Result<bool> {
    Ok(false)
}

/// Waits for the daemon to go: once it has let go of its lock, which it does after closing
/// its socket.
async fn wait_until_stopped(socket: &Socket) -> anyhow::Result<()> {
    let deadline = std::time::Instant::now() + Duration::from_secs(30);
    let mut pause = Backoff::new(FIRST_POLL, LAST_POLL);
    while socket.connect().await?.is_some() || Running::find()?.is_some() {
        anyhow::ensure!(
            std::time::Instant::now() < deadline,
            "the daemon on {socket} did not stop"
        );
        tokio::time::sleep(pause.next()).await;
    }
    Ok(())
}
