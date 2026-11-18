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
    /// The [`control::VERSION`] of the build it is. A daemon from before it wrote one says
    /// none.
    version: Option<String>,
}

impl Running {
    fn lock_path() -> anyhow::Result<PathBuf> {
        Ok(config::state_dir()?.join("daemon.lock"))
    }

    /// Its process id, its socket, which processes the id is among, and its build's
    /// [`control::VERSION`], a line each. Not in the lock file itself, which Windows doesn't
    /// let others read while it is locked.
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
        Ok(Some(Self::parse(&info)))
    }

    /// What a daemon wrote of itself ([`Running::info_path`]), which is nothing for a moment
    /// as it starts.
    fn parse(info: &str) -> Self {
        let mut lines = info.lines().map(str::trim);
        let mut next = || {
            lines
                .next()
                .filter(|line| !line.is_empty())
                .map(str::to_owned)
        };
        Self {
            pid: next(),
            socket: next().as_deref().map(Socket::named),
            among: next(),
            version: next(),
        }
    }

    /// Fails with [`control::OtherBuild`] if it is of another build than this, which a command
    /// can't talk to, without connecting to it: one from before it wrote its build says so by
    /// leaving it out, and never greets a command.
    fn check_build(&self) -> Result<(), control::OtherBuild> {
        // Not before it has written anything.
        if self.pid.is_none() || self.version.as_deref() == Some(control::VERSION) {
            return Ok(());
        }
        Err(control::OtherBuild(self.version.clone()))
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

    /// Whether its pid is among this process's, and so names it here: not from a container
    /// sharing the state directory with a daemon outside it, whose pid is another's.
    fn local(&self) -> bool {
        self.among.as_deref() == Some(processes().as_str())
    }

    /// Whether it is of a build from before pid files named their build, which spoke another
    /// protocol, and can't be asked to stop.
    fn predates(&self) -> bool {
        self.pid.is_some() && self.version.is_none()
    }

    /// How to end it by hand, which is the one way out for a daemon that can't be asked: by
    /// its pid, if that names it here.
    fn by_hand(&self) -> String {
        if self.local() {
            let pid = self.pid.as_deref().unwrap_or("unknown");
            format!("End it by hand (pid {pid}), then run `musubi daemon start`.")
        } else {
            "End it where it runs, then run `musubi daemon start`.".to_owned()
        }
    }

    /// What gets a daemon that isn't listening, or is of another build, going again. One that
    /// speaks the protocol of another build is asked to stop on its socket, wherever it runs,
    /// and one that doesn't listen is waited for to listen again, if it is of this build. One
    /// from before the protocol can't be asked, and is ended by hand.
    fn remedy(&self) -> String {
        let other_protocol = self
            .version
            .as_deref()
            .is_some_and(|theirs| theirs != control::VERSION);
        if other_protocol || (self.local() && !self.predates()) {
            RESTART.to_owned()
        } else {
            self.by_hand()
        }
    }
}

const RESTART: &str = "`musubi daemon restart` restarts it.";

/// Which processes this one's id is among: on Linux, its pid namespace, which a container has
/// of its own, though it may share the state directory, and so see the lock of a daemon whose
/// pid names no process of its own. Elsewhere, every process on the machine.
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
    Some(if running.local() {
        format!(
            "running (pid {pid}), but not listening on {socket}; restart it with `musubi daemon \
             restart`"
        )
    } else {
        format!("running (pid {pid}) elsewhere, not listening on {socket}; end it where it runs")
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
        format!(
            "{}\n{socket}\n{}\n{}\n",
            std::process::id(),
            processes(),
            control::VERSION
        ),
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
/// saying so, rather than `None`, which would have a command go around the daemon. One of
/// another build is an error that says how to restart it, or for one from before this
/// protocol, which can't be stopped from here, to end it by hand.
pub async fn running(socket: &Socket) -> anyhow::Result<Option<ControlClient>> {
    find_running(socket).await.map_err(|err| {
        if !err.is::<control::OtherBuild>() {
            return err;
        }
        let hint = match Running::find() {
            Ok(Some(running)) => running.remedy(),
            _ => RESTART.to_owned(),
        };
        crate::ui::with_hint(anyhow::anyhow!("{err}"), hint)
    })
}

async fn find_running(socket: &Socket) -> anyhow::Result<Option<ControlClient>> {
    // Before connecting to one of another build, which may never greet.
    if let Some(running) = Running::find()? {
        running.check_build()?;
    }
    if let Some(client) = running_on(socket).await? {
        return Ok(Some(client));
    }
    let Some(running) = Running::find()? else {
        return Ok(None);
    };
    running.check_build()?;
    match running.elsewhere(socket) {
        Some(theirs) if login::managed() => running_on(theirs).await,
        Some(_) => Err(running.refusal(socket)),
        None => Ok(None),
    }
}

/// A daemon of this build, which speaks its control protocol, on `socket`, if there is one,
/// and it greets. One of another build, or from before this protocol, is an error
/// ([`control::OtherBuild`]); one that doesn't greet in time is another
/// ([`control::Unresponsive`]).
async fn running_on(socket: &Socket) -> anyhow::Result<Option<ControlClient>> {
    let Some(client) = socket.connect().await? else {
        return Ok(None);
    };
    client.check(Duration::from_secs(10)).await?;
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
/// running. It is asked to stop on the socket it listens on, which may not be `socket`, and
/// obeys whatever build asks. No process is ever signalled: a pid file may be left by a daemon
/// killed hard, and name anything by now. One that isn't listening, as for a daemon starting,
/// is asked once it listens. One that listens, but doesn't greet, is asked again until it does:
/// it is busy. Either, if it still hasn't by the deadline, fails with the way to end it by
/// hand, as one from before this protocol does at once, which can't be asked ([`try_stop`]).
pub async fn stop(socket: &Socket) -> anyhow::Result<bool> {
    let deadline = std::time::Instant::now() + Duration::from_secs(30);
    let mut pause = Backoff::new(FIRST_POLL, LAST_POLL);
    loop {
        match try_stop(socket, Running::find()?).await? {
            Tried::NotRunning => return Ok(false),
            Tried::Asked => break,
            Tried::Waiting(waiting) => {
                if std::time::Instant::now() >= deadline {
                    return Err(waiting.unstoppable(socket));
                }
            }
        }
        tokio::time::sleep(pause.next()).await;
    }
    wait_until_stopped(socket).await?;
    Ok(true)
}

/// What one try at stopping the daemon came to.
#[derive(Debug)]
enum Tried {
    /// No daemon runs.
    NotRunning,
    /// It was asked to stop.
    Asked,
    /// It can't be stopped yet: it may be starting, or busy, or listen again soon.
    Waiting(Waiting),
}

/// A daemon that couldn't be asked to stop yet.
#[derive(Debug)]
struct Waiting {
    pid: String,
    /// How to end it by hand ([`Running::by_hand`]).
    hint: String,
    /// Whether it took the connection, which it didn't answer.
    listening: bool,
}

impl Waiting {
    /// Why it couldn't be stopped in the time there was.
    fn unstoppable(&self, socket: &Socket) -> anyhow::Error {
        let pid = &self.pid;
        let said = if self.listening {
            format!("this machine's daemon (pid {pid}) did not answer in time")
        } else {
            format!("this machine's daemon (pid {pid}) isn't listening on {socket}")
        };
        crate::ui::with_hint(anyhow::anyhow!(said), self.hint.clone())
    }
}

/// Tries once to stop the daemon `running` describes, if there is one.
///
/// A daemon that greets is asked to stop, which every build obeys. One that took the connection
/// but didn't greet is of this build and busy, to be asked again, unless its pid file says it
/// is from before this protocol, which can't be asked: that fails at once, saying to end it by
/// hand. One that isn't listening is waited for, and never signalled.
async fn try_stop(socket: &Socket, running: Option<Running>) -> anyhow::Result<Tried> {
    let mut reached = reach(socket).await?;
    if matches!(reached, Reached::Nobody)
        && let Some(theirs) = running
            .as_ref()
            .and_then(|running| running.elsewhere(socket))
    {
        reached = reach(theirs).await.unwrap_or(Reached::Nobody);
    }
    if let Reached::Client(client) = &reached {
        // The daemon may be gone before its reply arrives.
        client.stop(Duration::from_secs(10)).await.ok();
        return Ok(Tried::Asked);
    }
    let Some(running) = running else {
        return Ok(Tried::NotRunning);
    };
    let listening = matches!(reached, Reached::Listening);
    if listening && running.predates() {
        let pid = running.pid.as_deref().unwrap_or("unknown");
        return Err(crate::ui::with_hint(
            anyhow::anyhow!(
                "this machine's daemon (pid {pid}) is from an earlier build of musubi, which \
                 can't be stopped by this one"
            ),
            running.by_hand(),
        ));
    }
    Ok(Tried::Waiting(Waiting {
        pid: running.pid.as_deref().unwrap_or("unknown").to_owned(),
        hint: running.by_hand(),
        listening,
    }))
}

/// What [`reach`] found on a socket.
enum Reached {
    /// A daemon that speaks the control protocol of any build.
    Client(ControlClient),
    /// Something that took the connection, but didn't greet as a daemon of this protocol does:
    /// one from before it, which never greets, or one of this build that is busy. The pid file
    /// says which.
    Listening,
    /// None, or one that closed the connection before it greeted, as when it stops.
    Nobody,
}

/// The daemon on `socket`, to stop it.
async fn reach(socket: &Socket) -> anyhow::Result<Reached> {
    match socket.connect().await {
        Ok(Some(client)) => Ok(Reached::Client(client)),
        Ok(None) => Ok(Reached::Nobody),
        Err(err) if err.is::<control::OtherBuild>() || err.is::<control::Unresponsive>() => {
            Ok(Reached::Listening)
        }
        Err(err) => Err(err),
    }
}

/// Waits for the daemon to go: once it has let go of its lock, which it does after closing
/// its socket.
async fn wait_until_stopped(socket: &Socket) -> anyhow::Result<()> {
    let deadline = std::time::Instant::now() + Duration::from_secs(30);
    let mut pause = Backoff::new(FIRST_POLL, LAST_POLL);
    while socket.connect_stream().await?.is_some() || Running::find()?.is_some() {
        anyhow::ensure!(
            std::time::Instant::now() < deadline,
            "the daemon on {socket} did not stop"
        );
        tokio::time::sleep(pause.next()).await;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What a daemon of this build writes of itself.
    fn written(version: &str) -> String {
        format!("42\n/tmp/daemon.sock\nmachine\n{version}\n")
    }

    /// What a command says of a daemon from the pid file it wrote, without connecting.
    fn said_of(info: &str) -> Option<String> {
        Running::parse(info)
            .check_build()
            .err()
            .map(|other| other.to_string())
    }

    /// A daemon of this build is let be; one from before the pid file named its build, with
    /// the three lines it wrote then, and one of another, are of another build.
    #[test]
    fn a_pid_file_names_the_build_of_its_daemon() {
        assert_eq!(said_of(&written(control::VERSION)), None);
        // Starting: nothing written yet, or not all of it.
        assert_eq!(said_of(""), None);
        let earlier = "42\n/tmp/daemon.sock\nmachine\n";
        assert_eq!(
            said_of(earlier).unwrap(),
            "the running daemon is from an earlier build of musubi"
        );
        let later = written("99.0.0/control-1");
        assert_eq!(
            said_of(&later).unwrap(),
            format!(
                "the running daemon is musubi 99.0.0, but this is {}",
                env!("CARGO_PKG_VERSION")
            )
        );
        // The same release, from before the protocol last changed.
        let tagged = written(&format!("{}/control-0", env!("CARGO_PKG_VERSION")));
        assert!(said_of(&tagged).unwrap().contains("from another build"));
        // Reading the file keeps what it said of the rest.
        let running = Running::parse(&written(control::VERSION));
        assert_eq!(running.pid.as_deref(), Some("42"));
        assert_eq!(running.among.as_deref(), Some("machine"));
        assert_eq!(running.version.as_deref(), Some(control::VERSION));
        assert_eq!(Running::parse(earlier).version, None);
        // Only a daemon with a pid, and no build, is from before pid files named it.
        assert!(Running::parse(earlier).predates());
        assert!(!Running::parse(&written(control::VERSION)).predates());
        assert!(!Running::parse("").predates());
    }

    /// A daemon is told by its pid file, written by whoever holds its lock, but a daemon killed
    /// hard leaves it behind, naming a process that may be anything by now. `stop` never
    /// signals a process, whatever the pid file says.
    #[cfg(unix)]
    mod stopping {
        use std::os::unix::net::UnixListener;
        use std::process::Child;
        use std::process::Command;

        use tokio::time::Instant as TokioInstant;

        use super::*;

        /// A daemon that listens, but never greets. Connections wait to be accepted, and never
        /// are, as of a daemon that is busy, or from before the protocol changed.
        fn silent(dir: &Path) -> (UnixListener, Socket) {
            let path = dir.join("daemon.sock");
            (UnixListener::bind(&path).unwrap(), Socket::Path(path))
        }

        /// The pid file of a daemon `pid`, of the build `version`, or of one that wrote none.
        fn info(pid: u32, version: Option<&str>) -> Running {
            info_among(pid, &processes(), version)
        }

        /// The same, of a daemon whose pid is among the processes `among`, as in a container
        /// that shares the state directory.
        fn info_among(pid: u32, among: &str, version: Option<&str>) -> Running {
            let version = version.map(|version| format!("{version}\n"));
            let info = format!(
                "{pid}\n/tmp/daemon.sock\n{among}\n{}",
                version.unwrap_or_default()
            );
            Running::parse(&info)
        }

        const CONTAINER: &str = "pid:[0]";

        /// A process of no use to anyone, which something stopping it by mistake ends.
        fn bystander() -> Reaped {
            Reaped(Command::new("sleep").arg("60").spawn().unwrap())
        }

        /// Ends the process when the test does, whether or not it passes.
        struct Reaped(Child);

        impl Drop for Reaped {
            fn drop(&mut self) {
                self.0.kill().ok();
                self.0.wait().ok();
            }
        }

        impl Reaped {
            fn pid(&self) -> u32 {
                self.0.id()
            }

            fn alive(&mut self) -> bool {
                self.0.try_wait().unwrap().is_none()
            }
        }

        const OTHER: &str = "0.0.1/control-1";

        /// A daemon from before the protocol changed listens and never greets, and can't be
        /// asked to stop: `stop` fails at once, and not after the half minute that waiting
        /// takes, with the way out, and leaves its process alone.
        #[tokio::test(start_paused = true)]
        async fn a_daemon_from_before_this_protocol_is_left_to_be_ended_by_hand() {
            let dir = musubi_testutil::tempdir();
            let (_listener, socket) = silent(dir.path());
            let mut old = bystander();
            let started = TokioInstant::now();
            let err = try_stop(&socket, Some(info(old.pid(), None)))
                .await
                .unwrap_err();
            assert_eq!(
                err.to_string(),
                format!(
                    "this machine's daemon (pid {}) is from an earlier build of musubi, which \
                     can't be stopped by this one",
                    old.pid()
                )
            );
            assert_eq!(
                info(old.pid(), None).by_hand(),
                format!(
                    "End it by hand (pid {}), then run `musubi daemon start`.",
                    old.pid()
                )
            );
            assert!(started.elapsed() < Duration::from_secs(5));
            assert!(old.alive());
            // From a container sharing the state directory, its pid names nothing there.
            try_stop(&socket, Some(info_among(old.pid(), CONTAINER, None)))
                .await
                .unwrap_err();
            assert!(old.alive());
        }

        /// What a command says is what to do about the daemon, by what its pid file shows of
        /// it: a daemon that speaks the protocol of another build is restarted, wherever it
        /// runs, one from before it is ended by hand, by its pid if that is ours to name.
        #[tokio::test(start_paused = true)]
        async fn a_command_says_what_to_do_by_what_it_knows() {
            let dir = musubi_testutil::tempdir();
            let (_listener, socket) = silent(dir.path());
            let old = info(42, None);
            // Before connecting, as every command does.
            let err = old.check_build().unwrap_err();
            assert_eq!(
                err.to_string(),
                "the running daemon is from an earlier build of musubi"
            );
            assert_eq!(
                old.remedy(),
                "End it by hand (pid 42), then run `musubi daemon start`."
            );
            // Were it asked, it would say nothing.
            let err = running_on(&socket).await.err().unwrap();
            assert!(err.is::<control::Unresponsive>());
            // Not ours to name.
            assert_eq!(
                info_among(42, CONTAINER, None).remedy(),
                "End it where it runs, then run `musubi daemon start`."
            );
            // A daemon that speaks the protocol of another build is restarted, even from a
            // container, where it is asked over the socket.
            for other in [
                info(42, Some(OTHER)),
                info_among(42, CONTAINER, Some(OTHER)),
            ] {
                assert!(other.check_build().is_err());
                assert_eq!(other.remedy(), RESTART);
            }
            // One of this build that doesn't listen is waited for, if it is here.
            assert_eq!(info(42, Some(control::VERSION)).remedy(), RESTART);
            assert_eq!(
                info_among(42, CONTAINER, Some(control::VERSION)).remedy(),
                "End it where it runs, then run `musubi daemon start`."
            );
        }

        /// A daemon of another build that speaks the protocol is asked to stop on its socket,
        /// as one of any build is, and isn't signalled.
        #[tokio::test(start_paused = true)]
        async fn a_daemon_of_another_build_that_greets_is_asked_to_stop() {
            use std::sync::Arc;
            use std::sync::atomic::AtomicBool;
            use std::sync::atomic::Ordering;

            let dir = musubi_testutil::tempdir();
            let socket = Socket::Path(dir.path().join("daemon.sock"));
            let listener = socket.listen().unwrap();
            let mut other = bystander();
            let stopped = Arc::new(AtomicBool::new(false));
            let answer = {
                let stopped = stopped.clone();
                move |request: control::Request| {
                    let stopped = stopped.clone();
                    async move {
                        if request == control::Request::Stop {
                            stopped.store(true, Ordering::SeqCst);
                        }
                        control::Response::Stop
                    }
                }
            };
            let requests = control::service(answer).await.unwrap();
            tokio::spawn(async move {
                loop {
                    let stream = crate::socket::accept(&listener).await;
                    tokio::spawn(control::serve(requests.clone(), stream));
                }
            });
            let tried = try_stop(&socket, Some(info(other.pid(), Some(OTHER))))
                .await
                .unwrap();
            assert!(matches!(tried, Tried::Asked), "{tried:?}");
            assert!(stopped.load(Ordering::SeqCst));
            assert!(other.alive());
        }

        /// Nothing is ended while nothing listens, whatever the pid file says of the daemon: it
        /// may be starting, or its socket was deleted and it will listen again, or be left by
        /// one killed hard, whose pid names anything by now. `stop` waits, and at the deadline
        /// says how to end it by hand.
        #[tokio::test(start_paused = true)]
        async fn nothing_is_ended_while_nothing_listens() {
            let dir = musubi_testutil::tempdir();
            let socket = Socket::Path(dir.path().join("daemon.sock"));
            let mut other = bystander();
            let versions = [None, Some(OTHER), Some(control::VERSION)];
            for version in versions {
                let tried = try_stop(&socket, Some(info(other.pid(), version)))
                    .await
                    .unwrap();
                let Tried::Waiting(waiting) = tried else {
                    panic!("{tried:?}");
                };
                assert!(!waiting.listening);
                assert!(other.alive());
                let err = waiting.unstoppable(&socket);
                assert_eq!(
                    err.to_string(),
                    format!(
                        "this machine's daemon (pid {}) isn't listening on {socket}",
                        other.pid()
                    )
                );
                assert_eq!(
                    waiting.hint,
                    format!(
                        "End it by hand (pid {}), then run `musubi daemon start`.",
                        other.pid()
                    )
                );
            }
            // As in a container, which can't name the pid.
            let tried = try_stop(&socket, Some(info_among(other.pid(), CONTAINER, None)))
                .await
                .unwrap();
            let Tried::Waiting(waiting) = tried else {
                panic!("{tried:?}");
            };
            assert_eq!(
                waiting.hint,
                "End it where it runs, then run `musubi daemon start`."
            );
            assert!(other.alive());
        }

        /// No daemon, nothing to stop.
        #[tokio::test(start_paused = true)]
        async fn no_daemon_is_not_stopped() {
            let dir = musubi_testutil::tempdir();
            let socket = Socket::Path(dir.path().join("daemon.sock"));
            let tried = try_stop(&socket, None).await.unwrap();
            assert!(matches!(tried, Tried::NotRunning), "{tried:?}");
        }

        /// A daemon of this build that is slow to greet, as a busy one is, isn't another
        /// build, and isn't signalled: it is asked to stop again, until it greets.
        #[tokio::test(start_paused = true)]
        async fn a_busy_daemon_of_this_build_is_asked_again() {
            use std::sync::Arc;
            use std::sync::atomic::AtomicBool;
            use std::sync::atomic::Ordering;

            let dir = musubi_testutil::tempdir();
            let socket = Socket::Path(dir.path().join("daemon.sock"));
            let listener = socket.listen().unwrap();
            let mut busy = bystander();
            let stopped = Arc::new(AtomicBool::new(false));
            let answer = {
                let stopped = stopped.clone();
                move |request: control::Request| {
                    let stopped = stopped.clone();
                    async move {
                        if request == control::Request::Stop {
                            stopped.store(true, Ordering::SeqCst);
                        }
                        control::Response::Stop
                    }
                }
            };
            let requests = control::service(answer).await.unwrap();
            tokio::spawn(async move {
                // The first connection is not greeted, as for a daemon busy with something
                // else, and held open: the next are.
                let _held = crate::socket::accept(&listener).await;
                loop {
                    let stream = crate::socket::accept(&listener).await;
                    tokio::spawn(control::serve(requests.clone(), stream));
                }
            });
            let pid = busy.pid();
            let running = || Some(info(pid, Some(control::VERSION)));
            let started = TokioInstant::now();
            let tried = try_stop(&socket, running()).await.unwrap();
            let Tried::Waiting(waiting) = tried else {
                panic!("{tried:?}");
            };
            assert!(waiting.listening);
            assert!(started.elapsed() < Duration::from_secs(5));
            assert!(busy.alive() && !stopped.load(Ordering::SeqCst));
            let tried = try_stop(&socket, running()).await.unwrap();
            assert!(matches!(tried, Tried::Asked), "{tried:?}");
            assert!(stopped.load(Ordering::SeqCst));
            assert!(busy.alive());
            let err = waiting.unstoppable(&socket);
            assert_eq!(
                err.to_string(),
                format!(
                    "this machine's daemon (pid {}) did not answer in time",
                    busy.pid()
                )
            );
            assert_eq!(
                waiting.hint,
                format!(
                    "End it by hand (pid {}), then run `musubi daemon start`.",
                    busy.pid()
                )
            );
        }

        /// What listens and is slow to greet isn't said to be of another build, to a command
        /// that asks for it.
        #[tokio::test(start_paused = true)]
        async fn a_busy_daemon_is_not_called_another_build() {
            let dir = musubi_testutil::tempdir();
            let (_listener, socket) = silent(dir.path());
            let err = running_on(&socket).await.err().unwrap();
            assert_eq!(err.to_string(), "the daemon did not answer in time");
        }
    }
}
