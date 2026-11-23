//! `musubi hub`: serving a hub directory on a local socket, which `musubi hub connect`
//! relays to and commands on its machine connect to; and asking a hub about its hives.

use std::fmt::Write as _;
use std::fs;
use std::io;
use std::io::BufRead as _;
use std::io::IsTerminal as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::Duration;

use anyhow::Context as _;
use async_trait::async_trait;
use bytes::Bytes;
use interprocess::local_socket::tokio::Listener;
use interprocess::local_socket::tokio::Stream;
use jj_cli::formatter::FormatterExt as _;
use musubi_sync::server::HubServer;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HUB_TOKEN;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use musubi_sync::wire::rpc_subject;
use musubi_transport::MemoryNetwork;
use musubi_transport::StreamTransport;
use musubi_transport::Transport;
use musubi_transport::TransportError;
use musubi_transport::stream::Connector;
use musubi_transport::stream::Reader;
use musubi_transport::stream::WhileDisconnected;
use musubi_transport::stream::Writer;
use serde::Deserialize;
use serde::Serialize;
use tokio::sync::oneshot;

use crate::config;
use crate::lock::try_lock;
use crate::login;
use crate::login::Service;
use crate::socket;
use crate::socket::Socket;
use crate::ssh;
use crate::tls;
use crate::ui::Ui;

/// What marks a directory as a hub's, and holds its settings.
const HUB_FILE: &str = "hub.toml";

/// Where releases up to 0.47 made the hub by default, in the home directory.
// Compatibility until 2027-02-21: remove this, the step in `choose_dir` that looks for a hub
// here, the hint `serve` prints, and what docs/reference/configuration.md says of it.
const OLD_DEFAULT_DIR: &str = "musubi-hub";

/// The largest message the hub takes. Larger attachments move in chunks of about this size
/// (see [`musubi_sync::remote`]).
const MAX_PAYLOAD: usize = 1 << 20;

#[derive(Debug, Default, Serialize, Deserialize)]
struct HubSettings {
    /// The host name other machines ssh to this one by, once `--advertise` has given one: a
    /// machine's own name for itself isn't always one they can use.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    advertise: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    listen: Option<std::net::SocketAddr>,
}

impl HubSettings {
    fn configure(&mut self, args: &ServeArgs) -> anyhow::Result<()> {
        if let Some(listen) = args.listen {
            anyhow::ensure!(
                listen.port() != 0,
                "the TLS listener needs a fixed, nonzero port"
            );
            self.listen = Some(listen);
            if args.advertise.is_none() && !self.advertise.as_deref().is_some_and(tls::is_tls) {
                let host = whoami::hostname().context("finding this machine's host name")?;
                self.advertise = Some(format!("musubi://{host}:{}", listen.port()));
            }
        }
        if let Some(advertise) = &args.advertise {
            self.advertise = Some(advertise.clone());
        }
        if let Some(advertise) = &self.advertise {
            if tls::is_tls(advertise) {
                tls::validate_endpoint(advertise)?;
                anyhow::ensure!(
                    self.listen.is_some(),
                    "a TLS hub address needs --listen IP:PORT"
                );
            } else {
                anyhow::ensure!(
                    self.listen.is_none(),
                    "advertise the TLS address as musubi://host:port"
                );
            }
        }
        Ok(())
    }

    fn load(dir: &Path) -> anyhow::Result<Self> {
        let path = dir.join(HUB_FILE);
        let text = fs::read_to_string(&path).with_context(|| format!("reading {path:?}"))?;
        toml::from_str(&text).with_context(|| format!("{path:?}"))
    }

    fn save(&self, dir: &Path) -> anyhow::Result<()> {
        config::write_private(&dir.join(HUB_FILE), toml::to_string(self)?.as_bytes())
    }
}

pub struct ServeArgs {
    pub dir: Option<PathBuf>,
    pub advertise: Option<String>,
    pub listen: Option<std::net::SocketAddr>,
}

impl From<crate::cli::HubArgs> for ServeArgs {
    fn from(args: crate::cli::HubArgs) -> Self {
        Self {
            dir: args.dir,
            advertise: args.advertise,
            listen: args.listen,
        }
    }
}

/// The directory to serve, in order of precedence: `dir`, the current directory if it is a
/// hub's, `musubi.hub-dir`, `~/musubi-hub` if it is a hub's, and [`config::default_hub_dir`];
/// and whether it is `~/musubi-hub`, found so.
fn choose_dir(dir: Option<PathBuf>) -> anyhow::Result<(PathBuf, bool)> {
    if let Some(dir) = dir {
        return Ok((dir, false));
    }
    if let Ok(cwd) = std::env::current_dir()
        && cwd.join(HUB_FILE).exists()
    {
        return Ok((cwd, false));
    }
    if let Some(dir) = config::hub_directory()? {
        return Ok((dir, false));
    }
    // A hub stays where an earlier release made it: this machine's repositories name it by
    // its directory.
    if let Ok(home) = etcetera::home_dir()
        && home.join(OLD_DEFAULT_DIR).join(HUB_FILE).exists()
    {
        return Ok((home.join(OLD_DEFAULT_DIR), true));
    }
    Ok((config::default_hub_dir()?, false))
}

/// The socket of the hub serving `dir`, unless its path is too long to use.
fn socket_for(dir: &Path) -> anyhow::Result<Socket> {
    let socket = Socket::hub(dir);
    if let Some(over) = socket.too_long() {
        anyhow::bail!(
            "the hub's socket, {socket}, would be {over} bytes longer than this system allows; \
             serve the hub from a shorter path"
        );
    }
    Ok(socket)
}

/// What to run to share a repository through the hub serving `dir`, on other machines and
/// on this one.
fn instructions(settings: &HubSettings, dir: &Path) -> anyhow::Result<String> {
    // What other machines pass as --hub: the name they ssh to this machine by.
    let public = match &settings.advertise {
        Some(host) => host.clone(),
        None => whoami::hostname().unwrap_or_else(|_| "localhost".to_owned()),
    };
    // And what this one passes, which commands here leave out if it is the default.
    let local = dir.display().to_string();
    let default_here = config::UserState::load()?
        .default_hub()?
        .is_some_and(|hub| {
            hub == local
                || (is_local(&hub)
                    && Socket::hub(Path::new(&hub)).too_long().is_none()
                    && fs::canonicalize(&hub)
                        .is_ok_and(|hub| fs::canonicalize(dir).is_ok_and(|dir| dir == hub)))
        });
    let mut text = format!(
        "To share a repository:               musubi create --hub {public}\n\
         To add another machine's copy of it: musubi join --hub {public}\n\
         To make a new copy of a hive:        musubi clone <name> [<dir>] --hub {public}\n"
    );
    if settings.listen.is_some() {
        writeln!(
            text,
            "Other machines need an invitation from `musubi hub invite --dir {}` on this machine.",
            crate::ui::shell_word(&local)
        )?;
    } else {
        writeln!(
            text,
            "Other machines reach this hub over ssh: use the name they ssh to this machine by, \
             if it isn't {public}."
        )?;
    }
    if default_here {
        text.push_str("On this machine, leave out --hub.\n");
    } else {
        writeln!(
            text,
            "On this machine, use --hub {}.",
            crate::ui::shell_word(&local)
        )
        .ok();
    }
    Ok(text)
}

pub fn serve(ui: &Ui, args: ServeArgs) -> anyhow::Result<()> {
    let default = args.dir.is_none();
    let (dir, old_default) = choose_dir(args.dir.clone())?;
    // One hub per user by default; `--dir` runs more on purpose.
    let state = config::state_dir()?;
    let _user_lock = if default {
        let Some(lock) = try_lock(&state.join("hub.lock"))? else {
            let serving = fs::read_to_string(state.join("hub.path")).unwrap_or_default();
            anyhow::bail!(
                "a hub is already running, serving {}; use --dir to run another",
                serving.trim()
            );
        };
        Some(lock)
    } else {
        None
    };
    let created = !dir.join(HUB_FILE).exists();
    fs::create_dir_all(&dir).with_context(|| format!("creating {dir:?}"))?;
    // As commands keep it, which is not canonical: on Windows that is a `\\?\` path, which
    // git can't use.
    let dir = local_dir(&dir)?;
    let Some(_dir_lock) = try_lock(&dir.join("hub.lock"))? else {
        anyhow::bail!("a hub is already serving {}", dir.display());
    };
    if old_default {
        // Compatibility until 2027-02-21: remove this hint.
        writeln!(
            ui.hint(),
            "Earlier releases made hubs in ~/{OLD_DEFAULT_DIR}, and a later release will stop \
             looking there. To keep serving this hub, run `jj config set --user musubi.hub-dir \
             '~/{OLD_DEFAULT_DIR}'`. Don't move it: this machine's repositories name it by its \
             path."
        )?;
    }
    if default {
        fs::write(state.join("hub.path"), dir.display().to_string())?;
        if let Ok(log) = config::hub_log() {
            crate::daemon::trim_log(&log);
        }
    }
    let mut settings = if created {
        HubSettings::default()
    } else {
        HubSettings::load(&dir)?
    };
    settings.configure(&args)?;
    let tls_hub = settings
        .listen
        .map(|_| tls::Hub::open(&dir).map(Arc::new))
        .transpose()?;
    // Bind before announcing success; a service must not appear ready with TLS unavailable.
    let tls_listener = settings
        .listen
        .map(std::net::TcpListener::bind)
        .transpose()
        .context("binding the TLS hub listener")?;
    if let Some(listener) = &tls_listener {
        listener.set_nonblocking(true)?;
    }
    let socket = socket_for(&dir)?;
    settings.save(&dir)?;
    let server = HubServer::open(&dir)?;
    let greeting = match (created, server.hive_count()) {
        (true, _) => format!("Created a new hub in {}", dir.display()),
        (false, 1) => format!("Serving 1 hive from {}", dir.display()),
        (false, n) => format!("Serving {n} hives from {}", dir.display()),
    };
    // Whoever reads stdout may have stopped already; the hub serves all the same.
    writeln!(ui.stdout(), "{greeting}").ok();
    config::UserState::save_default_hub(&dir.display().to_string())?;
    let instructions = instructions(&settings, &dir)?;
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    let result = runtime.block_on(async {
        // The hub's service and the connections it serves meet here. No faults, so the seed
        // doesn't matter.
        let network = MemoryNetwork::new(0, MAX_PAYLOAD);
        // Holding the hub directory's lock, nothing else listens here.
        let listener = socket.listen()?;
        let (answering, answers) = oneshot::channel();
        let accepting = accept(listener, Arc::new(network.connect()), answers);
        let tls_accepting = async {
            match (tls_hub, tls_listener) {
                (Some(hub), Some(listener)) => {
                    let listener = tokio::net::TcpListener::from_std(listener)?;
                    hub.serve(listener, Arc::new(network.connect())).await
                }
                _ => std::future::pending().await,
            }
        };
        let ready = || {
            answering.send(()).ok();
            // Whoever reads stdout may stop before the end, as `musubi hub | head -1` does;
            // the hub serves all the same.
            let mut out = ui.stdout();
            out.write_all(instructions.as_bytes())
                .and_then(|()| out.flush())
                .ok();
            tracing::info!("serving {}", dir.display());
        };
        tokio::select! {
            result = server.run(Arc::new(network.connect()), ready) => result,
            () = accepting => Ok(()),
            result = tls_accepting => result,
            () = interrupted() => Ok(()),
        }
    });
    if let Socket::Path(path) = &socket {
        fs::remove_file(path).ok();
    }
    result
}

/// `musubi hub install`: has the service manager run `musubi hub` in the directory it would
/// serve, as this user's hub, from login or boot on, and waits for the hub to answer.
pub fn install(ui: &Ui, args: ServeArgs, at_boot: bool) -> anyhow::Result<()> {
    anyhow::ensure!(!cfg!(windows), "musubi can't run a hub at login on Windows");
    login::prepare_hub_install(at_boot)?;
    let (dir, _) = choose_dir(args.dir.clone())?;
    fs::create_dir_all(&dir).with_context(|| format!("creating {dir:?}"))?;
    // The path the hub, run there, finds its directory by, symbolic links resolved, which it
    // saves as this machine's default hub.
    let dir = fs::canonicalize(&dir)?;
    socket_for(&dir)?;
    let mut settings = if dir.join(HUB_FILE).exists() {
        HubSettings::load(&dir)?
    } else {
        HubSettings::default()
    };
    settings.configure(&args)?;
    if settings.listen.is_some() {
        tls::Hub::open(&dir)?;
    }
    let state = config::create_state_dir()?;
    // Before stopping the hub an earlier install runs, which may serve another directory:
    // whatever else serves this one would refuse it anyway.
    let installed = login::installed(Service::Hub);
    let replacing = installed
        && fs::read_to_string(state.join("hub.path"))
            .ok()
            .and_then(|served| fs::canonicalize(served.trim()).ok())
            .is_some_and(|served| served == dir);
    if !replacing && try_lock(&dir.join("hub.lock"))?.is_none() {
        anyhow::bail!(
            "a hub is already serving {}; stop it, then run this again",
            dir.display()
        );
    }
    if !installed && try_lock(&state.join("hub.lock"))?.is_none() {
        let serving = fs::read_to_string(state.join("hub.path")).unwrap_or_default();
        anyhow::bail!(
            "a hub is already running, serving {}; stop it, then run this again",
            serving.trim()
        );
    }
    let stopping = login::uninstall(Service::Hub)?;
    // The service manager may return before the hub it stops has let go of its lock.
    let deadline = std::time::Instant::now() + Duration::from_secs(10);
    let user_lock = loop {
        match try_lock(&state.join("hub.lock"))? {
            Some(lock) => break lock,
            None if stopping && std::time::Instant::now() < deadline => {
                std::thread::sleep(Duration::from_millis(100));
            }
            None => {
                let serving = fs::read_to_string(state.join("hub.path")).unwrap_or_default();
                anyhow::bail!(
                    "a hub is already running, serving {}; stop it, then run this again",
                    serving.trim()
                );
            }
        }
    };
    let Some(dir_lock) = try_lock(&dir.join("hub.lock"))? else {
        anyhow::bail!(
            "a hub is already serving {}; stop it, then run this again",
            dir.display()
        );
    };
    drop((user_lock, dir_lock));
    // Made a hub's now, the directory is what `musubi hub` serves when run in it.
    settings.save(&dir)?;
    let described = login::install_hub(&dir, at_boot)?;
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    runtime
        .block_on(async {
            let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
            loop {
                match open_local(&dir).await {
                    Ok(_) => return Ok(()),
                    // As text: its hint, to start a hub, is no help when one failed to.
                    Err(err) if tokio::time::Instant::now() >= deadline => {
                        return Err(anyhow::anyhow!("{err:#}"));
                    }
                    Err(_) => tokio::time::sleep(Duration::from_millis(100)).await,
                }
            }
        })
        .with_context(|| {
            format!(
                "the hub didn't start; see {}",
                login::log_hint(Service::Hub)
            )
        })?;
    let mut out = ui.stdout();
    let when = if at_boot { "at boot" } else { login::STARTS };
    writeln!(
        out,
        "The hub serves {}, and runs {when} from now on, through {described}.",
        dir.display()
    )?;
    out.write_all(instructions(&settings, &dir)?.as_bytes())?;
    if cfg!(target_os = "linux") && !at_boot {
        writeln!(
            ui.hint(),
            "To start it at boot and keep it running after logout: `musubi hub install \
             --at-boot --dir {}`",
            crate::ui::shell_word(&dir.display().to_string())
        )?;
    }
    Ok(())
}

/// Serves each connection to the hub's socket, once the hub answers requests, relaying what
/// comes through `transport`.
async fn accept(listener: Listener, transport: Arc<dyn Transport>, answers: oneshot::Receiver<()>) {
    answers.await.ok();
    loop {
        let stream = socket::accept(&listener).await;
        let transport = transport.clone();
        tokio::spawn(async move {
            let (reader, writer) = tokio::io::split(stream);
            if let Err(err) = musubi_transport::stream::serve(transport, reader, writer).await {
                tracing::debug!("a connection ended: {err}");
            }
        });
    }
}

/// Waits for ^C, or on Unix, SIGTERM, as service managers stop what they run.
pub async fn interrupted() {
    #[cfg(unix)]
    {
        let Ok(mut terminate) =
            tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())
        else {
            tokio::signal::ctrl_c().await.ok();
            return;
        };
        tokio::select! {
            _ = tokio::signal::ctrl_c() => {}
            _ = terminate.recv() => {}
        }
    }
    #[cfg(not(unix))]
    tokio::signal::ctrl_c().await.ok();
}

/// A connection to a hub, and over ssh, what keeps it from working while it doesn't.
pub struct Connection {
    pub transport: Arc<dyn Transport>,
    place: Place,
}

/// Where a hub is.
enum Place {
    /// The directory of a hub on this machine.
    Local(PathBuf),
    /// An ssh destination, and what ssh says of it.
    Ssh {
        hub: String,
        health: ssh::Health,
    },
    Tls {
        hub: String,
        link: tls::Link,
    },
}

impl Connection {
    /// Why the hub can't be reached, for a transport that has lost its connection, in the
    /// words of the commands that connect to it: what a hub's socket on this machine says
    /// now, or what ssh last said, without running it again. `None` if nothing says so.
    pub async fn out_of_reach(&self) -> Option<String> {
        match &self.place {
            Place::Local(dir) => open_local(dir).await.err().map(|err| format!("{err:#}")),
            Place::Ssh { hub, health } => {
                health.problem().map(|problem| out_of_reach(hub, &problem))
            }
            Place::Tls { hub, link } => link.problem().map(|problem| out_of_reach(hub, &problem)),
        }
    }

    /// `err`, with why the hub can't be reached, if ssh says, waiting a moment for it to say
    /// why it didn't connect.
    pub async fn explain(&self, err: anyhow::Error) -> anyhow::Error {
        let problem = match &self.place {
            Place::Local(_) => None,
            Place::Ssh { health, .. } => health.problem_once_known().await,
            Place::Tls { link, .. } => link.problem(),
        };
        match problem {
            Some(problem) => err.context(problem),
            None => err,
        }
    }
}

/// Whether `hub`, as given to --hub, is the directory of a hub on this machine, rather than
/// an ssh destination.
pub fn is_local(hub: &str) -> bool {
    Path::new(hub).is_absolute()
}

/// `hub` as given to --hub, in the form commands keep: a hub directory here in the form
/// [`local_dir`] gives, which given relative would be taken for an ssh destination, and a
/// name for this machine made the directory of its hub, as [`on_this_machine`] does.
pub fn resolve(hub: &str) -> String {
    if tls::is_tls(hub) {
        return hub.to_owned();
    }
    let dir = Path::new(hub);
    if (is_local(hub) || dir.join(HUB_FILE).is_file())
        && let Ok(dir) = local_dir(dir)
    {
        return dir.display().to_string();
    }
    if is_local(hub) {
        return hub.to_owned();
    }
    on_this_machine(hub)
}

/// The directory of a hub on this machine in the one form commands keep it in, so that
/// however it was given, as `../hub` or `/srv/hub/`, it is the same hub: absolute, without
/// `.`, `..` or a trailing `/`, and its symbolic links kept, as `musubi hub` prints it.
pub fn local_dir(dir: &Path) -> io::Result<PathBuf> {
    let normal = crate::repo::lexically_normal(&std::path::absolute(dir)?);
    // Except where `..` follows a symbolic link, and so names the directory above its target:
    // then canonical. Not on Windows, whose canonical paths git can't use, and which takes
    // `..` by its words.
    if cfg!(not(windows))
        && let (Ok(canonical), Ok(normal)) = (dir.canonicalize(), normal.canonicalize())
        && canonical != normal
    {
        return Ok(canonical);
    }
    Ok(normal)
}

/// The ssh destination `hub`, or if it names this machine, the directory of the hub
/// `musubi hub` last served there without `--dir`, which `musubi hub connect` relays to: its
/// socket reaches it with no ssh to this machine.
pub fn on_this_machine(hub: &str) -> String {
    if let Ok(dir) = default_dir()
        && let Ok(settings) = HubSettings::load(&dir)
        && names_this_machine(
            hub,
            whoami::hostname().ok().as_deref(),
            settings.advertise.as_deref(),
        )
    {
        return dir.display().to_string();
    }
    hub.to_owned()
}

/// Whether the ssh destination `dest` is this machine, as `host` names itself, or the hub
/// advertises it, by those names or as localhost. With a user, it may be another's account.
fn names_this_machine(dest: &str, host: Option<&str>, advertise: Option<&str>) -> bool {
    !dest.contains('@')
        && ["localhost", "127.0.0.1", "::1"]
            .into_iter()
            .chain(host)
            .chain(advertise)
            .any(|name| name.eq_ignore_ascii_case(dest))
}

/// The directory of the hub `musubi hub` last served without `--dir`.
fn default_dir() -> anyhow::Result<PathBuf> {
    let path = config::state_dir()?.join("hub.path");
    let text = fs::read_to_string(&path).map_err(|_| {
        let err = anyhow::anyhow!("no hub has run on this machine");
        crate::ui::with_hint(err, "`musubi hub` starts one")
    })?;
    Ok(PathBuf::from(text.trim()))
}

/// Connects to `hub`, an ssh destination or the directory of a hub on this machine, giving
/// up after `limit`.
pub async fn connect(hub: &str, limit: Duration) -> anyhow::Result<Connection> {
    connect_with(hub, limit, WhileDisconnected::Wait).await
}

/// [`connect`], with requests made while the connection is lost doing as `while_disconnected`
/// says.
pub async fn connect_with(
    hub: &str,
    limit: Duration,
    while_disconnected: WhileDisconnected,
) -> anyhow::Result<Connection> {
    if tls::is_tls(hub) {
        let link = tls::Link::new(hub)?;
        let connecting = StreamTransport::connect_with(Arc::new(link.clone()), while_disconnected);
        let transport = tokio::time::timeout(limit, connecting)
            .await
            .map_err(|_| {
                anyhow::anyhow!(out_of_reach(
                    hub,
                    &link
                        .problem()
                        .unwrap_or_else(|| "connection timed out".to_owned())
                ))
            })??;
        return Ok(Connection {
            transport: Arc::new(transport),
            place: Place::Tls {
                hub: hub.to_owned(),
                link,
            },
        });
    }
    let unreachable = |problem: Option<String>| match problem {
        Some(problem) => anyhow::anyhow!(out_of_reach(hub, &problem)),
        None => anyhow::anyhow!("the hub at {hub} is out of reach"),
    };
    if is_local(hub) {
        let dir = PathBuf::from(hub);
        // Nothing to wait for if no hub is serving it.
        let first = Mutex::new(Some(open_local(&dir).await?));
        let local = Local {
            dir: dir.clone(),
            first,
        };
        let connecting = StreamTransport::connect_with(Arc::new(local), while_disconnected);
        let transport = tokio::time::timeout(limit, connecting)
            .await
            .map_err(|_| unreachable(None))??;
        return Ok(Connection {
            transport: Arc::new(transport),
            place: Place::Local(dir),
        });
    }

    let link = ssh::Link::new(hub)?;
    let health = link.health();
    let connecting = StreamTransport::connect_with(Arc::new(link), while_disconnected);
    let transport = tokio::time::timeout(limit, connecting)
        .await
        .map_err(|_| unreachable(health.problem()))??;
    Ok(Connection {
        transport: Arc::new(transport),
        place: Place::Ssh {
            hub: hub.to_owned(),
            health,
        },
    })
}

/// That the hub at `hub` is out of reach, and why.
fn out_of_reach(hub: &str, problem: &str) -> String {
    format!("the hub at {hub} is out of reach: {problem}")
}

/// Local administration of TLS identity and authorization, never over the enrollment link.
pub fn tls_hub(dir: Option<PathBuf>) -> anyhow::Result<tls::Hub> {
    let (dir, _) = choose_dir(dir)?;
    let settings = HubSettings::load(&dir)?;

    if settings.listen.is_none() {
        return Err(crate::ui::with_hint(
            anyhow::anyhow!("this hub has no TLS listener"),
            format!(
                "Run `musubi hub --dir {} --listen IP:PORT`.",
                crate::ui::shell_word(&dir.display().to_string())
            ),
        ));
    }

    tls::Hub::open(&dir)
}

pub async fn prepare_tls(ui: &Ui, hub: &str) -> anyhow::Result<()> {
    if !tls::has_credentials(hub)? {
        enroll(ui, hub).await?;
    }
    Ok(())
}

pub async fn enroll(ui: &Ui, hub: &str) -> anyhow::Result<()> {
    tls::validate_endpoint(hub)?;
    if io::stdin().is_terminal() {
        let mut out = ui.stderr();
        writeln!(out, "Please enter the invitation (paste the whole block):")?;
        out.flush()?;
    }
    let invitation = read_invitation(io::stdin().lock())?;
    let settings = ui.settings()?;
    tls::prepare(hub, invitation.trim(), settings.operation_hostname()).await
}

fn read_invitation(input: impl io::BufRead) -> anyhow::Result<String> {
    let mut input = input.take(8193);
    let mut key = String::new();
    loop {
        let before = key.len();
        if input.read_line(&mut key)? == 0 || key[before..].trim().is_empty() {
            break;
        }
        let words = key.split_ascii_whitespace().count();
        // English BIP-39 words have at most eight ASCII letters. Reject malformed tokens
        // without waiting for EOF or another line.
        if words >= 48
            || key
                .split_ascii_whitespace()
                .any(|word| word.len() > 8 || !word.bytes().all(|b| b.is_ascii_alphabetic()))
        {
            break;
        }
    }
    anyhow::ensure!(
        !key.trim().is_empty() && key.len() <= 8192,
        "expected an invitation from `musubi hub invite` on stdin"
    );
    Ok(key)
}

/// Opens connections to a hub on this machine, through its socket.
struct Local {
    dir: PathBuf,
    /// The first connection, opened to see that the hub is there.
    first: Mutex<Option<Stream>>,
}

#[async_trait]
impl Connector for Local {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        let first = self
            .first
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        let stream = match first {
            Some(stream) => stream,
            None => open_local(&self.dir).await.map_err(io::Error::other)?,
        };
        let (reader, writer) = tokio::io::split(stream);
        Ok((Box::new(reader), Box::new(writer)))
    }
}

/// Connects to the socket of the hub serving `dir`, on this machine.
async fn open_local(dir: &Path) -> anyhow::Result<Stream> {
    let not_serving = || {
        let err = anyhow::anyhow!("no hub is serving {}", dir.display());
        crate::ui::with_hint(err, "`musubi hub` starts one")
    };
    if !dir.join(HUB_FILE).exists() {
        return Err(not_serving());
    }
    Socket::hub(&std::path::absolute(dir)?)
        .connect_stream()
        .await?
        .ok_or_else(not_serving)
}

/// `musubi hub remove`: removes a hive from a hub.
pub async fn remove(ui: &Ui, hive: String, hub: Option<String>) -> anyhow::Result<()> {
    let hub = config::UserState::hub(hub.as_deref())?;
    let reply = ask(&hub, HubWideRequest::Remove { name: hive }).await?;
    if let HubWideReply::Hive(info) = reply {
        let mut out = ui.stdout();
        write!(out, "Removed hive ")?;
        writeln!(out.labeled("hive"), "{}", info.name)?;
    }
    Ok(())
}

/// `musubi hub rename`: renames a hive on a hub.
pub async fn rename(
    ui: &Ui,
    hive: String,
    new_name: String,
    hub: Option<String>,
) -> anyhow::Result<()> {
    let hub = config::UserState::hub(hub.as_deref())?;
    let request = HubWideRequest::Rename {
        name: hive.clone(),
        to: new_name,
    };
    let reply = ask(&hub, request).await?;
    let HubWideReply::Renamed { from, hive } = reply else {
        anyhow::bail!("unexpected reply from the hub: {reply:?}");
    };
    let mut out = ui.stdout();
    if from == hive.name {
        write!(out, "Hive ")?;
        write!(out.labeled("hive"), "{from}")?;
        writeln!(out, " already has that name")?;
    } else {
        write!(out, "Renamed hive ")?;
        write!(out.labeled("hive"), "{from}")?;
        write!(out, " to ")?;
        writeln!(out.labeled("hive"), "{}", hive.name)?;
    }
    Ok(())
}

/// Asks `hub` about its hives; a refusal is an error.
pub async fn ask(hub: &str, request: HubWideRequest) -> anyhow::Result<HubWideReply> {
    // Over ssh, longer than ssh's own ConnectTimeout.
    let limit = Duration::from_secs(if is_local(hub) { 10 } else { 30 });
    let connection = connect(hub, limit).await?;
    ask_over(&connection, hub, request).await
}

pub async fn ask_over(
    connection: &Connection,
    hub: &str,
    request: HubWideRequest,
) -> anyhow::Result<HubWideReply> {
    ask_within(connection, hub, request, Duration::from_secs(60)).await
}

/// [`ask_over`], waiting at most `limit` for the answer.
pub async fn ask_within(
    connection: &Connection,
    hub: &str,
    request: HubWideRequest,
    limit: Duration,
) -> anyhow::Result<HubWideReply> {
    let subject = rpc_subject(HUB_TOKEN);
    let payload = Bytes::from(Envelope::encode(request)?);
    let reply = match connection.transport.request(&subject, payload, limit).await {
        Ok(reply) => reply,
        Err(TransportError::NoResponders(_)) => {
            let err = anyhow::anyhow!("no hub is serving at {hub}");
            return Err(crate::ui::with_hint(err, "`musubi hub` there starts one"));
        }
        Err(err) => {
            let err = anyhow::Error::new(err).context("asking the hub");
            return Err(connection.explain(err).await);
        }
    };
    match Envelope::decode(&reply)? {
        HubWideReply::Error(message) => anyhow::bail!("{message}"),
        HubWideReply::Reset(reset) => Err(musubi_sync::remote::HiveReset(reset).into()),
        reply => Ok(reply),
    }
}

/// `musubi hub connect`: relays stdin and stdout to the socket of the hub serving `dir` (by
/// default, this user's hub), as the command a machine's daemon runs over ssh to reach it.
pub fn relay(dir: Option<PathBuf>) -> anyhow::Result<()> {
    let dir = match dir {
        Some(dir) => dir,
        None => default_dir()?,
    };
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    let result = runtime.block_on(async {
        use tokio::io::AsyncWriteExt as _;
        let stream = open_local(&dir).await?;
        let (mut from_hub, mut to_hub) = tokio::io::split(stream);
        let mut stdin = tokio::io::stdin();
        let mut stdout = tokio::io::stdout();
        let up = async {
            tokio::io::copy(&mut stdin, &mut to_hub).await?;
            to_hub.shutdown().await
        };
        let down = tokio::io::copy(&mut from_hub, &mut stdout);
        // Either side closing ends the relay.
        tokio::select! {
            result = up => result?,
            result = down => {
                result?;
            }
        }
        anyhow::Ok(())
    });
    // Dropping the runtime would wait for the read of stdin in progress, keeping the ssh
    // open after the hub closed the connection.
    runtime.shutdown_background();
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tls_settings_survive_restart_without_changing_ssh_hubs() {
        let mut settings = HubSettings::default();
        let args = ServeArgs {
            dir: None,
            advertise: Some("musubi://100.114.177.64:49655".to_owned()),
            listen: Some("0.0.0.0:49655".parse().unwrap()),
        };
        settings.configure(&args).unwrap();
        let saved = toml::to_string(&settings).unwrap();
        let mut restored: HubSettings = toml::from_str(&saved).unwrap();
        restored
            .configure(&ServeArgs {
                dir: None,
                advertise: None,
                listen: None,
            })
            .unwrap();
        assert_eq!(restored.listen, args.listen);
        assert_eq!(restored.advertise, args.advertise);
        let old: HubSettings = toml::from_str("advertise = 'devbox'").unwrap();
        assert!(old.listen.is_none());
        assert_eq!(old.advertise.as_deref(), Some("devbox"));
        assert_eq!(
            resolve("musubi://localhost:49655"),
            "musubi://localhost:49655"
        );
    }

    #[test]
    fn tls_invitation_input_stops_at_a_complete_block_or_malformed_token() -> anyhow::Result<()> {
        let group = format!("{}art", "abandon ".repeat(23));
        let phrase = format!("{group} {group}");
        let block = format!("{}\n", tls::key_block(&phrase));
        let mut input = io::Cursor::new(format!("{block}not part of the invitation\n"));
        assert_eq!(read_invitation(&mut input)?, block);
        assert_eq!(input.position(), block.len() as u64);
        let short = format!("{group} {group}");
        for text in [
            format!("{}\n", tls::key_block(&short)),
            format!("{short}\n"),
        ] {
            let mut input = io::Cursor::new(format!("{text}not part of the invitation\n"));
            assert_eq!(read_invitation(&mut input)?, text);
            assert_eq!(input.position(), text.len() as u64);
        }
        for malformed in ["not-a-word\n", "waytoolong\n"] {
            let mut input = io::Cursor::new(format!("{malformed}{phrase}\n"));
            assert_eq!(read_invitation(&mut input)?, malformed);
            assert_eq!(input.position(), malformed.len() as u64);
        }
        assert!(read_invitation(io::Cursor::new("")).is_err());
        assert!(read_invitation(io::Cursor::new("a".repeat(8193))).is_err());
        assert_eq!(
            read_invitation(io::Cursor::new("abandon\n\nanother line\n"))?,
            "abandon\n\n"
        );
        Ok(())
    }

    #[test]
    fn tls_settings_refuse_an_unusable_advertised_address() {
        for (advertise, listen) in [
            ("musubi://host:49655", None),
            ("host", Some("0.0.0.0:49655")),
            ("musubi://host:49655/path", Some("0.0.0.0:49655")),
            ("musubi://host:0", Some("0.0.0.0:0")),
        ] {
            let args = ServeArgs {
                dir: None,
                advertise: Some(advertise.to_owned()),
                listen: listen.map(|address| address.parse().unwrap()),
            };
            assert!(
                HubSettings::default().configure(&args).is_err(),
                "{advertise}"
            );
        }
    }

    #[test]
    fn names_for_this_machine_skip_ssh() {
        let here = |dest| names_this_machine(dest, Some("devbox"), Some("devbox.example.com"));
        for dest in [
            "localhost",
            "127.0.0.1",
            "::1",
            "devbox",
            "DevBox",
            "devbox.example.com",
        ] {
            assert!(here(dest), "{dest}");
        }
        // Other machines, and another account here, which may be another user's hub.
        for dest in ["laptop", "devbox.other.com", "you@localhost"] {
            assert!(!here(dest), "{dest}");
        }
        assert!(!names_this_machine("devbox", None, None));
    }

    /// However a hub's directory here is spelled, it is one hub, named as `musubi hub` names
    /// it: through its symbolic links, unless `..` follows one.
    #[cfg(unix)]
    #[test]
    fn a_hub_directory_has_one_form() {
        let root = tempfile::tempdir().unwrap();
        // As `musubi hub` would be given it, not canonical: on macOS the temporary directory
        // is behind a link.
        let root = root.path();
        let hub = root.join("hub");
        fs::create_dir_all(hub.join("sub")).unwrap();
        std::os::unix::fs::symlink(hub.join("sub"), root.join("link")).unwrap();
        for given in [
            hub.clone(),
            root.join("hub/"),
            root.join("hub/."),
            root.join("hub/sub/.."),
            root.join("elsewhere/../hub"),
        ] {
            assert_eq!(local_dir(&given).unwrap(), hub, "{given:?}");
        }
        // `link/..` is the directory above its target, not `root`.
        assert_eq!(
            local_dir(&root.join("link/..")).unwrap(),
            hub.canonicalize().unwrap()
        );
    }
}

#[cfg(test)]
mod request_tests;
