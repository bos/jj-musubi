//! `musubi hub`: serving a hub directory on a local socket, which `musubi hub connect`
//! relays to and commands on its machine connect to; and asking a hub about its hives.

use std::fmt::Write as _;
use std::fs;
use std::io;
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
use musubi_transport::stream::Writer;
use serde::Deserialize;
use serde::Serialize;
use tokio::sync::oneshot;

use crate::config;
use crate::lock::try_lock;
use crate::socket;
use crate::socket::Socket;
use crate::ssh;

/// What marks a directory as a hub's, and holds its settings.
const HUB_FILE: &str = "hub.toml";

/// The directory `musubi hub` uses without `--dir`.
const DEFAULT_DIR: &str = "musubi-hub";

/// The largest message the hub takes. Larger attachments move in chunks of about this size
/// (see [`musubi_sync::remote`]).
const MAX_PAYLOAD: usize = 1 << 20;

#[derive(Debug, Default, Serialize, Deserialize)]
struct HubSettings {
    /// The host name other machines ssh to this one by, once `--advertise` has given one: a
    /// machine's own name for itself isn't always one they can use.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    advertise: Option<String>,
}

impl HubSettings {
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
}

pub fn serve(args: ServeArgs) -> anyhow::Result<()> {
    let cwd = std::env::current_dir()?;
    let default = args.dir.is_none();
    let dir = match args.dir {
        Some(dir) => dir,
        None if cwd.join(HUB_FILE).exists() => cwd,
        None => cwd.join(DEFAULT_DIR),
    };
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
    // Absolute, but not canonical: on Windows that is a `\\?\` path, which git can't use.
    let dir = std::path::absolute(&dir)?;
    let Some(_dir_lock) = try_lock(&dir.join("hub.lock"))? else {
        anyhow::bail!("a hub is already serving {}", dir.display());
    };
    if default {
        fs::write(state.join("hub.path"), dir.display().to_string())?;
    }
    let mut settings = if created {
        HubSettings::default()
    } else {
        HubSettings::load(&dir)?
    };
    if args.advertise.is_some() {
        settings.advertise = args.advertise;
    }
    let socket = Socket::hub(&dir);
    if let Some(over) = socket.too_long() {
        anyhow::bail!(
            "the hub's socket, {socket}, would be {over} bytes longer than this system allows; \
             serve the hub from a shorter path"
        );
    }
    settings.save(&dir)?;
    let server = HubServer::open(&dir)?;
    match (created, server.hive_count()) {
        (true, _) => println!("Created a new hub in {}", dir.display()),
        (false, 1) => println!("Serving 1 hive from {}", dir.display()),
        (false, n) => println!("Serving {n} hives from {}", dir.display()),
    }
    // What other machines pass as --hub: the name they ssh to this machine by.
    let public = match &settings.advertise {
        Some(host) => host.clone(),
        None => whoami::hostname().unwrap_or_else(|_| "localhost".to_owned()),
    };
    // And what this one passes, which commands here leave out if it is the default.
    let local = dir.display().to_string();
    let mut saved = false;
    let user = config::UserConfig::update(|user| {
        if user.hub.is_none() {
            user.hub = Some(local.clone());
            saved = true;
        }
    })?;
    let default_here = user.hub.as_deref() == Some(local.as_str());
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
        let ready = || {
            answering.send(()).ok();
            // Whoever reads stdout may stop before the end, as `musubi hub | head -1` does;
            // println! would panic then, and the hub would stop serving.
            let mut stdout = io::stdout().lock();
            let mut text = String::new();
            if saved {
                let path = config::UserConfig::path()
                    .map(|path| path.display().to_string())
                    .unwrap_or_default();
                writeln!(text, "Saved this hub as this machine's default ({path}).").ok();
            }
            writeln!(
                text,
                "To share a repository:               musubi create --hub {public}\n\
                 To add another machine's copy of it: musubi join --hub {public}\n\
                 To make a new copy of a hive:        musubi clone <name> <dir> --hub {public}\n\
                 Other machines reach this hub over ssh: use the name they ssh to this machine \
                 by, if it isn't {public}."
            )
            .ok();
            if default_here {
                writeln!(text, "On this machine, leave out --hub.").ok();
            } else {
                writeln!(text, "On this machine, use --hub {local}.").ok();
            }
            stdout
                .write_all(text.as_bytes())
                .and_then(|()| stdout.flush())
                .ok();
            tracing::info!("serving {}", dir.display());
        };
        tokio::select! {
            result = server.run(Arc::new(network.connect()), ready) => result,
            () = accepting => Ok(()),
            () = interrupted() => Ok(()),
        }
    });
    if let Socket::Path(path) = &socket {
        fs::remove_file(path).ok();
    }
    result
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
    health: Option<ssh::Health>,
}

impl Connection {
    /// Why the hub can't be reached now, as far as ssh says.
    pub fn problem(&self) -> Option<String> {
        self.health.as_ref().and_then(ssh::Health::problem)
    }

    /// `err`, with why the hub can't be reached, if ssh says.
    pub fn explain(&self, err: anyhow::Error) -> anyhow::Error {
        match self.problem() {
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

/// `hub` as given to --hub, with a hub directory here made absolute, which given relative
/// would be taken for an ssh destination.
pub fn absolute(hub: &str) -> String {
    if !is_local(hub)
        && Path::new(hub).join(HUB_FILE).is_file()
        && let Ok(dir) = std::path::absolute(hub)
    {
        return dir.display().to_string();
    }
    hub.to_owned()
}

/// Connects to `hub`, an ssh destination or the directory of a hub on this machine, giving
/// up after `limit`.
pub async fn connect(hub: &str, limit: Duration) -> anyhow::Result<Connection> {
    let out_of_reach = |problem: Option<String>| match problem {
        Some(problem) => anyhow::anyhow!("the hub at {hub} is out of reach: {problem}"),
        None => anyhow::anyhow!("the hub at {hub} is out of reach"),
    };
    if is_local(hub) {
        let dir = PathBuf::from(hub);
        // Nothing to wait for if no hub is serving it.
        let first = Mutex::new(Some(open_local(&dir).await?));
        let local = Local { dir, first };
        let transport = tokio::time::timeout(limit, StreamTransport::connect(Arc::new(local)))
            .await
            .map_err(|_| out_of_reach(None))??;
        return Ok(Connection {
            transport: Arc::new(transport),
            health: None,
        });
    }
    let link = ssh::Link::new(hub)?;
    let health = link.health();
    let transport = tokio::time::timeout(limit, StreamTransport::connect(Arc::new(link)))
        .await
        .map_err(|_| out_of_reach(health.problem()))??;
    Ok(Connection {
        transport: Arc::new(transport),
        health: Some(health),
    })
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
        format!(
            "no hub is serving {} here; start one with `musubi hub`",
            dir.display()
        )
    };
    anyhow::ensure!(dir.join(HUB_FILE).exists(), not_serving());
    Socket::hub(&std::path::absolute(dir)?)
        .connect_stream()
        .await?
        .with_context(not_serving)
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
    let subject = rpc_subject(HUB_TOKEN);
    let payload = Bytes::from(Envelope::encode(request)?);
    let reply = match connection
        .transport
        .request(&subject, payload, Duration::from_secs(60))
        .await
    {
        Ok(reply) => reply,
        Err(TransportError::NoResponders(_)) => {
            anyhow::bail!("no hub is serving at {hub}; is `musubi hub` running?")
        }
        Err(err) => {
            return Err(connection.explain(anyhow::Error::new(err).context("asking the hub")));
        }
    };
    match Envelope::decode(&reply)? {
        HubWideReply::Error(message) => anyhow::bail!("{message}"),
        reply => Ok(reply),
    }
}

/// `musubi hub connect`: relays stdin and stdout to the socket of the hub serving `dir` (by
/// default, this user's hub), as the command a machine's daemon runs over ssh to reach it.
pub fn relay(dir: Option<PathBuf>) -> anyhow::Result<()> {
    let dir = match dir {
        Some(dir) => dir,
        None => {
            let path = config::state_dir()?.join("hub.path");
            let text = fs::read_to_string(&path)
                .context("no hub has run on this machine; start one with `musubi hub`")?;
            PathBuf::from(text.trim())
        }
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
