//! `musubi hub`: serving a hub directory, with a NATS server of its own unless given one;
//! and asking a hub about its hives.

use std::fs;
use std::net::TcpStream;
use std::path::Path;
use std::path::PathBuf;
use std::process::Child;
use std::process::Command;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;

use anyhow::Context as _;
use bytes::Bytes;
use musubi_sync::server::HubServer;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HUB_TOKEN;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use musubi_transport::NatsTransport;
use musubi_transport::Transport;
use musubi_transport::TransportError;
use serde::Deserialize;
use serde::Serialize;

use crate::config;
use crate::config::default_subject_prefix;

/// What marks a directory as a hub's, and holds its own NATS server's settings.
const HUB_FILE: &str = "hub.toml";

/// The directory `musubi hub` uses without `--dir`.
const DEFAULT_DIR: &str = "musubi-hub";

#[derive(Debug, Default, Serialize, Deserialize)]
struct HubSettings {
    /// The NATS server the hub runs, chosen the first time it runs without `--nats`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    nats: Option<NatsSettings>,
}

#[derive(Debug, Serialize, Deserialize)]
struct NatsSettings {
    port: u16,
    /// A token clients must give, once `--token` has asked for one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    token: Option<String>,
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
    pub nats: Option<String>,
    pub advertise: Option<String>,
    /// Have the NATS server it starts require a token.
    pub token: bool,
}

/// Holds a lock file for as long as it lives.
struct Lock(#[expect(dead_code, reason = "held for its lock")] fs::File);

/// Takes the lock at `path`, or says what holds it.
fn try_lock(path: &Path) -> anyhow::Result<Option<Lock>> {
    if let Some(dir) = path.parent() {
        fs::create_dir_all(dir)?;
    }
    let file = fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(path)
        .with_context(|| format!("opening {path:?}"))?;
    match file.try_lock() {
        Ok(()) => Ok(Some(Lock(file))),
        Err(fs::TryLockError::WouldBlock) => Ok(None),
        Err(fs::TryLockError::Error(err)) => Err(err).with_context(|| format!("locking {path:?}")),
    }
}

/// Kills the NATS server the hub started when the hub stops.
struct NatsChild(Child);

impl Drop for NatsChild {
    fn drop(&mut self) {
        self.0.kill().ok();
        self.0.wait().ok();
    }
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
    if args.nats.is_none() {
        let nats = match settings.nats.take() {
            Some(nats) => nats,
            None => NatsSettings {
                port: free_port()?,
                token: None,
            },
        };
        let token = match nats.token {
            None if args.token => Some(uuid::Uuid::new_v4().simple().to_string()),
            token => token,
        };
        settings.nats = Some(NatsSettings { token, ..nats });
    }
    settings.save(&dir)?;
    let server = HubServer::open(&dir, &default_subject_prefix())?;
    match (created, server.hive_count()) {
        (true, _) => println!("Created a new hub in {}", dir.display()),
        (false, 1) => println!("Serving 1 hive from {}", dir.display()),
        (false, n) => println!("Serving {n} hives from {}", dir.display()),
    }
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    runtime.block_on(async {
        let (local, public, _child) = match (&args.nats, &settings.nats) {
            (Some(url), _) => (url.clone(), url.clone(), None),
            (None, Some(nats)) => {
                let child = start_nats(&dir, nats)?;
                if child.is_none() && nats.token.is_some() {
                    // A server left by a hub that ran without a token would let anyone in.
                    let open = format!("nats://127.0.0.1:{}", nats.port);
                    if connect(&open, Duration::from_secs(2)).await.is_ok() {
                        anyhow::bail!(
                            "the NATS server already on port {} doesn't require the hub's \
                             token; stop it (its pid is in {}) and start the hub again",
                            nats.port,
                            dir.join("nats.pid").display()
                        );
                    }
                }
                let host = match args.advertise {
                    Some(host) => host,
                    None => whoami::hostname().unwrap_or_else(|_| "localhost".to_owned()),
                };
                let credentials = nats
                    .token
                    .as_ref()
                    .map_or(String::new(), |token| format!("{token}@"));
                (
                    format!("nats://{credentials}127.0.0.1:{}", nats.port),
                    format!("nats://{credentials}{host}:{}", nats.port),
                    child,
                )
            }
            (None, None) => unreachable!("chosen above"),
        };
        let transport: Arc<dyn Transport> = Arc::new(
            tokio::time::timeout(Duration::from_secs(10), NatsTransport::connect(&local))
                .await
                .with_context(|| {
                    format!(
                        "cannot connect to the NATS server at {}",
                        without_credentials(&local)
                    )
                })??,
        );
        let ready = || {
            println!("To add a repository on any machine: musubi join --nats {public}");
            println!(
                "To make a new copy of a hive:       musubi clone <name> <dir> --nats {public}"
            );
            tracing::info!("serving {}", dir.display());
        };
        tokio::select! {
            result = server.run(transport, ready) => result,
            () = interrupted() => Ok(()),
        }
    })
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

/// A port nothing listens on now.
fn free_port() -> anyhow::Result<u16> {
    Ok(std::net::TcpListener::bind("0.0.0.0:0")?
        .local_addr()?
        .port())
}

/// Starts `nats-server` on the hub's port, with its token if it has one, unless one is already listening
/// there, as when a hub was killed and its server lived on.
fn start_nats(dir: &Path, nats: &NatsSettings) -> anyhow::Result<Option<NatsChild>> {
    if TcpStream::connect(("127.0.0.1", nats.port)).is_ok() {
        tracing::info!("using the NATS server already on port {}", nats.port);
        return Ok(None);
    }
    let log = dir.join("nats.log");
    let mut command = Command::new("nats-server");
    command.args(["-a", "0.0.0.0", "-p", &nats.port.to_string()]);
    // The token goes in a config file only its owner can read, not on the command line,
    // where anyone on the machine could see it.
    let conf = dir.join("nats.conf");
    match &nats.token {
        Some(token) => {
            let text = format!("authorization {{\n  token: \"{token}\"\n}}\n");
            config::write_private(&conf, text.as_bytes())?;
            command.arg("-c").arg(&conf);
        }
        None => match fs::remove_file(&conf) {
            Ok(()) => {}
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
            Err(err) => return Err(err).with_context(|| format!("removing {conf:?}")),
        },
    }
    let child = command
        .arg("-l")
        .arg(&log)
        .arg("-P")
        .arg(dir.join("nats.pid"))
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn();
    let child = match child {
        Ok(child) => NatsChild(child),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => anyhow::bail!(
            "nats-server is not on PATH. Install it (https://docs.nats.io/running-a-nats-service/\
             introduction/installation, or `brew install nats-server`), or pass --nats <url> \
             for a NATS server you run yourself"
        ),
        Err(err) => return Err(err).context("starting nats-server"),
    };
    let mut child = child;
    let deadline = Instant::now() + Duration::from_secs(10);
    while TcpStream::connect(("127.0.0.1", nats.port)).is_err() {
        if let Some(status) = child.0.try_wait()? {
            let log = fs::read_to_string(&log).unwrap_or_default();
            let tail: Vec<&str> = log.lines().rev().take(5).collect();
            let tail: Vec<&str> = tail.into_iter().rev().collect();
            anyhow::bail!(
                "nats-server exited ({status}) on port {}:\n{}\nIf something else has the port, \
                 choose another in {}",
                nats.port,
                tail.join("\n"),
                dir.join(HUB_FILE).display()
            );
        }
        anyhow::ensure!(
            Instant::now() < deadline,
            "nats-server did not start listening on port {}",
            nats.port
        );
        std::thread::sleep(Duration::from_millis(20));
    }
    Ok(Some(child))
}

/// `url` without the token or password in it, for showing.
pub fn without_credentials(url: &str) -> String {
    let Some((scheme, rest)) = url.split_once("://") else {
        return url.to_owned();
    };
    let authority_end = rest.find('/').unwrap_or(rest.len());
    match rest[..authority_end].rfind('@') {
        Some(at) => format!("{scheme}://{}", &rest[at + 1..]),
        None => url.to_owned(),
    }
}

/// Connects to the hub at `nats`, giving up after `limit`.
pub async fn connect(nats: &str, limit: Duration) -> anyhow::Result<Arc<dyn Transport>> {
    let transport = tokio::time::timeout(limit, NatsTransport::connect(nats))
        .await
        .map_err(|_| {
            anyhow::anyhow!("the hub at {} is out of reach", without_credentials(nats))
        })??;
    Ok(Arc::new(transport))
}

/// Asks the hub at `nats` about its hives; a refusal is an error.
pub async fn ask(nats: &str, request: HubWideRequest) -> anyhow::Result<HubWideReply> {
    let transport = connect(nats, Duration::from_secs(10)).await?;
    ask_over(&*transport, nats, request).await
}

pub async fn ask_over(
    transport: &dyn Transport,
    nats: &str,
    request: HubWideRequest,
) -> anyhow::Result<HubWideReply> {
    let subject = format!("{}.{HUB_TOKEN}.rpc", default_subject_prefix());
    let payload = Bytes::from(Envelope::encode(request)?);
    let reply = match transport
        .request(&subject, payload, Duration::from_secs(60))
        .await
    {
        Ok(reply) => reply,
        Err(TransportError::NoResponders(_)) => anyhow::bail!(
            "no hub is serving at {}; is `musubi hub` running?",
            without_credentials(nats)
        ),
        Err(err) => return Err(err).context("asking the hub"),
    };
    match Envelope::decode(&reply)? {
        HubWideReply::Error(message) => anyhow::bail!("{message}"),
        reply => Ok(reply),
    }
}
