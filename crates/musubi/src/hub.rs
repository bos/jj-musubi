//! `musubi hub`: serving a hub directory, with a NATS server of its own unless given one;
//! and asking a hub about its hives.

use std::fmt::Write as _;
use std::fs;
use std::io::Write as _;
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
use crate::ssh;

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
    /// The host name other machines reach it by, once `--advertise` has given one: a
    /// machine's own name for itself isn't always one they can use.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    advertise: Option<String>,
    /// The address it listens on, once `--listen` has given one; else only this machine's
    /// loopback, which other machines reach over ssh (see [`crate::ssh`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    listen: Option<String>,
}

impl NatsSettings {
    fn listen(&self) -> &str {
        self.listen.as_deref().unwrap_or(LOOPBACK)
    }

    /// Where this machine reaches the server.
    fn local_host(&self) -> &str {
        match self.listen() {
            "0.0.0.0" | "::" => LOOPBACK,
            listen => listen,
        }
    }

    /// Whether only this machine can reach the server.
    fn loopback_only(&self) -> bool {
        self.listen()
            .parse::<std::net::IpAddr>()
            .is_ok_and(|ip| ip.is_loopback())
            || self.listen() == "localhost"
    }

    /// Its URL on this machine, with its token if it has one.
    fn local_url(&self) -> String {
        format!(
            "nats://{}{}:{}",
            self.credentials(),
            self.local_host(),
            self.port
        )
    }

    fn credentials(&self) -> String {
        self.token
            .as_ref()
            .map_or(String::new(), |token| format!("{token}@"))
    }
}

const LOOPBACK: &str = "127.0.0.1";

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
    pub listen: Option<String>,
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
    let was_local = settings.nats.as_ref().map(NatsSettings::local_url);
    if args.nats.is_none() {
        let nats = match settings.nats.take() {
            Some(nats) => nats,
            None => NatsSettings {
                port: free_port()?,
                token: None,
                advertise: None,
                listen: None,
            },
        };
        let token = match nats.token {
            None if args.token => Some(uuid::Uuid::new_v4().simple().to_string()),
            token => token,
        };
        let advertise = args.advertise.clone().or(nats.advertise);
        let listen = args.listen.clone().or(nats.listen);
        settings.nats = Some(NatsSettings {
            token,
            advertise,
            listen,
            ..nats
        });
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
        // What other machines pass as --hub: over ssh, the name they reach this machine by,
        // unless they can reach its NATS server themselves.
        let (local, public, over_ssh, _child) = match (&args.nats, &settings.nats) {
            (Some(url), _) => (url.clone(), url.clone(), false, None),
            (None, Some(nats)) => {
                let child = start_nats(&dir, nats)?;
                if child.is_none() && nats.token.is_some() {
                    // A server left by a hub that ran without a token would let anyone in.
                    let open = format!("nats://{}:{}", nats.local_host(), nats.port);
                    if connect(&open, Duration::from_secs(2)).await.is_ok() {
                        anyhow::bail!(
                            "the NATS server already on port {} doesn't require the hub's \
                             token; stop it (its pid is in {}) and start the hub again",
                            nats.port,
                            dir.join("nats.pid").display()
                        );
                    }
                }
                let host = match &nats.advertise {
                    Some(host) => host.clone(),
                    None => whoami::hostname().unwrap_or_else(|_| "localhost".to_owned()),
                };
                let public = if nats.loopback_only() {
                    host
                } else {
                    format!("nats://{}{host}:{}", nats.credentials(), nats.port)
                };
                (nats.local_url(), public, nats.loopback_only(), child)
            }
            (None, None) => unreachable!("chosen above"),
        };
        // Commands on this machine need no --hub. A default that was this hub's URL before
        // --listen or --token changed it follows it.
        let mut saved = false;
        let user = config::UserConfig::update(|user| {
            if user.hub.is_none() || user.hub == was_local {
                saved = user.hub.as_deref() != Some(local.as_str());
                user.hub = Some(local.clone());
            }
        })?;
        let default_here = user.hub.as_deref() == Some(local.as_str());
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
            // Whoever reads stdout may stop before the end, as `musubi hub | head -1` does;
            // println! would panic then, and the hub would stop serving.
            let mut stdout = std::io::stdout().lock();
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
                 To make a new copy of a hive:        musubi clone <name> <dir> --hub {public}"
            )
            .ok();
            if over_ssh {
                writeln!(
                    text,
                    "Other machines reach this hub over ssh: use the name they ssh to this \
                     machine by, if it isn't {public}."
                )
                .ok();
            }
            if default_here {
                writeln!(text, "On this machine, leave out --hub.").ok();
            }
            stdout
                .write_all(text.as_bytes())
                .and_then(|()| stdout.flush())
                .ok();
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
    if TcpStream::connect((nats.local_host(), nats.port)).is_ok() {
        tracing::info!("using the NATS server already on port {}", nats.port);
        return Ok(None);
    }
    let log = dir.join("nats.log");
    let mut command = Command::new("nats-server");
    command.args(["-a", nats.listen(), "-p", &nats.port.to_string()]);
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
    while TcpStream::connect((nats.local_host(), nats.port)).is_err() {
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

/// Whether `hub`, as given to --hub, is a NATS URL rather than an ssh destination, which
/// may be an `ssh://` URL.
pub fn is_nats_url(hub: &str) -> bool {
    hub.contains("://") && !hub.starts_with("ssh://")
}

/// Connects to `hub`, a NATS URL or an ssh destination, giving up after `limit`.
pub async fn connect(hub: &str, limit: Duration) -> anyhow::Result<Connection> {
    let out_of_reach = |problem: Option<String>| {
        let shown = without_credentials(hub);
        match problem {
            Some(problem) => anyhow::anyhow!("the hub at {shown} is out of reach: {problem}"),
            None => anyhow::anyhow!("the hub at {shown} is out of reach"),
        }
    };
    if is_nats_url(hub) {
        let transport = tokio::time::timeout(limit, NatsTransport::connect(hub))
            .await
            .map_err(|_| out_of_reach(None))??;
        return Ok(Connection {
            transport: Arc::new(transport),
            health: None,
        });
    }
    let tunnel = ssh::Tunnel::open(hub).await?;
    let health = tunnel.health();
    let url = format!("nats://{LOOPBACK}:{}", tunnel.port());
    let nats = tokio::time::timeout(limit, NatsTransport::connect(&url))
        .await
        .map_err(|_| out_of_reach(health.problem()))??;
    Ok(Connection {
        transport: Arc::new(ssh::SshTransport::new(nats, tunnel)),
        health: Some(health),
    })
}

/// Asks `hub` about its hives; a refusal is an error.
pub async fn ask(hub: &str, request: HubWideRequest) -> anyhow::Result<HubWideReply> {
    // Over ssh, longer than ssh's own ConnectTimeout.
    let limit = Duration::from_secs(if is_nats_url(hub) { 10 } else { 30 });
    let connection = connect(hub, limit).await?;
    ask_over(&connection, hub, request).await
}

pub async fn ask_over(
    connection: &Connection,
    hub: &str,
    request: HubWideRequest,
) -> anyhow::Result<HubWideReply> {
    let subject = format!("{}.{HUB_TOKEN}.rpc", default_subject_prefix());
    let payload = Bytes::from(Envelope::encode(request)?);
    let reply = match connection
        .transport
        .request(&subject, payload, Duration::from_secs(60))
        .await
    {
        Ok(reply) => reply,
        Err(TransportError::NoResponders(_)) => anyhow::bail!(
            "no hub is serving at {}; is `musubi hub` running?",
            without_credentials(hub)
        ),
        Err(err) => {
            return Err(connection.explain(anyhow::Error::new(err).context("asking the hub")));
        }
    };
    match Envelope::decode(&reply)? {
        HubWideReply::Error(message) => anyhow::bail!("{message}"),
        reply => Ok(reply),
    }
}

/// `musubi hub connect`: relays stdin and stdout to the NATS server of the hub serving `dir`
/// (by default, this user's hub), as the command a machine's daemon runs over ssh to reach
/// it. A token the server requires goes into the client's `CONNECT`, so it never leaves
/// this machine.
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
    let settings = HubSettings::load(&dir)?;
    let nats = settings.nats.with_context(|| {
        format!(
            "the hub in {} serves on a NATS server it doesn't run; connect to that directly",
            dir.display()
        )
    })?;
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    let result = runtime.block_on(async {
        use tokio::io::AsyncBufReadExt as _;
        use tokio::io::AsyncWriteExt as _;
        let stream = tokio::net::TcpStream::connect((nats.local_host(), nats.port))
            .await
            .with_context(|| {
                format!(
                    "no hub is serving {} here (nothing listens on port {}); is `musubi hub` \
                     running?",
                    dir.display(),
                    nats.port
                )
            })?;
        stream.set_nodelay(true)?;
        let (mut from_hub, mut to_hub) = stream.into_split();
        let mut stdin = tokio::io::BufReader::new(tokio::io::stdin());
        let mut stdout = tokio::io::stdout();
        let up = async {
            if let Some(token) = &nats.token {
                let mut line = String::new();
                stdin.read_line(&mut line).await?;
                to_hub
                    .write_all(with_token(&line, token).as_bytes())
                    .await?;
            }
            tokio::io::copy_buf(&mut stdin, &mut to_hub).await?;
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
        Ok(())
    });
    // Dropping the runtime would wait for the read of stdin in progress, keeping the ssh
    // open after the server closed the connection.
    runtime.shutdown_background();
    result
}

/// A client's `CONNECT` line, giving `token`.
fn with_token(line: &str, token: &str) -> String {
    let Some(json) = line.strip_prefix("CONNECT ") else {
        return line.to_owned();
    };
    let Ok(serde_json::Value::Object(mut fields)) = serde_json::from_str(json.trim_end()) else {
        return line.to_owned();
    };
    fields.insert("auth_token".to_owned(), token.into());
    format!("CONNECT {}\r\n", serde_json::Value::Object(fields))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_relay_gives_the_token() {
        let line = with_token(
            "CONNECT {\"verbose\":false,\"pedantic\":false}\r\n",
            "s3cret",
        );
        let json = line.strip_prefix("CONNECT ").unwrap().trim_end();
        let fields: serde_json::Value = serde_json::from_str(json).unwrap();
        assert_eq!(fields["auth_token"], "s3cret");
        assert_eq!(fields["verbose"], false);
        assert!(line.ends_with("\r\n"));
        // Anything else passes through.
        assert_eq!(with_token("PING\r\n", "s3cret"), "PING\r\n");
    }
}
