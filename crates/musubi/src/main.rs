//! `musubi`: replicate jj repositories between machines.

mod agent;
mod config;
mod control;
mod daemon;
mod hub;
mod lock;
mod login;
mod repo;
mod settings;
mod socket;
mod ssh;
mod watch;

use std::collections::BTreeMap;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command as Process;
use std::time::Duration;

use anyhow::Context as _;
use clap::Parser;
use clap::Subcommand;
use jj_lib::object_id::ObjectId as _;
use musubi_hub::hub_dir::HiveInfo;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::JoinRequest;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use crate::config::HiveConfig;
use crate::config::UserConfig;
use crate::control::Synced;
use crate::daemon::Status;
use crate::repo::Located;
use crate::socket::Socket;

#[derive(Parser)]
#[command(
    name = "musubi",
    version,
    about = "Replicate jj repositories between machines"
)]
struct Cli {
    /// The daemon's control socket, in place of the usual one.
    #[arg(long, global = true, env = "MUSUBI_SOCKET", hide_env = true)]
    socket: Option<String>,
    /// What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`.
    /// It applies to this command, not to a daemon it starts, which uses `[daemon] log` in
    /// the user config.
    #[arg(long, global = true, value_name = "FILTER")]
    log: Option<String>,
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Run a hub, which stores hives and orders their updates. Serves every hive in its
    /// directory, to other machines over ssh.
    #[command(args_conflicts_with_subcommands = true)]
    Hub {
        #[command(subcommand)]
        action: Option<HubAction>,
        /// The hub's directory [default: ./musubi-hub, or the current directory if it is a
        /// hub's].
        #[arg(short, long)]
        dir: Option<PathBuf>,
        /// The host name other machines ssh to this one by, for the commands it prints
        /// [default: this machine's host name]. Once given, the hub keeps it (in hub.toml).
        #[arg(long)]
        advertise: Option<String>,
    },
    /// Start a hive on the hub from the repository in the current directory, for other
    /// copies of it to join.
    Create {
        /// The hive's name [default: the repository's name on its forge, from its `origin`
        /// remote, else the directory's name].
        name: Option<String>,
        #[command(flatten)]
        member: Member,
    },
    /// Make the repository in the current directory part of the hive on the hub it shares
    /// history and a remote with.
    Join {
        /// Join this hive (a name, a prefix of one, or an id), whatever its remotes.
        #[arg(long)]
        hive: Option<String>,
        #[command(flatten)]
        member: Member,
    },
    /// Create a new colocated repository from a hive.
    Clone {
        /// The hive: a name, a prefix of one, or an id.
        hive: String,
        destination: PathBuf,
        /// The hub, as `musubi hub` prints it [default: the one first joined].
        #[arg(long)]
        hub: Option<String>,
        /// This machine's name in the hive. Defaults to jj's `operation.hostname`.
        #[arg(long)]
        machine: Option<String>,
    },
    /// List the hub's hives, this machine's copies of them, and how their syncing goes
    /// (the default command).
    #[command(alias = "status")]
    List,
    /// Stop syncing the repository in the current directory.
    Leave,
    /// Sync the repository in the current directory now.
    Sync,
    /// Run the daemon that keeps this machine's repositories in sync, or control it.
    Daemon {
        #[command(subcommand)]
        action: Option<DaemonAction>,
    },
    /// Tools for investigating a hive, not for everyday use.
    #[command(hide = true, subcommand)]
    Debug(Debug),
}

/// How a repository takes part in a hive, for `create` and `join`.
#[derive(clap::Args)]
struct Member {
    /// This machine's name in the hive, which other machines show its workspaces under, as
    /// in `laptop/default`. Defaults to jj's `operation.hostname`.
    #[arg(long)]
    machine: Option<String>,
    /// Replicate the whole operation history, not just the current state.
    #[arg(long)]
    full_history: bool,
    /// The hub, as `musubi hub` prints it: the name this machine ssh-es to the hub's machine
    /// by, or on that machine, the hub's directory [default: the one first joined].
    #[arg(long)]
    hub: Option<String>,
}

#[derive(Subcommand)]
enum Debug {
    /// Translate an operation id between this machine's id and the hive's.
    OpId { id: String },
}

#[derive(Subcommand)]
enum HubAction {
    /// Remove a hive from the hub. Its store moves to the hub's `removed/` directory.
    Rm {
        hive: String,
        #[arg(long)]
        hub: Option<String>,
    },
    /// Rename a hive.
    Rename {
        hive: String,
        new_name: String,
        #[arg(long)]
        hub: Option<String>,
    },
    /// Relay stdin and stdout to this machine's hub: what other machines run over ssh to
    /// reach it.
    Connect {
        /// The hub's directory [default: the one `musubi hub` last served without --dir].
        #[arg(short, long)]
        dir: Option<PathBuf>,
    },
}

#[derive(Subcommand)]
enum DaemonAction {
    /// Start the daemon in the background, unless it is running.
    Start,
    /// Stop the running daemon.
    Stop,
    /// Stop the running daemon, if any, and start a new one in the background.
    Restart,
    /// Start the daemon at login from now on (a launchd agent on macOS, a systemd user
    /// unit on Linux, a Run registry entry on Windows), and now.
    Install,
    /// Stop starting the daemon at login, and stop it.
    Uninstall,
}

/// What to log: `--log`, else `RUST_LOG`, else for the daemon `[daemon] log` in the user
/// config. Otherwise the hub and the daemon log what they do, and other commands only
/// warn, since they say what they did themselves.
fn log_filter(cli: &Cli) -> anyhow::Result<tracing_subscriber::EnvFilter> {
    let daemon = matches!(cli.command, Some(Command::Daemon { action: None }));
    let hub = matches!(cli.command, Some(Command::Hub { action: None, .. }));
    if let Some(filter) = &cli.log {
        return parse_filter(filter).with_context(|| format!("bad log filter {filter:?}"));
    }
    // Other programs read RUST_LOG too, so one this can't read is passed over, not fatal.
    if let Ok(filter) = std::env::var("RUST_LOG")
        && !filter.is_empty()
    {
        match parse_filter(&filter) {
            Ok(filter) => return Ok(filter),
            Err(err) => eprintln!("Ignoring RUST_LOG={filter:?} ({err})."),
        }
    }
    if daemon && let Some(filter) = UserConfig::load()?.daemon.log {
        return parse_filter(&filter)
            .with_context(|| format!("bad log filter {filter:?} under [daemon] in the config"));
    }
    if daemon || hub {
        return parse_filter("info");
    }
    // Commands say why a hub is out of reach in their error; the ssh link would say it
    // again at every retry.
    parse_filter("warn,musubi::ssh=off")
}

/// Parses a filter in `RUST_LOG`'s syntax.
fn parse_filter(filter: &str) -> anyhow::Result<tracing_subscriber::EnvFilter> {
    Ok(tracing_subscriber::EnvFilter::try_new(filter)?)
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    tracing_subscriber::fmt()
        .with_env_filter(log_filter(&cli)?)
        .with_writer(std::io::stderr)
        .init();
    // Serving a hub, and `hub connect`, are for other machines, whose agents aren't this
    // machine's; the daemon itself has the link, or the service manager's agent.
    if !matches!(
        cli.command,
        Some(
            Command::Hub {
                action: None | Some(HubAction::Connect { .. }),
                ..
            } | Command::Daemon { action: None }
        )
    ) && let Err(err) = agent::refresh()
    {
        tracing::debug!("not pointing the daemon at this ssh agent: {err:#}");
    }
    let cwd = std::env::current_dir()?;
    let socket = || Socket::locate(cli.socket.as_deref());
    match cli.command.unwrap_or(Command::List) {
        Command::Hub {
            action: None,
            dir,
            advertise,
        } => hub::serve(hub::ServeArgs { dir, advertise }),
        Command::Hub {
            action: Some(HubAction::Connect { dir }),
            ..
        } => hub::relay(dir),
        Command::Hub {
            action: Some(HubAction::Rm { hive, hub }),
            ..
        } => block_on(async {
            let hub = UserConfig::hub(hub.as_deref())?;
            let reply = hub::ask(&hub, HubWideRequest::Remove { name: hive }).await?;
            if let HubWideReply::Hive(info) = reply {
                println!("Removed hive {}", info.name);
            }
            Ok(())
        }),
        Command::Hub {
            action:
                Some(HubAction::Rename {
                    hive,
                    new_name,
                    hub,
                }),
            ..
        } => block_on(async {
            let hub = UserConfig::hub(hub.as_deref())?;
            let request = HubWideRequest::Rename {
                name: hive.clone(),
                to: new_name,
            };
            if let HubWideReply::Hive(info) = hub::ask(&hub, request).await? {
                println!("Renamed hive {hive} to {}", info.name);
            }
            Ok(())
        }),
        Command::Create { name, member } => {
            join(&cwd, JoinChoice::Create(name), &member, &socket()?)
        }
        Command::Join { hive, member } => {
            let choice = hive.map_or(JoinChoice::Match, JoinChoice::Hive);
            join(&cwd, choice, &member, &socket()?)
        }
        Command::Clone {
            hive,
            destination,
            hub,
            machine,
        } => clone(
            &destination,
            &hive,
            hub.as_deref(),
            machine.as_deref(),
            &socket()?,
        ),
        Command::List => list(&cwd, socket()),
        Command::Leave => leave(&cwd, &socket()?),
        Command::Daemon { action: None } => daemon::run(&socket()?),
        Command::Daemon {
            action: Some(DaemonAction::Start),
        } => block_on(async {
            daemon::ensure(&socket()?).await?;
            Ok(())
        }),
        Command::Daemon {
            action: Some(DaemonAction::Install),
        } => block_on(async {
            let socket = socket()?;
            // The service manager starts the daemon from now on, so stop one started
            // otherwise.
            daemon::stop(&socket).await?;
            let described = login::install()?;
            daemon::ensure(&socket).await?;
            println!("The daemon starts at login from now on, through {described}.");
            if cfg!(target_os = "linux") {
                println!(
                    "To keep it running while you're logged out, as on a server: \
                     loginctl enable-linger"
                );
            }
            Ok(())
        }),
        Command::Daemon {
            action: Some(DaemonAction::Uninstall),
        } => block_on(async {
            let socket = socket()?;
            let was = login::uninstall()?;
            daemon::stop(&socket).await?;
            if was {
                println!("The daemon no longer starts at login, and is stopped.");
            } else {
                println!("The daemon wasn't set to start at login.");
            }
            Ok(())
        }),
        Command::Daemon {
            action: Some(DaemonAction::Stop),
        } => block_on(async {
            if daemon::stop(&socket()?).await? {
                println!("Stopped the daemon.");
            } else {
                println!("No daemon is running.");
            }
            Ok(())
        }),
        Command::Daemon {
            action: Some(DaemonAction::Restart),
        } => block_on(async {
            let socket = socket()?;
            daemon::stop(&socket).await?;
            daemon::ensure(&socket).await?;
            println!("Started the daemon.");
            Ok(())
        }),
        Command::Sync => sync(&cwd, &socket()?),
        Command::Debug(Debug::OpId { id }) => op_id(&cwd, &id),
    }
}

fn block_on<T>(future: impl Future<Output = anyhow::Result<T>>) -> anyhow::Result<T> {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?
        .block_on(future)
}

/// Makes the repository at `start` part of a hive: the hub decides which (see
/// `musubi_hub::matching`); then this records the membership and has the daemon serve it.
fn join(start: &Path, choice: JoinChoice, member: &Member, socket: &Socket) -> anyhow::Result<()> {
    let Member {
        machine,
        full_history,
        hub,
    } = member;
    let (hub, machine, full_history) = (hub.as_deref(), machine.as_deref(), *full_history);
    let located = Located::find(start)?;
    if let Some(hive) = HiveConfig::load(&located.repo_path)? {
        anyhow::bail!(
            "this repository is already part of hive {}; `musubi leave` first to join another",
            hive.display_name()
        );
    }
    let hub = UserConfig::hub(hub)?;
    set_machine_name(&located, machine)?;
    let node = located.open()?;
    let summary = node.join_summary()?;
    let request = JoinRequest {
        choice,
        backend: summary.backend,
        remotes: summary
            .remotes
            .into_iter()
            .flat_map(|(name, remote)| {
                let urls: Vec<String> = remote.urls().map(str::to_owned).collect();
                urls.into_iter().map(move |url| (name.clone(), url))
            })
            .collect(),
        dir_name: located
            .workspace_root
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default(),
        roots: summary.roots.iter().map(|id| id.hex()).collect(),
        remote_targets: summary.remote_targets.iter().map(|id| id.hex()).collect(),
        machine: node.machine().key().to_owned(),
    };
    drop(node);
    let joined = match block_on(ask_preparing(&hub, HubWideRequest::Join(request)))? {
        HubWideReply::Joined(joined) => joined,
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    };
    become_node(&located, &joined.hive, &hub, full_history)?;
    let count = joined.hive.machines.len();
    let machines = if count == 1 {
        "1 machine".to_owned()
    } else {
        format!("{count} machines")
    };
    if joined.created {
        println!("Created hive {}", joined.hive.name);
    } else {
        println!(
            "Joined hive {} ({}), {machines}",
            joined.hive.name, joined.reason
        );
    }
    start_serving(&located, socket)
}

/// Asks `hub`, over ssh first making sure this machine's key works there.
async fn ask_preparing(hub: &str, request: HubWideRequest) -> anyhow::Result<HubWideReply> {
    if !hub::is_local(hub) {
        ssh::prepare(hub).await?;
    }
    hub::ask(hub, request).await
}

fn set_machine_name(located: &Located, machine: Option<&str>) -> anyhow::Result<()> {
    if let Some(name) = machine {
        let settings = settings::load(&located.workspace_root, &located.repo_path)?;
        let machine = NodeRepo::name_machine(&located.repo_path, name, &settings)?;
        // The same name again, as when retrying a refused join, is no change.
        anyhow::ensure!(
            machine.name() == musubi_jj::workspaces::sanitize(name),
            "this repository's machine is already named {}",
            machine.name()
        );
    }
    Ok(())
}

/// Records that the repository is part of `hive`: the join operation (unless replicating
/// full history), its hive config, and its place in the user's config. The first hub joined
/// becomes the user's default.
fn become_node(
    located: &Located,
    hive: &HiveInfo,
    hub: &str,
    full_history: bool,
) -> anyhow::Result<()> {
    let mut node = located.open()?;
    let machine = node.machine().name().to_owned();
    if !full_history {
        node.create_join_operation(&format!("musubi: {machine} joins the hive"))?;
    }
    let config = HiveConfig {
        hive: hive
            .id
            .parse()
            .context("the hub sent a malformed hive id")?,
        name: Some(hive.name.clone()),
        hub: hub.to_owned(),
        node: machine,
    };
    config.save(&located.repo_path)?;
    UserConfig::add_repo(&located.workspace_root)?;
    let mut saved = false;
    UserConfig::update(|config| {
        if config.hub.is_none() {
            config.hub = Some(hub.to_owned());
            saved = true;
        }
    })?;
    if saved {
        println!(
            "Saved {hub} as this machine's default hub ({}).",
            UserConfig::path()?.display()
        );
    }
    Ok(())
}

/// Has the daemon, started if need be, serve the repository, and reports its first sync.
/// Without a daemon, syncs once.
fn start_serving(located: &Located, socket: &Socket) -> anyhow::Result<()> {
    /// How asking the daemon to serve the repository went.
    enum Served {
        /// There was no daemon to ask, nor could one be started.
        NoDaemon(anyhow::Error),
        Synced(Synced),
        /// The daemon serves it, but its first sync failed, saying this.
        Failed(String),
    }
    let workspace = located.workspace_root.clone();
    // The client lives on the runtime that made it, so one runtime does it all.
    let served = block_on(async {
        let client = match daemon::ensure(socket).await {
            Ok(client) => client,
            Err(err) => return Ok(Served::NoDaemon(err)),
        };
        println!("Syncing...");
        let first = client
            .add(control::context(Duration::from_secs(3600)), workspace)
            .await
            .context("asking the daemon to serve this repository")?;
        Ok::<_, anyhow::Error>(match first {
            Ok(synced) => Served::Synced(synced),
            Err(message) => Served::Failed(message),
        })
    })?;
    match served {
        Served::NoDaemon(err) => {
            eprintln!("Could not start the daemon ({err:#}); syncing once instead.");
            let synced = sync_directly(located)?;
            println!(
                "Synced (hive at #{}). Run `musubi daemon` to keep it in sync.",
                synced.seq
            );
            Ok(())
        }
        Served::Synced(synced) => {
            println!(
                "Synced with the hub (hive at #{}). The daemon keeps it in sync from now on.",
                synced.seq
            );
            if !login::installed() {
                println!("To start the daemon at login too: musubi daemon install");
            }
            Ok(())
        }
        Served::Failed(message) => anyhow::bail!(
            "the first sync failed: {message}\nThe daemon keeps trying; `musubi list` shows how \
             it goes."
        ),
    }
}

fn clone(
    destination: &Path,
    hive: &str,
    hub: Option<&str>,
    machine: Option<&str>,
    socket: &Socket,
) -> anyhow::Result<()> {
    let hub = UserConfig::hub(hub)?;
    let reply = block_on(ask_preparing(
        &hub,
        HubWideRequest::Resolve {
            name: hive.to_owned(),
        },
    ))?;
    let HubWideReply::Hive(info) = reply else {
        anyhow::bail!("unexpected reply from the hub: {reply:?}");
    };
    let dest = destination.to_str().context("destination is not UTF-8")?;
    let init: &[&str] = match info.backend {
        Backend::Git => &["git", "init", "--colocate"],
        Backend::Simple => &["debug", "init-simple"],
    };
    let mut jj = Process::new("jj");
    musubi_jj::git_command::without_repository_env(&mut jj);
    let status = jj.args(init).arg(dest).status()?;
    anyhow::ensure!(status.success(), "`jj {} {dest}` failed", init.join(" "));
    let located = Located::find(destination)?;
    set_machine_name(&located, machine)?;
    become_node(&located, &info, &hub, false)?;
    println!("Cloning hive {} into {}", info.name, destination.display());
    start_serving(&located, socket)
}

/// Syncs once, in this process.
fn sync_directly(located: &Located) -> anyhow::Result<Synced> {
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    block_on(daemon::sync_once(located, &hive))
}

/// Syncs through the daemon when it serves the repository, else directly.
fn sync(start: &Path, socket: &Socket) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    let served = UserConfig::load()?.repos.contains(&located.workspace_root);
    let through_daemon = block_on(async {
        if !served {
            return Ok(None);
        }
        let Some(client) = daemon::running(socket).await? else {
            return Ok(None);
        };
        let workspace = located.workspace_root.clone();
        let synced = client
            .sync(control::context(Duration::from_secs(3600)), workspace)
            .await?;
        Ok::<_, anyhow::Error>(Some(synced))
    })?;
    let synced = match through_daemon {
        Some(Ok(synced)) => synced,
        Some(Err(message)) => anyhow::bail!("{message}"),
        None => sync_directly(&located)?,
    };
    println!("Synced (hive at #{}).", synced.seq);
    Ok(())
}

fn leave(start: &Path, socket: &Socket) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    block_on(async {
        if let Some(client) = daemon::running(socket).await? {
            client
                .remove(
                    control::context(Duration::from_secs(120)),
                    located.workspace_root.clone(),
                )
                .await?
                .map_err(anyhow::Error::msg)?;
        }
        Ok(())
    })?;
    UserConfig::remove_repo(&located.workspace_root)?;
    std::fs::remove_file(HiveConfig::path(&located.repo_path))?;
    std::fs::remove_file(Status::path(&located.repo_path)).ok();
    println!(
        "This repository no longer syncs with hive {}. Everything it has stays.",
        hive.display_name()
    );
    Ok(())
}

/// A repository on this machine that is part of a hive.
struct Copy {
    located: Located,
    hive: HiveConfig,
    status: Option<Status>,
}

/// Lists what it can: a daemon or hub out of reach is a line of the listing.
fn list(start: &Path, socket: anyhow::Result<Socket>) -> anyhow::Result<()> {
    let config = UserConfig::load()?;
    let (daemon, statuses) = block_on(async {
        let running = match &socket {
            Ok(socket) => daemon::running(socket).await,
            Err(err) => Err(anyhow::anyhow!("{err:#}")),
        };
        let client = match running {
            Ok(Some(client)) => client,
            Ok(None) => return Ok((Ok(false), BTreeMap::new())),
            Err(err) => return Ok((Err(err), BTreeMap::new())),
        };
        let statuses: BTreeMap<PathBuf, Status> = client
            .status(control::context(Duration::from_secs(10)))
            .await?
            .into_iter()
            .map(|repo| (repo.workspace, repo.status))
            .collect();
        Ok::<_, anyhow::Error>((Ok(true), statuses))
    })?;
    let mut copies = vec![];
    for workspace in &config.repos {
        let Ok(located) = Located::find(workspace) else {
            println!(
                "{} is gone; remove it from {}",
                workspace.display(),
                UserConfig::path()?.display()
            );
            continue;
        };
        let Some(hive) = HiveConfig::load(&located.repo_path)? else {
            continue;
        };
        let status = statuses
            .get(workspace)
            .cloned()
            .or_else(|| Status::load(&located.repo_path));
        copies.push(Copy {
            located,
            hive,
            status,
        });
    }
    // Every hub this machine knows of, the default first.
    let mut hubs: Vec<String> = config.hub.iter().cloned().collect();
    for copy in &copies {
        if !hubs.contains(&copy.hive.hub) {
            hubs.push(copy.hive.hub.clone());
        }
    }
    if hubs.is_empty() {
        println!("No hubs yet: run `musubi hub` on one machine, then the join command it prints.");
    }
    for hub in &hubs {
        let here: Vec<&Copy> = copies.iter().filter(|copy| &copy.hive.hub == hub).collect();
        match block_on(list_hub(hub)) {
            Ok(hives) => {
                println!("Hub {hub}:");
                if hives.is_empty() {
                    println!("  no hives yet");
                }
                for info in &hives {
                    let machines = match info.machines.as_slice() {
                        [] => "no machines yet".to_owned(),
                        [one] => format!("1 machine: {one}"),
                        all => format!("{} machines: {}", all.len(), all.join(", ")),
                    };
                    println!("  {}  {machines}", info.name);
                    for copy in here.iter().filter(|c| c.hive.hive.to_string() == info.id) {
                        print_copy(copy);
                    }
                }
                for copy in here
                    .iter()
                    .filter(|copy| !hives.iter().any(|h| h.id == copy.hive.hive.to_string()))
                {
                    println!("  {}  (no longer on the hub)", copy.hive.display_name());
                    print_copy(copy);
                }
            }
            Err(err) => {
                println!("Hub {hub}: {err:#}. This machine's copies:");
                for copy in &here {
                    println!("  {}", copy.hive.display_name());
                    print_copy(copy);
                }
            }
        }
    }
    let at_login = if login::installed() {
        "starts at login"
    } else {
        "doesn't start at login; `musubi daemon install` makes it"
    };
    match daemon {
        Ok(true) => println!(
            "Daemon: running, serving {} repositories; {at_login}",
            statuses.len()
        ),
        Ok(false) => println!("Daemon: not running ({at_login}); `musubi daemon start` starts it"),
        Err(err) => println!("Daemon: {err:#}"),
    }
    if let Ok(located) = Located::find(start)
        && let Some(hive) = HiveConfig::load(&located.repo_path)?
    {
        print_details(&located, &hive)?;
    }
    Ok(())
}

async fn list_hub(hub: &str) -> anyhow::Result<Vec<HiveInfo>> {
    // Over ssh, through a ProxyCommand, connecting takes a while.
    let limit = Duration::from_secs(if hub::is_local(hub) { 3 } else { 15 });
    let connection = hub::connect(hub, limit).await?;
    match hub::ask_over(&connection, hub, HubWideRequest::List).await? {
        HubWideReply::Hives(hives) => Ok(hives),
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    }
}

fn print_copy(copy: &Copy) {
    println!(
        "    here: {}  {}",
        copy.located.workspace_root.display(),
        describe(copy.status.as_ref())
    );
}

fn describe(status: Option<&Status>) -> String {
    let Some(status) = status else {
        return "not synced yet".to_owned();
    };
    if let Some(error) = &status.error {
        return format!("sync failing: {error}");
    }
    match status.last_success {
        Some(t) => format!("synced {}s ago", daemon::now().saturating_sub(t)),
        None => "not synced yet".to_owned(),
    }
}

/// The current repository's replication state, in detail.
fn print_details(located: &Located, hive: &HiveConfig) -> anyhow::Result<()> {
    println!();
    println!("This repository:");
    println!("  Hive:      {} ({})", hive.display_name(), hive.hive);
    println!("  Hub:       {}", hive.hub);
    println!("  Machine:   {}", hive.node);
    let mut node = located.open()?;
    for (machine, workspace, commit) in node.machine_workspaces()? {
        let short = &commit.hex()[..12];
        println!("             {workspace}@{machine} is at {short}");
    }
    if let Some(status) = Status::load(&located.repo_path) {
        println!("  Last sync: {}", describe(Some(&status)));
        if let (Some(seq), Some(head)) = (status.known_seq, &status.known_head) {
            println!("  Hub head:  #{seq} {}", &head[..12.min(head.len())]);
        }
    }
    Ok(())
}

fn op_id(start: &Path, id: &str) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    let mut node = located.open()?;
    let prefix =
        jj_lib::object_id::HexPrefix::try_from_hex(id).context("not a hex operation id")?;
    let local = pollster::block_on(
        node.loader()
            .op_store()
            .resolve_operation_id_prefix(&prefix),
    )?;
    if let jj_lib::object_id::PrefixResolution::SingleMatch(local) = local {
        let canonical = node.canonicalize(&local)?;
        println!("local {} = hive {}", local.hex(), canonical.hex());
        return Ok(());
    }
    if let Some(canonical) = node.canonical_store().resolve_prefix(id)? {
        match node.local_of(&canonical) {
            Some(local) => println!("hive {} = local {}", canonical.hex(), local.hex()),
            None => println!(
                "hive {} is not realized on this machine yet",
                canonical.hex()
            ),
        }
        return Ok(());
    }
    anyhow::bail!("no operation {id} here or in the hive")
}
