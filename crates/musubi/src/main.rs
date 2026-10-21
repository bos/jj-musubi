//! `musubi`: replicate jj repositories between machines.

mod config;
mod control;
mod daemon;
mod hub;
mod repo;
mod settings;
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
use musubi_hub::hub_dir::JoinRequest;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use crate::config::HiveConfig;
use crate::config::UserConfig;
use crate::control::Socket;
use crate::daemon::Status;
use crate::repo::Located;

#[derive(Parser)]
#[command(version, about = "Replicate jj repositories between machines")]
struct Cli {
    /// The daemon's control socket, in place of the usual one.
    #[arg(long, global = true, env = "MUSUBI_SOCKET", hide_env = true)]
    socket: Option<String>,
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Run a hub, which stores hives and orders their updates. Serves every hive in its
    /// directory, and starts a NATS server for them unless given one.
    #[command(args_conflicts_with_subcommands = true)]
    Hub {
        #[command(subcommand)]
        action: Option<HubAction>,
        /// The hub's directory [default: ./musubi-hub, or the current directory if it is a
        /// hub's].
        #[arg(short, long)]
        dir: Option<PathBuf>,
        /// A NATS server to serve on, in place of starting one.
        #[arg(long)]
        nats: Option<String>,
        /// The host name other machines reach this one by, for the join command it
        /// prints [default: this machine's host name].
        #[arg(long)]
        advertise: Option<String>,
        /// Have the NATS server it starts require a token, which the URLs it prints then
        /// carry. Once chosen, the hub keeps it (in hub.toml).
        #[arg(long, conflicts_with = "nats")]
        token: bool,
    },
    /// Make the repository in the current directory part of a hive: the one on the hub it
    /// shares history and a remote with, or a new one.
    Join {
        /// Join this hive (a name, a prefix of one, or an id).
        #[arg(long, conflicts_with = "new")]
        hive: Option<String>,
        /// Start a new hive with this name, even if one matches.
        #[arg(long, value_name = "NAME")]
        new: Option<String>,
        /// This machine's name in the hive, which other machines show its workspaces under,
        /// as in `laptop/default`. Defaults to jj's `operation.hostname`.
        #[arg(long)]
        machine: Option<String>,
        /// Replicate the whole operation history, not just the current state.
        #[arg(long)]
        full_history: bool,
        /// The hub's NATS URL, as `musubi hub` prints it [default: the one first joined].
        #[arg(long)]
        nats: Option<String>,
    },
    /// Create a new colocated repository from a hive.
    Clone {
        /// The hive: a name, a prefix of one, or an id.
        hive: String,
        destination: PathBuf,
        /// The hub's NATS URL [default: the one first joined].
        #[arg(long)]
        nats: Option<String>,
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
        nats: Option<String>,
    },
    /// Rename a hive.
    Rename {
        hive: String,
        new_name: String,
        #[arg(long)]
        nats: Option<String>,
    },
}

#[derive(Subcommand)]
enum DaemonAction {
    /// Stop the running daemon.
    Stop,
    /// Stop the running daemon, if any, and start a new one in the background.
    Restart,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    // The hub and the daemon log what they do; other commands say it themselves.
    let serving = matches!(
        cli.command,
        Some(Command::Hub { action: None, .. } | Command::Daemon { action: None })
    );
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| {
                tracing_subscriber::EnvFilter::new(if serving { "info" } else { "warn" })
            }),
        )
        .with_writer(std::io::stderr)
        .init();
    let cwd = std::env::current_dir()?;
    let socket = || Socket::locate(cli.socket.as_deref());
    match cli.command.unwrap_or(Command::List) {
        Command::Hub {
            action: None,
            dir,
            nats,
            advertise,
            token,
        } => hub::serve(hub::ServeArgs {
            dir,
            nats,
            advertise,
            token,
        }),
        Command::Hub {
            action: Some(HubAction::Rm { hive, nats }),
            ..
        } => block_on(async {
            let nats = UserConfig::nats(nats.as_deref())?;
            let reply = hub::ask(&nats, HubWideRequest::Remove { name: hive }).await?;
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
                    nats,
                }),
            ..
        } => block_on(async {
            let nats = UserConfig::nats(nats.as_deref())?;
            let request = HubWideRequest::Rename {
                name: hive.clone(),
                to: new_name,
            };
            if let HubWideReply::Hive(info) = hub::ask(&nats, request).await? {
                println!("Renamed hive {hive} to {}", info.name);
            }
            Ok(())
        }),
        Command::Join {
            hive,
            new,
            machine,
            full_history,
            nats,
        } => {
            let choice = match (hive, new) {
                (Some(hive), _) => Choice::Hive(hive),
                (None, Some(name)) => Choice::New(name),
                (None, None) => Choice::Match,
            };
            join(
                &cwd,
                choice,
                nats.as_deref(),
                machine.as_deref(),
                full_history,
                &socket()?,
            )
        }
        Command::Clone {
            hive,
            destination,
            nats,
            machine,
        } => clone(
            &destination,
            &hive,
            nats.as_deref(),
            machine.as_deref(),
            &socket()?,
        ),
        Command::List => list(&cwd, socket()),
        Command::Leave => leave(&cwd, &socket()?),
        Command::Daemon { action: None } => daemon::run(&socket()?),
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

/// Which hive `musubi join` joins.
enum Choice {
    /// Whichever matches, or a new one.
    Match,
    Hive(String),
    New(String),
}

/// Makes the repository at `start` part of a hive: the hub decides which (see
/// `musubi_hub::matching`); then this records the membership and has the daemon serve it.
fn join(
    start: &Path,
    choice: Choice,
    nats: Option<&str>,
    machine: Option<&str>,
    full_history: bool,
    socket: &Socket,
) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    if let Some(hive) = HiveConfig::load(&located.repo_path)? {
        anyhow::bail!(
            "this repository is already part of hive {}; `musubi leave` first to join another",
            hive.display_name()
        );
    }
    let nats = UserConfig::nats(nats)?;
    set_machine_name(&located, machine)?;
    let node = located.open()?;
    let summary = node.join_summary()?;
    let (hive, new) = match choice {
        Choice::Match => (None, None),
        Choice::Hive(hive) => (Some(hive), None),
        Choice::New(name) => (None, Some(name)),
    };
    let request = JoinRequest {
        hive,
        new,
        backend: summary.backend.to_owned(),
        remotes: summary
            .remotes
            .into_iter()
            .filter_map(|(name, remote)| Some((name, remote.url?)))
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
    let joined = match block_on(hub::ask(&nats, HubWideRequest::Join(request)))? {
        HubWideReply::Joined(joined) => joined,
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    };
    become_node(&located, &joined.hive, &nats, full_history)?;
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

fn set_machine_name(located: &Located, machine: Option<&str>) -> anyhow::Result<()> {
    if let Some(name) = machine {
        let path = located.repo_path.join("musubi/machine");
        let machine = musubi_jj::workspaces::Machine::load_or_create(&path, name)?;
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
    nats: &str,
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
        nats_url: nats.to_owned(),
        subject_prefix: config::default_subject_prefix(),
        node: machine,
    };
    config.save(&located.repo_path)?;
    UserConfig::add_repo(&located.workspace_root)?;
    UserConfig::update(|config| {
        config.nats.get_or_insert_with(|| nats.to_owned());
    })?;
    Ok(())
}

/// Has the daemon, started if need be, serve the repository, and reports its first sync.
/// Without a daemon, syncs once.
fn start_serving(located: &Located, socket: &Socket) -> anyhow::Result<()> {
    let workspace = located.workspace_root.clone();
    // The client lives on the runtime that made it, so one runtime does it all.
    let synced = block_on(async {
        let client = match daemon::ensure(socket).await {
            Ok(client) => client,
            Err(err) => return Ok(Err(err)),
        };
        println!("Syncing...");
        let synced = client
            .add(control::context(Duration::from_secs(3600)), workspace)
            .await
            .context("asking the daemon to serve this repository")?;
        Ok(Ok(synced))
    })?;
    match synced {
        Err(err) => {
            eprintln!("Could not start the daemon ({err:#}); syncing once instead.");
            sync_directly(located)?;
            println!("Synced. Run `musubi daemon` to keep it in sync.");
            Ok(())
        }
        Ok(Ok(synced)) => {
            println!(
                "Synced with the hub (hive at #{}). The daemon keeps it in sync from now on.",
                synced.seq
            );
            Ok(())
        }
        Ok(Err(message)) => anyhow::bail!(
            "the first sync failed: {message}\nThe daemon keeps trying; `musubi list` shows how \
             it goes."
        ),
    }
}

fn clone(
    destination: &Path,
    hive: &str,
    nats: Option<&str>,
    machine: Option<&str>,
    socket: &Socket,
) -> anyhow::Result<()> {
    let nats = UserConfig::nats(nats)?;
    let reply = block_on(hub::ask(
        &nats,
        HubWideRequest::Resolve {
            name: hive.to_owned(),
        },
    ))?;
    let HubWideReply::Hive(info) = reply else {
        anyhow::bail!("unexpected reply from the hub: {reply:?}");
    };
    let dest = destination.to_str().context("destination is not UTF-8")?;
    let init: &[&str] = match info.backend.as_str() {
        "git" => &["git", "init", "--colocate"],
        _ => &["debug", "init-simple"],
    };
    let status = Process::new("jj").args(init).arg(dest).status()?;
    anyhow::ensure!(status.success(), "`jj {} {dest}` failed", init.join(" "));
    let located = Located::find(destination)?;
    set_machine_name(&located, machine)?;
    become_node(&located, &info, &nats, false)?;
    println!("Cloning hive {} into {}", info.name, destination.display());
    start_serving(&located, socket)
}

/// Syncs once, in this process.
fn sync_directly(located: &Located) -> anyhow::Result<()> {
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    block_on(async {
        let transport = hub::connect(&hive.nats_url, Duration::from_secs(30)).await?;
        let blobs = located.repo_path.join("musubi/blobs");
        let remote = musubi_sync::remote::RemoteHub::new(
            transport,
            hive.rpc_subject(),
            &blobs,
            Duration::from_secs(60),
        )?;
        let mut driver = musubi_sync::driver::NodeDriver::new(located.open()?, remote)?;
        driver.sync().await?;
        Ok(())
    })
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
    match through_daemon {
        Some(Ok(synced)) => println!("Synced (hive at #{}).", synced.seq),
        Some(Err(message)) => anyhow::bail!("{message}"),
        None => sync_directly(&located)?,
    }
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
    let mut hubs: Vec<String> = config.nats.iter().cloned().collect();
    for copy in &copies {
        if !hubs.contains(&copy.hive.nats_url) {
            hubs.push(copy.hive.nats_url.clone());
        }
    }
    if hubs.is_empty() {
        println!("No hubs yet: run `musubi hub` on one machine, then the join command it prints.");
    }
    for nats in &hubs {
        let here: Vec<&Copy> = copies
            .iter()
            .filter(|copy| &copy.hive.nats_url == nats)
            .collect();
        let shown = hub::without_credentials(nats);
        match block_on(list_hub(nats)) {
            Ok(hives) => {
                println!("Hub {shown}:");
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
                println!("Hub {shown}: {err:#}. This machine's copies:");
                for copy in &here {
                    println!("  {}", copy.hive.display_name());
                    print_copy(copy);
                }
            }
        }
    }
    match daemon {
        Ok(true) => println!("Daemon: running, serving {} repositories", statuses.len()),
        Ok(false) if copies.is_empty() => {}
        Ok(false) => println!("Daemon: not running; `musubi daemon restart` starts it"),
        Err(err) => println!("Daemon: {err:#}"),
    }
    if let Ok(located) = Located::find(start)
        && let Some(hive) = HiveConfig::load(&located.repo_path)?
    {
        print_details(&located, &hive)?;
    }
    Ok(())
}

async fn list_hub(nats: &str) -> anyhow::Result<Vec<HiveInfo>> {
    let transport = hub::connect(nats, Duration::from_secs(3)).await?;
    match hub::ask_over(&*transport, nats, HubWideRequest::List).await? {
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
    println!("  Hub:       {}", hub::without_credentials(&hive.nats_url));
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
