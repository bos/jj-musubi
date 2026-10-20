//! `musubi`: replicate jj repositories between machines.

mod config;
mod daemon;
mod repo;
mod settings;
mod watch;

use std::path::Path;
use std::path::PathBuf;
use std::process::Command as Process;
use std::sync::Arc;

use anyhow::Context as _;
use clap::Parser;
use clap::Subcommand;
use jj_lib::object_id::ObjectId as _;
use musubi_hub::store::Backend;
use musubi_sync::hub::HubAdapter;
use musubi_sync::service::HubService;
use musubi_transport::NatsTransport;
use musubi_transport::Transport;
use uuid::Uuid;

use crate::config::DaemonConfig;
use crate::config::HiveConfig;
use crate::repo::Located;

#[derive(Parser)]
#[command(version, about = "Replicate jj repositories between machines")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Run a hub, which stores a hive and orders its updates. Creates the hive, with a new
    /// id, the first time it runs on a directory.
    Hub {
        /// Directory holding the hub's store; created if missing.
        #[arg(long)]
        dir: PathBuf,
        /// NATS server to serve on.
        #[arg(long)]
        nats: String,
        /// The hive's id, when creating it; a new one is generated otherwise.
        #[arg(long)]
        hive: Option<Uuid>,
        /// The backend of the hive's repositories (only needed when creating the store).
        #[arg(long, default_value = "git")]
        backend: String,
    },
    /// Make the repository in the current directory part of an existing hive.
    Join {
        hive: Uuid,
        #[arg(long)]
        nats: String,
        /// This machine's name in the hive, shown in labels such as `default@laptop`.
        /// Defaults to jj's `operation.hostname`.
        #[arg(long)]
        machine: Option<String>,
        /// Replicate the whole operation history, not just the current state.
        #[arg(long)]
        full_history: bool,
    },
    /// Create a new colocated repository from a hive.
    Clone {
        hive: Uuid,
        destination: PathBuf,
        #[arg(long)]
        nats: String,
        /// This machine's name in the hive. Defaults to jj's `operation.hostname`.
        #[arg(long)]
        machine: Option<String>,
    },
    /// Serve every configured repository until interrupted.
    Daemon,
    /// Sync the repository in the current directory once, then exit.
    Sync,
    /// Show the replication state of the repository in the current directory.
    Status,
    /// Translate an operation id between this machine's id and the hive's.
    OpId { id: String },
}

fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info")),
        )
        .with_writer(std::io::stderr)
        .init();
    let cwd = std::env::current_dir()?;
    match Cli::parse().command {
        Command::Hub {
            dir,
            nats,
            hive,
            backend,
        } => hub(&dir, &nats, hive, &backend),
        Command::Join {
            hive,
            nats,
            machine,
            full_history,
        } => join(&cwd, hive, &nats, machine.as_deref(), full_history),
        Command::Clone {
            hive,
            destination,
            nats,
            machine,
        } => clone(&destination, hive, &nats, machine.as_deref()),
        Command::Daemon => daemon::run(),
        Command::Sync => sync_once(&cwd),
        Command::Status => status(&cwd),
        Command::OpId { id } => op_id(&cwd, &id),
    }
}

fn subjects(hive: Uuid) -> (String, String) {
    let config = HiveConfig {
        hive,
        nats_url: String::new(),
        subject_prefix: "musubi".into(),
        node: String::new(),
    };
    (config.rpc_subject(), config.head_subject())
}

fn hub(dir: &Path, nats: &str, hive: Option<Uuid>, backend: &str) -> anyhow::Result<()> {
    let hive_file = dir.join("hive");
    let adapter = if dir.exists() {
        let stored: Uuid = std::fs::read_to_string(&hive_file)?.trim().parse()?;
        anyhow::ensure!(
            hive.is_none_or(|hive| hive == stored),
            "{} holds hive {stored}, not {}",
            dir.display(),
            hive.unwrap_or(stored)
        );
        HubAdapter::open(dir)?
    } else {
        let backend = match backend {
            "git" => Backend::Git,
            "simple" => Backend::Simple,
            other => anyhow::bail!("unknown backend {other:?}; use git or simple"),
        };
        let adapter = HubAdapter::init(dir, backend)?;
        std::fs::write(&hive_file, hive.unwrap_or_else(Uuid::new_v4).to_string())?;
        adapter
    };
    let hive: Uuid = std::fs::read_to_string(&hive_file)?.trim().parse()?;
    println!("{hive}");
    let (rpc, head) = subjects(hive);
    let service = HubService::new(adapter, dir, rpc, head)?;
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    runtime.block_on(async {
        let transport: Arc<dyn Transport> = Arc::new(NatsTransport::connect(nats).await?);
        tracing::info!("serving hive {hive} from {}", dir.display());
        service.run(transport).await
    })
}

/// Makes the repository at `start` a node of `hive`: checks its workspace name, records the
/// join (unless replicating full history), saves the hive config, registers it with the
/// daemon, and syncs once.
fn join(
    start: &Path,
    hive: Uuid,
    nats: &str,
    machine: Option<&str>,
    full_history: bool,
) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    anyhow::ensure!(
        HiveConfig::load(&located.repo_path)?.is_none(),
        "this repository is already part of a hive"
    );
    if let Some(name) = machine {
        let path = located.repo_path.join("musubi/machine");
        anyhow::ensure!(!path.exists(), "this repository already has a machine name");
        musubi_jj::workspaces::Machine::load_or_create(&path, name)?;
    }
    let mut node = located.open()?;
    let machine = node.machine().name().to_owned();
    if !full_history {
        node.create_join_operation(&format!("musubi: {machine} joins the hive"))?;
    }
    let config = HiveConfig {
        hive,
        nats_url: nats.to_owned(),
        subject_prefix: "musubi".into(),
        node: machine,
    };
    config.save(&located.repo_path)?;
    DaemonConfig::add_repo(&located.workspace_root)?;
    println!("Joined hive {hive}. Syncing...");
    sync_once(start)?;
    println!("Done. `musubi daemon` keeps it in sync from now on.");
    Ok(())
}

fn clone(destination: &Path, hive: Uuid, nats: &str, machine: Option<&str>) -> anyhow::Result<()> {
    let parent = destination
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let dest = destination.to_str().context("destination is not UTF-8")?;
    let status = Process::new("jj")
        .args(["git", "init", "--colocate", dest])
        .current_dir(parent)
        .status()?;
    anyhow::ensure!(status.success(), "`jj git init --colocate {dest}` failed");
    join(destination, hive, nats, machine, false)
}

fn sync_once(start: &Path) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    runtime.block_on(async {
        let transport: Arc<dyn Transport> = Arc::new(NatsTransport::connect(&hive.nats_url).await?);
        let blobs = located.repo_path.join("musubi/blobs");
        let remote = musubi_sync::remote::RemoteHub::new(
            transport,
            hive.rpc_subject(),
            &blobs,
            std::time::Duration::from_secs(60),
        )?;
        let mut driver = musubi_sync::driver::NodeDriver::new(located.open()?, remote)?;
        driver.sync().await?;
        Ok(())
    })
}

fn status(start: &Path) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    let Some(hive) = HiveConfig::load(&located.repo_path)? else {
        println!("Not part of a hive.");
        return Ok(());
    };
    println!("Hive:      {}", hive.hive);
    println!("Hub:       {}", hive.nats_url);
    println!("Machine:   {}", hive.node);
    let mut node = located.open()?;
    for (machine, workspace, commit) in node.machine_workspaces()? {
        let short = &commit.hex()[..12];
        println!("           {workspace}@{machine} is at {short}");
    }
    match daemon::Status::load(&located.repo_path) {
        None => println!("Never synced by the daemon."),
        Some(status) => {
            let ago = |t: Option<u64>| {
                t.map_or("never".to_owned(), |t| {
                    let now = std::time::SystemTime::now()
                        .duration_since(std::time::SystemTime::UNIX_EPOCH)
                        .map_or(0, |d| d.as_secs());
                    format!("{}s ago", now.saturating_sub(t))
                })
            };
            println!("Last sync: {}", ago(status.last_success));
            if let (Some(seq), Some(head)) = (status.known_seq, status.known_head) {
                println!("Hub head:  #{seq} {}", &head[..12.min(head.len())]);
            }
            if let Some(error) = status.error {
                println!("Error:     {error}");
            }
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
