//! `musubi`: replicate jj repositories between machines.

mod agent;
mod completion;
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
mod top;
mod watch;

use std::collections::BTreeMap;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command as Process;
use std::time::Duration;

use anyhow::Context as _;
use clap::Parser;
use clap::Subcommand;
use clap::ValueHint;
use clap_complete::ArgValueCandidates;
use jj_lib::object_id::ObjectId as _;
use musubi_hub::hub_dir::HiveInfo;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::JoinRequest;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::remote::HiveGone;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use crate::config::HiveConfig;
use crate::config::Settings;
use crate::config::UserState;
use crate::control::Synced;
use crate::daemon::Status;
use crate::repo::Located;
use crate::socket::Socket;

#[derive(Parser)]
#[command(
    name = "musubi",
    version,
    about = "Replicate jj repositories between machines",
    after_help = "Run `musubi <command> --help` for more on a command. The user guide is at \
                  https://github.com/bos/jj-musubi/blob/main/docs/README.md"
)]
struct Cli {
    /// The daemon's control socket, in place of the usual one.
    #[arg(
        long,
        global = true,
        env = "MUSUBI_SOCKET",
        hide_env = true,
        help_heading = "Global options"
    )]
    socket: Option<String>,
    /// What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`.
    /// It applies to this command, not to a daemon it starts, which uses `musubi.daemon.log`
    /// in jj's config.
    #[arg(
        long,
        global = true,
        value_name = "FILTER",
        help_heading = "Global options"
    )]
    log: Option<String>,
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Run a hub, which stores hives and orders their updates. Serves every hive in its
    /// directory, to other machines over ssh.
    ///
    /// Runs until stopped, logging what it does. The first time, it creates the directory.
    /// If this machine has no default hub yet, it becomes it. It prints the commands other
    /// machines run to share a repository through it.
    #[command(args_conflicts_with_subcommands = true)]
    Hub {
        #[command(subcommand)]
        action: Option<HubAction>,
        /// The hub's directory [default: ./musubi-hub, or the current directory if it is a
        /// hub's].
        #[arg(short, long, value_hint = ValueHint::DirPath)]
        dir: Option<PathBuf>,
        /// The host name other machines ssh to this one by, for the commands it prints
        /// [default: this machine's host name]. Once given, the hub keeps it (in hub.toml).
        #[arg(long)]
        advertise: Option<String>,
    },
    /// Start a hive on the hub from the repository in the current directory, for other
    /// copies of it to join.
    ///
    /// Without a name, it is refused if the repository belongs in a hive the hub already
    /// has: `musubi join` joins that one. It starts the daemon if it isn't running, and
    /// returns once the repository has synced.
    Create {
        /// The hive's name [default: the repository's name on its forge, from its `origin`
        /// remote, else its first remote, else the directory's name].
        name: Option<String>,
        #[command(flatten)]
        member: Member,
    },
    /// Make the repository in the current directory part of the hive on the hub it shares
    /// history and a remote with.
    ///
    /// The hub chooses the hive that has some of the repository's history and one of its
    /// remotes' URLs. It refuses a repository that matches no hive or several, and a fork,
    /// which shares history but not a remote: choose a hive yourself with `--hive`, or start
    /// a new one with `musubi create`. It starts the daemon if it isn't running, and returns
    /// once the repository has synced.
    ///
    /// Unless jj's config sets it already, it sets `musubi.forget-after` in the repository's
    /// config: how long the copy may go unused before the hive forgets it, `6h` when an agent
    /// runs it, `never` otherwise. `musubi create` and `musubi clone` do too.
    Join {
        /// Join this hive (a name, a prefix of one, or an id), whatever its remotes.
        #[arg(long, add = ArgValueCandidates::new(completion::hives))]
        hive: Option<String>,
        #[command(flatten)]
        member: Member,
    },
    /// Create a new colocated repository from a hive.
    ///
    /// It makes the repository, joins it to the hive, and returns once it has synced, with
    /// the daemon keeping it in sync from then on.
    Clone {
        /// The hive: a name, a prefix of one, or an id.
        #[arg(add = ArgValueCandidates::new(completion::hives))]
        hive: String,
        /// The new repository's directory.
        #[arg(value_hint = ValueHint::DirPath)]
        destination: PathBuf,
        /// The hub, as `musubi hub` prints it [default: this machine's default hub].
        #[arg(long, add = ArgValueCandidates::new(completion::hubs))]
        hub: Option<String>,
        /// This machine's name in the hive. Defaults to jj's `operation.hostname`.
        #[arg(long)]
        machine: Option<String>,
    },
    /// List the hub's hives, this machine's copies of them, and how their syncing goes
    /// (the default command).
    ///
    /// In a hive's repository, it also shows the repository's hive, hub and machine name,
    /// where every machine's working copy is, each copy in the hive, when it was last used,
    /// and when it will be forgotten (`musubi.forget-after`), and its last sync.
    #[command(alias = "status")]
    List,
    /// Watch what flows through the hubs, and what is wrong, as it happens.
    ///
    /// For each hive, it shows the bytes a second coming into its hub and going out, the
    /// operations and commits machines have sent since the hub started, and what came in
    /// lately. For each machine, it shows when the hub last heard from its daemon, how far
    /// behind it is, and how its syncing goes. Above them it lists the issues: hubs out of
    /// reach, requests the hub failed, and machines that are offline, behind, or failing
    /// to sync, and whether this machine's daemon is running.
    ///
    /// It asks this machine's default hub and the hubs of its copies, or the hub `--hub`
    /// names. Without a terminal, or with `--once`, it prints what it sees once, without
    /// rates.
    Top {
        /// The hub to watch, as `musubi hub` prints it [default: every hub this machine
        /// uses].
        #[arg(long, add = ArgValueCandidates::new(completion::hubs))]
        hub: Option<String>,
        /// How often to refresh, in seconds. `+` and `-` change it as it runs.
        #[arg(short, long, value_name = "SECONDS", default_value_t = 5,
              value_parser = clap::value_parser!(u64).range(1..=3600))]
        interval: u64,
        /// Print what it sees once, and stop.
        #[arg(long)]
        once: bool,
    },
    /// Take the repository in the current directory out of its hive, and stop syncing it.
    ///
    /// It records what changed in the working copy, then tells the hive, with this copy's
    /// last work, so that the other machines stop showing its working copies. The repository
    /// keeps everything it has, its working copy included, and the hive keeps everything it
    /// sent. If the hive can't be told, it fails, and the repository stays part of the hive.
    Leave {
        /// Leave even if the hive can't be told. The other machines go on showing this copy
        /// until one of them forgets it.
        #[arg(long)]
        force: bool,
    },
    /// Forget another machine's copy of this repository: the other machines stop showing its
    /// working copies, and the hub stops counting it.
    ///
    /// For a machine that went away without `musubi leave`, as a short-lived machine can.
    /// Its working-copy commit is abandoned if it's empty, and otherwise stays as an ordinary
    /// commit. If the copy is still there, the hive shows it again as soon as it's used.
    Forget {
        /// The machine, as its working copies are named here: `laptop` for `laptop/default@`,
        /// or `laptop-1a2b` for `laptop-1a2b/default@`. The name `musubi list` gives it will
        /// do too, if no other machine has that name.
        machine: String,
    },
    /// Sync the repository in the current directory now.
    ///
    /// The daemon syncs by itself whenever the repository or its hive changes, so this is
    /// rarely needed, except to see at once how a sync goes. It asks the daemon to sync, if
    /// the daemon serves the repository, and otherwise syncs in this process.
    Sync,
    /// Run the daemon that keeps this machine's repositories in sync, or control it.
    ///
    /// Without a subcommand, it runs the daemon in the foreground, logging to standard
    /// error. Other commands start it in the background when they need it, logging to
    /// `daemon.log` in musubi's state directory, or under systemd, to the journal.
    Daemon {
        #[command(subcommand)]
        action: Option<DaemonAction>,
    },
    /// Print a script that completes musubi's commands, flags, and paths in a shell.
    ///
    /// Run it in your shell's startup file, as `source <(musubi completion zsh)`, or save it
    /// where your shell looks for completions.
    #[command(after_long_help = completion::AS_YOU_TYPE)]
    Completion {
        /// The shell.
        shell: completion::Shell,
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
    /// by, or on that machine, the hub's directory [default: this machine's default hub].
    #[arg(long, add = ArgValueCandidates::new(completion::hubs))]
    hub: Option<String>,
}

#[derive(Subcommand)]
enum Debug {
    /// Translate an operation id between this machine's id and the hive's.
    OpId {
        /// An operation id, or a prefix of one: this machine's, or the hive's.
        id: String,
    },
}

#[derive(Subcommand)]
enum HubAction {
    /// Remove a hive from the hub. Each machine's copy stops syncing with it as it hears,
    /// keeping everything it has.
    ///
    /// The hive's store moves to the hub's `removed/` directory, and is emptied a day or so
    /// later. Its machines leave it as `musubi leave` would; `musubi create` and `musubi
    /// join` make a new hive of the repository if it's wanted again.
    #[command(alias = "rm")]
    Remove {
        /// The hive: its whole name, or its id.
        #[arg(add = ArgValueCandidates::new(completion::hives))]
        hive: String,
        /// The hub, as `musubi hub` prints it [default: this machine's default hub].
        #[arg(long, add = ArgValueCandidates::new(completion::hubs))]
        hub: Option<String>,
    },
    /// Rename a hive.
    Rename {
        /// The hive: a name, a prefix of one, or an id.
        #[arg(add = ArgValueCandidates::new(completion::hives))]
        hive: String,
        /// The hive's new name.
        new_name: String,
        /// The hub, as `musubi hub` prints it [default: this machine's default hub].
        #[arg(long, add = ArgValueCandidates::new(completion::hubs))]
        hub: Option<String>,
    },
    /// Relay stdin and stdout to this machine's hub: what other machines run over ssh to
    /// reach it.
    Connect {
        /// The hub's directory [default: the one `musubi hub` last served without --dir].
        #[arg(short, long, value_hint = ValueHint::DirPath)]
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

/// What to log: `--log`, else `RUST_LOG`, else for the daemon `musubi.daemon.log` in jj's
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
    if daemon && let Some(filter) = Settings::load()?.daemon_log {
        return parse_filter(&filter)
            .with_context(|| format!("bad log filter {filter:?} in musubi.daemon.log"));
    }
    if daemon || hub {
        return parse_filter("info");
    }
    // Anything logged would land in the middle of the screen; top shows what goes wrong.
    if matches!(cli.command, Some(Command::Top { once: false, .. }))
        && std::io::IsTerminal::is_terminal(&std::io::stdout())
    {
        return parse_filter("off");
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
    completion::complete_if_asked();
    let cli = Cli::parse();
    tracing_subscriber::fmt()
        .with_env_filter(log_filter(&cli)?)
        .with_writer(std::io::stderr)
        .init();
    // Serving a hub, and `hub connect`, are for other machines, whose agents aren't this
    // machine's; the daemon itself has the link, or the service manager's agent. Every shell
    // may print its completion script as it starts, which says nothing of whose agent to use.
    if !matches!(
        cli.command,
        Some(
            Command::Hub {
                action: None | Some(HubAction::Connect { .. }),
                ..
            } | Command::Daemon { action: None }
                | Command::Completion { .. }
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
            action: Some(HubAction::Remove { hive, hub }),
            ..
        } => block_on(async {
            let hub = UserState::hub(hub.as_deref())?;
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
            let hub = UserState::hub(hub.as_deref())?;
            let request = HubWideRequest::Rename {
                name: hive.clone(),
                to: new_name,
            };
            if let HubWideReply::Hive(info) = hub::ask(&hub, request).await? {
                if hive == info.name {
                    println!("Hive {hive} already has that name");
                } else {
                    println!("Renamed hive {hive} to {}", info.name);
                }
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
        Command::Top {
            hub,
            interval,
            once,
        } => top::run(
            top::Args {
                hub,
                interval: Duration::from_secs(interval),
                once,
            },
            socket(),
        ),
        Command::Leave { force } => leave(&cwd, &socket()?, force),
        Command::Forget { machine } => forget(&cwd, &machine, &socket()?),
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
        Command::Completion { shell } => completion::print_script(shell),
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
    // `musubi join` in a repository that is part of a hive joins that hive again, made again
    // if its hub has lost it.
    let (choice, hub) = match (HiveConfig::load(&located.repo_path)?, choice) {
        (None, choice) => (choice, UserState::hub(hub)?),
        (Some(hive), JoinChoice::Match) => {
            let remake = JoinChoice::Remake {
                id: hive.hive.to_string(),
                name: hive.name.clone(),
            };
            (
                remake,
                hub.map_or_else(|| Ok(hive.hub.clone()), |hub| UserState::hub(Some(hub)))?,
            )
        }
        (Some(hive), _) => anyhow::bail!(
            "this repository is already part of hive {}; `musubi leave` first to join another",
            hive.display_name()
        ),
    };
    let remaking = matches!(choice, JoinChoice::Remake { .. });
    configured_forget_after(settings::load(&located.workspace_root, &located.repo_path)?.config())?;
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
    if remaking {
        // The daemon serves the repository with the hub it knew: start it over, as for a
        // repository newly joined.
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
            Ok::<_, anyhow::Error>(())
        })?;
    }
    if remaking && joined.created {
        println!(
            "Made hive {} again from this repository; its other machines fill it as they sync",
            joined.hive.name
        );
    } else if remaking {
        println!(
            "Hive {} is on the hub, and this repository is part of it",
            joined.hive.name
        );
    } else if joined.created {
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
/// full history), its hive config, and that the daemon serves it. The first hub joined
/// becomes the user's default.
fn become_node(
    located: &Located,
    hive: &HiveInfo,
    hub: &str,
    full_history: bool,
) -> anyhow::Result<()> {
    let mut node = located.open()?;
    let machine = node.machine().name().to_owned();
    let description = format!("musubi: {machine} joins the hive");
    if full_history {
        node.mark_joined(&description)?;
    } else {
        node.create_join_operation(&description)?;
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
    drop(node);
    set_forget_after(located)?;
    UserState::add_repo(&located.workspace_root)?;
    if UserState::save_default_hub(hub)? {
        println!(
            "Saved {hub} as this machine's default hub. To choose another: jj config set \
             --user musubi.hub <hub>"
        );
    }
    Ok(())
}

/// The environment variables that say an agent is running musubi, as the devbox tool
/// detects agents.
const AGENT_VARIABLES: [&str; 3] = [
    "CODEX_THREAD_ID",
    "CODEX_SESSION_ID",
    "CLAUDE_CODE_SESSION_ID",
];

/// How long an agent's copy may go unused before the hive forgets it, by default.
const AGENT_FORGET_AFTER: &str = "6h";

/// Sets `musubi.forget-after` in the repository's config, unless jj's config sets it
/// already: `6h` if an agent is joining, as on a short-lived machine, `never` otherwise. A
/// value in the user's config, as an agent's image might set, wins, and so does the one
/// set when the repository last joined. Says which.
fn set_forget_after(located: &Located) -> anyhow::Result<()> {
    let key = musubi_jj::node::FORGET_AFTER_KEY;
    let settings = settings::load(&located.workspace_root, &located.repo_path)?;
    let name: jj_lib::config::ConfigNamePathBuf = key.parse()?;
    let (value, how) = match configured_forget_after(settings.config())? {
        Some((source, after)) => (
            musubi_jj::presence::format_forget_after(after),
            format!("as your {source} config says"),
        ),
        None => {
            let agent = AGENT_VARIABLES
                .iter()
                .any(|var| std::env::var_os(var).is_some());
            let value = if agent { AGENT_FORGET_AFTER } else { "never" };
            let path = settings::repo_config_path(&located.repo_path)?
                .context("this repository has no config of its own")?;
            let mut file = jj_lib::config::ConfigFile::load_or_empty(
                jj_lib::config::ConfigSource::Repo,
                &path,
            )?;
            file.set_value(&name, value)?;
            file.save()?;
            let why = if agent {
                "since an agent is joining it"
            } else {
                "since a person, not an agent, is joining it"
            };
            (value.to_owned(), why.to_owned())
        }
    };
    match value.as_str() {
        "never" => println!(
            "The hive keeps this copy however long it goes unused, {how}. To have it forgotten \
             once unused for 6 hours: jj config set --repo {key} 6h"
        ),
        after => println!(
            "The hive forgets this copy once it goes unused for {after}, {how}. To keep it: jj \
             config set --repo {key} never"
        ),
    }
    Ok(())
}

/// `musubi.forget-after` as `config` sets it, and where: `None` if nothing does. Fails if
/// its value is neither `never` nor a duration, before a command joining a copy writes
/// anything.
fn configured_forget_after(
    config: &jj_lib::config::StackedConfig,
) -> anyhow::Result<Option<(jj_lib::config::ConfigSource, Option<Duration>)>> {
    let key = musubi_jj::node::FORGET_AFTER_KEY;
    let name: jj_lib::config::ConfigNamePathBuf = key.parse()?;
    let Some((source, value)) = config
        .layers()
        .iter()
        .rev()
        .filter(|layer| layer.source != jj_lib::config::ConfigSource::Default)
        .find_map(|layer| {
            let item = layer.look_up_item(&name).ok()??;
            Some((layer.source, item.as_str().map(str::to_owned)))
        })
    else {
        return Ok(None);
    };
    let after = value
        .as_deref()
        .and_then(musubi_jj::presence::parse_forget_after)
        .with_context(|| {
            format!(
                "{key} in your {source} config is neither `never` nor a duration such as `6h`; \
                 fix it and run this again"
            )
        })?;
    Ok(Some((source, after)))
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
    let hub = UserState::hub(hub)?;
    configured_forget_after(&settings::user_config()?)?;
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
    let synced = sync_quietly(start, socket)?;
    println!("Synced (hive at #{}).", synced.seq);
    Ok(())
}

/// [`sync`], saying nothing.
fn sync_quietly(start: &Path, socket: &Socket) -> anyhow::Result<Synced> {
    let located = Located::find(start)?;
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    let served = UserState::load()?.repos.contains(&located.workspace_root);
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
        None => match sync_directly(&located) {
            Ok(synced) => synced,
            // As the daemon would: the hive is over.
            Err(err) if HiveGone::of(&err) == Some(HiveGone::Removed) => {
                daemon::leave_hive(&located, &hive)?;
                anyhow::bail!(
                    "{err:#}, so this repository no longer syncs with it; everything it has stays"
                );
            }
            Err(err) => return Err(err),
        },
    };
    Ok(synced)
}

fn leave(start: &Path, socket: &Socket, force: bool) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    // So that the daemon doesn't sync it meanwhile.
    let served = block_on(async {
        let Some(client) = daemon::running(socket).await? else {
            return Ok(false);
        };
        client
            .remove(
                control::context(Duration::from_secs(120)),
                located.workspace_root.clone(),
            )
            .await?
            .map_err(anyhow::Error::msg)?;
        Ok::<_, anyhow::Error>(true)
    })?;
    let name = hive.display_name();
    let told = match snapshot(&located) {
        Err(err) => Err(("record what changed in the working copy".to_owned(), err)),
        Ok(()) => tell_the_hive(&located, &hive)
            .map_err(|err| (format!("tell hive {name} that this repository leaves"), err)),
    };
    if let Err((doing, err)) = told {
        if !force {
            if served {
                // As before: the daemon serves it again.
                block_on(async {
                    if let Some(client) = daemon::running(socket).await? {
                        let context = control::context(Duration::from_secs(10));
                        client
                            .add(context, located.workspace_root.clone())
                            .await
                            .ok();
                    }
                    Ok::<_, anyhow::Error>(())
                })
                .ok();
            }
            anyhow::bail!(
                "couldn't {doing} ({err:#}), so this repository is still part of hive {name}; \
                 `musubi leave --force` leaves without telling it"
            );
        }
        eprintln!("Couldn't {doing} ({err:#}); leaving anyway.");
    }
    // No next work of a copy out of its hive shows it there again: a working copy the hive
    // abandoned gets a new commit now.
    if let Err(err) = located
        .open()
        .and_then(|mut node| Ok(node.give_back_working_copies()?))
    {
        eprintln!("Couldn't give this repository's working copies new commits ({err:#}).");
    }
    daemon::leave_hive(&located, &hive)?;
    println!(
        "This repository has left hive {name}, and no longer syncs with it. Everything it \
         has stays."
    );
    Ok(())
}

/// Records what changed in the working copy, as any `jj` command would first, so that it
/// leaves with the rest of this copy's work.
fn snapshot(located: &Located) -> anyhow::Result<()> {
    let mut jj = Process::new("jj");
    musubi_jj::git_command::without_repository_env(&mut jj);
    let output = jj
        .args(["util", "snapshot"])
        .current_dir(&located.workspace_root)
        .output()
        .context("running `jj util snapshot`")?;
    anyhow::ensure!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr).trim()
    );
    Ok(())
}

/// How many times `musubi leave` forgets this copy and syncs, while work done here meanwhile
/// goes up with the forget and keeps the copy in the hive.
const LEAVE_ATTEMPTS: usize = 3;

/// Forgets this machine's copy and syncs, so that the hive has this copy's last work and
/// knows it left, and puts this copy's working copies back here, whether or not it could.
fn tell_the_hive(located: &Located, hive: &HiveConfig) -> anyhow::Result<()> {
    let mut removed: BTreeMap<jj_lib::ref_name::WorkspaceNameBuf, jj_lib::backend::CommitId> =
        BTreeMap::new();
    let mut told = Err(anyhow::anyhow!("never tried"));
    for _ in 0..LEAVE_ATTEMPTS {
        match leave_once(located, hive, &mut removed) {
            Ok(true) => {
                told = Ok(());
                break;
            }
            // A `jj` command run here meanwhile went up too, and its work, which the forget
            // didn't see, keeps the copy in the hive: forget it again.
            Ok(false) => {
                told = Err(anyhow::anyhow!(
                    "work done in this repository while it left kept it in the hive"
                ));
            }
            Err(err) => {
                told = Err(err);
                break;
            }
        }
    }
    if !removed.is_empty() {
        let removed: Vec<_> = removed.into_iter().collect();
        if let Err(err) = located
            .open()
            .and_then(|mut node| Ok(node.restore_workspaces(&removed)?))
        {
            eprintln!(
                "Couldn't put back this repository's working copies ({err:#}). `jj op log` \
                 lists `musubi: leave`; `jj op restore` to the operation before it brings them \
                 back."
            );
        }
    }
    told
}

/// One round of [`tell_the_hive`]: forgets this copy, recording the workspaces that removes,
/// and syncs. Returns whether the hive's head, and this copy's, have it gone.
fn leave_once(
    located: &Located,
    hive: &HiveConfig,
    removed: &mut BTreeMap<jj_lib::ref_name::WorkspaceNameBuf, jj_lib::backend::CommitId>,
) -> anyhow::Result<bool> {
    let mut node = located.open()?;
    // A change to this copy's `musubi.forget-after` the daemon hasn't recorded yet goes up
    // before the forget, not after it, as the sync would otherwise record it, bringing the
    // copy back.
    node.record_forget_after()?;
    // Gone already, as after a leave that couldn't tell the hive, it syncs what it has.
    for (name, commit) in node.forget_self()?.unwrap_or_default() {
        removed.entry(name).or_insert(commit);
    }
    drop(node);
    match block_on(daemon::sync_once(located, hive)) {
        Ok(_) => {}
        // Nothing to tell a hive that is over.
        Err(err) if HiveGone::of(&err) == Some(HiveGone::Removed) => return Ok(true),
        Err(err) => return Err(err),
    }
    let mut node = located.open()?;
    Ok(!node.present_copies()?.1.is_present(node.machine().key()))
}

fn forget(start: &Path, machine: &str, socket: &Socket) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    let mut node = located.open()?;
    let this =
        |node: &NodeRepo| machine == node.machine().name() || machine == node.machine().key();
    // One this machine hasn't heard of yet may have joined since it last synced.
    let key = match node.machine_named(machine)? {
        Some(key) => key,
        None if this(&node) => anyhow::bail!(
            "{machine} is this machine; `musubi leave` takes this repository out of hive {}",
            hive.display_name()
        ),
        None => {
            drop(node);
            sync_quietly(start, socket)?;
            node = located.open()?;
            node.machine_named(machine)?.with_context(|| {
                format!(
                    "no machine {machine} shows here in hive {}; `jj workspace list` names \
                     those that do",
                    hive.display_name()
                )
            })?
        }
    };
    if node.forget_copy(&key, machine)? {
        println!("Forgot {machine}: the other machines stop showing it as they sync.");
    }
    drop(node);
    sync(start, socket)
}

/// A repository on this machine that is part of a hive.
struct Copy {
    located: Located,
    hive: HiveConfig,
    status: Option<Status>,
}

/// Lists what it can: a daemon or hub out of reach is a line of the listing.
fn list(start: &Path, socket: anyhow::Result<Socket>) -> anyhow::Result<()> {
    let state = UserState::load()?;
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
    for workspace in &state.repos {
        let Ok(located) = Located::find(workspace) else {
            println!(
                "{} is gone; remove it from {}",
                workspace.display(),
                UserState::path()?.display()
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
    let hubs = UserState::known_hubs(state.default_hub()?, copies.iter().map(|copy| &copy.hive));
    if hubs.is_empty() {
        println!("No hubs yet: run `musubi hub` on one machine, then the join command it prints.");
    }
    for hub in &hubs {
        let here: Vec<&Copy> = copies.iter().filter(|copy| &copy.hive.hub == hub).collect();
        match block_on(list_hub(hub)) {
            Ok(hives) => {
                // A copy shows its hive's name while the hub is out of reach, so keep up with
                // renames.
                for copy in &here {
                    if let Some(info) = hives.iter().find(|h| h.id == copy.hive.hive.to_string())
                        && copy.hive.name.as_deref() != Some(info.name.as_str())
                        // Unless a leave or a join has changed it since it was read.
                        && HiveConfig::load(&copy.located.repo_path).ok().flatten().as_ref()
                            == Some(&copy.hive)
                    {
                        let renamed = HiveConfig {
                            name: Some(info.name.clone()),
                            ..copy.hive.clone()
                        };
                        // Only for showing: failing to save it mustn't stop the listing.
                        renamed.save(&copy.located.repo_path).ok();
                    }
                }
                println!("Hub {hub}:");
                if hives.is_empty() {
                    println!("  no hives yet");
                }
                for info in &hives {
                    println!("  {}  {}", info.name, machines(info));
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

/// The machines in a hive, as `musubi list` shows them.
fn machines(info: &HiveInfo) -> String {
    match info.machines.as_slice() {
        [] => "no machines yet".to_owned(),
        [one] => format!("1 machine: {one}"),
        all => format!("{} machines: {}", all.len(), all.join(", ")),
    }
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

/// A duration in its largest whole unit, as `musubi list` shows how long ago or how soon:
/// `40s`, `12m`, `3h`, `2d`.
fn roughly(duration: Duration) -> String {
    let secs = duration.as_secs();
    match secs {
        0..60 => format!("{secs}s"),
        60..3_600 => format!("{}m", secs / 60),
        3_600..86_400 => format!("{}h", secs / 3_600),
        _ => format!("{}d", secs / 86_400),
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
    if !node.present_copies()?.1.is_present(node.machine().key()) {
        println!("             forgotten by the hive, which shows it again once it's used");
    }
    for (workspace, commit) in node.machine_workspaces()? {
        let short = &commit.hex()[..12];
        println!("             {workspace}@ is at {short}");
    }
    let now = std::time::SystemTime::now();
    for (index, copy) in node.activity()?.iter().enumerate() {
        let label = if index == 0 {
            "  Copies:    "
        } else {
            "             "
        };
        let this = if copy.key == node.machine().key() {
            " (this one)"
        } else {
            ""
        };
        let since = now.duration_since(copy.last_work).unwrap_or_default();
        let forgotten = match copy.forget_after {
            None => "never forgotten".to_owned(),
            Some(after) => {
                let after_text = musubi_jj::presence::format_forget_after(Some(after));
                match after.checked_sub(since) {
                    Some(left) if !left.is_zero() => format!(
                        "forgotten once unused for {after_text}, in {}",
                        roughly(left)
                    ),
                    _ => format!("forgotten once unused for {after_text}, any moment now"),
                }
            }
        };
        println!(
            "{label}{}{this}: last used {} ago, {forgotten}",
            copy.name,
            roughly(since)
        );
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
