//! `musubi`: replicate jj repositories between machines.

mod agent;
mod completion;
mod config;
mod control;
mod copy;
mod daemon;
mod hub;
mod listing;
mod lock;
mod login;
mod open_files;
mod repo;
mod settings;
mod socket;
mod ssh;
mod status;
mod top;
mod ui;
mod watch;

use std::collections::BTreeMap;
use std::io::IsTerminal as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command as Process;
use std::process::ExitCode;
use std::time::Duration;

use anyhow::Context as _;
use clap::CommandFactory as _;
use clap::Parser;
use clap::Subcommand;
use clap::ValueHint;
use clap_complete::ArgValueCandidates;
use jj_cli::formatter::FormatterExt as _;
use jj_cli::ui::ColorChoice;
use jj_lib::object_id::ObjectId as _;
use musubi_hub::hub_dir::HiveInfo;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::JoinRequest;
use musubi_hub::hub_dir::Joined;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::remote::HiveGone;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::config::Settings;
use crate::config::UserState;
use crate::control::Synced;
use crate::daemon::Status;
use crate::listing::Line;
use crate::listing::Lister;
use crate::repo::Located;
use crate::socket::Socket;
use crate::ui::Ui;

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
    /// When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color`
    /// says].
    #[arg(
        long,
        global = true,
        value_name = "WHEN",
        help_heading = "Global options"
    )]
    color: Option<ColorChoice>,
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
        #[command(flatten)]
        args: HubArgs,
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
        /// Sync this repository as the copy it was made from, which must be gone: for a copy
        /// moved by copying it and deleting the original, or restored onto a new machine.
        /// musubi otherwise takes it for a duplicate, and syncs nothing.
        #[arg(long, conflicts_with = "hive")]
        original: bool,
        #[command(flatten)]
        member: Member,
    },
    /// Create a new colocated repository from a hive.
    ///
    /// It makes the repository, joins it to the hive, and returns once it has synced, with
    /// the daemon keeping it in sync from then on. It checks out the hive's trunk, as
    /// `jj git clone` checks out a remote's default branch.
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
    List {
        /// Print only a line for each hub, each of its hives, and each copy of one here, in
        /// that order, with this template, in jj's template language, in place of
        /// `musubi.templates.list` in jj's config. A copy's line has its hive's `hub`,
        /// `reached`, `hive`, `id` and `machines`; a copy that isn't where it was, of a hive
        /// no hub here lists, has only its hive's `id`. The keywords:
        ///
        /// * `hub: String`: The hub, as `--hub` takes it.
        /// * `reached: Boolean`: Whether the hub answered.
        /// * `hive: String`: The hive's name; empty on a hub's line.
        /// * `id: String`: The hive's id; empty on a hub's line.
        /// * `machines: List<String>`: The machines in the hive, as its hub knows them.
        /// * `path: Option<FsPath>`: Where the copy is; none on a hub's line or a hive's.
        /// * `status: String`: How the copy's syncing goes; empty on a hub's line or a
        ///   hive's.
        /// * `problem: String`: What's wrong, if anything: why the hub is out of reach, that
        ///   the hive is no longer on it, or why the copy's syncing fails.
        ///
        /// `json(self)` gives the whole line, for a script.
        #[arg(long, short = 'T', verbatim_doc_comment)]
        #[arg(add = ArgValueCandidates::new(completion::template_aliases))]
        template: Option<String>,
    },
    /// Show what musubi does with the repository in the current directory: its hive, whether
    /// it syncs, and whether the hub has its latest work.
    ///
    /// It shows the repository's hive, hub and machine name, its last sync, every machine's
    /// working copies, each copy in the hive with when it was last used and when it will be
    /// forgotten (`musubi.forget-after`), and the daemon: whether it runs and serves the
    /// repository, its process, socket, and log. It warns of what keeps the repository from
    /// syncing, saying what to do. Outside a hive, it says so, and shows the default hub and
    /// the daemon; so too in a repository musubi doesn't sync, as one made by copying a
    /// copy's files, saying why.
    ///
    /// It never starts the daemon or asks the hub, so it answers at once.
    Status {
        /// Print only the report, with this template, in jj's template language. Outside a
        /// hive, a hive's strings are empty and its booleans false. The keywords:
        ///
        /// * `repository: Option<FsPath>`: The workspace the current directory is in; none
        ///   outside a jj repository.
        /// * `hive: String`: The repository's hive.
        /// * `id: String`: The hive's id.
        /// * `hub: String`: The hive's hub.
        /// * `machine: String`: This machine's name in the hive.
        /// * `default_hub: String`: The hub commands use without `--hub`; empty if none.
        /// * `head: Option<Integer>`: The hive's head, as of the last sync; none before it.
        /// * `status: String`: When the repository last synced.
        /// * `problem: String`: Why musubi doesn't sync the repository, though it has a
        ///   hive's record, as when it was made by copying a copy's files; else why its
        ///   syncing fails, if it does.
        /// * `sent: Boolean`: Whether the hub has all this machine's work, as far as the
        ///   last sync tells; false if it can't tell.
        /// * `forgotten: Boolean`: Whether the hive has forgotten this copy, until it's used.
        /// * `daemon_running: Boolean`: Whether the daemon runs; false if that can't be told.
        /// * `serving: Boolean`: Whether the daemon serves the repository.
        ///
        /// `json(self)` gives the whole report, for a script or an agent, with `null` for
        /// what can't be told.
        #[arg(long, short = 'T', verbatim_doc_comment)]
        #[arg(add = ArgValueCandidates::new(completion::template_aliases))]
        template: Option<String>,
    },
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
        /// Instead, stop syncing the copy that was at this path, which is gone: deleted, say.
        /// `musubi list` lists these. The other machines go on showing it until one of them
        /// forgets it.
        #[arg(conflicts_with = "force", value_hint = ValueHint::DirPath)]
        path: Option<PathBuf>,
    },
    /// Forget another machine's copy of this repository: the other machines stop showing its
    /// working copies, and the hub stops counting it.
    ///
    /// For a machine that went away without `musubi leave`, as a short-lived machine can.
    /// Its working-copy commit is abandoned if it's empty, and otherwise stays as an ordinary
    /// commit. If the copy is still there, the hive shows it again as soon as it's used.
    Forget {
        /// The machine, as its working copies are named here: `laptop` for `laptop/default@`,
        /// `laptop-1a2b` for `laptop-1a2b/default@`, or, where even the start of its id is
        /// another machine's, its whole id, as in `laptop-1a2b3c4d/default@`. The name
        /// `musubi list` gives it will do too, if no other machine could have that name.
        machine: String,
    },
    /// Sync the repository in the current directory now.
    ///
    /// The daemon syncs by itself whenever the repository or its hive changes, so this is
    /// rarely needed, except to see at once how a sync goes. It asks the daemon to sync, if
    /// the daemon serves the repository, and otherwise syncs in this process, saying if
    /// that's because the daemon isn't running.
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
    /// by, or on that machine, the hub's directory, or the machine's name or `localhost`, for
    /// the hub `musubi hub` serves there without `--dir`, reached without ssh [default: this
    /// machine's default hub].
    #[arg(long, add = ArgValueCandidates::new(completion::hubs))]
    hub: Option<String>,
}

/// Where a hub is, and what it tells other machines, for `hub` and `hub install`.
#[derive(clap::Args)]
struct HubArgs {
    /// The hub's directory [default: the current directory if it is a hub's, or else
    /// ~/musubi-hub].
    #[arg(short, long, value_hint = ValueHint::DirPath)]
    dir: Option<PathBuf>,
    /// The host name other machines ssh to this one by, for the commands it prints
    /// [default: this machine's host name]. Once given, the hub keeps it (in hub.toml).
    #[arg(long)]
    advertise: Option<String>,
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
    /// Run the hub at login from now on (a launchd agent on macOS, a systemd user unit on
    /// Linux), and now, as this machine's hub.
    ///
    /// It serves the directory `musubi hub` would, creating it the first time. On Linux,
    /// the hub stops when you log out, unless `loginctl enable-linger` keeps your services
    /// running. Run it again to serve another directory, or after moving `musubi` or `git`.
    Install {
        #[command(flatten)]
        args: HubArgs,
    },
    /// Stop running the hub at login, and stop it.
    Uninstall,
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
fn log_filter(cli: &Cli, ui: &Ui) -> anyhow::Result<tracing_subscriber::EnvFilter> {
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
            Err(err) => writeln!(ui.warning(), "Ignoring RUST_LOG={filter:?} ({err}).")?,
        }
    }
    if daemon && let Some(filter) = Settings::load()?.daemon_log {
        return parse_filter(&filter)
            .with_context(|| format!("bad log filter {filter:?} in musubi.daemon.log"));
    }
    // jj's library logs every lock it takes and every index it builds, at length.
    if daemon || hub {
        return parse_filter("info,jj_lib=warn");
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

fn main() -> ExitCode {
    completion::complete_if_asked();
    let cli = match Cli::try_parse() {
        Ok(cli) => cli,
        Err(err) => {
            let ui = Ui::new(early_color()).unwrap_or_else(|_| Ui::plain());
            return ui.clap_error(&err);
        }
    };
    let ui = match command_ui(&cli) {
        Ok(ui) => ui,
        Err(err) => return Ui::plain().finish(Err(err)),
    };
    let result = run(cli, &ui);
    ui.finish(result)
}

/// `--color`, read from a command line clap refused, as jj reads it, so that its help and
/// its errors print as it says.
fn early_color() -> Option<ColorChoice> {
    Cli::command()
        .disable_help_flag(true)
        .disable_version_flag(true)
        .ignore_errors(true)
        .try_get_matches()
        .ok()?
        .get_one::<ColorChoice>("color")
        .copied()
}

/// How `cli`'s command prints. What the daemon and the hub write to stderr is their log,
/// which never has colour, unless it's a terminal. What `hub connect` writes there goes back
/// over ssh, for musubi to read, so it reads no config, which mustn't keep other machines
/// from the hub.
fn command_ui(cli: &Cli) -> anyhow::Result<Ui> {
    match &cli.command {
        Some(Command::Hub {
            action: Some(HubAction::Connect { .. }),
            ..
        }) => Ok(Ui::plain()),
        Some(Command::Daemon { action: None } | Command::Hub { action: None, .. })
            if !std::io::stderr().is_terminal() =>
        {
            Ui::new(Some(ColorChoice::Never))
        }
        _ => Ui::new(cli.color),
    }
}

fn run(cli: Cli, ui: &Ui) -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(log_filter(&cli, ui)?)
        .with_writer(std::io::stderr)
        // A log file never has colour.
        .with_ansi(ui.color() && std::io::stderr().is_terminal())
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
    if matches!(
        cli.command,
        Some(Command::Hub { action: None, .. } | Command::Daemon { action: None })
    ) {
        open_files::raise();
    }
    let cwd = std::env::current_dir()?;
    let socket = || Socket::locate(cli.socket.as_deref());
    match cli.command.unwrap_or(Command::List { template: None }) {
        Command::Hub {
            action: None,
            args: HubArgs { dir, advertise },
        } => hub::serve(ui, hub::ServeArgs { dir, advertise }),
        Command::Hub {
            action:
                Some(HubAction::Install {
                    args: HubArgs { dir, advertise },
                }),
            ..
        } => hub::install(ui, hub::ServeArgs { dir, advertise }),
        Command::Hub {
            action: Some(HubAction::Uninstall),
            ..
        } => {
            if login::uninstall(login::Service::Hub)? {
                writeln!(
                    ui.stdout(),
                    "The hub no longer runs at login, and is stopped."
                )?;
            } else {
                writeln!(ui.stdout(), "The hub wasn't set to run at login.")?;
            }
            Ok(())
        }
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
                let mut out = ui.stdout();
                write!(out, "Removed hive ")?;
                writeln!(out.labeled("hive"), "{}", info.name)?;
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
                let mut out = ui.stdout();
                if hive == info.name {
                    write!(out, "Hive ")?;
                    write!(out.labeled("hive"), "{hive}")?;
                    writeln!(out, " already has that name")?;
                } else {
                    write!(out, "Renamed hive ")?;
                    write!(out.labeled("hive"), "{hive}")?;
                    write!(out, " to ")?;
                    writeln!(out.labeled("hive"), "{}", info.name)?;
                }
            }
            Ok(())
        }),
        Command::Create { name, member } => join(
            ui,
            &cwd,
            JoinChoice::Create(name),
            &member,
            false,
            &socket()?,
        ),
        Command::Join {
            hive,
            original,
            member,
        } => {
            let choice = hive.map_or(JoinChoice::Match, JoinChoice::Hive);
            join(ui, &cwd, choice, &member, original, &socket()?)
        }
        Command::Clone {
            hive,
            destination,
            hub,
            machine,
        } => clone(
            ui,
            &destination,
            &hive,
            hub.as_deref(),
            machine.as_deref(),
            &socket()?,
        ),
        Command::List { template } => list(ui, &cwd, template.as_deref(), socket()),
        Command::Status { template } => {
            let report = status::Report::gather(&cwd, socket());
            match template {
                Some(text) => report.print_template(ui, &text, &cwd),
                None => Ok(report.print(ui)?),
            }
        }
        Command::Top {
            hub,
            interval,
            once,
        } => top::run(
            ui,
            top::Args {
                hub,
                interval: Duration::from_secs(interval),
                once,
            },
            socket(),
        ),
        Command::Leave { force, path } => leave(ui, &cwd, &socket()?, force, path.as_deref()),
        Command::Forget { machine } => forget(ui, &cwd, &machine, &socket()?),
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
            let described = login::install(login::Service::Daemon, None)?;
            daemon::ensure(&socket).await?;
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
        }),
        Command::Daemon {
            action: Some(DaemonAction::Uninstall),
        } => block_on(async {
            let socket = socket()?;
            let was = login::uninstall(login::Service::Daemon)?;
            daemon::stop(&socket).await?;
            if was {
                writeln!(
                    ui.stdout(),
                    "The daemon no longer starts at login, and is stopped."
                )?;
            } else {
                writeln!(ui.stdout(), "The daemon wasn't set to start at login.")?;
            }
            Ok(())
        }),
        Command::Daemon {
            action: Some(DaemonAction::Stop),
        } => block_on(async {
            if daemon::stop(&socket()?).await? {
                writeln!(ui.stdout(), "Stopped the daemon.")?;
            } else {
                writeln!(ui.stdout(), "No daemon is running.")?;
            }
            Ok(())
        }),
        Command::Daemon {
            action: Some(DaemonAction::Restart),
        } => block_on(async {
            let socket = socket()?;
            daemon::stop(&socket).await?;
            daemon::ensure(&socket).await?;
            writeln!(ui.stdout(), "Started the daemon.")?;
            Ok(())
        }),
        Command::Sync => sync(ui, &cwd, &socket()?),
        Command::Completion { shell } => completion::print_script(ui, shell),
        Command::Debug(Debug::OpId { id }) => op_id(ui, &cwd, &id),
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
/// `original` makes a repository the copy of its key that isn't (see [`copy`]).
fn join(
    ui: &Ui,
    start: &Path,
    choice: JoinChoice,
    member: &Member,
    original: bool,
    socket: &Socket,
) -> anyhow::Result<()> {
    let Member {
        machine,
        full_history,
        hub,
    } = member;
    let (hub, machine, full_history) = (hub.as_deref(), machine.as_deref(), *full_history);
    let located = Located::find(start)?;
    copy::check_owner(&located.repo_path)?;
    let found = copy::Found::resolve(&located)?;
    let state = UserState::load()?;
    let entry = found.key.as_deref().and_then(|key| state.entry(key));
    let standing = copy::standing_of(&located, &found, entry);
    // `musubi join` in a repository that is part of a hive joins that hive again, made again
    // if its hub has lost it.
    let rejoin = |record: &HiveConfig| -> anyhow::Result<(JoinChoice, String)> {
        let remake = JoinChoice::Remake {
            id: record.hive.to_string(),
            name: record.name.clone(),
        };
        let hub = hub.map_or_else(|| Ok(record.hub.clone()), |hub| UserState::hub(Some(hub)))?;
        Ok((remake, hub))
    };
    let (choice, hub) = match (standing, &found.record, choice) {
        (copy::Standing::Outside, _, choice) => (choice, UserState::hub(hub)?),
        (copy::Standing::Removed, Some(record), JoinChoice::Match) => anyhow::bail!(
            "this repository's hive, {}, was removed from its hub; `musubi join --hive \
             <name>` joins another, and `musubi create` starts a new one",
            record.display_name()
        ),
        (copy::Standing::Removed, _, choice) => (choice, UserState::hub(hub)?),
        // From any of its workspaces, or through a bind mount: one entry serves them all.
        (copy::Standing::Copy, Some(record), JoinChoice::Match) => rejoin(record)?,
        (copy::Standing::Duplicate | copy::Standing::Unknown, Some(record), JoinChoice::Match)
            if original =>
        {
            if let Some(path) = entry.and_then(copy::whereabouts) {
                anyhow::bail!(
                    "the copy of this repository's key is at {}, so this repository isn't it; \
                     `musubi clone` makes another copy",
                    path.display()
                );
            }
            rejoin(record)?
        }
        (copy::Standing::Copy, Some(record), _) => anyhow::bail!(
            "this repository is already part of hive {}; `musubi leave` first to join another",
            record.display_name()
        ),
        (standing, record, _) => {
            anyhow::bail!("{}", copy::not_the_copy(standing, record.as_ref(), entry))
        }
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
    let joined = match block_on(ask_preparing(ui, &hub, HubWideRequest::Join(request)))? {
        HubWideReply::Joined(joined) => joined,
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    };
    become_node(
        ui,
        &located,
        &joined,
        &hub,
        full_history,
        found.record.as_ref(),
    )?;
    let count = joined.hive.machines.len();
    let machines = if count == 1 {
        "1 machine".to_owned()
    } else {
        format!("{count} machines")
    };
    // The daemon may serve the repository with the hub it knew: `start_serving` has it start
    // over.
    let mut out = ui.stdout();
    let name = &joined.hive.name;
    if remaking && joined.created {
        write!(out, "Made hive ")?;
        write!(out.labeled("hive"), "{name}")?;
        writeln!(out, " again from this repository")?;
    } else if remaking {
        write!(out, "Hive ")?;
        write!(out.labeled("hive"), "{name}")?;
        writeln!(out, " is on the hub, and this repository is part of it")?;
    } else if joined.created {
        write!(out, "Created hive ")?;
        writeln!(out.labeled("hive"), "{name}")?;
    } else {
        write!(out, "Joined hive ")?;
        write!(out.labeled("hive"), "{name}")?;
        writeln!(out, " ({}), {machines}", joined.reason)?;
    }
    drop(out);
    start_serving(ui, &located, socket)
}

/// The repository at `start`, its record and its entry, if it is the copy of its key here
/// ([`copy`]); else fails, saying what it is. A copy whose entry is at a path that no longer
/// holds it moved here: its entry follows it, and the daemon serves it here.
fn the_copy(
    ui: &Ui,
    start: &Path,
    socket: &Socket,
) -> anyhow::Result<(Located, HiveConfig, Entry)> {
    let located = Located::find(start)?;
    copy::check_owner(&located.repo_path)?;
    let found = copy::Found::resolve(&located)?;
    let state = UserState::load()?;
    let entry = found.key.as_deref().and_then(|key| state.entry(key));
    let standing = copy::standing_of(&located, &found, entry);
    let (copy::Standing::Copy, Some(record), Some(entry)) = (standing, &found.record, entry) else {
        anyhow::bail!(
            "{}",
            copy::not_the_copy(standing, found.record.as_ref(), entry)
        );
    };
    let entry = follow_move(ui, &located, entry, socket)?;
    Ok((located, record.clone(), entry))
}

/// Moves `entry` to `located`, the copy it names, if its path no longer holds it, and has
/// the daemon serve it there. Returns the entry as it is now.
fn follow_move(
    ui: &Ui,
    located: &Located,
    entry: &Entry,
    socket: &Socket,
) -> anyhow::Result<Entry> {
    if entry.path == located.workspace_root || copy::holds(entry, &entry.path) {
        return Ok(entry.clone());
    }
    let moved = Entry {
        path: located.workspace_root.clone(),
        ..entry.clone()
    };
    // Unless the daemon, or another command, changed it first, which may have made another
    // repository the copy.
    anyhow::ensure!(
        UserState::move_entry(entry, moved.path.clone())?,
        "this machine's record of this repository changed meanwhile; run the command again"
    );
    // Not with what the command prints, as `musubi list -T` prints only its lines.
    writeln!(
        ui.stderr(),
        "This repository moved here from {}; it syncs from here now",
        entry.path.display()
    )?;
    // The daemon starts serving it here at once, and syncs in its own time: the command
    // needn't wait for that.
    block_on(async {
        if let Some(client) = daemon::running(socket).await? {
            client
                .add(control::context(Duration::from_secs(2)), moved.key.clone())
                .await
                .ok();
        }
        Ok::<_, anyhow::Error>(())
    })?;
    Ok(moved)
}

/// Asks `hub`, over ssh first making sure this machine's key works there.
async fn ask_preparing(
    ui: &Ui,
    hub: &str,
    request: HubWideRequest,
) -> anyhow::Result<HubWideReply> {
    if !hub::is_local(hub) {
        ssh::prepare(ui, hub).await?;
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

/// Records that the repository is part of the hive it `joined`: the join operation (unless
/// replicating full history), its record, and its entry, for the daemon to serve it. A copy
/// whose record named another hive, `before`, forgets the copies its history brings that the
/// hive doesn't have. The first hub joined becomes the user's default.
fn become_node(
    ui: &Ui,
    located: &Located,
    joined: &Joined,
    hub: &str,
    full_history: bool,
    before: Option<&HiveConfig>,
) -> anyhow::Result<()> {
    let hive_id: uuid::Uuid = joined
        .hive
        .id
        .parse()
        .context("the hub sent a malformed hive id")?;
    let mut node = located.open()?;
    let machine = node.machine().name().to_owned();
    let key = node.machine().key().to_owned();
    let description = format!("musubi: {machine} joins the hive");
    if full_history {
        node.mark_joined(&description)?;
    } else {
        node.create_join_operation(&description)?;
    }
    // A hive doesn't take on the members of another: they aren't its own until they join it.
    if before.is_none_or(|before| before.hive != hive_id) {
        let keep: std::collections::BTreeSet<String> = joined.present.iter().cloned().collect();
        node.forget_copies_except(&keep)?;
    }
    drop(node);
    // Only joining gives the repository a jj config id, which its record and entry name.
    settings::repo_config_path(&located.repo_path)?;
    let config_id = copy::Found::read(&located.repo_path)?
        .config_id
        .context("jj gave this repository no config id")?;
    // Through the workspace it joined from already, if this is another of the same
    // repository's.
    let path = UserState::load()?
        .entry(&key)
        .filter(|entry| {
            Located::find(&entry.path)
                .is_ok_and(|other| copy::same_directory(&other.repo_path, &located.repo_path))
        })
        .map_or_else(
            || located.workspace_root.clone(),
            |entry| entry.path.clone(),
        );
    // The entry first: a record that names a config id no entry here does would make this
    // repository look like a duplicate, if what follows failed.
    UserState::put_entry(Entry {
        key,
        hive: hive_id,
        config_id: config_id.clone(),
        path,
    })?;
    let config = HiveConfig {
        hive: hive_id,
        name: Some(joined.hive.name.clone()),
        hub: hub.to_owned(),
        node: machine,
        config_id,
        state: Membership::Joined,
    };
    {
        let _lock = HiveConfig::lock(&located.repo_path)?;
        config.save(&located.repo_path)?;
    }
    set_forget_after(ui, located)?;
    UserState::save_default_hub(hub)?;
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
/// set when the repository last joined. Says so if it sets `6h`, which a person watching
/// an agent may not expect.
fn set_forget_after(ui: &Ui, located: &Located) -> anyhow::Result<()> {
    let settings = settings::load(&located.workspace_root, &located.repo_path)?;
    if configured_forget_after(settings.config())?.is_some() {
        return Ok(());
    }
    let name: jj_lib::config::ConfigNamePathBuf = musubi_jj::node::FORGET_AFTER_KEY.parse()?;
    let agent = AGENT_VARIABLES
        .iter()
        .any(|var| std::env::var_os(var).is_some());
    let value = if agent { AGENT_FORGET_AFTER } else { "never" };
    let path = settings::repo_config_path(&located.repo_path)?
        .context("this repository has no config of its own")?;
    let mut file =
        jj_lib::config::ConfigFile::load_or_empty(jj_lib::config::ConfigSource::Repo, &path)?;
    file.set_value(&name, value)?;
    file.save()?;
    if agent {
        writeln!(
            ui.stdout(),
            "The hive forgets this copy once it goes unused for {AGENT_FORGET_AFTER}."
        )?;
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
fn start_serving(ui: &Ui, located: &Located, socket: &Socket) -> anyhow::Result<()> {
    /// How asking the daemon to serve the repository went.
    enum Served {
        /// There was no daemon to ask, nor could one be started.
        NoDaemon(anyhow::Error),
        Synced(Synced),
        /// The daemon serves it, but its first sync failed, saying this.
        Failed(String),
    }
    let key = copy::Found::read(&located.repo_path)?
        .key
        .context("this repository has no machine key")?;
    // The client lives on the runtime that made it, so one runtime does it all.
    let served = block_on(async {
        let client = match daemon::ensure(socket).await {
            Ok(client) => client,
            Err(err) => return Ok(Served::NoDaemon(err)),
        };
        writeln!(ui.stdout(), "Syncing...")?;
        let first = client
            .add(control::context(Duration::from_secs(3600)), key)
            .await
            .context("asking the daemon to serve this repository")?;
        Ok::<_, anyhow::Error>(match first {
            Ok(synced) => Served::Synced(synced),
            Err(message) => Served::Failed(message),
        })
    })?;
    match served {
        Served::NoDaemon(err) => {
            writeln!(
                ui.warning(),
                "Could not start the daemon ({err:#}); syncing once instead."
            )?;
            let synced = sync_directly(located)?;
            writeln!(ui.stdout(), "Synced (hive at #{}).", synced.seq)?;
            writeln!(ui.hint(), "Run `musubi daemon` to keep it in sync.")?;
            Ok(())
        }
        Served::Synced(synced) => {
            writeln!(
                ui.stdout(),
                "Synced with the hub (hive at #{}).",
                synced.seq
            )?;
            Ok(())
        }
        // Unless it's a failure no retry gets past, as the daemon recorded before it answered.
        Served::Failed(message)
            if Status::load(&located.repo_path).is_some_and(|status| status.paused) =>
        {
            anyhow::bail!("the first sync failed: {message}")
        }
        Served::Failed(message) => anyhow::bail!(
            "the first sync failed: {message}\nThe daemon keeps trying; `musubi status` shows how \
             it goes."
        ),
    }
}

fn clone(
    ui: &Ui,
    destination: &Path,
    hive: &str,
    hub: Option<&str>,
    machine: Option<&str>,
    socket: &Socket,
) -> anyhow::Result<()> {
    let hub = UserState::hub(hub)?;
    configured_forget_after(&settings::user_config()?)?;
    let reply = block_on(ask_preparing(
        ui,
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
    let joined = Joined {
        hive: info.clone(),
        created: false,
        reason: String::new(),
        present: vec![],
    };
    become_node(ui, &located, &joined, &hub, false, None)?;
    let mut out = ui.stdout();
    write!(out, "Cloning hive ")?;
    write!(out.labeled("hive"), "{}", info.name)?;
    writeln!(out, " into {}", destination.display())?;
    drop(out);
    start_serving(ui, &located, socket)?;
    if let Err(err) = check_out_trunk(&located) {
        writeln!(
            ui.warning(),
            "Couldn't check out the hive's trunk ({err:#})."
        )?;
        writeln!(ui.hint(), "`jj new 'trunk()'` checks it out.")?;
    }
    Ok(())
}

/// Checks out the hive's trunk in a new copy, as `jj git clone` checks out the remote's
/// default branch: a new working-copy commit on it, unless the hive's `trunk()` is the root.
fn check_out_trunk(located: &Located) -> anyhow::Result<()> {
    let jj = |args: &[&str]| {
        let mut jj = Process::new("jj");
        musubi_jj::git_command::without_repository_env(&mut jj);
        jj.args(args).current_dir(&located.workspace_root);
        jj
    };
    let output = jj(&[
        "log",
        "--ignore-working-copy",
        "--no-graph",
        "-n1",
        "-r",
        "trunk() ~ root()",
        "-T",
        "commit_id",
    ])
    .output()
    .context("running `jj log`")?;
    anyhow::ensure!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr).trim()
    );
    let trunk = String::from_utf8_lossy(&output.stdout);
    if trunk.is_empty() {
        return Ok(());
    }
    // jj says where the working copy is now, as `jj git clone` does.
    let status = jj(&["new", &trunk]).status().context("running `jj new`")?;
    anyhow::ensure!(status.success(), "`jj new {trunk}` failed");
    Ok(())
}

/// Syncs once, in this process.
fn sync_directly(located: &Located) -> anyhow::Result<Synced> {
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    block_on(daemon::sync_once(located, &hive))
}

/// Syncs through the daemon when it serves the repository, else directly.
fn sync(ui: &Ui, start: &Path, socket: &Socket) -> anyhow::Result<()> {
    let (synced, stopped) = sync_quietly(ui, start, socket)?;
    writeln!(ui.stdout(), "Synced (hive at #{}).", synced.seq)?;
    if stopped {
        writeln!(
            ui.warning(),
            "The daemon isn't running, so this synced in its own process, and nothing keeps \
             this repository in sync."
        )?;
        writeln!(ui.hint(), "`musubi daemon start` starts it.")?;
    }
    Ok(())
}

/// [`sync`], saying nothing, and whether it synced here because the daemon that would serve
/// the repository isn't running.
fn sync_quietly(ui: &Ui, start: &Path, socket: &Socket) -> anyhow::Result<(Synced, bool)> {
    let (located, hive, entry) = the_copy(ui, start, socket)?;
    let mut stopped = false;
    let through_daemon = block_on(async {
        let Some(client) = daemon::running(socket).await? else {
            stopped = true;
            return Ok(None);
        };
        let synced = client
            .sync(control::context(Duration::from_secs(3600)), entry.key)
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
                daemon::leave_hive(&located, &hive, Membership::Removed)?;
                anyhow::bail!(
                    "{err:#}, so this repository no longer syncs with it; everything it has stays"
                );
            }
            Err(err) => return Err(err),
        },
    };
    Ok((synced, stopped))
}

/// Stops the daemon serving the copy whose entry is at `path`, which may be gone: the hive
/// isn't told, since only the copy can tell it.
fn leave_path(ui: &Ui, path: &Path, socket: &Socket) -> anyhow::Result<()> {
    // As entries are: canonical, though the copy is gone, by the directory that held it.
    let path = std::path::absolute(path)?;
    let path = match (path.parent().map(Path::canonicalize), path.file_name()) {
        (Some(Ok(parent)), Some(name)) => parent.join(name),
        _ => path,
    };
    let state = UserState::load()?;
    let entry = state
        .copies
        .iter()
        .find(|entry| entry.path == path)
        .with_context(|| format!("this machine syncs no copy at {}", path.display()))?;
    anyhow::ensure!(
        !copy::holds(entry, &entry.path),
        "the copy is at {}; `musubi leave` there takes it out of its hive",
        entry.path.display()
    );
    stop_serving(&entry.key, socket)?;
    UserState::remove_entry(&entry.key)?;
    writeln!(
        ui.stdout(),
        "This machine no longer syncs the copy at {}.",
        entry.path.display()
    )?;
    Ok(())
}

/// Stops the daemon, if it runs, serving `key`'s copy. Returns whether one runs.
fn stop_serving(key: &str, socket: &Socket) -> anyhow::Result<bool> {
    block_on(async {
        let Some(client) = daemon::running(socket).await? else {
            return Ok(false);
        };
        client
            .remove(control::context(Duration::from_secs(120)), key.to_owned())
            .await?
            .map_err(anyhow::Error::msg)?;
        Ok::<_, anyhow::Error>(true)
    })
}

fn leave(
    ui: &Ui,
    start: &Path,
    socket: &Socket,
    force: bool,
    path: Option<&Path>,
) -> anyhow::Result<()> {
    if let Some(path) = path {
        return leave_path(ui, path, socket);
    }
    let (located, hive, entry) = the_copy(ui, start, socket)?;
    // So that the daemon doesn't sync it meanwhile.
    let served = stop_serving(&entry.key, socket)?;
    let name = hive.display_name();
    let told = match snapshot(&located) {
        Err(err) => Err(("record what changed in the working copy".to_owned(), err)),
        Ok(()) => tell_the_hive(ui, &located, &hive)
            .map_err(|err| (format!("tell hive {name} that this repository leaves"), err)),
    };
    if let Err((doing, err)) = told {
        if !force {
            if served {
                // As before: the daemon serves it again.
                block_on(async {
                    if let Some(client) = daemon::running(socket).await? {
                        let context = control::context(Duration::from_secs(10));
                        client.add(context, entry.key.clone()).await.ok();
                    }
                    Ok::<_, anyhow::Error>(())
                })
                .ok();
            }
            anyhow::bail!(
                "couldn't {doing}: {err:#}; `musubi leave --force` leaves without telling the hive"
            );
        }
        writeln!(ui.warning(), "Couldn't {doing} ({err:#}); leaving anyway.")?;
    }
    // No next work of a copy out of its hive shows it there again: a working copy the hive
    // abandoned gets a new commit now.
    if let Err(err) = located
        .open()
        .and_then(|mut node| Ok(node.give_back_working_copies()?))
    {
        writeln!(
            ui.warning(),
            "Couldn't give this repository's working copies new commits ({err:#})."
        )?;
    }
    daemon::leave_hive(&located, &hive, Membership::Left)?;
    let mut out = ui.stdout();
    write!(out, "This repository has left hive ")?;
    write!(out.labeled("hive"), "{name}")?;
    writeln!(out, ".")?;
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
fn tell_the_hive(ui: &Ui, located: &Located, hive: &HiveConfig) -> anyhow::Result<()> {
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
            writeln!(
                ui.warning(),
                "Couldn't put back this repository's working copies ({err:#})."
            )?;
            writeln!(
                ui.hint(),
                "`jj op log` lists `musubi: leave`; `jj op restore` to the operation before it \
                 brings them back."
            )?;
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

fn forget(ui: &Ui, start: &Path, machine: &str, socket: &Socket) -> anyhow::Result<()> {
    let (located, hive, _) = the_copy(ui, start, socket)?;
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
            sync_quietly(ui, start, socket)?;
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
        let mut out = ui.stdout();
        write!(out, "Forgot ")?;
        write!(out.labeled("machine"), "{machine}")?;
        writeln!(out)?;
    }
    drop(node);
    sync(ui, start, socket)
}

/// A repository on this machine that is part of a hive.
struct Copy {
    located: Located,
    hive: HiveConfig,
    status: Option<Status>,
}

/// Lists what it can: a daemon or hub out of reach is a line of the listing.
fn list(
    ui: &Ui,
    cwd: &Path,
    template: Option<&str>,
    socket: anyhow::Result<Socket>,
) -> anyhow::Result<()> {
    let lister = Lister::new(ui, template, cwd)?;
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
        let statuses: BTreeMap<String, Status> = client
            .status(control::context(Duration::from_secs(10)))
            .await?
            .into_iter()
            .map(|repo| (repo.key, repo.status))
            .collect();
        Ok::<_, anyhow::Error>((Ok(true), statuses))
    })?;
    // A copy moved here is served here from now on.
    if let Ok(located) = Located::find(cwd)
        // jj, looking at it, could write to another user's repository.
        && copy::check_owner(&located.repo_path).is_ok()
        && let Ok(found) = copy::Found::resolve(&located)
        && let Some(entry) = found.key.as_deref().and_then(|key| state.entry(key))
        && copy::standing_of(&located, &found, Some(entry)) == copy::Standing::Copy
        && let Ok(socket) = &socket
        && let Err(err) = follow_move(ui, &located, entry, socket)
    {
        writeln!(
            ui.warning(),
            "Couldn't sync this repository from here: {err:#}"
        )?;
    }
    let state = UserState::load()?;
    let mut copies = vec![];
    let mut missing = vec![];
    // The missing copies printed under their hives.
    let mut shown: Vec<&Entry> = vec![];
    for entry in &state.copies {
        let located = Located::find(&entry.path)
            .ok()
            .filter(|_| copy::holds(entry, &entry.path));
        let Some((located, Some(hive))) = located.map(|located| {
            let hive = HiveConfig::load(&located.repo_path).ok().flatten();
            (located, hive)
        }) else {
            missing.push(entry);
            continue;
        };
        let status = statuses
            .get(&entry.key)
            .cloned()
            .or_else(|| Status::load(&located.repo_path));
        copies.push(Copy {
            located,
            hive,
            status,
        });
    }
    let hubs = UserState::known_hubs(state.default_hub()?, copies.iter().map(|copy| &copy.hive));
    if hubs.is_empty() && template.is_none() {
        no_hubs(ui)?;
    }
    for hub in &hubs {
        let here: Vec<&Copy> = copies.iter().filter(|copy| &copy.hive.hub == hub).collect();
        match block_on(list_hub(hub)) {
            Ok(hives) => {
                // A copy shows its hive's name while the hub is out of reach, so keep up with
                // renames.
                for copy in &here {
                    if let Some(info) = hives.iter().find(|h| h.id == copy.hive.hive.to_string()) {
                        copy.hive.note_name(&copy.located.repo_path, &info.name);
                    }
                }
                lister.print(&Line::hub(hub, None))?;
                for info in &hives {
                    let hive = Line::hive(hub, info);
                    lister.print(&hive)?;
                    for copy in here.iter().filter(|c| c.hive.hive.to_string() == info.id) {
                        lister.print(&copy_line(&hive, copy))?;
                    }
                    print_missing(&lister, &hive, &missing, &mut shown)?;
                }
                for copy in here
                    .iter()
                    .filter(|copy| !hives.iter().any(|h| h.id == copy.hive.hive.to_string()))
                {
                    let hive = hive_here(hub, true, copy);
                    lister.print(&Line {
                        problem: "no longer on the hub".to_owned(),
                        ..hive.clone()
                    })?;
                    lister.print(&copy_line(&hive, copy))?;
                    print_missing(&lister, &hive, &missing, &mut shown)?;
                }
            }
            Err(err) => {
                lister.print(&Line::hub(hub, Some(format!("{err:#}"))))?;
                for copy in &here {
                    let hive = hive_here(hub, false, copy);
                    lister.print(&hive)?;
                    lister.print(&copy_line(&hive, copy))?;
                    print_missing(&lister, &hive, &missing, &mut shown)?;
                }
            }
        }
    }
    // Copies not where their entries say, of hives no hub listed: with their hives' ids
    // alone, which their entries keep.
    for entry in missing.iter().filter(|entry| !shown.contains(entry)) {
        let hive = Line {
            id: entry.hive.to_string(),
            ..Line::default()
        };
        lister.print(&missing_line(&hive, entry))?;
    }
    // As jj's list commands print only their lines when given a template.
    if template.is_some() {
        return Ok(());
    }
    if let Some(entry) = missing.first() {
        writeln!(
            ui.hint(),
            "A copy not where it was syncs again if it comes back, or once jj runs in it where it \
             was moved to. If it's gone, `musubi leave {}` stops looking for it.",
            entry.path.display()
        )?;
    }
    let mut out = ui.stdout();
    let at_login = if login::installed(login::Service::Daemon) {
        "starts at login"
    } else {
        "doesn't start at login; `musubi daemon install` makes it"
    };
    write!(out, "Daemon: ")?;
    match daemon {
        Ok(true) => writeln!(
            out,
            "running, serving {} repositories; {at_login}",
            statuses.len()
        )?,
        Ok(false) => {
            write!(out.labeled("problem"), "not running")?;
            writeln!(out, " ({at_login}); `musubi daemon start` starts it")?;
        }
        Err(err) => writeln!(out.labeled("problem"), "{err:#}")?,
    }
    Ok(())
}

/// Says that this machine knows no hub, and what to do.
fn no_hubs(ui: &Ui) -> std::io::Result<()> {
    writeln!(ui.stdout(), "No hubs yet.")?;
    writeln!(
        ui.hint(),
        "Run `musubi hub` on one machine, then the join command it prints."
    )
}

/// The lines of the copies in `missing` of the hive on line `hive`, unless `shown` has them,
/// as it does from then on.
fn print_missing<'a>(
    lister: &Lister,
    hive: &Line,
    missing: &[&'a Entry],
    shown: &mut Vec<&'a Entry>,
) -> anyhow::Result<()> {
    for &entry in missing {
        if entry.hive.to_string() == hive.id && !shown.contains(&entry) {
            lister.print(&missing_line(hive, entry))?;
            shown.push(entry);
        }
    }
    Ok(())
}

/// The line of a copy that isn't where `entry` says, of the hive on line `hive`.
fn missing_line(hive: &Line, entry: &Entry) -> Line {
    let why = why_missing(entry);
    Line {
        path: Some(entry.path.clone()),
        status: format!("not syncing: {why}"),
        problem: why,
        ..hive.clone()
    }
}

/// Why `entry`'s path doesn't hold the copy it names.
fn why_missing(entry: &Entry) -> String {
    let Ok(located) = Located::find(&entry.path) else {
        return "it's missing".to_owned();
    };
    match copy::Found::read(&located.repo_path) {
        Ok(found) => match copy::check(entry, &found) {
            Ok(()) => "it is back".to_owned(),
            Err(why) => format!("the repository there isn't the copy: {why}"),
        },
        Err(err) => format!("{err:#}"),
    }
}

/// The machines in a hive, as shell completion shows them.
fn machines(info: &HiveInfo) -> String {
    match info.machines.as_slice() {
        [] => "no machines yet".to_owned(),
        [one] => format!("1 machine: {one}"),
        all => format!("{} machines: {}", all.len(), all.join(", ")),
    }
}

/// The line of `copy`'s hive, on `hub`, as this machine knows it: by name and id.
fn hive_here(hub: &str, reached: bool, copy: &Copy) -> Line {
    Line {
        hub: hub.to_owned(),
        reached,
        hive: copy.hive.display_name(),
        id: copy.hive.hive.to_string(),
        ..Line::default()
    }
}

/// The line of `copy`, of the hive on line `hive`.
fn copy_line(hive: &Line, copy: &Copy) -> Line {
    let status = copy.status.as_ref();
    Line {
        path: Some(copy.located.workspace_root.clone()),
        status: describe(status),
        problem: status
            .and_then(|status| status.error.clone())
            .unwrap_or_default(),
        ..hive.clone()
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

/// How syncing goes, as `status` says.
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

fn op_id(ui: &Ui, start: &Path, id: &str) -> anyhow::Result<()> {
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
        writeln!(
            ui.stdout(),
            "local {} = hive {}",
            local.hex(),
            canonical.hex()
        )?;
        return Ok(());
    }
    if let Some(canonical) = node.canonical_store().resolve_prefix(id)? {
        match node.local_of(&canonical) {
            Some(local) => writeln!(
                ui.stdout(),
                "hive {} = local {}",
                canonical.hex(),
                local.hex()
            )?,
            None => writeln!(
                ui.stdout(),
                "hive {} is not realized on this machine yet",
                canonical.hex()
            )?,
        }
        return Ok(());
    }
    anyhow::bail!("no operation {id} here or in the hive")
}
