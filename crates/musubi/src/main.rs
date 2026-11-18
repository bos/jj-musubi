//! `musubi`: replicate jj repositories between machines.

mod agent;
mod backoff;
mod cli;
mod clone_config;
mod completion;
mod config;
mod control;
mod copy;
mod daemon;
mod debug;
mod hub;
mod join;
mod leave;
mod list;
mod lock;
mod login;
mod open_files;
mod repo;
mod settings;
mod snapshot;
mod socket;
mod ssh;
mod status;
mod sync;
mod top;
mod ui;
mod upgrade;
mod watch;

use std::io::IsTerminal as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

use anyhow::Context as _;
use clap::CommandFactory as _;
use clap::Parser as _;
use jj_cli::ui::ColorChoice;
use musubi_hub::hub_dir::JoinChoice;

use crate::cli::Cli;
use crate::cli::Command;
use crate::cli::DaemonAction;
use crate::cli::Debug;
use crate::cli::HubAction;
use crate::cli::HubArgs;
use crate::config::Settings;
use crate::socket::Socket;
use crate::ui::Ui;

/// What to log: `--log`, else `RUST_LOG`, else for the daemon `musubi.daemon.log` in jj's
/// config. Otherwise the hub and the daemon log what they do, and other commands only
/// warn, since they say what they did themselves.
fn log_filter(cli: &Cli, ui: &Ui) -> anyhow::Result<tracing_subscriber::EnvFilter> {
    let role = Role::of(cli.command.as_ref());
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
    if role == Role::Daemon
        && let Some(filter) = Settings::load()?.daemon_log
    {
        return parse_filter(&filter)
            .with_context(|| format!("bad log filter {filter:?} in musubi.daemon.log"));
    }
    if role.serves() {
        return parse_filter(&serving_filter());
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

/// The crates of jj's that musubi builds, as targets of what they log.
const JJ_CRATES: &[&str] = &[
    "jj_cli",
    "jj_core",
    "jj_core_proc_macros",
    "jj_default_index",
    "jj_dsl",
    "jj_frontend",
    "jj_git_backend",
    "jj_lib",
    "jj_local_util",
    "jj_simple_stores",
];

/// What the hub and the daemon log unless told otherwise: what they do, and only warnings
/// from jj's crates, which log every lock they take and every index they build, at length.
fn serving_filter() -> String {
    std::iter::once("info".to_owned())
        .chain(JJ_CRATES.iter().map(|name| format!("{name}=warn")))
        .collect::<Vec<_>>()
        .join(",")
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
    match Role::of(cli.command.as_ref()) {
        Role::Relay => Ok(Ui::plain()),
        role if role.serves() && !std::io::stderr().is_terminal() => {
            Ui::new(Some(ColorChoice::Never))
        }
        _ => Ui::new(cli.color),
    }
}

/// What kind of process a command makes, which decides how it logs, prints and finds its ssh
/// agent. A command with no subcommand runs `list`, so is `Ordinary`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    /// `daemon` with no action: the serving daemon.
    Daemon,
    /// `hub` with no action: the serving hub.
    Hub,
    /// `hub connect`: the far end of an ssh link, whose stdio belongs to the protocol.
    Relay,
    /// `completion`: a shell printing its completion script as it starts.
    Completion,
    /// Everything else.
    Ordinary,
}

impl Role {
    fn of(command: Option<&Command>) -> Self {
        match command {
            Some(Command::Daemon { action: None }) => Self::Daemon,
            Some(Command::Hub { action: None, .. }) => Self::Hub,
            Some(Command::Hub {
                action: Some(HubAction::Connect { .. }),
                ..
            }) => Self::Relay,
            Some(Command::Completion { .. }) => Self::Completion,
            _ => Self::Ordinary,
        }
    }

    /// Whether this process serves until stopped, and logs what it does.
    fn serves(self) -> bool {
        matches!(self, Self::Daemon | Self::Hub)
    }

    /// Whether the ssh agent here is the user's own. Serving a hub, and `hub connect`, are for
    /// other machines, whose agents aren't this machine's; the daemon itself has the link, or
    /// the service manager's agent. Every shell may print its completion script as it starts,
    /// which says nothing of whose agent to use.
    fn has_users_agent(self) -> bool {
        self == Self::Ordinary
    }
}

fn run(cli: Cli, ui: &Ui) -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(log_filter(&cli, ui)?)
        .with_writer(std::io::stderr)
        // A log file never has colour.
        .with_ansi(ui.color() && std::io::stderr().is_terminal())
        .init();
    let role = Role::of(cli.command.as_ref());
    if role.has_users_agent()
        && let Err(err) = agent::refresh()
    {
        tracing::debug!("not pointing the daemon at this ssh agent: {err:#}");
    }
    if role.serves() {
        open_files::raise();
    }
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
                    at_boot,
                }),
            ..
        } => hub::install(ui, hub::ServeArgs { dir, advertise }, at_boot),
        Command::Hub {
            action: Some(HubAction::Uninstall),
            ..
        } => {
            if login::uninstall(login::Service::Hub)? {
                writeln!(
                    ui.stdout(),
                    "The hub's service is removed, and the hub is stopped."
                )?;
            } else {
                writeln!(ui.stdout(), "The hub had no installed service.")?;
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
        } => block_on(hub::remove(ui, hive, hub)),
        Command::Hub {
            action:
                Some(HubAction::Rename {
                    hive,
                    new_name,
                    hub,
                }),
            ..
        } => block_on(hub::rename(ui, hive, new_name, hub)),
        Command::Create { name, member } => join::join(
            ui,
            &cwd()?,
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
            join::join(ui, &cwd()?, choice, &member, original, &socket()?)
        }
        Command::Clone {
            hive,
            destination,
            hub,
            machine,
            lease,
        } => join::clone(
            ui,
            destination.as_deref(),
            &hive,
            hub.as_deref(),
            machine.as_deref(),
            lease,
            &socket()?,
        ),
        Command::List { template } => {
            list::list(ui, cwd().ok().as_deref(), template.as_deref(), socket())
        }
        Command::Status { template } => {
            let cwd = cwd();
            let report = status::Report::gather(cwd.as_deref(), socket());
            match template {
                // Paths in a template are shown from the current directory, or else from the
                // root, outside which nothing is.
                Some(text) => {
                    let from = cwd.as_deref().unwrap_or_else(|_| Path::new("/"));
                    report.print_template(ui, &text, from)
                }
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
        Command::Leave {
            path: Some(path), ..
        } => leave::leave_path(ui, &path, &socket()?),
        Command::Leave { force, path: None } => leave::leave(ui, &cwd()?, &socket()?, force),
        Command::Forget { machine } => leave::forget(ui, &cwd()?, &machine, &socket()?),
        Command::Daemon { action: None } => daemon::run(&socket()?),
        Command::Daemon {
            action: Some(DaemonAction::Start),
        } => block_on(async {
            daemon::ensure(&socket()?).await?;
            Ok(())
        }),
        Command::Daemon {
            action: Some(DaemonAction::Install),
        } => block_on(daemon::install(ui, &socket()?)),
        Command::Daemon {
            action: Some(DaemonAction::Uninstall),
        } => block_on(daemon::uninstall(ui, &socket()?)),
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
        Command::Sync {
            outgoing,
            approve,
            prune,
            dry_run,
        } => {
            let start = cwd()?;
            let socket = socket()?;
            if outgoing || approve.is_some() || !prune.is_empty() {
                sync::publication(ui, &start, &socket, approve.as_deref(), &prune, dry_run)
            } else {
                sync::sync(ui, &start, &socket)
            }
        }
        Command::Completion { shell } => completion::print_script(ui, shell),
        Command::Debug(Debug::OpId { id }) => debug::op_id(ui, &cwd()?, &id),
    }
}

/// The current directory, for the commands that act on the repository there.
fn cwd() -> anyhow::Result<PathBuf> {
    std::env::current_dir().map_err(|err| match err.kind() {
        std::io::ErrorKind::NotFound => anyhow::anyhow!("the current directory no longer exists"),
        _ => anyhow::anyhow!("can't read the current directory: {err}"),
    })
}

fn block_on<T>(future: impl Future<Output = anyhow::Result<T>>) -> anyhow::Result<T> {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?
        .block_on(future)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::sync::Arc;
    use std::sync::Mutex;

    use super::*;

    /// What a subscriber writes, kept to read back.
    #[derive(Clone, Default)]
    struct Kept(Arc<Mutex<Vec<u8>>>);

    impl std::io::Write for Kept {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.0.lock().unwrap().extend_from_slice(buf);
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn the_hub_and_the_daemon_log_only_warnings_from_jj() {
        // Every crate of jj's in the build, so that one jj adds is quieted too.
        let built: BTreeSet<String> = include_str!("../../../Cargo.lock")
            .lines()
            .filter_map(|line| line.strip_prefix("name = \"jj-")?.strip_suffix('"'))
            .filter(|name| *name != "musubi")
            .map(|name| format!("jj_{}", name.replace('-', "_")))
            .collect();
        let quieted: BTreeSet<String> = JJ_CRATES.iter().map(|&name| name.to_owned()).collect();
        assert_eq!(built, quieted);

        let kept = Kept::default();
        let writer = kept.clone();
        let subscriber = tracing_subscriber::fmt()
            .with_env_filter(parse_filter(&serving_filter()).unwrap())
            .with_writer(move || writer.clone())
            .with_ansi(false)
            .finish();
        tracing::subscriber::with_default(subscriber, || {
            tracing::info!(target: "jj_local_util::lock::unix", "attempting to lock");
            tracing::info!(target: "jj_default_index::store", "scanning operations");
            tracing::warn!(target: "jj_local_util::lock::unix", "a lock went wrong");
            tracing::info!(target: "musubi::daemon", "synced");
        });
        let log = String::from_utf8(kept.0.lock().unwrap().clone()).unwrap();
        assert!(
            !log.contains("attempting") && !log.contains("scanning"),
            "{log}"
        );
        assert!(
            log.contains("a lock went wrong") && log.contains("synced"),
            "{log}"
        );
    }
}
