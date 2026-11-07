//! `musubi`: replicate jj repositories between machines.

mod agent;
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
use std::process::ExitCode;
use std::time::Duration;

use anyhow::Context as _;
use clap::CommandFactory as _;
use clap::Parser as _;
use jj_cli::formatter::FormatterExt as _;
use jj_cli::ui::ColorChoice;
use musubi_hub::hub_dir::JoinChoice;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use crate::cli::Cli;
use crate::cli::Command;
use crate::cli::DaemonAction;
use crate::cli::Debug;
use crate::cli::HubAction;
use crate::cli::HubArgs;
use crate::config::Settings;
use crate::config::UserState;
use crate::socket::Socket;
use crate::ui::Ui;

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
        Command::Create { name, member } => join::join(
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
            join::join(ui, &cwd, choice, &member, original, &socket()?)
        }
        Command::Clone {
            hive,
            destination,
            hub,
            machine,
            lease,
        } => join::clone(
            ui,
            &destination,
            &hive,
            hub.as_deref(),
            machine.as_deref(),
            lease,
            &socket()?,
        ),
        Command::List { template } => list::list(ui, &cwd, template.as_deref(), socket()),
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
        Command::Leave { force, path } => {
            leave::leave(ui, &cwd, &socket()?, force, path.as_deref())
        }
        Command::Forget { machine } => leave::forget(ui, &cwd, &machine, &socket()?),
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
            // otherwise; and start it again if the service manager can't.
            let stopped = daemon::stop(&socket).await?;
            let described = match login::install(login::Service::Daemon, None) {
                Ok(described) => described,
                Err(err) => {
                    if stopped && let Err(again) = daemon::ensure(&socket).await {
                        writeln!(ui.warning(), "Couldn't start the daemon again: {again:#}")?;
                    }
                    return Err(err);
                }
            };
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
            let stopped = daemon::stop(&socket).await?;
            if was {
                writeln!(
                    ui.stdout(),
                    "The daemon no longer starts at login, and is stopped."
                )?;
            } else if stopped {
                writeln!(
                    ui.stdout(),
                    "Stopped the daemon. It wasn't set to start at login."
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
        Command::Sync => sync::sync(ui, &cwd, &socket()?),
        Command::Completion { shell } => completion::print_script(ui, shell),
        Command::Debug(Debug::OpId { id }) => debug::op_id(ui, &cwd, &id),
    }
}

fn block_on<T>(future: impl Future<Output = anyhow::Result<T>>) -> anyhow::Result<T> {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?
        .block_on(future)
}
