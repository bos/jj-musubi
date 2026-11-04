//! Command-line arguments, shared by parsing, help, and shell completion.

use std::path::PathBuf;

use clap::Parser;
use clap::Subcommand;
use clap::ValueHint;
use clap_complete::ArgValueCandidates;
use jj_cli::ui::ColorChoice;
use musubi_sync::wire::RELEASE;

use crate::completion;

#[derive(Parser)]
#[command(
    name = "musubi",
    version = RELEASE,
    about = "Replicate jj repositories between machines",
    after_help = "Run `musubi <command> --help` for more on a command. The user guide is at \
                  https://github.com/bos/jj-musubi/blob/main/docs/README.md"
)]
pub struct Cli {
    /// The daemon's control socket, in place of the usual one.
    #[arg(
        long,
        global = true,
        env = "MUSUBI_SOCKET",
        hide_env = true,
        help_heading = "Global options"
    )]
    pub socket: Option<String>,
    /// What to log, as a filter in `RUST_LOG`'s syntax: `debug`, or `info,musubi_sync=debug`.
    /// It applies to this command, not to a daemon it starts, which uses `musubi.daemon.log`
    /// in jj's config.
    #[arg(
        long,
        global = true,
        value_name = "FILTER",
        help_heading = "Global options"
    )]
    pub log: Option<String>,
    /// When to colour what it prints, as jj's `--color` does [default: as jj's `ui.color`
    /// says].
    #[arg(
        long,
        global = true,
        value_name = "WHEN",
        help_heading = "Global options"
    )]
    pub color: Option<ColorChoice>,
    #[command(subcommand)]
    pub command: Option<Command>,
}

#[derive(Subcommand)]
pub enum Command {
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
        /// A new or empty directory for the repository. Missing parent directories are made.
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
    /// reach, requests the hub failed, machines that are offline, behind, or failing to
    /// sync, and this machine's daemon not running, where it has copies to sync.
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
    ///
    /// If a hub reply leaves needed data missing, the sync fails. If the daemon serves
    /// this copy, it retries from the hub's current state. Run `musubi sync` again to retry
    /// at once.
    ///
    /// Trimming earlier history with `jj op abandon` preserves each copy's own Git state.
    /// Other copies remain in the hive or forgotten as they were.
    ///
    /// If jj made the result of an operation abandon ambiguous, syncing stops and gives a
    /// `jj op integrate` command to restore the missing history before trying again.
    Sync,
    /// Run the daemon that keeps this machine's repositories in sync, or control it.
    ///
    /// Without a subcommand, it runs the daemon in the foreground, logging to standard
    /// error. Other commands start it in the background when they need it, logging to
    /// `daemon.log` in musubi's state directory, or under systemd, to the journal.
    ///
    /// After detecting that the machine has woken, it ends old ssh connections and clears
    /// the delay from failed ssh attempts.
    ///
    /// When a hub runs a newer release of musubi, or a newer build deployed from source, the
    /// daemon runs the command `musubi.upgrade-command` names, if set, with `MUSUBI_UPGRADE_TO`
    /// set to it, and once the `musubi` it started from is that, starts again from it.
    /// Keep the installer in the foreground and preserve its standard input, which on
    /// Unix holds the upgrade lock across daemon restarts. While the daemon that launched
    /// it runs, the command may run for up to an hour; a timeout stops its process group on
    /// Unix, or the command process on Windows. A command surviving its daemon has no
    /// timeout monitor.
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
pub struct Member {
    /// This machine's name in the hive, which other machines show its workspaces under, as
    /// in `laptop/default`. Defaults to jj's `operation.hostname`.
    #[arg(long)]
    pub machine: Option<String>,
    /// Replicate the whole operation history, not just the current state.
    #[arg(long)]
    pub full_history: bool,
    /// The hub, as `musubi hub` prints it: the name this machine ssh-es to the hub's machine
    /// by, or on that machine, the hub's directory, or the machine's name or `localhost`, for
    /// the hub `musubi hub` serves there without `--dir`, reached without ssh [default: this
    /// machine's default hub].
    #[arg(long, add = ArgValueCandidates::new(completion::hubs))]
    pub hub: Option<String>,
}

/// Where a hub is, and what it tells other machines, for `hub` and `hub install`.
#[derive(clap::Args)]
pub struct HubArgs {
    /// The hub's directory [default: the current directory if it is a hub's, or else
    /// ~/musubi-hub].
    #[arg(short, long, value_hint = ValueHint::DirPath)]
    pub dir: Option<PathBuf>,
    /// The host name other machines ssh to this one by, for the commands it prints
    /// [default: this machine's host name]. Once given, the hub keeps it (in hub.toml).
    #[arg(long)]
    pub advertise: Option<String>,
}

#[derive(Subcommand)]
pub enum Debug {
    /// Translate an operation id between this machine's id and the hive's.
    OpId {
        /// An operation id, or a prefix of one: this machine's, or the hive's.
        id: String,
    },
}

#[derive(Subcommand)]
pub enum HubAction {
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
pub enum DaemonAction {
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
