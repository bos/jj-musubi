//! `musubi status`: what musubi does with the repository in the current directory, for people,
//! scripts and agents to ask before they act.
//!
//! It gathers a [`Report`] first and prints it after, so that how it prints can change
//! without changing what it finds out. It never starts the daemon, nor asks the hub: the last
//! sync says whether the hub was in reach.

use std::path::Path;
use std::time::Duration;
use std::time::SystemTime;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use musubi_jj::node::NodeRepo;

use crate::config::HiveConfig;
use crate::config::UserState;
use crate::control;
use crate::daemon;
use crate::login;
use crate::repo::Located;
use crate::socket::Socket;

/// What `musubi status` finds out.
pub struct Report {
    /// The jj workspace the directory is in, and its repository, if it is in one.
    pub located: Option<Located>,
    /// The repository's hive, if it is part of one.
    pub hive: Option<Hive>,
    /// The hub a command uses when not given `--hub`.
    pub default_hub: Option<String>,
    pub daemon: Daemon,
}

/// A repository's part in its hive.
pub struct Hive {
    pub config: HiveConfig,
    /// How its syncs go: the daemon's latest word if it serves the repository, else what the
    /// last sync recorded.
    pub sync: Option<daemon::Status>,
    /// Whether the hub has every operation of this machine's, as of the last sync; `None` if
    /// that can't be told, as before the first sync.
    pub sent: Option<bool>,
    /// Whether the hive has forgotten this copy, until it is next used.
    pub forgotten: bool,
    /// Each machine's working copies, this machine's first.
    pub working_copies: Vec<WorkingCopy>,
    /// Each copy in the hive.
    pub copies: Vec<Copy>,
}

/// A working copy, as `jj workspace list` shows one.
pub struct WorkingCopy {
    /// As jj names it here: `laptop/default`.
    pub name: String,
    pub commit: jj_lib::backend::CommitId,
    /// The commit's change id and description, if this repository has it yet.
    pub change: Option<(jj_lib::backend::ChangeId, String)>,
}

/// A copy in the hive.
pub struct Copy {
    /// Its machine's name, as its working copies are named here.
    pub name: String,
    pub this: bool,
    pub last_used: SystemTime,
    /// How long it may go unused before the hive forgets it; `None` for never.
    pub forget_after: Option<Duration>,
}

/// This machine's daemon.
pub struct Daemon {
    pub socket: Result<Socket, String>,
    /// Whether it runs, or why that can't be told, as when it is another release's.
    pub running: Result<bool, String>,
    pub pid: Option<String>,
    /// Whether it serves the repository; `None` outside a hive, or with no daemon to ask.
    pub serving: Option<bool>,
    /// How many repositories it serves.
    pub served: usize,
    pub at_login: bool,
    /// Where it logs: a file, or a description of where the service manager keeps it.
    pub log: String,
}

impl Report {
    /// Finds out about the repository containing `start`.
    pub fn gather(start: &Path, socket: anyhow::Result<Socket>) -> Self {
        let state = UserState::load().unwrap_or_default();
        let default_hub = state.default_hub().ok().flatten();
        let located = Located::find(start).ok();
        let config = located
            .as_ref()
            .and_then(|located| HiveConfig::load(&located.repo_path).ok().flatten());
        let (mut daemon, served) = Daemon::gather(socket);
        let hive = located.as_ref().zip(config).map(|(located, config)| {
            let mine = served.iter().find(|repo| {
                Located::find(&repo.workspace)
                    .is_ok_and(|other| other.repo_path == located.repo_path)
            });
            if daemon.running == Ok(true) {
                daemon.serving = Some(mine.is_some());
            }
            let sync = mine
                .map(|repo| repo.status.clone())
                .or_else(|| daemon::Status::load(&located.repo_path));
            Hive::gather(located, config, sync)
        });
        Self {
            located,
            hive,
            default_hub,
            daemon,
        }
    }

    pub fn print(&self) {
        let Some(located) = &self.located else {
            println!("This directory is not in a jj repository.");
            self.print_machine();
            return;
        };
        let Some(hive) = &self.hive else {
            println!(
                "This repository is not part of a hive: {}",
                located.workspace_root.display()
            );
            self.print_machine();
            hint(
                "`musubi join` makes it part of the hive it belongs in; `musubi create` starts \
                 one.",
            );
            return;
        };
        hive.print(&self.daemon);
        self.daemon.print();
        hive.warn(&self.daemon);
    }

    /// What this machine has, outside any hive.
    fn print_machine(&self) {
        match &self.default_hub {
            Some(hub) => println!("Default hub: {hub}"),
            None => println!("Default hub: none yet"),
        }
        self.daemon.print();
    }
}

impl Hive {
    fn gather(located: &Located, config: HiveConfig, sync: Option<daemon::Status>) -> Self {
        let mut hive = Self {
            config,
            sent: None,
            forgotten: false,
            working_copies: vec![],
            copies: vec![],
            sync,
        };
        // The rest needs the repository, which a sync failing may be failing to open: the
        // sync's error says why.
        if let Ok(mut node) = located.open() {
            hive.sent = sent(&node, hive.sync.as_ref());
            hive.read(&mut node).ok();
        }
        hive
    }

    /// What the repository says of the hive's copies and working copies.
    fn read(&mut self, node: &mut NodeRepo) -> anyhow::Result<()> {
        self.forgotten = !node.present_copies()?.1.is_present(node.machine().key());
        let store = node.loader().store().clone();
        self.working_copies = node
            .machine_workspaces()?
            .into_iter()
            .map(|(name, commit)| {
                let change = store
                    .get_commit(&commit)
                    .ok()
                    .map(|c| (c.change_id().clone(), c.description().to_owned()));
                WorkingCopy {
                    name,
                    commit,
                    change,
                }
            })
            .collect();
        let own = node.machine().key().to_owned();
        self.copies = node
            .activity()?
            .into_iter()
            .map(|copy| Copy {
                this: copy.key == own,
                name: copy.name,
                last_used: copy.last_work,
                forget_after: copy.forget_after,
            })
            .collect();
        // This machine's first, as its working copies are.
        self.copies.sort_by_key(|copy| !copy.this);
        Ok(())
    }

    fn print(&self, daemon: &Daemon) {
        let config = &self.config;
        let at = match self.sync.as_ref().and_then(|sync| sync.known_seq) {
            Some(seq) => format!(", at #{seq}"),
            None => String::new(),
        };
        println!("Hive: {} on {}{at}", config.display_name(), config.hub);
        let synced = match self.sync.as_ref().and_then(|sync| sync.last_success) {
            Some(t) => format!(
                "synced {} ago",
                roughly(Duration::from_secs(daemon::now().saturating_sub(t)))
            ),
            None => "not synced yet".to_owned(),
        };
        let sent = match self.sent {
            Some(true) => "; the hub has all its work",
            // Not while its syncs fail, which the warnings say.
            Some(false) if daemon.serving == Some(true) && !self.failing() => {
                "; the daemon sends its latest work soon"
            }
            Some(false) => "; the hub lacks its latest work",
            None => "",
        };
        println!("This machine: {}, {synced}{sent}", config.node);
        if self.forgotten {
            println!("Forgotten by the hive, which shows this copy again once it's used");
        }
        if !self.working_copies.is_empty() {
            println!("Working copies:");
            for wc in &self.working_copies {
                let commit = &wc.commit.hex()[..8];
                match &wc.change {
                    Some((change, description)) => {
                        let change = &change.reverse_hex()[..8];
                        let description = match description.lines().next() {
                            Some(line) if !line.is_empty() => line,
                            _ => "(no description set)",
                        };
                        println!("{}@: {change} {commit} {description}", wc.name);
                    }
                    None => println!("{}@: {commit}", wc.name),
                }
            }
        }
        if !self.copies.is_empty() {
            println!("Copies:");
            let now = SystemTime::now();
            for copy in &self.copies {
                let this = if copy.this { " (this machine)" } else { "" };
                let since = now.duration_since(copy.last_used).unwrap_or_default();
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
                    "{}{this}: used {} ago, {forgotten}",
                    copy.name,
                    roughly(since)
                );
            }
        }
    }

    /// Whether its last sync failed.
    fn failing(&self) -> bool {
        self.sync.as_ref().is_some_and(|sync| sync.error.is_some())
    }

    /// Says what keeps the repository from syncing, and what to do about it.
    fn warn(&self, daemon: &Daemon) {
        let failing = self.failing();
        if let Some(error) = self.sync.as_ref().and_then(|sync| sync.error.as_ref()) {
            warning(&format!("Syncing fails: {error}"));
            if daemon.serving == Some(true) {
                hint(&format!("The daemon keeps trying. Its log: {}", daemon.log));
            } else {
                hint("`musubi sync` tries again.");
            }
        }
        match (&daemon.running, daemon.serving) {
            // The daemon's line says why.
            (Err(_), _) => {}
            (Ok(false), _) => {
                warning(
                    "The daemon isn't running, so this repository syncs only when you run \
                     `musubi sync`.",
                );
                hint("`musubi daemon start` starts it.");
            }
            (Ok(true), Some(false)) => {
                warning("The daemon doesn't serve this repository.");
                hint("`musubi join`, with the hub in reach, has it serve the repository again.");
            }
            (Ok(true), _) => {}
        }
        // Unless a hint above says to run it already.
        if self.sent == Some(false)
            && daemon.serving != Some(true)
            && !failing
            && daemon.running != Ok(false)
        {
            hint("`musubi sync` sends this machine's latest work to the hub.");
        }
    }
}

impl Daemon {
    /// The daemon, and the repositories it serves.
    fn gather(socket: anyhow::Result<Socket>) -> (Self, Vec<control::RepoStatus>) {
        let at_login = login::installed();
        let log = if login::managed() {
            login::log_hint()
        } else {
            crate::config::daemon_log()
                .map_or_else(|err| format!("{err:#}"), |path| path.display().to_string())
        };
        let socket = socket.map_err(|err| format!("{err:#}"));
        let (running, served) = match &socket {
            Err(err) => (Err(err.clone()), vec![]),
            Ok(socket) => match crate::block_on(statuses(socket)) {
                Ok(Some(served)) => (Ok(true), served),
                Ok(None) => (Ok(false), vec![]),
                Err(err) => (Err(format!("{err:#}")), vec![]),
            },
        };
        let pid = match (&socket, &running) {
            (Ok(socket), Ok(true)) => socket
                .lock_path()
                .ok()
                .and_then(|lock| std::fs::read_to_string(lock.with_extension("pid")).ok())
                .map(|pid| pid.trim().to_owned()),
            _ => None,
        };
        let daemon = Self {
            socket,
            running,
            pid,
            serving: None,
            served: served.len(),
            at_login,
            log,
        };
        (daemon, served)
    }

    fn print(&self) {
        let at_login = if self.at_login {
            "starts at login"
        } else {
            "doesn't start at login"
        };
        let line = match &self.running {
            Ok(true) => {
                let pid = self
                    .pid
                    .as_ref()
                    .map(|pid| format!(" (pid {pid})"))
                    .unwrap_or_default();
                let serving = match self.serving {
                    Some(true) => "serving this repository".to_owned(),
                    Some(false) => "not serving this repository".to_owned(),
                    None if self.served == 1 => "serving 1 repository".to_owned(),
                    None => format!("serving {} repositories", self.served),
                };
                format!("running{pid}, {serving}; {at_login}")
            }
            Ok(false) => format!("not running; {at_login}"),
            Err(err) => format!("{err}; {at_login}"),
        };
        println!("Daemon: {line}");
        if let Ok(socket) = &self.socket {
            println!("Daemon socket: {socket}");
        }
        println!("Daemon log: {}", self.log);
    }
}

/// What the running daemon serves, or `None` if no daemon is running.
async fn statuses(socket: &Socket) -> anyhow::Result<Option<Vec<control::RepoStatus>>> {
    let Some(client) = daemon::running(socket).await? else {
        return Ok(None);
    };
    Ok(Some(
        client
            .status(control::context(Duration::from_secs(10)))
            .await?,
    ))
}

/// Whether the hub has every one of this machine's operations, as of the hub's head at the
/// last sync: whether each op head here is in the hive's history up to it. `None` if it
/// can't be told.
fn sent(node: &NodeRepo, sync: Option<&daemon::Status>) -> Option<bool> {
    let head = sync?.known_head.as_ref()?;
    let head = OperationId::try_from_hex(head)?;
    let store = node.canonical_store();
    if !store.has_operation(&head) {
        return None;
    }
    for local in node.local_heads().ok()? {
        // An operation with no id in the hive yet hasn't been sent.
        let Some(canonical) = node.canonical_of(&local) else {
            return Some(false);
        };
        if !store.is_ancestor_of(&canonical, &head).ok()? {
            return Some(false);
        }
    }
    Some(true)
}

fn warning(message: &str) {
    eprintln!("Warning: {message}");
}

fn hint(message: &str) {
    eprintln!("Hint: {message}");
}

/// A duration in its largest whole unit, as musubi shows how long ago or how soon: `40s`,
/// `12m`, `3h`, `2d`.
pub fn roughly(duration: Duration) -> String {
    let secs = duration.as_secs();
    match secs {
        0..60 => format!("{secs}s"),
        60..3_600 => format!("{}m", secs / 60),
        3_600..86_400 => format!("{}h", secs / 3_600),
        _ => format!("{}d", secs / 86_400),
    }
}
