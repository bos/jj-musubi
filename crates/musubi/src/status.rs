//! `musubi status`: what musubi does with the repository in the current directory, for people,
//! scripts and agents to ask before they act.
//!
//! It gathers a [`Report`] first and prints it after, so that how it prints can change
//! without changing what it finds out. It never starts the daemon, nor asks the hub: the last
//! sync says whether the hub was in reach.

use std::io;
use std::io::Write as _;
use std::path::Path;
use std::time::Duration;
use std::time::SystemTime;

use jj_cli::formatter::FormatterExt as _;
use jj_cli::generic_templater::GenericTemplateLanguage;
use jj_cli::generic_templater::GenericTemplatePropertyKind;
use jj_cli::templater::BoxedTemplateProperty;
use jj_cli::templater::TemplatePropertyExt as _;
use jj_cli::templater::WrapTemplateProperty;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::settings::UserSettings;
use musubi_jj::node::NodeRepo;

use crate::config::HiveConfig;
use crate::config::UserState;
use crate::control;
use crate::copy;
use crate::daemon;
use crate::login;
use crate::repo::Located;
use crate::socket::Socket;
use crate::ui::Ui;

/// What `musubi status` finds out.
#[derive(Clone)]
pub struct Report {
    /// The jj workspace the directory is in, and its repository, if it is in one.
    pub located: Option<Located>,
    /// The repository's hive, if it is part of one, as the copy musubi syncs.
    pub hive: Option<Hive>,
    /// Why musubi doesn't sync the repository, though its record says it is part of a hive
    /// (it was made from a copy's files, say: docs/internals/copies.md), or why that can't
    /// be told; and what to do.
    pub not_synced: Option<copy::NotTheCopy>,
    /// The hub a command uses when not given `--hub`.
    pub default_hub: Option<String>,
    pub daemon: Daemon,
}

/// A repository's part in its hive.
#[derive(Clone)]
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
#[derive(Clone)]
pub struct WorkingCopy {
    /// As jj names it here: `laptop/default`.
    pub name: String,
    pub commit: jj_lib::backend::CommitId,
    /// The commit's change id and description, if this repository has it yet.
    pub change: Option<(jj_lib::backend::ChangeId, String)>,
}

/// A copy in the hive.
#[derive(Clone)]
pub struct Copy {
    /// Its machine's name, as its working copies are named here.
    pub name: String,
    pub this: bool,
    pub last_used: SystemTime,
    /// How long it may go unused before the hive forgets it; `None` for never.
    pub forget_after: Option<Duration>,
}

/// This machine's daemon.
#[derive(Clone)]
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
        let (mut daemon, served) = Daemon::gather(socket);
        // What the repository is to musubi, before anything opens it, which would give it a
        // key if it had none; and not as another user, as whom jj could write to it.
        let found = located.as_ref().map(|located| {
            copy::check_owner(&located.repo_path)?;
            let found = copy::Found::resolve(located)?;
            let entry = found.key.as_deref().and_then(|key| state.entry(key));
            let standing = copy::standing_of(located, &found, entry);
            Ok::<_, anyhow::Error>((found.clone(), entry.cloned(), standing))
        });
        let mut not_synced = None;
        let mut hive = None;
        if let Some(Err(err)) = &found {
            not_synced = Some(copy::NotTheCopy {
                why: format!("{err:#}"),
                what_to_do: None,
            });
        }
        if let (Some(located), Some(Ok((found, entry, standing)))) = (&located, found) {
            match (standing, found.record, &entry) {
                (copy::Standing::Copy, Some(config), Some(entry)) => {
                    let mine = served.iter().find(|repo| repo.key == entry.key);
                    if daemon.running == Ok(true) {
                        daemon.serving = Some(mine.is_some());
                    }
                    let sync = mine
                        .map(|repo| repo.status.clone())
                        .or_else(|| daemon::Status::load(&located.repo_path));
                    hive = Some(Hive::gather(located, config, sync));
                }
                (copy::Standing::Outside, _, _) => {}
                (standing, record, entry) => {
                    not_synced = Some(copy::not_the_copy(
                        standing,
                        record.as_ref(),
                        entry.as_ref(),
                    ));
                }
            }
        }
        Self {
            located,
            hive,
            not_synced,
            default_hub,
            daemon,
        }
    }

    /// Prints only the report, through `text`, a template in jj's template language, as
    /// `musubi status -T` does.
    pub fn print_template(&self, ui: &Ui, text: &str, cwd: &Path) -> anyhow::Result<()> {
        let template = ui.parse_template(&language(&ui.settings()?, cwd), text)?;
        template.format(self, ui.stdout().as_mut())?;
        Ok(())
    }

    /// How the repository's syncs go, if it is part of a hive.
    fn sync(&self) -> Option<&daemon::Status> {
        self.hive.as_ref()?.sync.as_ref()
    }

    /// The report, for `json(self)`, in the user guide's words.
    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            // Lossily, as a path that isn't UTF-8 has no JSON string.
            "repository": self
                .located
                .as_ref()
                .map(|located| located.workspace_root.to_string_lossy()),
            "hive": self.hive.as_ref().map(Hive::to_json),
            "not_synced": self.not_synced.as_ref().map(|not| &not.why),
            "default_hub": self.default_hub,
            "daemon": self.daemon.to_json(),
        })
    }

    pub fn print(&self, ui: &Ui) -> io::Result<()> {
        let Some(located) = &self.located else {
            writeln!(ui.stdout(), "This directory is not in a jj repository.")?;
            return self.print_machine(ui);
        };
        if let Some(not) = &self.not_synced {
            // As a sentence of its own.
            let mut why = not.why.clone();
            if let Some(first) = why.get_mut(..1) {
                first.make_ascii_uppercase();
            }
            writeln!(ui.stdout().labeled("problem"), "{why}.")?;
            self.print_machine(ui)?;
            if let Some(advice) = &not.what_to_do {
                writeln!(ui.hint(), "{advice}.")?;
            }
            return Ok(());
        }
        let Some(hive) = &self.hive else {
            writeln!(
                ui.stdout(),
                "This repository is not part of a hive: {}",
                located.workspace_root.display()
            )?;
            self.print_machine(ui)?;
            return writeln!(
                ui.hint(),
                "`musubi join` makes it part of the hive it belongs in; `musubi create` starts \
                 one."
            );
        };
        hive.print(ui, &self.daemon)?;
        self.daemon.print(ui)?;
        hive.warn(ui, &self.daemon)
    }

    /// What this machine has, outside any hive.
    fn print_machine(&self, ui: &Ui) -> io::Result<()> {
        match &self.default_hub {
            Some(hub) => writeln!(ui.stdout(), "Default hub: {hub}")?,
            None => writeln!(ui.stdout(), "Default hub: none yet")?,
        }
        self.daemon.print(ui)
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

    fn print(&self, ui: &Ui, daemon: &Daemon) -> io::Result<()> {
        let mut out = ui.stdout();
        let config = &self.config;
        let at = match self.sync.as_ref().and_then(|sync| sync.known_seq) {
            Some(seq) => format!(", at #{seq}"),
            None => String::new(),
        };
        write!(out, "Hive: ")?;
        write!(out.labeled("hive"), "{}", config.display_name())?;
        writeln!(out, " on {}{at}", config.hub)?;
        let synced = self.synced();
        let sent = match self.sent {
            Some(true) => "; the hub has all its work",
            // Not while its syncs fail, which the warnings say.
            Some(false) if daemon.serving == Some(true) && !self.failing() => {
                "; the daemon sends its latest work soon"
            }
            Some(false) => "; the hub lacks its latest work",
            None => "",
        };
        write!(out, "This machine: ")?;
        write!(out.labeled("machine"), "{}", config.node)?;
        writeln!(out, ", {synced}{sent}")?;
        if self.forgotten {
            writeln!(
                out.labeled("problem"),
                "Forgotten by the hive, which shows this copy again once it's used"
            )?;
        }
        if !self.working_copies.is_empty() {
            writeln!(out, "Working copies:")?;
            for wc in &self.working_copies {
                write!(out.labeled("working_copies"), "{}@", wc.name)?;
                write!(out, ": ")?;
                let commit = &wc.commit.hex()[..8];
                match &wc.change {
                    Some((change, description)) => {
                        write!(out.labeled("change_id"), "{}", &change.reverse_hex()[..8])?;
                        write!(out, " ")?;
                        write!(out.labeled("commit_id"), "{commit}")?;
                        match description.lines().next() {
                            Some(line) if !line.is_empty() => writeln!(out, " {line}")?,
                            _ => {
                                write!(out, " ")?;
                                writeln!(
                                    out.labeled("description").labeled("placeholder"),
                                    "(no description set)"
                                )?;
                            }
                        }
                    }
                    None => writeln!(out.labeled("commit_id"), "{commit}")?,
                }
            }
        }
        if !self.copies.is_empty() {
            writeln!(out, "Copies:")?;
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
                write!(out.labeled("machine"), "{}", copy.name)?;
                writeln!(out, "{this}: used {} ago, {forgotten}", roughly(since))?;
            }
        }
        Ok(())
    }

    /// When the repository last synced.
    fn synced(&self) -> String {
        match self.sync.as_ref().and_then(|sync| sync.last_success) {
            Some(t) => format!(
                "synced {} ago",
                roughly(Duration::from_secs(daemon::now().saturating_sub(t)))
            ),
            None => "not synced yet".to_owned(),
        }
    }

    fn to_json(&self) -> serde_json::Value {
        let sync = self.sync.as_ref();
        let working_copies: Vec<serde_json::Value> = self
            .working_copies
            .iter()
            .map(|wc| {
                serde_json::json!({
                    "name": wc.name,
                    "commit": wc.commit.hex(),
                    "change": wc.change.as_ref().map(|(change, _)| change.reverse_hex()),
                    "description": wc.change.as_ref().map(|(_, description)| description),
                })
            })
            .collect();
        let copies: Vec<serde_json::Value> = self
            .copies
            .iter()
            .map(|copy| {
                serde_json::json!({
                    "machine": copy.name,
                    "this": copy.this,
                    "last_used": copy
                        .last_used
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .map_or(0, |since| since.as_secs()),
                    "forget_after": copy.forget_after.map(|after| after.as_secs()),
                })
            })
            .collect();
        serde_json::json!({
            "name": self.config.display_name(),
            "id": self.config.hive.to_string(),
            "hub": self.config.hub,
            "machine": self.config.node,
            "head": sync.and_then(|sync| sync.known_seq),
            "last_sync": sync.and_then(|sync| sync.last_success),
            "error": sync.and_then(|sync| sync.error.as_ref()),
            "sent": self.sent,
            "forgotten": self.forgotten,
            "working_copies": working_copies,
            "copies": copies,
        })
    }

    /// Whether its last sync failed.
    fn failing(&self) -> bool {
        self.sync.as_ref().is_some_and(|sync| sync.error.is_some())
    }

    /// Says what keeps the repository from syncing, and what to do about it.
    fn warn(&self, ui: &Ui, daemon: &Daemon) -> io::Result<()> {
        let failing = self.failing();
        if let Some(error) = self.sync.as_ref().and_then(|sync| sync.error.as_ref()) {
            writeln!(ui.warning(), "Syncing fails: {error}")?;
            if self.sync.as_ref().is_some_and(|sync| sync.paused) {
                writeln!(
                    ui.hint(),
                    "Retrying won't get past this; the warning says what will."
                )?;
            } else if daemon.serving == Some(true) {
                writeln!(
                    ui.hint(),
                    "The daemon keeps trying. Its log: {}",
                    daemon.log
                )?;
            } else {
                writeln!(ui.hint(), "`musubi sync` tries again.")?;
            }
        }
        match (&daemon.running, daemon.serving) {
            // The daemon's line says why.
            (Err(_), _) => {}
            (Ok(false), _) => {
                writeln!(
                    ui.warning(),
                    "The daemon isn't running, so this repository syncs only when you run \
                     `musubi sync`."
                )?;
                writeln!(ui.hint(), "`musubi daemon start` starts it.")?;
            }
            (Ok(true), Some(false)) => {
                writeln!(ui.warning(), "The daemon doesn't serve this repository.")?;
                writeln!(
                    ui.hint(),
                    "`musubi join`, with the hub in reach, has it serve the repository again."
                )?;
            }
            (Ok(true), _) => {}
        }
        // Unless a hint above says to run it already.
        if self.sent == Some(false)
            && daemon.serving != Some(true)
            && !failing
            && daemon.running != Ok(false)
        {
            writeln!(
                ui.hint(),
                "`musubi sync` sends this machine's latest work to the hub."
            )?;
        }
        Ok(())
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

    fn print(&self, ui: &Ui) -> io::Result<()> {
        let at_login = if self.at_login {
            "starts at login"
        } else {
            "doesn't start at login"
        };
        let mut out = ui.stdout();
        write!(out, "Daemon: ")?;
        match &self.running {
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
                writeln!(out, "running{pid}, {serving}; {at_login}")?;
            }
            Ok(false) => {
                write!(out.labeled("problem"), "not running")?;
                writeln!(out, "; {at_login}")?;
            }
            Err(err) => {
                write!(out.labeled("problem"), "{err}")?;
                writeln!(out, "; {at_login}")?;
            }
        }
        if let Ok(socket) = &self.socket {
            writeln!(out, "Daemon socket: {socket}")?;
        }
        writeln!(out, "Daemon log: {}", self.log)
    }

    fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "running": self.running.as_ref().ok(),
            "error": self.running.as_ref().err(),
            "pid": self.pid,
            "serving": self.serving,
            "served": self.served,
            "at_login": self.at_login,
            "socket": self.socket.as_ref().ok().map(ToString::to_string),
            "log": self.log,
        })
    }
}

/// What `json(self)` gives: the report in the user guide's words.
impl serde::Serialize for Report {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.to_json().serialize(serializer)
    }
}

type Language = GenericTemplateLanguage<'static, Report>;

impl<'a> WrapTemplateProperty<'a, Report> for GenericTemplatePropertyKind<'a, Report> {
    fn wrap_property(property: BoxedTemplateProperty<'a, Report>) -> Self {
        Self::Self_(property)
    }
}

/// The keywords of a report, as `musubi status --help` gives them.
fn language(settings: &UserSettings, cwd: &Path) -> Language {
    let mut language = Language::new(settings, cwd);
    keyword(&mut language, "repository", |report| {
        report
            .located
            .as_ref()
            .map(|located| located.workspace_root.clone())
    });
    keyword(&mut language, "hive", |report| {
        report
            .hive
            .as_ref()
            .map(|hive| hive.config.display_name())
            .unwrap_or_default()
    });
    keyword(&mut language, "id", |report| {
        report
            .hive
            .as_ref()
            .map(|hive| hive.config.hive.to_string())
            .unwrap_or_default()
    });
    keyword(&mut language, "hub", |report| {
        report
            .hive
            .as_ref()
            .map(|hive| hive.config.hub.clone())
            .unwrap_or_default()
    });
    keyword(&mut language, "machine", |report| {
        report
            .hive
            .as_ref()
            .map(|hive| hive.config.node.clone())
            .unwrap_or_default()
    });
    keyword(&mut language, "default_hub", |report| {
        report.default_hub.clone().unwrap_or_default()
    });
    keyword(&mut language, "head", |report| {
        report
            .sync()
            .and_then(|sync| sync.known_seq)
            .map(|seq| i64::try_from(seq).unwrap_or(i64::MAX))
    });
    keyword(&mut language, "status", |report| {
        report.hive.as_ref().map(Hive::synced).unwrap_or_default()
    });
    keyword(&mut language, "problem", |report| {
        report
            .not_synced
            .as_ref()
            .map(|not| not.why.clone())
            .or_else(|| report.sync().and_then(|sync| sync.error.clone()))
            .unwrap_or_default()
    });
    keyword(&mut language, "sent", |report| {
        report.hive.as_ref().and_then(|hive| hive.sent) == Some(true)
    });
    keyword(&mut language, "forgotten", |report| {
        report.hive.as_ref().is_some_and(|hive| hive.forgotten)
    });
    keyword(&mut language, "daemon_running", |report| {
        report.daemon.running == Ok(true)
    });
    keyword(&mut language, "serving", |report| {
        report.daemon.serving == Some(true)
    });
    language
}

/// Adds keyword `name`, whose value is `value` of the report.
fn keyword<O: 'static>(language: &mut Language, name: &'static str, value: fn(&Report) -> O)
where
    GenericTemplatePropertyKind<'static, Report>: WrapTemplateProperty<'static, O>,
{
    language.add_keyword(name, move |report| {
        Ok(report.map(move |report| value(&report)).into_dyn_wrapped())
    });
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
