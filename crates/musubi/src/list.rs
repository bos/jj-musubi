//! Gathering and printing this machine's hubs, hives, and copies.

mod template;

use std::collections::BTreeMap;
use std::io::Write as _;
use std::path::Path;
use std::time::Duration;

use jj_cli::formatter::FormatterExt as _;
use musubi_hub::hub_dir::HiveInfo;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use self::template::Line;
use self::template::Lister;
use crate::block_on;
use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::UserState;
use crate::control;
use crate::copy;
use crate::daemon;
use crate::daemon::Status;
use crate::hub;
use crate::login;
use crate::repo::Located;
use crate::repo::follow_move;
use crate::socket::Socket;
use crate::ui::Ui;

/// A repository on this machine that is part of a hive.
struct Copy {
    located: Located,
    hive: HiveConfig,
    status: Option<Status>,
}

/// Lists what it can: a daemon or hub out of reach is a line of the listing.
pub fn list(
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
            "running, serving {}; {at_login}",
            repositories(statuses.len())
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
pub fn no_hubs(ui: &Ui) -> std::io::Result<()> {
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
pub fn machines(info: &HiveInfo) -> String {
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

pub async fn list_hub(hub: &str) -> anyhow::Result<Vec<HiveInfo>> {
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

/// `n` repositories, in words.
fn repositories(n: usize) -> String {
    if n == 1 {
        "1 repository".to_owned()
    } else {
        format!("{n} repositories")
    }
}
