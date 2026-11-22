//! `musubi resume`: making a paused hive again from this copy alone, without its history, and
//! what every other copy does once it hears of that (docs/internals/design.md, "Pausing and
//! resetting a hive").

use std::fs;
use std::io::BufRead as _;
use std::io::IsTerminal as _;
use std::io::Write as _;
use std::path::Path;
use std::time::Duration;

use anyhow::Context as _;
use jj_cli::formatter::FormatterExt as _;
use jj_lib::object_id::ObjectId as _;
use musubi_hub::hub_dir::HiveId;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::Reset;
use musubi_jj::node::NodeRepo;
use musubi_sync::remote::HiveReset;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use crate::block_on;
use crate::config::HiveConfig;
use crate::copy;
use crate::daemon;
use crate::hub;
use crate::join;
use crate::leave;
use crate::repo::Located;
use crate::repo::the_copy;
use crate::settings;
use crate::socket::Socket;
use crate::status::roughly;
use crate::ui;
use crate::ui::Ui;

/// Why a copy of hive `reset` reset no longer syncs, as an error and `musubi status` say.
pub fn reset_why(reset: &Reset) -> String {
    let since = Duration::from_secs(daemon::now().saturating_sub(reset.at));
    format!(
        "hive {} was reset (by {}, {} ago) to remove history this copy still has, so it no \
         longer syncs",
        reset.name,
        reset.by,
        roughly(since)
    )
}

/// What to do in a copy of hive `reset` reset, as a hint says, without its full stop.
pub fn rescue(reset: &Reset) -> String {
    format!(
        "Make a new copy with `musubi clone {} <dir>`, bring across any work it lacks, then \
         delete this copy; \"Clean up history on every machine\" in the user guide says how",
        ui::shell_word(&reset.name)
    )
}

/// The error of a copy of hive `reset` reset, with what to do as its hint.
pub fn error(reset: &Reset) -> anyhow::Error {
    ui::with_hint(
        anyhow::anyhow!("{}", reset_why(reset)),
        format!("{}.", rescue(reset)),
    )
}

/// `err`, from asking the hub about the copy at `located`'s hive, or if it says a hive was
/// reset, what [`heard`] makes of that.
pub fn explain(located: &Located, err: anyhow::Error) -> anyhow::Error {
    match HiveReset::of(&err) {
        Some(reset) => heard(located, &reset).unwrap_or_else(|err| err),
        None => err,
    }
}

/// That a `musubi resume` in this copy stopped after the hub reset the hive, and before this
/// copy joined the new one: running it again finishes it.
#[derive(Debug)]
pub struct Unfinished(pub String);

impl std::fmt::Display for Unfinished {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "resetting hive {} from this copy didn't finish", self.0)
    }
}

impl std::error::Error for Unfinished {}

/// What to do about an [`Unfinished`] reset, as a hint says.
pub const UNFINISHED_HINT: &str = "Run `musubi resume` here again to finish it.";

/// Records, in the copy at `located`, that its hive was reset from another copy, whatever it
/// recorded before, and stops this machine's daemon serving it, unless the reset was this
/// copy's own, which a `musubi resume` that stopped partway made. A reset of another hive,
/// whose history the copy carries, it records nothing of. Returns the error to show either way.
pub fn heard(located: &Located, reset: &Reset) -> anyhow::Result<anyhow::Error> {
    if own(located, reset) {
        return Ok(ui::with_hint(
            Unfinished(reset.name.clone()).into(),
            UNFINISHED_HINT,
        ));
    }
    daemon::record_reset(located, reset)?;
    Ok(error(reset))
}

/// `err`, a sync's failure in the copy at `located`, as an [`Unfinished`] reset where it says
/// the hive was reset from this copy, which a `musubi resume` that stopped partway made.
pub fn mark_own(located: &Located, err: anyhow::Error) -> anyhow::Error {
    match HiveReset::of(&err) {
        Some(reset) if own(located, &reset) => Unfinished(reset.name).into(),
        _ => err,
    }
}

/// Whether `err` comes of an [`Unfinished`] reset.
pub fn unfinished(err: &anyhow::Error) -> bool {
    err.chain().any(|cause| cause.is::<Unfinished>())
}

/// Whether `reset` is the copy at `located`'s own.
pub fn own(located: &Located, reset: &Reset) -> bool {
    copy::Found::read(&located.repo_path)
        .ok()
        .and_then(|found| found.key)
        .is_some_and(|key| key == reset.key)
}

/// Makes the paused hive of the copy at `start` again from this copy's current state alone,
/// once the user says so (`yes` says it for them): a new hive, which this copy joins as a
/// repository that never shared its history joins one, and which the old one's other copies
/// can only clone. `force` resets it though it has work this copy hasn't received.
pub fn resume(
    ui: &Ui,
    start: &Path,
    socket: &Socket,
    yes: bool,
    force: bool,
) -> anyhow::Result<()> {
    let (located, hive, entry) = the_copy(ui, start, socket)?;
    located.refuse_slashed_workspaces(false)?;
    let id = HiveId::from(hive.hive);
    let asked = block_on(hub::ask(
        &hive.hub,
        HubWideRequest::Resolve {
            name: id.to_string(),
        },
    ));
    // A hive the hub has under no name, as one reset, is the reset's to explain.
    let others = match asked {
        Ok(HubWideReply::Hive(info)) => {
            if info.paused.is_none() {
                return Err(ui::with_hint(
                    anyhow::anyhow!("hive {} isn't paused", info.name),
                    "Run `musubi pause`, clean up this copy with jj, then run `musubi resume` \
                     again.",
                ));
            }
            let mut others = info.machines;
            others.retain(|machine| *machine != hive.node);
            others
        }
        Ok(other) => anyhow::bail!("unexpected reply from the hub: {other:?}"),
        Err(err) if HiveReset::of(&err).is_some() => {
            return Err(explain(&located, err));
        }
        Err(_) => vec![],
    };
    if !yes {
        confirm(ui, &hive.display_name(), &others)?;
    }
    // So that the daemon doesn't sync it meanwhile.
    let served = leave::stop_serving(&entry.key, socket)?;
    let joined = match reset_here(ui, &located, &hive, force) {
        Ok(joined) => joined,
        Err(err) => {
            if served {
                // As before: the daemon serves it again, which a reset made goes on to say.
                block_on(async {
                    if let Some(client) = daemon::running(socket).await? {
                        let limit = Duration::from_secs(10);
                        client.add(entry.key.clone(), limit).await.ok();
                    }
                    Ok::<_, anyhow::Error>(())
                })
                .ok();
            }
            return Err(explain(&located, err));
        }
    };
    let mut out = ui.stdout();
    write!(out, "Reset hive ")?;
    write!(out.labeled("hive"), "{}", joined.hive.name)?;
    writeln!(out, " from this copy; the hub has none of its old history.")?;
    drop(out);
    // Its first sync sends the new hive this copy's current state.
    join::start_serving(ui, &located, socket)?;
    writeln!(
        ui.hint(),
        "This machine still has the old history; \"Remove data from a machine's disk\" in \
         the user guide says how to remove it."
    )?;
    Ok(())
}

/// Asks the user whether to reset hive `name`, whose other copies are on machines `others`.
fn confirm(ui: &Ui, name: &str, others: &[String]) -> anyhow::Result<()> {
    if !std::io::stdin().is_terminal() {
        return Err(ui::with_hint(
            anyhow::anyhow!("`musubi resume` asks before it resets the hive"),
            "Run it in a terminal, or with `--yes` to reset it without asking.",
        ));
    }
    let others = if others.is_empty() {
        "Every other copy".to_owned()
    } else {
        format!("Every other copy ({})", others.join(", "))
    };
    let mut err = ui.stderr();
    writeln!(
        err,
        "This makes hive {name} this copy's current state, with none of its operation history, \
         and deletes the old history from the hub."
    )?;
    writeln!(
        err,
        "{others} stops syncing for good, to be replaced by a new copy."
    )?;
    write!(err, "Continue? [y/N] ")?;
    err.flush()?;
    drop(err);
    let mut answer = String::new();
    std::io::stdin().lock().read_line(&mut answer)?;
    anyhow::ensure!(
        matches!(answer.trim().to_ascii_lowercase().as_str(), "y" | "yes"),
        "hive {name} is still paused; nothing changed"
    );
    Ok(())
}

/// Has the hub reset hive `hive`, the copy at `located`'s, and makes this copy part of the new
/// hive: forgets the old hive's other machines' workspaces, and what musubi kept of the old
/// hive, then joins the new one as a repository that never shared its history would.
fn reset_here(
    ui: &Ui,
    located: &Located,
    hive: &HiveConfig,
    force: bool,
) -> anyhow::Result<musubi_hub::hub_dir::Joined> {
    let joining = HiveConfig::join_lock(ui, &located.repo_path)?;
    let settings = settings::load(&located.workspace_root, &located.repo_path)?;
    let machine =
        NodeRepo::machine_of(&located.repo_path)?.context("this repository has no machine key")?;
    let node = located.open_as(&settings, machine.clone())?;
    let choice = JoinChoice::Reset {
        id: HiveId::from(hive.hive),
        base: node.accepted_base().0.hex(),
        force,
    };
    let (request, remotes) = join::request(located, &node, choice, &machine)?;
    drop(node);
    let asked = block_on(join::ask_preparing(
        ui,
        &hive.hub,
        HubWideRequest::Join(request),
    ));
    let asked = asked.map_err(|err| {
        if format!("{err:#}").ends_with(musubi_hub::hub_dir::LACKS_WORK) {
            ui::with_hint(
                err,
                "Run `musubi pause --cancel` and `musubi sync` here, then `musubi pause` and \
                 clean up again; or run `musubi resume --force` to leave that work out.",
            )
        } else {
            err
        }
    })?;
    let joined = match asked {
        HubWideReply::Joined(joined) => joined,
        other => anyhow::bail!("unexpected reply from the hub: {other:?}"),
    };
    // A crash from here on leaves the record naming the old hive, whose hub answers the reset
    // again for this copy, as `musubi resume` asks again.
    located.open()?.forget_other_machines()?;
    forget_hive_state(&located.repo_path)?;
    join::become_node(
        located,
        &joined,
        &hive.hub,
        false,
        Some(hive),
        &remotes,
        None,
    )?;
    drop(joining);
    Ok(joined)
}

/// Deletes what musubi kept of the old hive in the repository whose `.jj/repo` directory is
/// `repo_path`: everything in its `musubi` directory but its machine key, its record, which
/// joining replaces, and lock files, which this command and others hold.
fn forget_hive_state(repo_path: &Path) -> anyhow::Result<()> {
    let dir = repo_path.join("musubi");
    for entry in fs::read_dir(&dir).with_context(|| format!("reading {}", dir.display()))? {
        let entry = entry?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name == "machine" || name == "hive.toml" || name.ends_with(".lock") {
            continue;
        }
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            fs::remove_dir_all(&path)
        } else {
            fs::remove_file(&path)
        }
        .with_context(|| format!("deleting {}", path.display()))?;
    }
    Ok(())
}
