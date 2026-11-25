//! Leaving a hive and forgetting copies, while preserving their working copies.

use std::collections::BTreeMap;
use std::io::Write as _;
use std::path::Path;
use std::process::Command as Process;
use std::time::Duration;

use anyhow::Context as _;
use jj_cli::formatter::FormatterExt as _;
use musubi_jj::node::NodeRepo;
use musubi_sync::progress::Progress;
use musubi_sync::remote::HiveGone;

use crate::block_on;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::config::UserState;
use crate::copy;
#[cfg(test)]
use crate::copy::conformance::detach::{Write, after};
use crate::daemon;
use crate::repo::Located;
use crate::repo::the_copy;
use crate::socket::Socket;
use crate::sync::sync;
use crate::sync::sync_quietly;
use crate::ui;
use crate::ui::Ui;

/// Stops the daemon serving the copy whose entry is at `path`, which may be gone: the hive
/// isn't told, since only the copy can tell it.
pub fn leave_path(ui: &Ui, path: &Path, socket: &Socket) -> anyhow::Result<()> {
    // As entries are: canonical, though the copy is gone, by the directory that held it.
    let path = std::path::absolute(path)?;
    let path = match (path.parent().map(dunce::canonicalize), path.file_name()) {
        (Some(Ok(parent)), Some(name)) => parent.join(name),
        _ => path,
    };
    // The plain form of the whole path, as entries are saved: it may be short enough for it
    // where the canonical parent, just checked, isn't, or the other way about.
    let path = crate::config::plain(&path);
    let state = UserState::load()?;
    let entry = state
        .copies
        .iter()
        .find(|entry| entry.path == path)
        .with_context(|| format!("this machine syncs no copy at {}", path.display()))?;
    // Moved, as jj saw, though nothing followed it yet.
    if let Some(at) = copy::whereabouts(entry) {
        anyhow::bail!(
            "the copy is at {}; `musubi leave` there takes it out of its hive",
            at.display()
        );
    }
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
            .remove(key.to_owned(), Duration::from_secs(120))
            .await?
            .map_err(anyhow::Error::msg)?;
        Ok::<_, anyhow::Error>(true)
    })
}

pub fn leave(ui: &Ui, start: &Path, socket: &Socket, force: bool) -> anyhow::Result<()> {
    let located = Located::find(start)?;
    copy::check_owner(&located.repo_path)?;
    let _membership = HiveConfig::join_lock(ui, &located.repo_path)?;
    if leave_inactive(ui, &located)? || retire_kept_key(ui, &located)? {
        return Ok(());
    }
    let (located, hive, entry) = the_copy(ui, start, socket)?;
    // Telling the hive that this copy leaves takes a sync, which a workspace name with a `/`
    // stops, before anything changes: renaming the workspace is quick, and leaves with the
    // copy's last work, which `--force` leaves out.
    let slashed = match located.refuse_slashed_workspaces(true) {
        Err(err) if !force => return Err(err),
        slashed => slashed,
    };
    // So that the daemon doesn't sync it meanwhile.
    let served = stop_serving(&entry.key, socket)?;
    let name = hive.display_name();
    let told = match slashed.map(|()| snapshot(&located)) {
        Err(err) => Err((
            format!("tell hive {name} that this repository leaves"),
            "`musubi leave --force` leaves without telling the hive",
            err,
        )),
        Ok(Err(err)) => Err((
            "record what changed in the working copy".to_owned(),
            "if the working copy is stale, `jj workspace update-stale` updates it",
            err,
        )),
        Ok(Ok(())) => tell_the_hive(ui, &located, &hive).map_err(|err| {
            (
                format!("tell hive {name} that this repository leaves"),
                "`musubi leave --force` leaves without telling the hive",
                err,
            )
        }),
    };
    if let Err((doing, hint, err)) = told {
        if !force {
            if served {
                // As before: the daemon serves it again.
                block_on(async {
                    if let Some(client) = daemon::running(socket).await? {
                        let limit = Duration::from_secs(10);
                        client.add(entry.key.clone(), limit).await.ok();
                    }
                    Ok::<_, anyhow::Error>(())
                })
                .ok();
            }
            return Err(ui::with_hint(
                anyhow::anyhow!("couldn't {doing}: {err:#}"),
                hint,
            ));
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
    detach(&located, Some(&hive))?;
    left(ui, &name)
}

/// Completes a leave that stopped partway through, or detaches from a hive the hub removed.
fn leave_inactive(ui: &Ui, located: &Located) -> anyhow::Result<bool> {
    let found = copy::Found::resolve(located)?;
    if matches!(copy::standing(&found, None), copy::Standing::Duplicate) {
        return Ok(false);
    }
    let Some(record) = found.record.filter(|record| !record.joined()) else {
        return Ok(false);
    };
    let name = record.display_name();
    finish_detaching(located)?;
    left(ui, &name)?;
    Ok(true)
}

/// Retires the machine key of a repository that is part of no hive but kept the key a hub
/// took, as a join whose first sync was stopped leaves it, so that `musubi join --machine` can
/// name a new one. Returns whether it was one.
fn retire_kept_key(ui: &Ui, located: &Located) -> anyhow::Result<bool> {
    let _lock = HiveConfig::lock(&located.repo_path)?;
    if HiveConfig::load(&located.repo_path)?.is_some() {
        return Ok(false);
    }
    let Some(machine) = NodeRepo::machine_of(&located.repo_path)? else {
        return Ok(false);
    };
    // Not one whose key this machine syncs a copy of, as another repository made from this
    // one's files that joined since.
    if UserState::load()?.entry(machine.key()).is_some() {
        return Ok(false);
    }
    retire_machine(located)?;
    writeln!(
        ui.stdout(),
        "This repository isn't part of a hive; it no longer has a machine name (it was {}).",
        machine.name()
    )?;
    Ok(true)
}

/// Clears inactive membership. The join lock holds across this and the caller's membership
/// checks. If interrupted, the record stays until the key and daemon entry are gone.
pub(crate) fn finish_detaching(located: &Located) -> anyhow::Result<()> {
    detach(located, None)
}

/// Commits a leave locally once the caller has stopped the worker and completed the final
/// sync, or finishes clearing an already inactive membership.
pub(crate) fn detach(located: &Located, leaving: Option<&HiveConfig>) -> anyhow::Result<()> {
    let path = &located.repo_path;
    let _lock = HiveConfig::lock(path)?;
    let Some(record) = HiveConfig::load(path)? else {
        return Ok(());
    };
    if let Some(expected) = leaving {
        anyhow::ensure!(
            record.hive == expected.hive && record.hub == expected.hub,
            "this repository's hive changed during leave"
        );
    }
    if record.joined() {
        anyhow::ensure!(leaving.is_some(), "this repository is still part of a hive");
        HiveConfig {
            state: Membership::Left,
            ..record
        }
        .save(path)?;
        #[cfg(test)]
        after(Write::MarkLeft);
    }
    retire_machine(located)?;
    std::fs::remove_file(daemon::Status::path(path)).ok();
    std::fs::remove_file(HiveConfig::path(path))?;
    #[cfg(test)]
    after(Write::ClearRecord);
    Ok(())
}

/// Retires the repository's machine key, if it has one, and drops its entry, in the order
/// [`detach`] needs: the key recorded retired before it is cleared.
pub(crate) fn retire_machine(located: &Located) -> anyhow::Result<()> {
    let path = &located.repo_path;
    if let Some(machine) = NodeRepo::machine_of(path)? {
        if let Some(retirement) = located.open()?.begin_retiring_machine()? {
            #[cfg(test)]
            after(Write::MarkHistory);
            retirement.record()?;
            #[cfg(test)]
            after(Write::RetireKey);
        }
        UserState::remove_entry(machine.key())?;
        #[cfg(test)]
        after(Write::DropEntry);
        NodeRepo::clear_machine(path)?;
        #[cfg(test)]
        after(Write::ClearKey);
    }
    Ok(())
}

fn left(ui: &Ui, name: &str) -> anyhow::Result<()> {
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
    match block_on(daemon::sync_once(located, hive, &Progress::default())) {
        Ok(_) => {}
        // Nothing to tell a hive that is over.
        Err(err) if HiveGone::of(&err) == Some(HiveGone::Removed) => return Ok(true),
        Err(err) => return Err(err),
    }
    let mut node = located.open()?;
    Ok(!node.present_copies()?.1.is_present(node.machine().key()))
}

pub fn forget(ui: &Ui, start: &Path, machine: &str, socket: &Socket) -> anyhow::Result<()> {
    let (located, hive, _) = the_copy(ui, start, socket)?;
    let mut node = located.open()?;
    let this_machine = || {
        anyhow::anyhow!(
            "{machine} is this machine; `musubi leave` takes this repository out of hive {}",
            hive.display_name()
        )
    };
    // By its key or the name `musubi status` gives it, as `laptop-1a2b` while another copy is
    // `laptop` too, whichever other machine a name like that could mean.
    let own = node.machine().key().to_owned();
    if machine == own || shown_name(&mut node, &own)?.as_deref() == Some(machine) {
        return Err(this_machine());
    }
    // One this machine hasn't heard of yet may have joined since it last synced.
    let key = match node.machine_named(machine)? {
        Some(key) => key,
        // Any other name it could be shown under, where no other machine could have it.
        None if musubi_jj::workspaces::could_be_shown_as(&own, machine) => {
            return Err(this_machine());
        }
        None => {
            drop(node);
            sync_quietly(ui, start, socket)?;
            node = located.open()?;
            node.machine_named(machine)?.with_context(|| {
                format!(
                    "no machine {machine} shows here in hive {}; `musubi status` names \
                     those that do",
                    hive.display_name()
                )
            })?
        }
    };
    // By the name it is shown under, which says which copy a plain name meant.
    let shown = shown_name(&mut node, &key)?.unwrap_or_else(|| machine.to_owned());
    if node.forget_copy(&key, &shown)? {
        let mut out = ui.stdout();
        write!(out, "Forgot ")?;
        write!(out.labeled("machine"), "{shown}")?;
        writeln!(out)?;
    }
    drop(node);
    sync(ui, start, socket)
}

/// The name `musubi status` gives the copy whose machine key is `key`, if it is present.
fn shown_name(node: &mut NodeRepo, key: &str) -> anyhow::Result<Option<String>> {
    Ok(node
        .activity()?
        .into_iter()
        .find(|copy| copy.key == key)
        .map(|copy| copy.name))
}
