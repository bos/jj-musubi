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
use crate::control;
use crate::copy;
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

pub fn leave(
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
        Err(err) => Err((
            "record what changed in the working copy".to_owned(),
            "if the working copy is stale, `jj workspace update-stale` updates it",
            err,
        )),
        Ok(()) => tell_the_hive(ui, &located, &hive).map_err(|err| {
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
                        let context = control::context(Duration::from_secs(10));
                        client.add(context, entry.key.clone()).await.ok();
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
                    "no machine {machine} shows here in hive {}; `musubi status` names \
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
