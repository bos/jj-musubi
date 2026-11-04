//! Explicit syncs, through the daemon when possible, and their progress reports.

use std::path::Path;
use std::time::Duration;

use anyhow::Context as _;
use musubi_sync::progress::Activity;
use musubi_sync::progress::Progress;
use musubi_sync::remote::HiveGone;

use crate::block_on;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::control;
use crate::control::ControlClient;
use crate::control::Synced;
use crate::daemon;
use crate::repo::Located;
use crate::repo::the_copy;
use crate::socket::Socket;
use crate::ui::Ui;

/// Syncs once, in this process.
pub fn sync_directly(ui: &Ui, located: &Located) -> anyhow::Result<Synced> {
    let hive =
        HiveConfig::load(&located.repo_path)?.context("this repository is not part of a hive")?;
    let progress = Progress::default();
    let sync = daemon::sync_once(located, &hive, &progress);
    block_on(ui.while_waiting(sync, || async { Some(progress.get()) }))
}

/// Syncs through the daemon when it serves the repository, else directly.
pub fn sync(ui: &Ui, start: &Path, socket: &Socket) -> anyhow::Result<()> {
    let (_, stopped) = sync_quietly(ui, start, socket)?;
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
pub fn sync_quietly(ui: &Ui, start: &Path, socket: &Socket) -> anyhow::Result<(Synced, bool)> {
    let (located, hive, entry) = the_copy(ui, start, socket)?;
    let mut stopped = false;
    let through_daemon = block_on(async {
        let Some(client) = daemon::running(socket).await? else {
            stopped = true;
            return Ok(None);
        };
        let sync = client.sync(
            control::context(Duration::from_secs(3600)),
            entry.key.clone(),
        );
        let synced = ui
            .while_waiting(sync, daemon_progress(&client, &entry.key))
            .await?;
        Ok::<_, anyhow::Error>(Some(synced))
    })?;
    let synced = match through_daemon {
        Some(Ok(synced)) => synced,
        Some(Err(message)) => anyhow::bail!("{message}"),
        None => match sync_directly(ui, &located) {
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
/// Asks the daemon what its sync of `key`'s copy is doing, each time it is called.
pub fn daemon_progress(
    client: &ControlClient,
    key: &str,
) -> impl FnMut() -> std::pin::Pin<Box<dyn Future<Output = Option<Activity>>>> {
    let (client, key) = (client.clone(), key.to_owned());
    move || {
        let (client, key) = (client.clone(), key.clone());
        Box::pin(async move {
            let context = control::context(Duration::from_secs(1));
            client.progress(context, key).await.ok().flatten()
        })
    }
}
