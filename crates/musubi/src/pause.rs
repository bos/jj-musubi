//! `musubi pause`: stopping a whole hive syncing, and starting it again.

use std::io::Write as _;
use std::path::Path;

use jj_cli::formatter::FormatterExt as _;
use musubi_hub::hub_dir::HiveId;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;

use crate::block_on;
use crate::hub;
use crate::repo::the_copy;
use crate::socket::Socket;
use crate::status::paused_by;
use crate::sync::sync_quietly;
use crate::ui::Ui;

/// Pauses the hive of the copy at `start`, or with `cancel`, lifts its pause. Asks the hub
/// without syncing first, which a copy that lost history couldn't, then syncs this copy, so
/// that `musubi status` here says at once how the hive is.
pub fn pause(ui: &Ui, start: &Path, socket: &Socket, cancel: bool) -> anyhow::Result<()> {
    let (located, hive, _) = the_copy(ui, start, socket)?;
    let id = HiveId::from(hive.hive);
    let request = if cancel {
        HubWideRequest::Unpause { hive: id }
    } else {
        HubWideRequest::Pause {
            hive: id,
            machine: hive.node.clone(),
        }
    };
    let reply = block_on(hub::ask(&hive.hub, request))
        .map_err(|err| crate::reset::explain(&located, err))?;
    let HubWideReply::PauseChanged { hive: info, before } = reply else {
        anyhow::bail!("unexpected reply from the hub: {reply:?}");
    };
    let (lead, tail) = match (cancel, &before) {
        (false, None) => (
            "Paused hive ",
            ": nothing syncs with it until `musubi resume` or `musubi pause --cancel`.".to_owned(),
        ),
        (false, Some(pause)) => (
            "Hive ",
            format!(" was paused already {}.", paused_by(pause)),
        ),
        (true, Some(_)) => ("Hive ", " syncs again.".to_owned()),
        (true, None) => ("Hive ", " isn't paused.".to_owned()),
    };
    let mut out = ui.stdout();
    write!(out, "{lead}")?;
    write!(out.labeled("hive"), "{}", info.name)?;
    writeln!(out, "{tail}")?;
    drop(out);
    // Paused, the hub answers this sync's first request that the hive is paused, before it
    // changes anything here. Unpaused, it's a sync like any other.
    if let Err(err) = sync_quietly(ui, start, socket)
        && cancel
    {
        ui.warn_with_hints("Syncing fails: ", &err)?;
    }
    Ok(())
}
