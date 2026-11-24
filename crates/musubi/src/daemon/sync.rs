//! Replication setup shared by background workers and foreground `musubi sync`.
//!
//! Driver construction and membership removal have one implementation in both paths; a
//! foreground sync records its result with the same persisted status as a worker.

use std::fs;
use std::sync::Mutex;
use std::sync::PoisonError;

use jj_lib::object_id::ObjectId as _;
use musubi_sync::driver::NodeDriver;
use musubi_sync::progress::Progress;
use musubi_sync::remote::OpenConnection;
use musubi_sync::remote::REQUEST_TIMEOUT;
use musubi_sync::remote::RemoteHub;

use super::connections::CONNECT_TIMEOUT;
use super::status::Status;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::config::UserState;
use crate::control::Synced;
use crate::copy;
use crate::hub::Connection;
use crate::repo::Located;

/// Makes the repository at `located` no longer part of `hive`, keeping everything it has:
/// marks its record `membership`, left as `musubi leave` leaves or removed as the hub said,
/// and stops this machine's daemon serving it. Returns false, doing nothing, if it isn't part
/// of `hive` through the same hub (any more), as when it left it, joined another, or moved
/// to another hub, meanwhile.
pub fn leave_hive(
    located: &Located,
    hive: &HiveConfig,
    membership: Membership,
) -> anyhow::Result<bool> {
    leave_as(located, hive, |now| HiveConfig {
        state: membership,
        ..now
    })
}

/// [`leave_hive`], recording that the hive was reset from another copy, as `reset` says, so
/// that this copy never joins a hive again.
pub fn leave_reset_hive(
    located: &Located,
    hive: &HiveConfig,
    reset: &musubi_hub::hub_dir::Reset,
) -> anyhow::Result<bool> {
    leave_as(located, hive, |now| HiveConfig {
        state: Membership::Reset,
        reset: Some(reset.clone()),
        ..now
    })
}

/// Records, in the copy at `located`, that its hive was reset, as `reset` says, whatever its
/// record said, as after a `musubi leave --force` that couldn't tell the hive, so that it never
/// joins a hive again, and stops this machine's daemon serving it. Does nothing, returning
/// false, if its record names another hive, or none.
pub fn record_reset(located: &Located, reset: &musubi_hub::hub_dir::Reset) -> anyhow::Result<bool> {
    let _lock = HiveConfig::lock(&located.repo_path)?;
    let Some(now) = HiveConfig::load(&located.repo_path)?
        .filter(|now| now.hive.to_string() == reset.hive.as_str())
    else {
        return Ok(false);
    };
    let key = copy::Found::read(&located.repo_path)?.key;
    HiveConfig {
        state: Membership::Reset,
        reset: Some(reset.clone()),
        ..now
    }
    .save(&located.repo_path)?;
    if let Some(key) = key
        && UserState::load()?
            .entry(&key)
            .is_some_and(|entry| entry.hive.to_string() == reset.hive.as_str())
    {
        UserState::remove_entry(&key)?;
    }
    fs::remove_file(Status::path(&located.repo_path)).ok();
    Ok(true)
}

/// [`leave_hive`], recording the copy's record as `record` makes it of the record now.
fn leave_as(
    located: &Located,
    hive: &HiveConfig,
    record: impl FnOnce(HiveConfig) -> HiveConfig,
) -> anyhow::Result<bool> {
    let _lock = HiveConfig::lock(&located.repo_path)?;
    let Some(now) = HiveConfig::load(&located.repo_path)?
        .filter(|now| now.joined() && now.hive == hive.hive && now.hub == hive.hub)
    else {
        return Ok(false);
    };
    let key = copy::Found::read(&located.repo_path)?.key;
    // The record first: an entry for a record that says it left is suspended, where a record
    // that says joined with no entry here would look like a duplicate, if this failed between.
    record(now).save(&located.repo_path)?;
    if let Some(key) = key {
        UserState::remove_entry(&key)?;
    }
    fs::remove_file(Status::path(&located.repo_path)).ok();
    Ok(true)
}

/// Connects to the hive's hub, and opens the repository to sync with it there.
pub(super) fn open_driver(
    located: &Located,
    hive: &HiveConfig,
    connection: &Connection,
    own_connections: Option<OpenConnection>,
    progress: &Progress,
) -> anyhow::Result<(NodeDriver, String)> {
    let blobs = located.repo_path.join("musubi/blobs");
    let mut remote = RemoteHub::new(
        connection.transport.clone(),
        hive.rpc_subject(),
        &blobs,
        REQUEST_TIMEOUT,
    )?
    .with_progress(progress.clone());
    if let Some(open) = own_connections {
        remote = remote.with_own_connections(open);
    }
    let repo = located.open()?;
    let machine = repo.machine().key().to_owned();
    let driver = NodeDriver::new(repo, remote)?;
    Ok((driver, machine))
}

/// The hive's head as `driver` knows it.
pub(super) fn known(driver: &NodeDriver) -> Synced {
    let known = driver.known();
    Synced {
        seq: known.seq,
        head: known.head.hex(),
    }
}

/// Syncs once, in this process, as the daemon would, and records how it went for
/// `musubi status`.
/// `progress` records what it is doing.
pub async fn sync_once(
    located: &Located,
    hive: &HiveConfig,
    progress: &Progress,
) -> anyhow::Result<Synced> {
    let mut status = Status::load(&located.repo_path).unwrap_or_default();
    let opened = async {
        let connection = crate::hub::connect(&hive.hub, CONNECT_TIMEOUT).await?;
        let (mut driver, _) = open_driver(located, hive, &connection, None, progress)?;
        // As the daemon does, for `musubi status` in the meantime: once, at the first answer.
        if status.hive_paused.is_some() {
            let mut lifted = status.clone();
            lifted.pause_lifted();
            let (lifted, repo_path) = (Mutex::new(Some(lifted)), located.repo_path.clone());
            driver.on_answer(move || {
                if let Some(lifted) = lifted.lock().unwrap_or_else(PoisonError::into_inner).take() {
                    lifted.save(&repo_path);
                }
            });
        }
        anyhow::Ok((connection, driver))
    };
    let (connection, mut driver) = match opened.await {
        Ok(opened) => opened,
        Err(err) => {
            status.failed(&err);
            status.save(&located.repo_path);
            return Err(err);
        }
    };
    let result = match driver.sync().await {
        Ok(synced) => Ok(synced),
        Err(err) => Err(crate::reset::mark_own(
            located,
            connection.explain(err).await,
        )),
    };
    let synced = known(&driver);
    status.synced(result.as_ref().err(), &synced);
    status.save(&located.repo_path);
    result.map(|_| synced)
}
