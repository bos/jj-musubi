//! Replication setup shared by background workers and foreground `musubi sync`.
//!
//! Driver construction and membership removal have one implementation in both paths; a
//! foreground sync records its result with the same persisted status as a worker.

use std::fs;

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

/// Records inactive `membership` for the repository at `located` and drops its daemon entry,
/// as when the hub says its hive was removed. Returns false, doing nothing, if it isn't part
/// of `hive` through the same hub (any more), as when it left it, joined another, or moved
/// to another hub, meanwhile.
pub fn leave_hive(
    located: &Located,
    hive: &HiveConfig,
    membership: Membership,
) -> anyhow::Result<bool> {
    leave_as(located, hive, |now| {
        Some(HiveConfig {
            state: membership,
            ..now
        })
    })
}

/// Takes the repository at `located` out of `hive`, whose first sync was stopped before it
/// applied any of the hive's history: drops its record and its entry, keeping the machine key
/// the hub took, as a join that stopped once it had kept the key does, so that joining again
/// takes up that key. Returns false, doing nothing, as [`leave_hive`] does.
pub fn unjoin(located: &Located, hive: &HiveConfig) -> anyhow::Result<bool> {
    leave_as(located, hive, |_| None)
}

/// [`leave_hive`], recording the copy's record as `record` makes it of the record now, or
/// dropping it if that makes none.
fn leave_as(
    located: &Located,
    hive: &HiveConfig,
    record: impl FnOnce(HiveConfig) -> Option<HiveConfig>,
) -> anyhow::Result<bool> {
    let _lock = HiveConfig::lock(&located.repo_path)?;
    let Some(now) = HiveConfig::load(&located.repo_path)?
        .filter(|now| now.joined() && now.hive == hive.hive && now.hub == hive.hub)
    else {
        return Ok(false);
    };
    let key = copy::Found::read(&located.repo_path)?.key;
    // The record first: an entry for a record that says it left, or for none, is suspended,
    // where a record that says joined with no entry here would look like a duplicate, if this
    // failed between.
    match record(now) {
        Some(record) => record.save(&located.repo_path)?,
        None => fs::remove_file(HiveConfig::path(&located.repo_path))?,
    }
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
        let (driver, _) = open_driver(located, hive, &connection, None, progress)?;
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
        Err(err) => Err(connection.explain(err).await),
    };
    let synced = known(&driver);
    status.synced(result.as_ref().err(), &synced);
    status.save(&located.repo_path);
    result.map(|_| synced)
}
