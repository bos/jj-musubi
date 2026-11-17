//! A copy's worker: its command channel, status, progress and dedicated sync thread.
//!
//! The server owns only a `Worker` handle. This module owns stopping and joining the thread,
//! locating its copy, retrying failed sessions, and reacting to repository and hub changes.

#[cfg(unix)]
use std::fs;
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::SystemTime;

use anyhow::Context as _;
use bytes::Bytes;
use musubi_hub::activity::Report;
use musubi_sync::progress::Activity;
use musubi_sync::progress::Progress;
use musubi_sync::remote::HiveGone;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HUB_TOKEN;
use musubi_sync::wire::HeadNotice;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use musubi_sync::wire::RELEASE;
use musubi_sync::wire::release_of;
use musubi_sync::wire::rpc_subject;
use tokio::sync::mpsc;
use tokio::sync::oneshot;
use tokio::sync::watch;

use super::Suspended;
use super::connections::Hubs;
use super::status::SharedStatus;
use super::status::Status;
use super::status::now;
use super::status::publication_held;
use super::sync::known;
use super::sync::leave_hive;
use super::sync::open_driver;
use crate::config::Entry;
use crate::config::HiveConfig;
use crate::config::Membership;
use crate::config::UserState;
use crate::control::Synced;
use crate::copy;
use crate::hub::Connection;
use crate::repo::Located;
use crate::watch::Watcher;

const POLL_INTERVAL: Duration = Duration::from_secs(30);
const MAX_BACKOFF: Duration = Duration::from_secs(60);
const REPORT_TIMEOUT: Duration = Duration::from_secs(10);
/// How often a repository that syncs is checked for whether gc is due.
const GC_CHECK_INTERVAL: Duration = Duration::from_secs(60 * 60);

pub(super) enum Command {
    /// Sync now, and say how it went.
    Sync(oneshot::Sender<Result<Synced, String>>),
}

/// The server's handle to one copy. Its channel, state and thread stay together until stopped.
pub(super) struct Worker {
    commands: mpsc::UnboundedSender<Command>,
    /// Stopping abandons any sync in progress, as a crash the protocol recovers from.
    stop: watch::Sender<bool>,
    status: SharedStatus,
    progress: Progress,
    thread: std::thread::JoinHandle<()>,
}

impl Worker {
    pub(super) fn start(key: String, hubs: Arc<Hubs>) -> Self {
        let (commands, receiver) = mpsc::unbounded_channel();
        let (stop, stopped) = watch::channel(false);
        let initial = UserState::load()
            .ok()
            .and_then(|state| state.entry(&key).cloned())
            .filter(|entry| copy::holds(entry, &entry.path))
            .and_then(|entry| Located::find(&entry.path).ok())
            .and_then(|located| Status::load(&located.repo_path))
            .unwrap_or_default();
        let status = SharedStatus::new(initial);
        let progress = Progress::default();
        let thread = {
            let status = status.clone();
            let progress = progress.clone();
            std::thread::Builder::new()
                .name(format!("serve {key}"))
                .spawn(move || serve(&key, receiver, stopped, &status, &progress, &hubs))
                .expect("spawning a thread")
        };
        Self {
            commands,
            stop,
            status,
            progress,
            thread,
        }
    }

    pub(super) fn is_finished(&self) -> bool {
        self.thread.is_finished()
    }

    /// Enqueues the request while the registry is locked; waiting for it needs no registry lock.
    pub(super) fn request_sync(&self) -> Result<oneshot::Receiver<Result<Synced, String>>, String> {
        let (reply, result) = oneshot::channel();
        self.commands
            .send(Command::Sync(reply))
            .map_err(|_| "the daemon stopped serving this repository".to_owned())?;
        Ok(result)
    }

    pub(super) async fn stop(self) {
        self.stop.send(true).ok();
        tokio::task::spawn_blocking(move || self.thread.join().ok())
            .await
            .ok();
    }

    pub(super) fn progress(&self) -> Activity {
        self.progress.get()
    }

    pub(super) fn status(&self) -> Status {
        self.status.snapshot()
    }
}

/// Serves one copy until told to stop: a single-threaded runtime, since jj-lib's
/// repository handles are used from one thread.
fn serve(
    key: &str,
    commands: mpsc::UnboundedReceiver<Command>,
    stop: watch::Receiver<bool>,
    status: &SharedStatus,
    progress: &Progress,
    hubs: &Hubs,
) {
    // Everything this thread logs is about this copy. At error level, the span stays on
    // under any filter that shows anything.
    let _span = tracing::error_span!("sync", copy = %key).entered();
    let runtime = match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime,
        Err(err) => {
            tracing::error!("{err}");
            return;
        }
    };
    runtime.block_on(async {
        let mut stop = stop;
        tokio::select! {
            () = serve_retrying(key, commands, status, progress, hubs) => {}
            () = stopped(&mut stop) => {}
        }
    });
}

/// Waits until told to stop, or until nothing can tell it anything any more.
async fn stopped(stop: &mut watch::Receiver<bool>) {
    stop.wait_for(|stop| *stop).await.ok();
}

/// Serves a copy, starting over after anything goes wrong, such as the hub being out of
/// reach, the repository's git store moving, or the copy not being where its entry says: it
/// may be servable soon.
async fn serve_retrying(
    key: &str,
    mut commands: mpsc::UnboundedReceiver<Command>,
    status: &SharedStatus,
    progress: &Progress,
    hubs: &Hubs,
) {
    let mut waiting = vec![];
    let mut backoff = Duration::from_secs(1);
    loop {
        let started = now();
        match serve_async(key, &mut commands, status, progress, &mut waiting, hubs).await {
            Ok(()) => return,
            Err(err) => {
                let message = format!("{err:#}");
                if err.downcast_ref::<Suspended>().is_some() {
                    tracing::warn!("{message}; looking again in {backoff:?}");
                } else {
                    tracing::error!("{message}; retrying in {backoff:?}");
                }
                // Into the copy, if it is where its entry says; never into what is there
                // instead.
                let copy = UserState::load()
                    .ok()
                    .and_then(|state| state.entry(key).cloned())
                    .filter(|entry| copy::holds(entry, &entry.path))
                    .and_then(|entry| Located::find(&entry.path).ok());
                status.record(copy.as_ref(), |status| status.failed(&err));
                for waiter in waiting.drain(..) {
                    waiter.send(Err(message.clone())).ok();
                }
            }
        }
        let succeeded = status.succeeded_since(started);
        if succeeded {
            backoff = Duration::from_secs(1);
        }
        if pause(backoff, &mut commands, &mut waiting).await {
            return;
        }
        backoff = (backoff * 2).min(MAX_BACKOFF);
    }
}

/// Waits `delay`, answering commands meanwhile. Returns whether nothing can send commands
/// any more; a sync request ends the wait early.
pub(super) async fn pause(
    delay: Duration,
    commands: &mut mpsc::UnboundedReceiver<Command>,
    waiting: &mut Vec<oneshot::Sender<Result<Synced, String>>>,
) -> bool {
    let sleep = tokio::time::sleep(delay);
    tokio::pin!(sleep);
    tokio::select! {
        () = &mut sleep => false,
        command = commands.recv() => match command {
            None => true,
            Some(Command::Sync(reply)) => {
                waiting.push(reply);
                false
            }
        },
    }
}

/// Finds the copy `key`'s entry names: at its path, or where jj last saw it, which moves the
/// entry there.
fn find_copy(key: &str) -> anyhow::Result<Option<(Entry, Located)>> {
    let Some(entry) = UserState::load()?.entry(key).cloned() else {
        return Ok(None);
    };
    if copy::holds(&entry, &entry.path) {
        let located = Located::find(&entry.path)?;
        return Ok(Some((entry, located)));
    }
    if let Some(path) = copy::moved_to(&entry) {
        tracing::info!(
            "the copy moved from {} to {}; serving it there",
            entry.path.display(),
            path.display()
        );
        if !UserState::move_entry(&entry, path.clone())? {
            return Err(Suspended("its entry changed while the daemon found it".to_owned()).into());
        }
        let moved = Entry { path, ..entry };
        let located = Located::find(&moved.path)?;
        return Ok(Some((moved, located)));
    }
    let why = match Located::find(&entry.path) {
        Err(_) => format!("{} is missing", entry.path.display()),
        Ok(located) => {
            let found = copy::Found::read(&located.repo_path)?;
            let why = copy::check(&entry, &found)
                .err()
                .unwrap_or_else(|| "it changed".to_owned());
            format!(
                "the repository at {} isn't the copy: {why}",
                entry.path.display()
            )
        }
    };
    Err(Suspended(why).into())
}

/// The identity of `path`'s directory, which changes when it is replaced, as by restoring a
/// backup, though what is in it may not.
#[cfg(unix)]
fn identity(path: &Path) -> Option<(u64, u64)> {
    use std::os::unix::fs::MetadataExt as _;
    let metadata = fs::metadata(path).ok()?;
    Some((metadata.dev(), metadata.ino()))
}

#[cfg(not(unix))]
fn identity(_path: &Path) -> Option<(u64, u64)> {
    None
}

async fn serve_async(
    key: &str,
    commands: &mut mpsc::UnboundedReceiver<Command>,
    status: &SharedStatus,
    progress: &Progress,
    waiting: &mut Vec<oneshot::Sender<Result<Synced, String>>>,
    hubs: &Hubs,
) -> anyhow::Result<()> {
    // No entry: the copy left, or its hive was removed.
    let Some((entry, located)) = find_copy(key)? else {
        return Ok(());
    };
    let hive = HiveConfig::load(&located.repo_path)?
        .with_context(|| format!("{} is not part of a hive", entry.path.display()))?;
    let workspace = &entry.path;
    let mut opened = identity(&located.repo_path);
    let connection = hubs.connect(&hive.hub).await?;
    let own = hubs.own_connections(&hive.hub);
    let (mut driver, machine) = open_driver(&located, &hive, &connection, own, progress)?;
    let transport = connection.transport.clone();
    let mut notices = transport.subscribe(&hive.head_subject()).await?;
    let mut reconnections = transport.reconnections();
    let mut watcher = Watcher::op_heads(&located.repo_path)?;
    // Where jj records the copy's path, which it rewrites when it finds the copy moved. A
    // copy moved is news only there, until the poll: the op heads watch, on the old path,
    // sees nothing on macOS, and on Linux sees heads under paths that no longer exist.
    let mut moves = crate::settings::config_id_dir(&entry.config_id).and_then(|dir| {
        Watcher::moves(&dir)
            .inspect_err(|err| tracing::debug!("{err:#}"))
            .ok()
    });
    let mut poll = tokio::time::interval(POLL_INTERVAL);
    let mut backoff = Duration::from_millis(500);
    let mut retry = false;
    // Whether the connection coming back has cut short a wait to retry since the last sync
    // that worked.
    let mut woke_early = false;
    // Why the hub was out of reach when last asked, to log once rather than at every retry.
    let mut unreachable: Option<String> = None;
    let mut gc_checked: Option<std::time::Instant> = None;
    tracing::info!("serving in hive {}", hive.display_name());
    loop {
        // After a failure, try again once the backoff has passed, rather than waiting for
        // something to change; and sync at once when asked.
        let trigger = if retry {
            "a retry".to_owned()
        } else if !waiting.is_empty() {
            "a request".to_owned()
        } else {
            tokio::select! {
                _ = poll.tick() => "the poll interval".to_owned(),
                () = watcher.changed() => "a local operation".to_owned(),
                () = crate::watch::changed(moves.as_mut()) => match copy::moved_to(&entry) {
                    // Served where it is now, once found again.
                    Some(path) => {
                        return Err(Suspended(format!("the copy moved to {}", path.display())).into());
                    }
                    None => continue,
                },
                // Announcements made while it was disconnected, as while the machine
                // slept, are lost.
                () = reconnections.next() => "reconnecting to the hub".to_owned(),
                notice = notices.next() => {
                    let Some(notice) = notice else { anyhow::bail!("lost the head subscription") };
                    match Envelope::<HeadNotice>::decode(&notice.payload) {
                        Ok(notice) => {
                            let seq = notice.seq;
                            driver.notice(notice)?;
                            format!("the hub announcing {seq}")
                        }
                        Err(err) => {
                            tracing::warn!("ignoring announcement: {err:#}");
                            "an unreadable announcement".to_owned()
                        }
                    }
                }
                command = commands.recv() => match command {
                    None => return Ok(()),
                    Some(Command::Sync(reply)) => {
                        waiting.push(reply);
                        "a request".to_owned()
                    }
                },
            }
        };
        // Still the copy, before anything is read from it or written to it, its status
        // included.
        let found = copy::Found::read(&located.repo_path)?;
        if let Err(why) = copy::check(&entry, &found) {
            let why = format!(
                "the repository at {} isn't the copy: {why}",
                workspace.display()
            );
            for waiter in waiting.drain(..) {
                waiter.send(Err(format!("suspended: {why}"))).ok();
            }
            return Err(Suspended(why).into());
        }
        // While the hub is out of reach, a sync could only wait for its requests to time
        // out. Say why instead, to `musubi status` and to any command waiting, and wait for
        // the connection to come back, or for the backoff to pass. A reconnection from now
        // on ends the wait.
        reconnections.seen();
        if !transport.connected()
            && let Some(why) = connection.out_of_reach().await
        {
            if unreachable.as_ref() != Some(&why) {
                tracing::warn!("{why}");
            }
            status.record(Some(&located), |status| {
                status.failed(&anyhow::anyhow!("{why}"));
            });
            for waiter in waiting.drain(..) {
                waiter.send(Err(why.clone())).ok();
            }
            unreachable = Some(why);
            retry = true;
            // Nothing failed here, so nothing need start over; and the connection coming
            // back always ends the wait, since no sync ran that could lose it again.
            let stopped = tokio::select! {
                stopped = pause(backoff, commands, waiting) => stopped,
                () = reconnections.next() => false,
            };
            if stopped {
                return Ok(());
            }
            backoff = (backoff * 2).min(MAX_BACKOFF);
            continue;
        }
        unreachable = None;
        // Reopen when the directory or jj's settings change. The stores keep their signer
        // and other settings from when they opened, so updating the loader alone would
        // keep signing with the old key. An unchanged config keeps the existing caches.
        let now_identity = identity(&located.repo_path);
        let settings = crate::settings::load(&located.workspace_root, &located.repo_path)?;
        if now_identity != opened || !crate::settings::unchanged(driver.settings(), &settings) {
            tracing::info!("the repository's directory or settings changed; opening it afresh");
            let settings = driver
                .settings()
                .with_new_config(settings.config().clone())?;
            driver.reopen(located.open_with_settings(&settings)?)?;
            watcher = Watcher::op_heads(&located.repo_path)?;
            opened = now_identity;
        }
        tracing::debug!("syncing after {trigger}");
        let started = std::time::Instant::now();
        // Reconnecting during the sync, which may miss announcements, calls for another.
        reconnections.seen();
        let held_before = status.publication_held();
        let result = driver.sync().await;
        tracing::debug!("sync took {:?}", started.elapsed());
        let synced = known(&driver);
        // Why the hub is out of reach, if the connector knows, says more than a timeout.
        let result = match result {
            Ok(synced) => Ok(synced),
            Err(err) => Err(connection.explain(err).await),
        };
        // The hive is over: leave it, then say so, so that whoever asked finds it left.
        if let Err(err) = &result
            && HiveGone::of(err) == Some(HiveGone::Removed)
        {
            let message = format!(
                "{err:#}, so this repository no longer syncs with it; everything it has stays"
            );
            // Changed meanwhile, as by `musubi join --hub`: start over with what it is now.
            anyhow::ensure!(
                leave_hive(&located, &hive, Membership::Removed)?,
                "this repository's hive or hub changed while it synced"
            );
            tracing::warn!("{message}");
            for waiter in waiting.drain(..) {
                waiter.send(Err(message.clone())).ok();
            }
            return Ok(());
        }
        let reply = match &result {
            Ok(_) => Ok(synced.clone()),
            Err(err) => Err(format!("{err:#}")),
        };
        status.record(Some(&located), |status| {
            status.synced(result.as_ref().err(), &synced);
        });
        report(
            &connection,
            &located.repo_path,
            &hive,
            &machine,
            synced.seq,
            reply.as_ref().err(),
        );
        for waiter in waiting.drain(..) {
            waiter.send(reply.clone()).ok();
        }
        match result {
            Ok(_) => {
                backoff = Duration::from_millis(500);
                retry = false;
                woke_early = false;
                if gc_checked.is_none_or(|checked| checked.elapsed() >= GC_CHECK_INTERVAL) {
                    gc_checked = Some(std::time::Instant::now());
                    collect_garbage(&located);
                }
            }
            Err(err) => {
                if publication_held(&err) {
                    if !held_before {
                        tracing::warn!("{err:#}");
                    }
                    // No reconnect/reopen loop for a policy hold. Keep the immutable
                    // accounting cache, and keep listening for incoming and local work.
                    retry = false;
                    backoff = Duration::from_millis(500);
                    continue;
                }
                tracing::warn!("{err:#}");
                // What failed may be that the copy is no longer there, as when it was moved
                // or deleted during the sync: then open nothing there, which would write.
                if !copy::holds(&entry, workspace) {
                    return Err(Suspended(format!(
                        "the copy is no longer at {}",
                        workspace.display()
                    ))
                    .into());
                }
                // Lost replies are indistinguishable from lost requests, and the open
                // repository's cached state may be what failed: start over, reopened.
                if let Err(err) = located.open().and_then(|repo| driver.reopen(repo)) {
                    tracing::warn!("cannot reopen: {err:#}");
                    driver.restart();
                }
                // So too may the watcher, if the directory it watches was replaced, as by
                // restoring a backup: one watching a deleted directory never wakes.
                match Watcher::op_heads(&located.repo_path) {
                    Ok(new) => watcher = new,
                    Err(err) => tracing::debug!("cannot watch afresh: {err:#}"),
                }
                retry = true;
                // The connection coming back while it waits, as after the machine slept, ends
                // the wait, but only once: a sync that itself loses the connection would
                // otherwise come straight back, again and again.
                reconnections.seen();
                let stopped = tokio::select! {
                    stopped = pause(backoff, commands, waiting) => stopped,
                    () = reconnections.next(), if !woke_early => {
                        woke_early = true;
                        false
                    }
                };
                if stopped {
                    return Ok(());
                }
                backoff = (backoff * 2).min(MAX_BACKOFF);
            }
        }
    }
}

/// Whether a gc runs, in any repository the daemon serves: one at a time is enough.
static COLLECTING: AtomicBool = AtomicBool::new(false);

/// Starts a gc in the repository on a thread of its own, if it is due (see `musubi_jj::gc`)
/// and none is running, so that syncs go on meanwhile.
fn collect_garbage(located: &Located) {
    if !musubi_jj::gc::due(&located.repo_path, SystemTime::now())
        || COLLECTING.swap(true, Ordering::AcqRel)
    {
        return;
    }
    let (workspace_root, repo_path) = (located.workspace_root.clone(), located.repo_path.clone());
    let spawned = std::thread::Builder::new()
        .name(format!("gc {}", repo_path.display()))
        .spawn(move || {
            /// Lets the next gc start once this one ends, however it ends.
            struct Done;
            impl Drop for Done {
                fn drop(&mut self) {
                    COLLECTING.store(false, Ordering::Release);
                }
            }
            let _done = Done;
            let collected = crate::settings::load(&workspace_root, &repo_path)
                .and_then(|settings| Ok(musubi_jj::gc::collect_if_due(&repo_path, &settings)?));
            match collected {
                Ok(true) => tracing::info!("collected garbage in {}", repo_path.display()),
                Ok(false) => {}
                Err(err) => {
                    tracing::warn!("collecting garbage in {}: {err:#}", repo_path.display());
                }
            }
        });
    if let Err(err) = spawned {
        COLLECTING.store(false, Ordering::Release);
        tracing::warn!("starting gc: {err}");
    }
}

/// Tells the hub how a sync went, for `musubi top`, without waiting for its answer: a sync
/// that failed may have failed to reach it. The answer, when it comes, has the hive's name,
/// recorded for `musubi status` should the hive have been renamed, and the hub's release,
/// which any release can read, for this machine to upgrade to if it is newer.
fn report(
    connection: &Arc<Connection>,
    repo_path: &Path,
    hive: &HiveConfig,
    machine: &str,
    seq: u64,
    error: Option<&String>,
) {
    let request = HubWideRequest::Report {
        hive: hive.hive.to_string(),
        report: Report {
            machine: machine.to_owned(),
            seq,
            error: error.cloned(),
            version: RELEASE.to_owned(),
        },
    };
    let Ok(payload) = Envelope::encode(request) else {
        return;
    };
    // The connection, not just its transport, so that while the report waits, the daemon
    // shares it rather than connecting again.
    let connection = connection.clone();
    let (repo_path, hive) = (repo_path.to_owned(), hive.clone());
    tokio::spawn(async move {
        let subject = rpc_subject(HUB_TOKEN);
        match connection
            .transport
            .request(&subject, Bytes::from(payload), REPORT_TIMEOUT)
            .await
        {
            Ok(reply) => {
                if let Some(release) = release_of(&reply) {
                    crate::upgrade::consider(release);
                }
                if let Ok(HubWideReply::Hive(info)) = Envelope::decode(&reply)
                    && info.id == hive.hive.to_string()
                {
                    hive.note_name(&repo_path, &info.name);
                }
            }
            Err(err) => tracing::debug!("could not report to the hub: {err}"),
        }
    });
}
