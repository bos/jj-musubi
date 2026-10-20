//! The node daemon: one thread per repository, each syncing whenever its op heads change,
//! a head announcement arrives, or the poll timer fires.

use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use std::time::SystemTime;

use anyhow::Context as _;
use jj_lib::object_id::ObjectId as _;
use musubi_sync::driver::NodeDriver;
use musubi_sync::remote::RemoteHub;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HeadNotice;
use musubi_transport::NatsTransport;
use musubi_transport::Transport;
use serde::Deserialize;
use serde::Serialize;

use crate::config::DaemonConfig;
use crate::config::HiveConfig;
use crate::repo::Located;
use crate::watch::OpHeadsWatcher;

const POLL_INTERVAL: Duration = Duration::from_secs(30);
const REQUEST_TIMEOUT: Duration = Duration::from_secs(30);
const MAX_BACKOFF: Duration = Duration::from_secs(60);

/// What `musubi status` shows, written by the daemon after every sync attempt.
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct Status {
    pub last_attempt: Option<u64>,
    pub last_success: Option<u64>,
    pub known_seq: Option<u64>,
    pub known_head: Option<String>,
    pub error: Option<String>,
}

impl Status {
    pub fn path(repo_path: &Path) -> PathBuf {
        repo_path.join("musubi/status.json")
    }

    pub fn load(repo_path: &Path) -> Option<Self> {
        serde_json::from_slice(&std::fs::read(Self::path(repo_path)).ok()?).ok()
    }

    fn save(&self, repo_path: &Path) {
        if let Ok(json) = serde_json::to_vec_pretty(self) {
            std::fs::write(Self::path(repo_path), json).ok();
        }
    }
}

fn now() -> u64 {
    SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

/// Serves every configured repository until interrupted.
pub fn run() -> anyhow::Result<()> {
    let config = DaemonConfig::load()?;
    anyhow::ensure!(
        !config.repos.is_empty(),
        "no repositories configured; run `musubi init` or `musubi join` in one first"
    );
    let mut threads = vec![];
    for workspace in config.repos {
        threads.push(std::thread::spawn(move || {
            if let Err(err) = serve(&workspace) {
                tracing::error!("{}: {err:#}", workspace.display());
            }
        }));
    }
    for thread in threads {
        thread.join().ok();
    }
    Ok(())
}

/// Serves one repository: a single-threaded runtime, since jj-lib's repository handles are
/// used from one thread.
pub fn serve(workspace: &Path) -> anyhow::Result<()> {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;
    runtime.block_on(serve_async(workspace))
}

async fn serve_async(workspace: &Path) -> anyhow::Result<()> {
    let located = Located::find(workspace)?;
    let hive = HiveConfig::load(&located.repo_path)?
        .with_context(|| format!("{} is not part of a hive", workspace.display()))?;
    let transport: Arc<dyn Transport> = Arc::new(NatsTransport::connect(&hive.nats_url).await?);
    let mut notices = transport.subscribe(&hive.head_subject()).await?;
    let mut watcher = OpHeadsWatcher::new(&located.repo_path)?;
    let blobs = located.repo_path.join("musubi/blobs");
    let remote = RemoteHub::new(transport, hive.rpc_subject(), &blobs, REQUEST_TIMEOUT)?;
    let mut driver = NodeDriver::new(located.open()?, remote)?;
    let mut poll = tokio::time::interval(POLL_INTERVAL);
    let mut backoff = Duration::from_millis(500);
    tracing::info!("serving {} in hive {}", workspace.display(), hive.hive);
    loop {
        tokio::select! {
            _ = poll.tick() => {}
            () = watcher.changed() => {}
            notice = notices.next() => {
                let Some(notice) = notice else { anyhow::bail!("lost the head subscription") };
                match Envelope::<HeadNotice>::decode(&notice.payload) {
                    Ok(notice) => driver.notice(notice)?,
                    Err(err) => tracing::warn!("ignoring announcement: {err:#}"),
                }
            }
        }
        let mut status = Status::load(&located.repo_path).unwrap_or_default();
        status.last_attempt = Some(now());
        match driver.sync().await {
            Ok(_) => {
                backoff = Duration::from_millis(500);
                status.last_success = Some(now());
                status.error = None;
            }
            Err(err) => {
                tracing::warn!("{}: {err:#}", workspace.display());
                status.error = Some(format!("{err:#}"));
                // Lost replies are indistinguishable from lost requests; start over.
                driver.restart();
                tokio::time::sleep(backoff).await;
                backoff = (backoff * 2).min(MAX_BACKOFF);
            }
        }
        let (seq, head) = driver.known();
        status.known_seq = Some(*seq);
        status.known_head = Some(head.hex());
        status.save(&located.repo_path);
    }
}
