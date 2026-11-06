//! Recovery through the production worker, after a push has changed real hub storage.

#![allow(clippy::unwrap_used)]

use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::time::Duration;

use futures::FutureExt as _;
use jj_lib::object_id::ObjectId as _;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::JoinRequest;
use musubi_jj::node::NodeRepo;
use musubi_jj::op_id::CanonicalOp;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use musubi_transport::MemoryNetwork;
use musubi_transport::Subscription;
use musubi_transport::TransportError;

use super::*;
use crate::driver::NodeDriver;
use crate::remote::RemoteHub;
use crate::wire::HeadNotice;
use crate::wire::HubRequest;
use crate::wire::WireAttachment;

const TIMEOUT: Duration = Duration::from_secs(10);
const INJECTED: &str = "injected panic after accepting a head";

/// Per-worker hooks, absent outside unit tests. No storage or repository state is faked.
#[derive(Default)]
pub(super) struct WorkerHooks {
    opens: AtomicUsize,
    /// Whether to panic once the hub accepts a head.
    armed: AtomicBool,
    accepted: Mutex<Option<(u64, OpId)>>,
    /// How many protocol requests the hub has worked out an answer to, as of the reply it
    /// last sent.
    afresh: AtomicU64,
}

impl WorkerHooks {
    pub(super) fn opened(&self) {
        self.opens.fetch_add(1, Ordering::SeqCst);
    }

    pub(super) fn handled(&self, service: &HubService, notice: Option<&HeadNotice>) {
        self.afresh.store(service.afresh(), Ordering::SeqCst);
        if notice.is_some() && self.armed.swap(false, Ordering::SeqCst) {
            let (seq, head) = service.hub().store().head();
            *self.accepted.lock().unwrap() = Some((seq, head.clone()));
            panic!("{INJECTED}");
        }
    }
}

struct RunningWorker {
    worker: Worker,
    forward: tokio::task::JoinHandle<()>,
}

impl RunningWorker {
    async fn start(
        server: &HubServer,
        network: &MemoryNetwork,
        hive: &str,
        recovery: Option<Arc<WorkerHooks>>,
    ) -> Self {
        let transport: Arc<dyn Transport> = Arc::new(network.connect());
        let mut incoming = transport.subscribe(&rpc_subject(hive)).await.unwrap();
        let dir = server.lock().hive_dir(hive).unwrap().to_owned();
        let worker = spawn_worker(
            hive.to_owned(),
            dir,
            server.hubs.clone(),
            server.activity.clone(),
            transport,
            recovery,
        );
        let requests = worker.requests.clone();
        // Route to this worker alone: HubServer's fallback cannot hide a stopped thread.
        let forward = tokio::spawn(async move {
            while let Some(message) = incoming.next().await {
                if requests.send(message).is_err() {
                    break;
                }
            }
        });
        Self { worker, forward }
    }

    async fn stop(self) {
        self.forward.abort();
        drop(self.forward.await);
        drop(self.worker.requests);
        tokio::task::spawn_blocking(move || self.worker.thread.join().unwrap())
            .await
            .unwrap();
    }
}

async fn create_hive(server: &mut HubServer, repo: &TestRepo) -> String {
    let node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    let summary = node.join_summary().unwrap();
    let request = HubWideRequest::Join(JoinRequest {
        backend: summary.backend,
        remotes: vec![],
        dir_name: repo.machine().to_owned(),
        roots: summary.roots.iter().map(|id| id.hex()).collect(),
        remote_targets: vec![],
        machine: node.machine().key().to_owned(),
        choice: JoinChoice::Create(Some(repo.machine().to_owned())),
    });
    match server
        .handle_hub_wide(&Envelope::encode(request).unwrap(), 1024 * 1024)
        .await
    {
        HubWideReply::Joined(joined) => joined.hive.id,
        other => panic!("expected a new hive, got {other:?}"),
    }
}

fn driver(repo: &TestRepo, transport: Arc<dyn Transport>, hive: &str) -> NodeDriver {
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    node.create_join_operation("musubi: join").unwrap();
    let remote = RemoteHub::new(
        transport,
        rpc_subject(hive),
        &repo.repo_path().join("musubi/blobs"),
        TIMEOUT,
    )
    .unwrap();
    NodeDriver::new(node, remote).unwrap()
}

/// A node's link to a hub that takes longer than the node's timeout to work out the answer
/// to any protocol request, as to a fetch or a push of a large history: the reply to each it
/// works out comes too late.
struct SlowHub {
    inner: Arc<dyn Transport>,
    hooks: Arc<WorkerHooks>,
    late: AtomicUsize,
    /// Of those, requests too large to send whole.
    late_uploaded: AtomicUsize,
}

#[async_trait::async_trait]
impl Transport for SlowHub {
    fn max_payload(&self) -> usize {
        self.inner.max_payload()
    }

    async fn publish(&self, subject: &str, payload: Bytes) -> Result<(), TransportError> {
        self.inner.publish(subject, payload).await
    }

    async fn subscribe(&self, subject: &str) -> Result<Subscription, TransportError> {
        self.inner.subscribe(subject).await
    }

    async fn request(
        &self,
        subject: &str,
        payload: Bytes,
        timeout: Duration,
    ) -> Result<Bytes, TransportError> {
        // The node sends one request at a time, and the hub answers one at a time.
        let before = self.hooks.afresh.load(Ordering::SeqCst);
        let uploaded = matches!(
            Envelope::<HubRequest>::decode(&payload),
            Ok(HubRequest::Indirect { .. })
        );
        let reply = self.inner.request(subject, payload, timeout).await?;
        if self.hooks.afresh.load(Ordering::SeqCst) > before {
            self.late.fetch_add(1, Ordering::SeqCst);
            if uploaded {
                self.late_uploaded.fetch_add(1, Ordering::SeqCst);
            }
            return Err(TransportError::Timeout);
        }
        Ok(reply)
    }
}

/// A hub that takes longer than a node's timeout to answer a push or a fetch, as for a large
/// history, still gets the node synced: the node asks again, and the hub answers the repeat
/// with the reply it worked out, rather than working it out again and missing the timeout
/// every time (issue 124). Without either, the first sync fails. Messages are small, so that
/// requests, replies and what they carry travel as blobs, and the node must upload them again.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_hub_slower_than_the_timeout_still_syncs() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    alpha.write_file("work", "a large history\n");
    alpha.jj(&["commit", "-m", "a large history"]);
    let dir = env.root().join("hub");
    std::fs::create_dir(&dir).unwrap();
    let mut server = HubServer::open(&dir).unwrap();
    let hive = create_hive(&mut server, &alpha).await;
    let network = MemoryNetwork::new(1, 256);
    let hooks = Arc::new(WorkerHooks::default());
    let worker = RunningWorker::start(&server, &network, &hive, Some(hooks.clone())).await;
    let link = Arc::new(SlowHub {
        inner: Arc::new(network.connect()),
        hooks,
        late: AtomicUsize::new(0),
        late_uploaded: AtomicUsize::new(0),
    });

    // alpha's sync pushes, beta's fetches what it pushed and pushes its own, and alpha's
    // fetches that.
    let mut alpha_driver = driver(&alpha, link.clone(), &hive);
    alpha_driver.sync().await.unwrap();
    let beta = env.init_repo("beta");
    let mut beta_driver = driver(&beta, link.clone(), &hive);
    beta_driver.sync().await.unwrap();
    alpha_driver.sync().await.unwrap();
    assert_eq!(alpha_driver.known(), beta_driver.known());
    assert_eq!(
        beta.jj(&[
            "file",
            "show",
            "work",
            "-r",
            "description(substring:'large')"
        ]),
        "a large history\n"
    );
    assert!(link.late.load(Ordering::SeqCst) >= 3);
    assert!(link.late_uploaded.load(Ordering::SeqCst) >= 1);

    worker.stop().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_worker_reopens_its_service_after_a_panic() {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    alpha.write_file("work", "before the panic\n");
    alpha.jj(&["commit", "-m", "before the panic"]);
    let gamma = env.init_repo("gamma");
    gamma.write_file("other", "another hive\n");
    gamma.jj(&["commit", "-m", "another hive"]);
    let dir = env.root().join("hub");
    std::fs::create_dir(&dir).unwrap();
    let mut server = HubServer::open(&dir).unwrap();
    let hive = create_hive(&mut server, &alpha).await;
    let other_hive = create_hive(&mut server, &gamma).await;
    let hive_dir = server.lock().hive_dir(&hive).unwrap().to_owned();
    let network = MemoryNetwork::new(1, 1024 * 1024);
    let recovery = Arc::new(WorkerHooks::default());
    recovery.armed.store(true, Ordering::SeqCst);
    let worker = RunningWorker::start(&server, &network, &hive, Some(recovery.clone())).await;
    let other_worker = RunningWorker::start(&server, &network, &other_hive, None).await;
    let client: Arc<dyn Transport> = Arc::new(network.connect());
    let mut notices = client.subscribe(&head_subject(&hive)).await.unwrap();
    let mut alpha_driver = driver(&alpha, client.clone(), &hive);

    // The real push imports objects and operations and appends a head before the hook fires.
    let err = alpha_driver.sync().await.unwrap_err();
    assert!(format!("{err:#}").contains(INJECTED), "{err:#}");
    assert_eq!(recovery.opens.load(Ordering::SeqCst), 1);
    assert!(!worker.worker.thread.is_finished());
    let accepted = recovery.accepted.lock().unwrap().clone().unwrap();
    assert!(accepted.0 > 0);
    let store = HubStore::open(&hive_dir).unwrap();
    assert_eq!(store.head(), (accepted.0, &accepted.1));
    assert!(store.missing_closure(&accepted.1).unwrap().is_empty());
    let records = HubAdapter::new(store, &hive_dir).unwrap();
    let records = musubi_core::hub::HubStorage::records(&records);

    // An error reply must not promise rollback: fetch the accepted head on the SAME worker.
    let fetch = HubRequest::Protocol(Request::Fetch {
        machine: NodeRepo::open(&alpha.repo_path(), &alpha.settings())
            .unwrap()
            .machine()
            .key()
            .to_owned(),
        base: vec![0; 64],
        haves: WireAttachment::Haves(vec![]),
        records,
    });
    let reply = client
        .request(
            &rpc_subject(&hive),
            Bytes::from(Envelope::encode(fetch).unwrap()),
            TIMEOUT,
        )
        .await
        .unwrap();
    match Envelope::<HubReply>::decode(&reply).unwrap() {
        HubReply::Protocol(Reply::Fetched { seq, head, .. }) => {
            assert_eq!((seq, head), (accepted.0, accepted.1.to_bytes()));
        }
        other => panic!("expected the reopened head, got {other:?}"),
    }
    // A healthy retained service could answer too; count the actual construction to prove
    // the catch path discarded it. Removing `service = None` must fail this assertion.
    assert_eq!(recovery.opens.load(Ordering::SeqCst), 2);
    assert!(notices.next().now_or_never().is_none());

    let mut gamma_driver = driver(&gamma, client.clone(), &other_hive);
    gamma_driver.sync().await.unwrap();
    alpha_driver.restart();
    alpha_driver.sync().await.unwrap();
    let beta = env.init_repo("beta");
    let mut beta_driver = driver(&beta, client.clone(), &hive);
    beta_driver.sync().await.unwrap();
    alpha.write_file("later", "after the panic\n");
    alpha.jj(&["commit", "-m", "after the panic"]);
    alpha_driver
        .reopen(NodeRepo::open(&alpha.repo_path(), &alpha.settings()).unwrap())
        .unwrap();
    alpha_driver.sync().await.unwrap();
    beta_driver.sync().await.unwrap();
    alpha_driver.sync().await.unwrap();
    assert_eq!(alpha_driver.known(), beta_driver.known());
    for (file, description) in [("work", "before the panic"), ("later", "after the panic")] {
        assert_eq!(
            beta.jj(&[
                "file",
                "show",
                file,
                "-r",
                &format!("description(substring:'{description}')")
            ]),
            format!("{description}\n")
        );
    }
    // The final fetch is a barrier: earlier pushes have sent their notices by now.
    let store = HubStore::open(&hive_dir).unwrap();
    let mut published = 0;
    let mut last = accepted;
    while let Some(Some(message)) = notices.next().now_or_never() {
        let notice = Envelope::<HeadNotice>::decode(&message.payload).unwrap();
        let head = OpId::new(notice.head);
        assert!(notice.seq > last.0);
        assert!(store.missing_closure(&head).unwrap().is_empty());
        assert!(
            store
                .canonical()
                .is_ancestor_of(&CanonicalOp(last.1.clone()), &CanonicalOp(head.clone()))
                .unwrap()
        );
        last = (notice.seq, head);
        published += 1;
    }
    assert!(published > 0);
    assert_eq!(store.head(), (last.0, &last.1));
    assert_eq!(alpha_driver.known(), &last);
    assert_eq!(recovery.opens.load(Ordering::SeqCst), 2);
    assert!(!worker.worker.thread.is_finished());
    assert!(!other_worker.worker.thread.is_finished());
    assert!(!server.hubs.is_poisoned());
    assert!(!server.activity.is_poisoned());

    worker.stop().await;
    other_worker.stop().await;
}
