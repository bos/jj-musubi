//! Nodes and a hub talking over real transports: the in-memory network (with a tiny payload
//! limit, so every bundle is chunked and large messages go indirect, and with faults), and
//! streams to a hub that relays them through it, as a hub's socket does.

#![allow(clippy::unwrap_used)]

use std::fmt::Write as _;
use std::sync::Arc;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::time::Duration;

use bytes::Bytes;

use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::driver::NodeDriver;
use musubi_sync::hub::HubAdapter;
use musubi_sync::remote::RemoteHub;
use musubi_sync::service::HubService;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HeadNotice;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use musubi_transport::Faults;
use musubi_transport::MemoryNetwork;
use musubi_transport::StreamTransport;
use musubi_transport::Subscription;
use musubi_transport::Transport;
use musubi_transport::TransportError;
use musubi_transport::stream::Connector;
use musubi_transport::stream::Reader;
use musubi_transport::stream::Writer;

const RPC: &str = "musubi.test.rpc";
const HEAD: &str = "musubi.test.head";

fn spawn_hub(env: &TestEnv, transport: Arc<dyn Transport>) {
    spawn_hub_with(env, transport, |service| service);
}

fn spawn_hub_with(
    env: &TestEnv,
    transport: Arc<dyn Transport>,
    configure: impl FnOnce(HubService) -> HubService,
) {
    let dir = env.root().join("hub");
    let hub = HubAdapter::init(&dir, Backend::Git).unwrap();
    let service = configure(HubService::new(hub, &dir, RPC.into(), HEAD.into()).unwrap());
    tokio::task::spawn_local(async move { service.run(transport, || {}).await.unwrap() });
}

fn driver(repo: &TestRepo, transport: Arc<dyn Transport>, timeout: Duration) -> NodeDriver {
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
        .unwrap();
    let blobs = repo.repo_path().join("musubi/blobs");
    let remote = RemoteHub::new(transport, RPC.into(), &blobs, timeout).unwrap();
    NodeDriver::new(node, remote).unwrap()
}

/// Syncs, retrying failed attempts: under faults a request can time out at any point.
async fn sync_until_ok(driver: &mut NodeDriver) {
    for attempt in 0..200 {
        match driver.sync().await {
            Ok(_) => return,
            Err(err) => {
                if attempt % 20 == 19 {
                    eprintln!("sync attempt {attempt} failed: {err:#}");
                }
                driver.restart();
                // Back off, as the daemon does; this also lets the hub task run.
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
        }
    }
    panic!("sync never succeeded");
}

fn visible(repo: &TestRepo) -> String {
    repo.jj(&[
        "log",
        "--no-graph",
        "-r",
        "all()",
        "-T",
        "commit_id ++ \" \" ++ description.first_line() ++ \"\\n\"",
    ])
}

async fn converge(drivers: &mut [NodeDriver]) {
    for _ in 0..3 {
        for driver in drivers.iter_mut() {
            sync_until_ok(driver).await;
        }
    }
}

async fn exchange_work(transport_for: impl Fn() -> Arc<dyn Transport>, timeout: Duration) {
    let env = TestEnv::new();
    let alpha = env.init_repo("alpha");
    let beta = env.init_repo("beta");
    spawn_hub(&env, transport_for());
    // Enough content that bundles span many chunks.
    let big = (0..2000).fold(String::new(), |mut text, i| {
        writeln!(text, "line {i}").unwrap();
        text
    });
    alpha.write_file("big", &big);
    alpha.jj(&["commit", "-m", "big file"]);
    beta.write_file("small", "small");
    beta.jj(&["commit", "-m", "small file"]);
    let mut drivers = [
        driver(&alpha, transport_for(), timeout),
        driver(&beta, transport_for(), timeout),
    ];
    converge(&mut drivers).await;
    alpha.jj(&["describe", "@-", "-m", "big file, reworded"]);
    converge(&mut drivers).await;
    assert_eq!(visible(&alpha), visible(&beta));
    assert!(visible(&beta).contains("big file, reworded"));
    assert_eq!(
        beta.jj(&[
            "file",
            "show",
            "-r",
            "description(substring:\"big file\")",
            "big"
        ]),
        big
    );
}

#[tokio::test(flavor = "current_thread")]
async fn memory_transport_with_tiny_payloads() {
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async {
            let network = MemoryNetwork::new(7, 4096);
            exchange_work(|| Arc::new(network.connect()), Duration::from_secs(10)).await;
        })
        .await;
}

#[tokio::test(flavor = "current_thread")]
async fn memory_transport_with_faults() {
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async {
            let network = MemoryNetwork::new(11, 8192);
            network.set_faults(Faults {
                drop_ppm: 50_000,
                duplicate_ppm: 50_000,
                delay_ppm: 50_000,
                max_delay: Duration::from_millis(30),
            });
            exchange_work(|| Arc::new(network.connect()), Duration::from_millis(300)).await;
        })
        .await;
}

/// Connects to a hub in this process over an in-memory pipe, the hub's side of each
/// connection relaying through `hub`.
struct Pipe {
    hub: Arc<dyn Transport>,
}

#[async_trait::async_trait]
impl Connector for Pipe {
    async fn connect(&self) -> std::io::Result<(Reader, Writer)> {
        let (ours, theirs) = tokio::io::duplex(64 * 1024);
        let (reader, writer) = tokio::io::split(theirs);
        tokio::spawn(musubi_transport::stream::serve(
            self.hub.clone(),
            reader,
            writer,
        ));
        let (reader, writer) = tokio::io::split(ours);
        Ok((Box::new(reader), Box::new(writer)))
    }
}

#[tokio::test(flavor = "current_thread")]
async fn streams_with_head_notifications() {
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async {
            let network = MemoryNetwork::new(13, 64 * 1024);
            let pipe = Arc::new(Pipe {
                hub: Arc::new(network.connect()),
            });
            let connect = || async {
                Arc::new(StreamTransport::connect(pipe.clone()).await.unwrap())
                    as Arc<dyn Transport>
            };
            let env = TestEnv::new();
            let alpha = env.init_repo("alpha");
            let beta = env.init_repo("beta");
            spawn_hub(&env, Arc::new(network.connect()));
            let beta_transport = connect().await;
            let mut notices = beta_transport.subscribe(HEAD).await.unwrap();
            let mut alpha_driver = driver(&alpha, connect().await, Duration::from_secs(10));
            let mut beta_driver = driver(&beta, beta_transport, Duration::from_secs(10));
            sync_until_ok(&mut beta_driver).await;

            alpha.write_file("f", "hello");
            alpha.jj(&["commit", "-m", "hello from alpha"]);
            sync_until_ok(&mut alpha_driver).await;
            // beta learns of the new head from the announcement, not from polling.
            let notice = tokio::time::timeout(Duration::from_secs(10), notices.next())
                .await
                .unwrap()
                .unwrap();
            let notice: HeadNotice = Envelope::decode(&notice.payload).unwrap();
            beta_driver.notice(notice).unwrap();
            sync_until_ok(&mut beta_driver).await;
            assert!(visible(&beta).contains("hello from alpha"));
        })
        .await;
}

/// A transport that counts the requests through it, and how many were in flight at once.
struct Counting {
    inner: Arc<dyn Transport>,
    requests: AtomicUsize,
    in_flight: AtomicUsize,
    most_in_flight: AtomicUsize,
}

impl Counting {
    fn new(inner: Arc<dyn Transport>) -> Arc<Self> {
        Arc::new(Self {
            inner,
            requests: AtomicUsize::new(0),
            in_flight: AtomicUsize::new(0),
            most_in_flight: AtomicUsize::new(0),
        })
    }

    /// The requests and the most in flight at once since the last call.
    fn take(&self) -> (usize, usize) {
        (
            self.requests.swap(0, Ordering::SeqCst),
            self.most_in_flight.swap(0, Ordering::SeqCst),
        )
    }
}

#[async_trait::async_trait]
impl Transport for Counting {
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
        self.requests.fetch_add(1, Ordering::SeqCst);
        let now = self.in_flight.fetch_add(1, Ordering::SeqCst) + 1;
        self.most_in_flight.fetch_max(now, Ordering::SeqCst);
        let reply = self.inner.request(subject, payload, timeout).await;
        self.in_flight.fetch_sub(1, Ordering::SeqCst);
        reply
    }
}

/// A sync that brings something new takes one round trip, and one that pushes takes two; a
/// transfer of many chunks keeps several in flight, rather than waiting for each.
#[tokio::test(flavor = "current_thread")]
async fn syncs_take_few_round_trips() {
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async {
            let network = MemoryNetwork::new(5, 64 * 1024);
            let env = TestEnv::new();
            let alpha = env.init_repo("alpha");
            let beta = env.init_repo("beta");
            spawn_hub(&env, Arc::new(network.connect()));
            let (alpha_net, beta_net) = (
                Counting::new(Arc::new(network.connect())),
                Counting::new(Arc::new(network.connect())),
            );
            let mut drivers = [
                driver(&alpha, alpha_net.clone(), Duration::from_secs(10)),
                driver(&beta, beta_net.clone(), Duration::from_secs(10)),
            ];
            converge(&mut drivers).await;

            alpha.write_file("small", "small");
            alpha.jj(&["commit", "-m", "small"]);
            alpha_net.take();
            drivers[0].sync().await.unwrap();
            assert_eq!(alpha_net.take().0, 2, "a push");
            beta_net.take();
            drivers[1].sync().await.unwrap();
            assert_eq!(beta_net.take().0, 1, "a fetch");

            // Incompressible content many chunks long.
            let mut big = vec![0; 1 << 20];
            blake3::Hasher::new()
                .update(b"big")
                .finalize_xof()
                .fill(&mut big);
            std::fs::write(alpha.path().join("big"), big).unwrap();
            alpha.jj(&["commit", "-m", "big"]);
            drivers[0].sync().await.unwrap();
            let (requests, most_in_flight) = alpha_net.take();
            assert!(most_in_flight > 1, "{requests} requests, one at a time");
            drivers[1].sync().await.unwrap();
            assert!(beta_net.take().1 > 1, "a download one chunk at a time");
            assert!(visible(&beta).contains("big"));
        })
        .await;
}

/// The hub deletes a blob it prepared for a node once the node has downloaded it, rather
/// than keeping every download for an hour: on git.git that was gigabytes.
#[tokio::test(flavor = "current_thread")]
async fn prepared_blobs_go_once_downloaded() {
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async {
            let network = MemoryNetwork::new(3, 64 * 1024);
            let env = TestEnv::new();
            let alpha = env.init_repo("alpha");
            let beta = env.init_repo("beta");
            spawn_hub_with(&env, Arc::new(network.connect()), |service| {
                service.with_served_blob_lifetime(Duration::ZERO)
            });
            let mut drivers = [
                driver(&alpha, Arc::new(network.connect()), Duration::from_secs(10)),
                driver(&beta, Arc::new(network.connect()), Duration::from_secs(10)),
            ];
            converge(&mut drivers).await;
            let mut big = vec![0; 1 << 20];
            blake3::Hasher::new()
                .update(b"big")
                .finalize_xof()
                .fill(&mut big);
            std::fs::write(alpha.path().join("big"), big).unwrap();
            alpha.jj(&["commit", "-m", "big"]);
            drivers[0].sync().await.unwrap();
            drivers[1].sync().await.unwrap();
            assert!(visible(&beta).contains("big"));
            // Any request lets the hub tidy up.
            drivers[1].sync().await.unwrap();
            let complete = env.root().join("hub/blobs/complete");
            let left: Vec<_> = std::fs::read_dir(complete).unwrap().collect();
            assert!(left.is_empty(), "prepared blobs left: {left:?}");
        })
        .await;
}
