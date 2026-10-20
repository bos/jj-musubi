//! Nodes and a hub talking over real transports: the in-memory network (with a tiny payload
//! limit, so every bundle is chunked and large messages go indirect, and with faults) and a
//! real `nats-server`.

#![allow(clippy::unwrap_used)]

use std::fmt::Write as _;
use std::sync::Arc;
use std::time::Duration;

use musubi_hub::store::Backend;
use musubi_jj::node::NodeRepo;
use musubi_sync::driver::NodeDriver;
use musubi_sync::hub::HubAdapter;
use musubi_sync::remote::RemoteHub;
use musubi_sync::service::HubService;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HeadNotice;
use musubi_testutil::NatsServer;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use musubi_transport::Faults;
use musubi_transport::MemoryNetwork;
use musubi_transport::NatsTransport;
use musubi_transport::Transport;

const RPC: &str = "musubi.test.rpc";
const HEAD: &str = "musubi.test.head";

fn spawn_hub(env: &TestEnv, transport: Arc<dyn Transport>) {
    let dir = env.root().join("hub");
    let hub = HubAdapter::init(&dir, Backend::Git).unwrap();
    let service = HubService::new(hub, &dir, RPC.into(), HEAD.into()).unwrap();
    tokio::task::spawn_local(async move { service.run(transport).await.unwrap() });
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

#[tokio::test(flavor = "current_thread")]
async fn nats_with_head_notifications() {
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async {
            let server = NatsServer::start(64 * 1024);
            let connect = || async {
                Arc::new(NatsTransport::connect(&server.url()).await.unwrap()) as Arc<dyn Transport>
            };
            let env = TestEnv::new();
            let alpha = env.init_repo("alpha");
            let beta = env.init_repo("beta");
            spawn_hub(&env, connect().await);
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
