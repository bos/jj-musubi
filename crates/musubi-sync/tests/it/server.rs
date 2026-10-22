//! A hub serving several hives: joining by matching, per-hive requests going to the right
//! hive, and the hub-wide requests.

#![allow(clippy::unwrap_used)]

use std::sync::Arc;
use std::time::Duration;

use bytes::Bytes;
use jj_lib::object_id::ObjectId as _;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_hub::hub_dir::JoinChoice;
use musubi_hub::hub_dir::JoinRequest;
use musubi_hub::hub_dir::Joined;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::bundle::BundleWriter;
use musubi_sync::driver::NodeDriver;
use musubi_sync::remote::RemoteHub;
use musubi_sync::server::HubServer;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HubReply;
use musubi_sync::wire::HubRequest;
use musubi_sync::wire::HubWideReply;
use musubi_sync::wire::HubWideRequest;
use musubi_sync::wire::WireAttachment;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use musubi_transport::MemoryNetwork;
use musubi_transport::Transport;

const TIMEOUT: Duration = Duration::from_secs(10);

async fn hub_wide(transport: &dyn Transport, request: HubWideRequest) -> HubWideReply {
    let reply = transport
        .request(
            "musubi.hub.rpc",
            Bytes::from(Envelope::encode(request).unwrap()),
            TIMEOUT,
        )
        .await
        .unwrap();
    Envelope::decode(&reply).unwrap()
}

fn join_request(repo: &TestRepo) -> JoinRequest {
    let node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    let summary = node.join_summary().unwrap();
    JoinRequest {
        backend: summary.backend,
        remotes: summary
            .remotes
            .into_iter()
            .flat_map(|(name, remote)| {
                let urls: Vec<String> = remote.urls().map(str::to_owned).collect();
                urls.into_iter().map(move |url| (name.clone(), url))
            })
            .collect(),
        dir_name: repo.machine().to_owned(),
        roots: summary.roots.iter().map(|id| id.hex()).collect(),
        remote_targets: summary.remote_targets.iter().map(|id| id.hex()).collect(),
        machine: node.machine().key().to_owned(),
        choice: JoinChoice::Match,
    }
}

fn creating(request: JoinRequest) -> JoinRequest {
    JoinRequest {
        choice: JoinChoice::Create(None),
        ..request
    }
}

async fn join(transport: &dyn Transport, request: JoinRequest) -> Result<Joined, String> {
    match hub_wide(transport, HubWideRequest::Join(request)).await {
        HubWideReply::Joined(joined) => Ok(joined),
        HubWideReply::Error(message) => Err(message),
        other => panic!("unexpected reply {other:?}"),
    }
}

async fn sync(repo: &TestRepo, transport: Arc<dyn Transport>, hive: &str) {
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    node.create_join_operation("musubi: join").unwrap();
    let blobs = repo.repo_path().join("musubi/blobs");
    let rpc = format!("musubi.{hive}.rpc");
    let remote = RemoteHub::new(transport, rpc, &blobs, TIMEOUT).unwrap();
    let mut driver = NodeDriver::new(node, remote).unwrap();
    driver.sync().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn one_hub_many_hives() {
    let env = TestEnv::new();
    let dir = env.root().join("hub");
    std::fs::create_dir(&dir).unwrap();
    let network = MemoryNetwork::new(1, 1024 * 1024);
    let server = HubServer::open(&dir).unwrap();
    let transport: Arc<dyn Transport> = Arc::new(network.connect());
    let (ready_tx, ready_rx) = tokio::sync::oneshot::channel();
    tokio::spawn(server.run(transport, move || {
        ready_tx.send(()).ok();
    }));
    ready_rx.await.unwrap();
    let client: Arc<dyn Transport> = Arc::new(network.connect());

    // An empty repository has nothing to match on.
    let alpha = env.init_repo("alpha");
    let err = join(&*client, join_request(&alpha)).await.unwrap_err();
    assert!(err.contains("commit something first"), "{err}");

    // The first copy creates a hive, named after its origin, but only when asked: joining
    // alone never creates one.
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "first"]);
    alpha.jj(&["bookmark", "create", "main", "-r", "@-"]);
    alpha.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.com/team/project.git",
    ]);
    let err = join(&*client, join_request(&alpha)).await.unwrap_err();
    assert!(err.contains("musubi create"), "{err}");
    let created = join(&*client, creating(join_request(&alpha)))
        .await
        .unwrap();
    assert!(created.created);
    assert_eq!(created.hive.name, "project");
    assert_eq!(created.hive.machines, ["alpha"]);
    let hive = created.hive.id.clone();
    sync(&alpha, client.clone(), &hive).await;

    // A copy with history in common and the same remote, by another URL form, joins it.
    let beta = env.init_repo("beta");
    beta.jj(&[
        "git",
        "remote",
        "add",
        "alpha",
        alpha.path().to_str().unwrap(),
    ]);
    beta.jj(&["git", "fetch", "--remote", "alpha"]);
    beta.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "git@example.com:team/project",
    ]);
    // Created instead, it would sync with nothing: refused, unless named.
    let err = join(&*client, creating(join_request(&beta)))
        .await
        .unwrap_err();
    assert!(
        err.contains("belongs in hive project (matched origin)"),
        "{err}"
    );
    let joined = join(&*client, join_request(&beta)).await.unwrap();
    assert!(!joined.created);
    assert_eq!(joined.hive.id, hive);
    assert_eq!(joined.reason, "matched origin");
    assert_eq!(joined.hive.machines, ["alpha", "beta"]);

    // So does one that spells it through a `url.<base>.insteadOf` alias of its own: the hub
    // matches the URL git uses.
    let aliased = env.init_repo("aliased");
    aliased.jj(&[
        "git",
        "remote",
        "add",
        "alpha",
        alpha.path().to_str().unwrap(),
    ]);
    aliased.jj(&["git", "fetch", "--remote", "alpha"]);
    aliased.jj(&["git", "remote", "remove", "alpha"]);
    aliased.git(&[
        "config",
        "url.https://example.com/.insteadOf",
        "musubi-test:",
    ]);
    aliased.jj(&["git", "remote", "add", "origin", "musubi-test:team/project"]);
    let joined = join(&*client, join_request(&aliased)).await.unwrap();
    assert_eq!(joined.hive.id, hive);
    assert_eq!(joined.reason, "matched origin");

    // A fork, with history in common but a remote of its own, isn't taken for the first:
    // joining it is refused, and created, it gets a hive of its own, named apart.
    let gamma = env.init_repo("gamma");
    gamma.jj(&[
        "git",
        "remote",
        "add",
        "alpha",
        alpha.path().to_str().unwrap(),
    ]);
    gamma.jj(&["git", "fetch", "--remote", "alpha"]);
    gamma.jj(&["git", "remote", "remove", "alpha"]);
    gamma.jj(&[
        "git",
        "remote",
        "add",
        "origin",
        "https://example.org/fork/project",
    ]);
    gamma.write_file("g", "g");
    gamma.jj(&["commit", "-m", "gamma's own"]);
    let err = join(&*client, join_request(&gamma)).await.unwrap_err();
    assert!(err.contains("hive project shares history"), "{err}");
    let fork = join(&*client, creating(join_request(&gamma)))
        .await
        .unwrap();
    assert!(fork.created);
    assert_eq!(fork.hive.name, "fork/project");
    sync(&gamma, client.clone(), &fork.hive.id).await;

    // Asked for by a prefix of its name, the first hive takes gamma too, since they share
    // history; an unrelated repository can't join it.
    let mut asking = join_request(&gamma);
    asking.choice = JoinChoice::Hive("pro".to_owned());
    assert_eq!(join(&*client, asking).await.unwrap().hive.id, hive);
    let delta = env.init_repo("delta");
    delta.write_file("d", "d");
    delta.jj(&["commit", "-m", "unrelated"]);
    let mut asking = join_request(&delta);
    asking.choice = JoinChoice::Hive("project".to_owned());
    let err = join(&*client, asking).await.unwrap_err();
    assert!(err.contains("shares no history"), "{err}");

    // Per-hive requests reach their own hive, and only hives the hub has.
    sync(&alpha, client.clone(), &hive).await;
    let reply = client
        .request(
            &format!("musubi.{}.rpc", uuid_like()),
            Bytes::from(Envelope::encode(HubReply::Error(String::new())).unwrap()),
            TIMEOUT,
        )
        .await
        .unwrap();
    let HubReply::Error(message) = Envelope::<HubReply>::decode(&reply).unwrap() else {
        panic!("expected an error");
    };
    assert!(message.contains("no hive"), "{message}");

    // Listing, resolving, renaming, removing.
    let HubWideReply::Hives(hives) = hub_wide(&*client, HubWideRequest::List).await else {
        panic!("expected hives");
    };
    let names: Vec<&str> = hives.iter().map(|h| h.name.as_str()).collect();
    assert_eq!(names, ["fork/project", "project"]);
    let project = hives.iter().find(|h| h.name == "project").unwrap();
    assert!(
        project
            .urls
            .contains(&"https://example.com/team/project.git".to_owned()),
        "{project:?}"
    );
    let rename = HubWideRequest::Rename {
        name: "fork".to_owned(),
        to: "project".to_owned(),
    };
    assert!(matches!(
        hub_wide(&*client, rename).await,
        HubWideReply::Error(m) if m.contains("already")
    ));
    let rename = HubWideRequest::Rename {
        name: "fork".to_owned(),
        to: "gamma".to_owned(),
    };
    assert!(matches!(hub_wide(&*client, rename).await, HubWideReply::Hive(h) if h.name == "gamma"));
    let remove = HubWideRequest::Remove {
        name: "gamma".to_owned(),
    };
    assert!(matches!(
        hub_wide(&*client, remove).await,
        HubWideReply::Hive(_)
    ));
    let resolve = HubWideRequest::Resolve {
        name: "gamma".to_owned(),
    };
    assert!(matches!(
        hub_wide(&*client, resolve).await,
        HubWideReply::Error(_)
    ));

    // A restarted hub reads its hives back, rebuilding a lost index.
    std::fs::remove_file(dir.join(&hive).join("index.json")).unwrap();
    let reopened = HubServer::open(&dir).unwrap();
    assert_eq!(reopened.hive_count(), 1);
    let index = musubi_hub::index::HiveIndex::load(&dir.join(&hive)).unwrap();
    assert_eq!(index.roots.len(), 1, "{index:?}");
    assert!(
        index.machines.iter().any(|m| m.starts_with("alpha#")),
        "{index:?}"
    );
}

fn uuid_like() -> &'static str {
    "00000000-0000-4000-8000-000000000000"
}

async fn hive_request(transport: &dyn Transport, hive: &str, request: HubRequest) -> HubReply {
    let reply = transport
        .request(
            &format!("musubi.{hive}.rpc"),
            Bytes::from(Envelope::encode(request).unwrap()),
            TIMEOUT,
        )
        .await
        .unwrap();
    Envelope::decode(&reply).unwrap()
}

/// A request that makes the hub panic, as jj-lib does decoding a view with a tag whose
/// target is empty, gets an error reply, and the hive goes on answering.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_request_that_panics_the_hub_gets_an_error() {
    let env = TestEnv::new();
    let dir = env.root().join("hub");
    std::fs::create_dir(&dir).unwrap();
    let network = MemoryNetwork::new(1, 1024 * 1024);
    let server = HubServer::open(&dir).unwrap();
    let (ready_tx, ready_rx) = tokio::sync::oneshot::channel();
    tokio::spawn(server.run(Arc::new(network.connect()), move || {
        ready_tx.send(()).ok();
    }));
    ready_rx.await.unwrap();
    let client: Arc<dyn Transport> = Arc::new(network.connect());
    let alpha = env.init_repo("alpha");
    alpha.write_file("a", "a");
    alpha.jj(&["commit", "-m", "first"]);
    let hive = join(&*client, creating(join_request(&alpha)))
        .await
        .unwrap()
        .hive
        .id;

    // A view whose one tag has a target with nothing in it.
    let view = [0x32, 0x05, 0x0a, 0x01, b't', 0x12, 0x00];
    let bundle = env.root().join("bundle");
    let mut writer = BundleWriter::create(&bundle).unwrap();
    writer.view(&[1; 64], &view).unwrap();
    writer.finish().unwrap();
    let push = Request::Push {
        ops: vec![vec![2; 64]],
        ops_attachment: WireAttachment::Inline(std::fs::read(&bundle).unwrap()),
        objects: WireAttachment::None,
        expected: vec![0; 64],
        new: vec![2; 64],
    };
    match hive_request(&*client, &hive, HubRequest::Protocol(push)).await {
        HubReply::Error(err) => assert!(err.contains("the hub failed"), "{err}"),
        other => panic!("unexpected reply {other:?}"),
    }
    let fetch = Request::Fetch {
        base: vec![0; 64],
        haves: WireAttachment::Haves(vec![]),
    };
    assert!(matches!(
        hive_request(&*client, &hive, HubRequest::Protocol(fetch)).await,
        HubReply::Protocol(Reply::Fetched { .. })
    ));
}
