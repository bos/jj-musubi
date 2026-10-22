//! What the protocol tests never send: malformed requests, and a link that dies or stalls
//! partway through a sync (docs/testing.md, "Faults").
//!
//! The protocol tests deliver well-formed messages, and lose, duplicate, or delay whole ones.
//! Here the hub takes requests no honest node sends, built from a real session's: cut short,
//! corrupted, spliced, pointing at the wrong blobs, from another version. And a real node's
//! link fails partway through a sync, as when the wifi goes off or a laptop's lid closes,
//! while the hub hears such requests and another machine carries on.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::time::Duration;
use std::time::SystemTime;

use bytes::Bytes;
use hegel::HealthCheck;
use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use musubi_core::hub::HubStorage as _;
use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_jj::node::NodeRepo;
use musubi_jj::objects::Backend;
use musubi_sync::Attachment;
use musubi_sync::OpId;
use musubi_sync::blobs::BlobId;
use musubi_sync::driver::NodeDriver;
use musubi_sync::hub::HubAdapter;
use musubi_sync::remote::RemoteHub;
use musubi_sync::service::HubService;
use musubi_sync::wire::Envelope;
use musubi_sync::wire::HubReply;
use musubi_sync::wire::HubRequest;
use musubi_sync::wire::WireAttachment;
use musubi_sync::wire::WireRequest;
use musubi_sync::wire::chunk_size;
use musubi_sync::wire::fit_error;
use musubi_sync::wire::map_reply;
use musubi_sync::wire::map_request;
use musubi_testutil::TestEnv;
use musubi_testutil::TestRepo;
use musubi_testutil::copy_tree;
use musubi_transport::MemoryNetwork;
use musubi_transport::Subscription;
use musubi_transport::Transport;
use musubi_transport::TransportError;

const RPC: &str = "musubi.test.rpc";
const HEAD: &str = "musubi.test.head";

/// Small, so that bundles travel as blobs of several chunks, more than a window of them.
const MAX_PAYLOAD: usize = 4096;

const TIMEOUT: Duration = Duration::from_secs(10);

/// How many requests a node may send once its link works. A sync here takes a few dozen; a
/// node that keeps sending without getting anywhere runs past this.
const RUNAWAY: usize = 2000;

/// The hub answers every request without panicking, with a reply that fits the transport,
/// its head only ever moves forward to an operation whose closure it has, and afterwards it
/// still answers a fetch from the root, which reads everything up to its head.
#[hegel::test(test_cases = 50, suppress_health_check = [HealthCheck::TooSlow])]
fn hub_survives_malformed_requests(tc: TestCase) {
    let session = session();
    let dir = tempfile::tempdir().unwrap();
    // Partway through a real session: blobs half uploaded, the head moved or not.
    let replayed = tc.draw(gs::integers::<usize>().max_value(session.seen.requests.len()));
    let mut hub = session.hub_after(replayed, &dir.path().join("hub"));
    for _ in 0..tc.draw(gs::integers::<usize>().min_value(1).max_value(6)) {
        let heads = heads(&hub, session);
        for request in malformed(&tc, &session.seen, &heads) {
            let before = hub.hub().head();
            let reply = match hub.handle_bytes(&request, MAX_PAYLOAD) {
                Ok((reply, _)) => reply,
                // As `HubService::run` and the hub's server answer an error.
                Err(err) => {
                    let error = fit_error(format!("{err:#}"), MAX_PAYLOAD);
                    Envelope::encode(HubReply::Error(error)).unwrap()
                }
            };
            assert!(reply.len() <= MAX_PAYLOAD, "a {}-byte reply", reply.len());
            Envelope::<HubReply>::decode(&reply).unwrap();
            check_head(&hub, &before);
        }
    }
    // Nothing it stored on the way keeps it from reading everything up to its head.
    let root = hub.hub().store().canonical().root_operation_id().to_bytes();
    let fetch = encode(HubRequest::Protocol(Request::Fetch {
        base: root,
        haves: WireAttachment::None,
    }));
    let (reply, _) = hub.handle_bytes(&fetch, MAX_PAYLOAD).unwrap();
    match Envelope::<HubReply>::decode(&reply).unwrap() {
        HubReply::Protocol(Reply::Fetched { head, .. }) => {
            assert_eq!(head, hub.hub().head().1.to_bytes());
        }
        HubReply::Indirect { .. } => {}
        other => panic!("a fetch from scratch got {other:?}"),
    }
}

/// A call whose link fails partway, in any of the ways a link fails, gets the reply it
/// would have had once the link is back and the call is made again, without sending
/// requests forever, while the hub hears malformed requests made from what the node sent.
/// Each case is one call of the session: a push and its uploads, or a fetch and its
/// downloads, from the hub's state just before it. A malformed push can still be a valid
/// one, though, and move the head; then the call need only succeed.
#[hegel::test(test_cases = 50, suppress_health_check = [HealthCheck::TooSlow])]
fn calls_finish_once_the_link_is_back(tc: TestCase) {
    let session = session();
    let call = pick(&tc, &session.calls);
    let at = tc.draw(gs::integers::<usize>().max_value(call.requests));
    let fault = tc.draw(gs::sampled_from(vec![
        Fault::Lost,
        Fault::ReplyLost,
        Fault::Stall,
    ]));
    run_local(async {
        let dir = tempfile::tempdir().unwrap();
        let hub_dir = dir.path().join("hub");
        let network = MemoryNetwork::new(1, MAX_PAYLOAD);
        let hub = session.hub_after(call.start, &hub_dir);
        serve(hub, Arc::new(network.connect())).await;
        let link = Link::new(Arc::new(network.connect()), &hub_dir, Some((at, fault)));
        let blobs = dir.path().join("node");
        let remote = RemoteHub::new(link.clone(), RPC.into(), &blobs, TIMEOUT).unwrap();
        let mut reply = remote.call(call.request(&session.seen, &blobs)).await;
        link.check_progress();
        let mut moved = false;
        if reply.is_err() {
            let seen = Seen::new(link.sent());
            let stranger = network.connect();
            for _ in 0..tc.draw(gs::integers::<usize>().max_value(3)) {
                for request in malformed(&tc, &seen, &[]) {
                    let reply = stranger.request(RPC, request.into(), TIMEOUT).await;
                    if let Ok(reply) = reply
                        && let Ok(HubReply::Protocol(Reply::Head {
                            kind: HeadKind::Accepted,
                            ..
                        })) = Envelope::decode(&reply)
                    {
                        moved = true;
                    }
                }
            }
            if tc.draw(gs::booleans()) {
                an_hour_passes(&hub_dir);
            }
            link.heal();
            reply = remote.call(call.request(&session.seen, &blobs)).await;
            link.check_progress();
        }
        let reply = map_reply(reply.unwrap(), |id| id.to_bytes(), |_| Ok(())).unwrap();
        if !moved {
            assert_eq!(reply, call.reply);
        }
    });
}

/// A node whose link fails partway through a sync gets its work to the hub once the link
/// is back, as the daemon retries, while the hub hears malformed requests and another
/// machine syncs. Slow, so fewer cases: [`calls_finish_once_the_link_is_back`] explores the
/// faults.
#[hegel::test(test_cases = 6, suppress_health_check = [HealthCheck::TooSlow])]
fn node_recovers_when_its_link_fails_partway(tc: TestCase) {
    run_local(async {
        let env = TestEnv::new();
        let alpha = env.init_repo("alpha");
        let beta = env.init_repo("beta");
        let hub_dir = env.root().join("hub");
        let network = MemoryNetwork::new(1, MAX_PAYLOAD);
        serve(fresh_hub(&hub_dir), Arc::new(network.connect())).await;
        let mut beta_node = driver(&beta, Arc::new(network.connect()));
        big_commit(&beta, "from beta");
        beta_node.sync().await.unwrap();

        // alpha downloads beta's commit and uploads its own, each several windows of chunks.
        big_commit(&alpha, "from alpha");
        let at = tc.draw(gs::integers::<usize>().max_value(50));
        let fault = tc.draw(gs::sampled_from(vec![
            Fault::Lost,
            Fault::ReplyLost,
            Fault::Stall,
        ]));
        let link = Link::new(Arc::new(network.connect()), &hub_dir, Some((at, fault)));
        let mut alpha_node = driver(&alpha, link.clone());
        // It fails, unless the fault comes after its last request or it gets past it.
        let failed = alpha_node.sync().await.is_err();
        link.check_progress();

        let seen = Seen::new(link.sent());
        let stranger = network.connect();
        for _ in 0..tc.draw(gs::integers::<usize>().max_value(3)) {
            for request in malformed(&tc, &seen, &[]) {
                stranger.request(RPC, request.into(), TIMEOUT).await.ok();
            }
        }
        beta.write_file("more", "more");
        beta.jj(&["commit", "-m", "more from beta"]);
        beta_node.sync().await.unwrap();
        if tc.draw(gs::booleans()) {
            an_hour_passes(&hub_dir);
        }

        link.heal();
        if failed {
            // As the daemon does after a failed sync.
            alpha_node.restart();
        }
        for attempt in 0.. {
            let synced = alpha_node.sync().await;
            link.check_progress();
            match synced {
                Ok(_) => break,
                Err(err) if attempt < 5 => {
                    eprintln!("sync attempt {attempt} failed: {err:#}");
                    alpha_node.restart();
                }
                Err(err) => panic!("alpha never synced again: {err:#}"),
            }
        }
        beta_node.sync().await.unwrap();
        assert_eq!(visible(&alpha), visible(&beta));
        assert!(visible(&beta).contains("from alpha"));
    });
}

/// A blob the hub prepares again, for another reply with the same content, lasts as long as
/// one it prepares for the first time, however old it is, and whether another download of
/// it finished just before or finishes during this one: the hub neither sweeps it as old
/// nor forgets it as downloaded while a node downloads it again. The stalls above sweep
/// every blob at once, so they never meet a blob prepared twice.
#[test]
fn blobs_prepared_again_last_as_long_as_new_ones() {
    let session = session();
    // A fetch with downloads: the objects it brings travel as a blob.
    let call = session
        .calls
        .iter()
        .find(|call| matches!(call.request, Request::Fetch { .. }) && call.requests > 1)
        .unwrap();
    let dir = tempfile::tempdir().unwrap();
    let hub_dir = dir.path().join("hub");
    // Short enough to wait out, as the minute the hub keeps a blob it has served.
    let served_lifetime = Duration::from_secs(1);
    let mut hub = session
        .hub_after(call.start, &hub_dir)
        .with_served_blob_lifetime(served_lifetime);
    let fetch = encode(HubRequest::Protocol(call.request.clone()));
    let (blob, len) = prepare(&mut hub, &fetch);
    download(&mut hub, blob, len);

    // Just after, another node's fetch gets the same blob, prepared long ago as far as the
    // sweep can tell.
    let file = hub_dir.join("blobs/prepared/complete").join(blob.hex());
    std::fs::File::options()
        .write(true)
        .open(file)
        .unwrap()
        .set_modified(SystemTime::now() - Duration::from_secs(2 * 3600))
        .unwrap();
    assert_eq!(prepare(&mut hub, &fetch), (blob, len));
    std::thread::sleep(served_lifetime);
    // It downloads slowly enough that the hub sweeps, as it does every hundred requests.
    for _ in 0..100 {
        chunk(&mut hub, blob, 0);
    }

    // Before it finishes, a third node's fetch gets the same blob. Then the second node
    // finishes, and the third downloads at a steady pace for longer than the hub keeps a
    // blob after its last chunk is served.
    assert_eq!(prepare(&mut hub, &fetch), (blob, len));
    download(&mut hub, blob, len);
    for _ in 0..11 {
        std::thread::sleep(served_lifetime / 10);
        chunk(&mut hub, blob, 0);
    }
    download(&mut hub, blob, len);
}

/// A node may upload a bundle with the same content as a blob the hub prepared for another
/// node's download, as a push of what the other node fetched. Its upload is its own: the
/// hub deletes it once it has the push, and the blob for the download stays.
#[test]
fn uploads_leave_prepared_blobs_alone() {
    let session = session();
    let fetch_call = session
        .calls
        .iter()
        .find(|call| matches!(call.request, Request::Fetch { .. }) && call.requests > 1)
        .unwrap();
    // A push that uploads its objects.
    let push_call = session
        .calls
        .iter()
        .find(|call| matches!(call.request, Request::Push { .. }) && call.requests > 1)
        .unwrap();
    let dir = tempfile::tempdir().unwrap();
    let mut hub = session.hub_after(fetch_call.start, &dir.path().join("hub"));
    let fetch = encode(HubRequest::Protocol(fetch_call.request.clone()));
    let (blob, len) = prepare(&mut hub, &fetch);
    let content = download(&mut hub, blob, len);

    // Another node pushes the same content.
    for request in upload(&content) {
        hub.handle_bytes(&request, MAX_PAYLOAD).unwrap();
    }
    let push = map_request(
        push_call.request.clone(),
        |id| id,
        |attachment| {
            Ok(match attachment {
                WireAttachment::Blob { .. } => WireAttachment::Blob { blob, len },
                other => other,
            })
        },
    )
    .unwrap();
    hub.handle_bytes(&encode(HubRequest::Protocol(push)), MAX_PAYLOAD)
        .ok();
    let upload = dir.path().join("hub/blobs/complete").join(blob.hex());
    assert!(!upload.exists(), "the hub kept the push's upload");
    // The first node asks again, as when a reply was lost.
    download(&mut hub, blob, len);
}

/// A node removes what it put in its blob store to upload, however the call ends: when the
/// link fails partway through the upload, and when the call is dropped partway, as the
/// daemon drops a sync when the connection to the hub comes back.
#[test]
fn calls_leave_no_uploads_behind() {
    let session = session();
    // A push that uploads its objects.
    let call = session
        .calls
        .iter()
        .find(|call| matches!(call.request, Request::Push { .. }) && call.requests > 1)
        .unwrap();
    run_local(async {
        let dir = tempfile::tempdir().unwrap();
        let hub_dir = dir.path().join("hub");
        let network = MemoryNetwork::new(1, MAX_PAYLOAD);
        serve(
            session.hub_after(call.start, &hub_dir),
            Arc::new(network.connect()),
        )
        .await;
        let blobs = dir.path().join("node");
        let stored = || std::fs::read_dir(blobs.join("complete")).unwrap().count();

        let link = Link::new(
            Arc::new(network.connect()),
            &hub_dir,
            Some((1, Fault::Lost)),
        );
        let remote = RemoteHub::new(link, RPC.into(), &blobs, TIMEOUT).unwrap();
        let reply = remote.call(call.request(&session.seen, &blobs)).await;
        assert!(reply.is_err());
        assert_eq!(stored(), 0);

        let remote =
            RemoteHub::new(Arc::new(network.connect()), RPC.into(), &blobs, TIMEOUT).unwrap();
        let mut reply = Box::pin(remote.call(call.request(&session.seen, &blobs)));
        // The hub can't answer until this yields, so the upload has begun and waits.
        assert!(futures::poll!(reply.as_mut()).is_pending());
        assert!(stored() > 0);
        drop(reply);
        assert_eq!(stored(), 0);
    });
}

/// A node deletes what it downloads once it is done with it, however the call ends: when
/// the link fails partway through the call's second download, when the call is dropped
/// there, and when it succeeds, once the reply is dropped. A partial download stays for a
/// later call to resume, until it has gone a day untouched.
#[test]
fn calls_leave_no_downloads_behind() {
    let session = session();
    // A fetch with two downloads, and the request that begins the second.
    let (call, second) = session
        .calls
        .iter()
        .find_map(|call| {
            let requests = &session.seen.requests[call.start..call.start + call.requests];
            let mut downloads = requests.iter().enumerate().filter_map(|(n, bytes)| {
                match Envelope::decode(bytes) {
                    Ok(HubRequest::GetChunk { blob, .. }) => Some((n, blob)),
                    _ => None,
                }
            });
            let (_, first) = downloads.next()?;
            let (second, _) = downloads.find(|(_, blob)| *blob != first)?;
            Some((call, second))
        })
        .unwrap();
    run_local(async {
        let dir = tempfile::tempdir().unwrap();
        let hub_dir = dir.path().join("hub");
        let network = MemoryNetwork::new(1, MAX_PAYLOAD);
        serve(
            session.hub_after(call.start, &hub_dir),
            Arc::new(network.connect()),
        )
        .await;
        let blobs = dir.path().join("node");
        let stored = |sub: &str| std::fs::read_dir(blobs.join(sub)).unwrap().count();
        let failing = |at| {
            let link = Link::new(
                Arc::new(network.connect()),
                &hub_dir,
                Some((at, Fault::Lost)),
            );
            RemoteHub::new(link, RPC.into(), &blobs, TIMEOUT).unwrap()
        };

        // The link fails just after the second download's first chunk.
        let reply = failing(second + 1)
            .call(call.request(&session.seen, &blobs))
            .await;
        assert!(reply.is_err());
        assert_eq!(stored("complete"), 0);
        assert_eq!(stored("partial"), 1);
        // A later call keeps the partial download until it has gone a day untouched.
        let request = call.request(&session.seen, &blobs);
        assert!(failing(0).call(request).await.is_err());
        assert_eq!(stored("partial"), 1);
        let partial = std::fs::read_dir(blobs.join("partial"))
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        std::fs::File::options()
            .write(true)
            .open(partial)
            .unwrap()
            .set_modified(SystemTime::now() - Duration::from_secs(2 * 24 * 3600))
            .unwrap();
        let request = call.request(&session.seen, &blobs);
        assert!(failing(0).call(request).await.is_err());
        assert_eq!(stored("partial"), 0);

        let remote =
            RemoteHub::new(Arc::new(network.connect()), RPC.into(), &blobs, TIMEOUT).unwrap();
        let mut reply = Box::pin(remote.call(call.request(&session.seen, &blobs)));
        // Until the first download is done, and the second waits on the hub.
        while stored("complete") == 0 {
            assert!(futures::poll!(reply.as_mut()).is_pending());
            tokio::task::yield_now().await;
        }
        drop(reply);
        assert_eq!(stored("complete"), 0);

        let reply = remote
            .call(call.request(&session.seen, &blobs))
            .await
            .unwrap();
        assert_eq!(stored("complete"), 2);
        drop(reply);
        assert_eq!(stored("complete"), 0);
    });
}

/// How a [`Link`] fails, from a given request on.
#[derive(Clone, Copy, Debug)]
enum Fault {
    /// The request and every later one never reach the hub: the wifi is off.
    Lost,
    /// The request reaches the hub, but its reply and every later request are lost: the
    /// lid closed just after it went.
    ReplyLost,
    /// Before the request arrives, an hour passes, and the hub gives up on the node's
    /// transfers in progress; then the link carries on, as when the lid opens again.
    Stall,
}

/// A node's link to the hub: it records what the node sends, and fails as told.
struct Link {
    inner: Arc<dyn Transport>,
    hub_dir: PathBuf,
    state: Mutex<LinkState>,
}

struct LinkState {
    sent: Vec<Vec<u8>>,
    /// The replies that came back, by request.
    replies: BTreeMap<usize, Vec<u8>>,
    fault: Option<(usize, Fault)>,
    since_healed: usize,
}

impl Link {
    fn new(inner: Arc<dyn Transport>, hub_dir: &Path, fault: Option<(usize, Fault)>) -> Arc<Self> {
        Arc::new(Self {
            inner,
            hub_dir: hub_dir.to_owned(),
            state: Mutex::new(LinkState {
                sent: vec![],
                replies: BTreeMap::new(),
                fault,
                since_healed: 0,
            }),
        })
    }

    fn sent(&self) -> Vec<Vec<u8>> {
        self.state.lock().unwrap().sent.clone()
    }

    fn replies(&self) -> BTreeMap<usize, Vec<u8>> {
        self.state.lock().unwrap().replies.clone()
    }

    fn heal(&self) {
        let mut state = self.state.lock().unwrap();
        state.fault = None;
        state.since_healed = 0;
    }

    fn check_progress(&self) {
        let since_healed = self.state.lock().unwrap().since_healed;
        assert!(
            since_healed <= RUNAWAY,
            "the node sent {since_healed} requests without finishing: it never starts over"
        );
    }
}

#[async_trait::async_trait]
impl Transport for Link {
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
        let (n, fault) = {
            let mut state = self.state.lock().unwrap();
            state.sent.push(payload.to_vec());
            state.since_healed += 1;
            if state.since_healed > RUNAWAY {
                return Err(TransportError::Other("runaway".to_owned()));
            }
            (state.sent.len() - 1, state.fault)
        };
        let reply = match fault {
            Some((at, Fault::Lost)) if n >= at => Err(TransportError::Timeout),
            Some((at, Fault::ReplyLost)) if n >= at => {
                if n == at {
                    self.inner.request(subject, payload, timeout).await.ok();
                }
                Err(TransportError::Timeout)
            }
            Some((at, Fault::Stall)) if n == at => {
                an_hour_passes(&self.hub_dir);
                self.inner.request(subject, payload, timeout).await
            }
            _ => self.inner.request(subject, payload, timeout).await,
        };
        if let Ok(reply) = &reply {
            self.state.lock().unwrap().replies.insert(n, reply.to_vec());
        }
        reply
    }
}

/// What an hour without a word from a node does at the hub: its sweep removes the
/// transfers in progress, uploads and prepared downloads alike.
fn an_hour_passes(hub_dir: &Path) {
    for store in ["blobs", "blobs/prepared"] {
        for sub in ["partial", "complete"] {
            for entry in std::fs::read_dir(hub_dir.join(store).join(sub)).unwrap() {
                std::fs::remove_file(entry.unwrap().path()).unwrap();
            }
        }
    }
}

/// The requests of a real session: one machine pushes, another fetches that and pushes its
/// own, and the first fetches that.
struct Session {
    seen: Seen,
    calls: Vec<Call>,
    head: Vec<u8>,
    /// The hub's directory as each call starts, `<n>` after the first `n` requests: copying
    /// one is much faster than replaying the requests. Not after every request: a hub is
    /// dozens of files, and while the rest of the suite runs, making thousands of files
    /// takes many times longer than replaying part of a call.
    snapshots: PathBuf,
}

impl Session {
    /// The session recorded in `dir`: its requests, their replies, by request, the head it
    /// ends at, and the hub's snapshots.
    fn load(dir: &Path) -> Self {
        let requests = read_frames(&dir.join("requests"));
        let replies = read_frames(&dir.join("replies"))
            .into_iter()
            .map(|frame| {
                let (n, reply) = frame.split_at(8);
                (
                    u64::from_le_bytes(n.try_into().unwrap()) as usize,
                    reply.to_vec(),
                )
            })
            .collect();
        Self {
            calls: Call::all(&requests, &replies),
            seen: Seen::new(requests),
            head: std::fs::read(dir.join("head")).unwrap(),
            snapshots: dir.join("snapshots"),
        }
    }

    /// A hub in `dir` that has handled the first `n` requests.
    fn hub_after(&self, n: usize, dir: &Path) -> HubService {
        let start = self
            .calls
            .iter()
            .map(|call| call.start)
            .filter(|&start| start <= n)
            .max()
            .unwrap_or(0);
        copy_tree(&self.snapshots.join(start.to_string()), dir);
        let mut hub =
            HubService::new(HubAdapter::open(dir).unwrap(), dir, RPC.into(), HEAD.into()).unwrap();
        for request in &self.seen.requests[start..n] {
            hub.handle_bytes(request, MAX_PAYLOAD).unwrap();
        }
        hub
    }
}

/// A protocol call in a session: `requests` of them from `start`, uploading its
/// attachments, then making the call, then downloading the reply's attachments.
struct Call {
    start: usize,
    requests: usize,
    request: WireRequest,
    /// The reply, without its attachments.
    reply: Reply<Vec<u8>, ()>,
}

impl Call {
    /// The calls of a session's requests.
    fn all(requests: &[Vec<u8>], replies: &BTreeMap<usize, Vec<u8>>) -> Vec<Self> {
        let requests: Vec<HubRequest> = requests
            .iter()
            .map(|bytes| Envelope::decode(bytes).unwrap())
            .collect();
        let mut calls = vec![];
        let mut start = 0;
        for (n, request) in requests.iter().enumerate() {
            let HubRequest::Protocol(request) = request else {
                continue;
            };
            let Ok(HubReply::Protocol(reply)) = Envelope::decode(&replies[&n]) else {
                panic!("request {n} of the session failed");
            };
            let downloads = requests[n + 1..]
                .iter()
                .take_while(|request| matches!(request, HubRequest::GetChunk { .. }))
                .count();
            let end = n + 1 + downloads;
            calls.push(Self {
                start,
                requests: end - start,
                request: request.clone(),
                reply: map_reply(reply, |id| id, |_| Ok(())).unwrap(),
            });
            start = end;
        }
        calls
    }

    /// The call as a node makes it, its attachments in files in `dir`.
    fn request(&self, seen: &Seen, dir: &Path) -> Request<OpId, Attachment> {
        map_request(self.request.clone(), OpId::new, |attachment| {
            let bytes = match attachment {
                WireAttachment::None => return Ok(Attachment::None),
                WireAttachment::Haves(ids) => {
                    return Ok(Attachment::Haves(
                        ids.into_iter().map(CommitId::new).collect(),
                    ));
                }
                WireAttachment::Inline(bytes) => bytes,
                WireAttachment::Blob { blob, .. } => seen.contents[&blob].clone(),
            };
            let file = tempfile::NamedTempFile::new_in(dir)?;
            std::fs::write(file.path(), bytes)?;
            Ok(Attachment::bundle(file.into_temp_path()))
        })
        .unwrap()
    }
}

/// The session, recorded once per build of this test binary (see
/// [`musubi_testutil::recorded`]): every test that uses it would otherwise record it again.
fn session() -> &'static Session {
    static SESSION: OnceLock<Session> = OnceLock::new();
    SESSION.get_or_init(|| {
        let base = Path::new(env!("CARGO_TARGET_TMPDIR"));
        Session::load(&musubi_testutil::recorded(base, "faults-session", record))
    })
}

/// Records a session in `dir`, for [`Session::load`].
fn record(dir: &Path) {
    let mut session = None;
    run_local(async {
        let env = TestEnv::new();
        let alpha = env.init_repo("alpha");
        let beta = env.init_repo("beta");
        let hub_dir = env.root().join("hub");
        let network = MemoryNetwork::new(1, MAX_PAYLOAD);
        serve(fresh_hub(&hub_dir), Arc::new(network.connect())).await;
        let link = Link::new(Arc::new(network.connect()), &hub_dir, None);
        let mut alpha_node = driver(&alpha, link.clone());
        let mut beta_node = driver(&beta, link.clone());
        big_commit(&alpha, "from alpha");
        alpha_node.sync().await.unwrap();
        big_commit(&beta, "from beta");
        beta_node.sync().await.unwrap();
        alpha_node.sync().await.unwrap();
        session = Some((link.sent(), link.replies(), alpha_node.known().1.to_bytes()));
    });
    let (requests, replies, head) = session.unwrap();
    std::fs::create_dir_all(dir).unwrap();
    write_frames(&dir.join("requests"), &requests);
    let replies: Vec<Vec<u8>> = replies
        .into_iter()
        .map(|(n, reply)| [(n as u64).to_le_bytes().as_slice(), &reply].concat())
        .collect();
    write_frames(&dir.join("replies"), &replies);
    std::fs::write(dir.join("head"), &head).unwrap();
    // Replayed, the requests take a fresh hub to the same head, so each snapshot is a
    // state the hub really passes through.
    let snapshots = dir.join("snapshots");
    let calls = Session::load(dir).calls;
    let hub_dir = tempfile::tempdir().unwrap();
    let hub_dir = hub_dir.path().join("hub");
    let mut hub = fresh_hub(&hub_dir);
    let starts: BTreeSet<usize> = calls.iter().map(|call| call.start).collect();
    copy_tree(&hub_dir, &snapshots.join("0"));
    for (n, request) in requests.iter().enumerate() {
        hub.handle_bytes(request, MAX_PAYLOAD).unwrap();
        if starts.contains(&(n + 1)) {
            copy_tree(&hub_dir, &snapshots.join((n + 1).to_string()));
        }
    }
    assert_eq!(hub.hub().head().1.to_bytes(), head);
}

/// Writes `frames` to one file, each after its length.
fn write_frames(path: &Path, frames: &[Vec<u8>]) {
    let mut bytes = vec![];
    for frame in frames {
        bytes.extend_from_slice(&(frame.len() as u64).to_le_bytes());
        bytes.extend_from_slice(frame);
    }
    std::fs::write(path, bytes).unwrap();
}

fn read_frames(path: &Path) -> Vec<Vec<u8>> {
    let bytes = std::fs::read(path).unwrap();
    let mut rest = bytes.as_slice();
    let mut frames = vec![];
    while !rest.is_empty() {
        let (len, tail) = rest.split_at(8);
        let (frame, tail) = tail.split_at(u64::from_le_bytes(len.try_into().unwrap()) as usize);
        frames.push(frame.to_vec());
        rest = tail;
    }
    frames
}

/// What some requests carried, to build malformed ones from.
#[derive(Default)]
struct Seen {
    requests: Vec<Vec<u8>>,
    /// Blobs uploaded or asked for.
    blobs: Vec<BlobId>,
    /// Attachments, and requests sent as blobs, that arrived whole.
    payloads: Vec<Vec<u8>>,
    /// The blobs among them, by id.
    contents: BTreeMap<BlobId, Vec<u8>>,
    pushes: Vec<WireRequest>,
    /// Operation and commit ids.
    ids: Vec<Vec<u8>>,
    /// Offsets, lengths, and totals.
    numbers: Vec<u64>,
}

impl Seen {
    fn new(requests: Vec<Vec<u8>>) -> Self {
        let mut seen = Self::default();
        let mut chunks: BTreeMap<BlobId, BTreeMap<u64, Vec<u8>>> = BTreeMap::new();
        for bytes in &requests {
            let Ok(request) = Envelope::<HubRequest>::decode(bytes) else {
                continue;
            };
            match request {
                HubRequest::PutChunk {
                    blob,
                    total,
                    offset,
                    data,
                } => {
                    seen.numbers.extend([total, offset]);
                    chunks.entry(blob).or_default().insert(offset, data);
                }
                HubRequest::GetChunk { blob, offset, len } => {
                    seen.blobs.push(blob);
                    seen.numbers.extend([offset, len]);
                }
                HubRequest::Indirect { blob } => seen.blobs.push(blob),
                HubRequest::Protocol(request) => {
                    if let Request::Push { .. } = request {
                        seen.pushes.push(request.clone());
                    }
                    let mut attachments = vec![];
                    map_request(
                        request,
                        |id| seen.ids.push(id),
                        |attachment| {
                            attachments.push(attachment);
                            Ok(())
                        },
                    )
                    .unwrap();
                    for attachment in attachments {
                        match attachment {
                            WireAttachment::None => {}
                            WireAttachment::Blob { blob, len } => {
                                seen.blobs.push(blob);
                                seen.numbers.push(len);
                            }
                            WireAttachment::Inline(bytes) => seen.payloads.push(bytes),
                            WireAttachment::Haves(ids) => seen.ids.extend(ids),
                        }
                    }
                }
            }
        }
        for (blob, chunks) in chunks {
            seen.blobs.push(blob);
            let mut content = vec![];
            for (offset, data) in chunks {
                let have = content.len() as u64;
                if offset <= have && offset + data.len() as u64 > have {
                    content.extend_from_slice(&data[usize::try_from(have - offset).unwrap()..]);
                }
            }
            if BlobId::of_bytes(&content) == blob {
                seen.payloads.push(content.clone());
                seen.contents.insert(blob, content);
            }
        }
        seen.blobs.sort();
        seen.blobs.dedup();
        seen.ids.sort();
        seen.ids.dedup();
        seen.numbers.sort_unstable();
        seen.numbers.dedup();
        seen.requests = requests;
        seen
    }
}

/// Requests no honest node sends, built from what `seen` carried, as requests that fit the
/// transport.
fn malformed(tc: &TestCase, seen: &Seen, heads: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let request = match tc.draw(gs::integers::<u8>().max_value(7)) {
        0 => tc.draw(gs::binary().max_size(64)),
        // A real request cut short, corrupted, or spliced.
        1 if !seen.requests.is_empty() => mutate(tc, pick(tc, &seen.requests), seen),
        2 => encode(HubRequest::PutChunk {
            blob: blob(tc, seen),
            total: number(tc, seen),
            offset: number(tc, seen),
            data: tc.draw(gs::binary().max_size(256)),
        }),
        3 => encode(HubRequest::GetChunk {
            blob: blob(tc, seen),
            offset: number(tc, seen),
            len: number(tc, seen),
        }),
        // A request that arrives as a blob, and is itself malformed or indirect.
        4 => {
            let inner = if seen.requests.is_empty() || tc.draw(gs::booleans()) {
                encode(HubRequest::Indirect {
                    blob: blob(tc, seen),
                })
            } else {
                mutate(tc, pick(tc, &seen.requests), seen)
            };
            return as_blob(&inner);
        }
        5 => encode(HubRequest::Protocol(protocol(tc, seen, heads))),
        6 if !seen.pushes.is_empty() => encode(HubRequest::Protocol(damaged_push(tc, seen))),
        // From a peer of another version, whose name for it can be too long to quote whole.
        _ => postcard::to_stdvec(&Envelope {
            protocol: tc.draw(gs::integers::<u32>()),
            jj_lib: tc
                .draw(gs::text().max_size(8))
                .repeat(tc.draw(gs::integers::<usize>().min_value(1).max_value(MAX_PAYLOAD))),
            body: HubRequest::Protocol(protocol(tc, seen, heads)),
        })
        .unwrap(),
    };
    if request.len() <= MAX_PAYLOAD {
        vec![request]
    } else {
        as_blob(&request)
    }
}

/// A real push with its bundles inline, one of them damaged: cut short, as by a connection
/// that died partway through its upload, or corrupted.
fn damaged_push(tc: &TestCase, seen: &Seen) -> WireRequest {
    let damaged = tc.draw(gs::integers::<usize>().max_value(1));
    let mut n = 0;
    map_request(
        pick(tc, &seen.pushes).clone(),
        |id| id,
        |attachment| {
            let bytes = match attachment {
                WireAttachment::Inline(bytes) => bytes,
                WireAttachment::Blob { blob, .. } if seen.contents.contains_key(&blob) => {
                    seen.contents[&blob].clone()
                }
                other => return Ok(other),
            };
            let damage = n == damaged;
            n += 1;
            Ok(WireAttachment::Inline(if damage {
                mutate(tc, &bytes, seen)
            } else {
                bytes
            }))
        },
    )
    .unwrap()
}

/// A protocol request with ids and attachments drawn from what `seen` carried and the
/// hub's `heads`, or made up.
fn protocol(tc: &TestCase, seen: &Seen, heads: &[Vec<u8>]) -> WireRequest {
    let ids = |tc: &TestCase| {
        (0..tc.draw(gs::integers::<usize>().max_value(3)))
            .map(|_| id(tc, seen, heads))
            .collect()
    };
    match tc.draw(gs::integers::<u8>().max_value(2)) {
        0 => Request::Fetch {
            base: id(tc, seen, heads),
            haves: attachment(tc, seen, heads),
        },
        1 => Request::GetObjects {
            for_ops: ids(tc),
            base: id(tc, seen, heads),
            haves: attachment(tc, seen, heads),
        },
        _ => Request::Push {
            ops: ids(tc),
            ops_attachment: attachment(tc, seen, heads),
            objects: attachment(tc, seen, heads),
            expected: id(tc, seen, heads),
            new: id(tc, seen, heads),
        },
    }
}

fn attachment(tc: &TestCase, seen: &Seen, heads: &[Vec<u8>]) -> WireAttachment {
    match tc.draw(gs::integers::<u8>().max_value(3)) {
        0 => WireAttachment::None,
        // A real bundle cut short or corrupted.
        1 if !seen.payloads.is_empty() => {
            WireAttachment::Inline(mutate(tc, pick(tc, &seen.payloads), seen))
        }
        2 => WireAttachment::Blob {
            blob: blob(tc, seen),
            len: number(tc, seen),
        },
        _ => WireAttachment::Haves(
            (0..tc.draw(gs::integers::<usize>().max_value(3)))
                .map(|_| id(tc, seen, heads))
                .collect(),
        ),
    }
}

/// `bytes` with up to three things gone wrong.
fn mutate(tc: &TestCase, bytes: &[u8], seen: &Seen) -> Vec<u8> {
    let mut bytes = bytes.to_vec();
    for _ in 0..tc.draw(gs::integers::<usize>().min_value(1).max_value(3)) {
        let at = tc.draw(gs::integers::<usize>().max_value(bytes.len()));
        match tc.draw(gs::integers::<u8>().max_value(4)) {
            // Cut short, as by a connection that died partway.
            0 => bytes.truncate(at),
            1 if at < bytes.len() => bytes[at] ^= 1 << tc.draw(gs::integers::<u8>().max_value(7)),
            // A length gone wrong: postcard's are varints, a bundle's little-endian u64s.
            2 => {
                let value = number(tc, seen).to_le_bytes();
                let end = (at + 8).min(bytes.len());
                bytes[at..end].copy_from_slice(&value[..end - at]);
            }
            3 => {
                let inserted = tc.draw(gs::binary().max_size(16));
                bytes.splice(at..at, inserted);
            }
            _ => {
                let end = tc.draw(gs::integers::<usize>().min_value(at).max_value(bytes.len()));
                bytes.drain(at..end);
            }
        }
    }
    bytes
}

/// An offset, length, or total: an extreme, one next to a number `seen` carried, or any.
fn number(tc: &TestCase, seen: &Seen) -> u64 {
    match tc.draw(gs::integers::<u8>().max_value(2)) {
        0 => tc.draw(gs::sampled_from(vec![
            0,
            1,
            u64::from(u32::MAX),
            u64::MAX / 2,
            u64::MAX - 1,
            u64::MAX,
        ])),
        1 if !seen.numbers.is_empty() => pick(tc, &seen.numbers)
            .wrapping_add_signed(tc.draw(gs::integers::<i64>().min_value(-2).max_value(2))),
        _ => tc.draw(gs::integers::<u64>()),
    }
}

fn blob(tc: &TestCase, seen: &Seen) -> BlobId {
    if !seen.blobs.is_empty() && tc.draw(gs::booleans()) {
        *pick(tc, &seen.blobs)
    } else {
        BlobId::of_bytes(&tc.draw(gs::binary().max_size(8)))
    }
}

fn id(tc: &TestCase, seen: &Seen, heads: &[Vec<u8>]) -> Vec<u8> {
    match tc.draw(gs::integers::<u8>().max_value(2)) {
        0 if !heads.is_empty() => pick(tc, heads).clone(),
        1 if !seen.ids.is_empty() => pick(tc, &seen.ids).clone(),
        _ => tc.draw(gs::binary().max_size(70)),
    }
}

fn pick<'a, T>(tc: &TestCase, items: &'a [T]) -> &'a T {
    &items[tc.draw(gs::integers::<usize>().max_value(items.len() - 1))]
}

fn encode(request: HubRequest) -> Vec<u8> {
    Envelope::encode(request).unwrap()
}

/// `bytes` uploaded as a blob, then sent as an indirect request.
fn as_blob(bytes: &[u8]) -> Vec<Vec<u8>> {
    let mut requests = upload(bytes);
    requests.push(encode(HubRequest::Indirect {
        blob: BlobId::of_bytes(bytes),
    }));
    requests
}

/// The requests that upload `bytes` as a blob.
fn upload(bytes: &[u8]) -> Vec<Vec<u8>> {
    let blob = BlobId::of_bytes(bytes);
    let chunk = chunk_size(MAX_PAYLOAD);
    bytes
        .chunks(chunk)
        .enumerate()
        .map(|(i, data)| {
            encode(HubRequest::PutChunk {
                blob,
                total: bytes.len() as u64,
                offset: (i * chunk) as u64,
                data: data.to_vec(),
            })
        })
        .collect()
}

/// Makes `fetch`, returning the blob the objects it brings travel as.
fn prepare(hub: &mut HubService, fetch: &[u8]) -> (BlobId, u64) {
    let (reply, _) = hub.handle_bytes(fetch, MAX_PAYLOAD).unwrap();
    let Ok(HubReply::Protocol(reply)) = Envelope::decode(&reply) else {
        panic!("the fetch failed");
    };
    let mut blobs = vec![];
    map_reply(
        reply,
        |id| id,
        |attachment| {
            if let WireAttachment::Blob { blob, len } = attachment {
                blobs.push((blob, len));
            }
            Ok(())
        },
    )
    .unwrap();
    let [blob] = blobs.as_slice() else {
        panic!("the fetch's reply has blobs {blobs:?}");
    };
    *blob
}

/// The chunk of `blob` at `offset`, as a node asks for it.
fn chunk(hub: &mut HubService, blob: BlobId, offset: u64) -> Vec<u8> {
    let request = encode(HubRequest::GetChunk {
        blob,
        offset,
        len: chunk_size(MAX_PAYLOAD) as u64,
    });
    let (reply, _) = hub
        .handle_bytes(&request, MAX_PAYLOAD)
        .unwrap_or_else(|err| panic!("the chunk at {offset}: {err:#}"));
    match Envelope::decode(&reply).unwrap() {
        HubReply::Chunk { data, .. } => data,
        other => panic!("asked for a chunk, got {other:?}"),
    }
}

/// Downloads all of `blob`, a chunk at a time.
fn download(hub: &mut HubService, blob: BlobId, len: u64) -> Vec<u8> {
    let mut content = vec![];
    while (content.len() as u64) < len {
        let data = chunk(hub, blob, content.len() as u64);
        assert!(!data.is_empty(), "the blob ends early");
        content.extend(data);
    }
    assert_eq!(BlobId::of_bytes(&content), blob);
    content
}

/// The ids a malformed request most needs to get anywhere: the hub's head, the root, and
/// where the session left the head.
fn heads(hub: &HubService, session: &Session) -> Vec<Vec<u8>> {
    let canonical = hub.hub().store().canonical();
    vec![
        hub.hub().head().1.to_bytes(),
        canonical.root_operation_id().to_bytes(),
        session.head.clone(),
    ]
}

/// The head moves only forward, to an operation whose closure the hub has (HubMonotone and
/// HubClosed, docs/protocol.md).
fn check_head(hub: &HubService, before: &(u64, OpId)) {
    let adapter = hub.hub();
    let (seq, head) = adapter.head();
    if head == before.1 {
        assert_eq!(seq, before.0);
    } else {
        assert!(
            seq > before.0,
            "the head's seq went from {} to {seq}",
            before.0
        );
        assert!(
            adapter.descends(&before.1, &head).unwrap(),
            "the head moved to an operation that doesn't descend from it"
        );
    }
    assert!(
        adapter.is_closed(&head).unwrap(),
        "the head's closure is incomplete"
    );
}

fn fresh_hub(dir: &Path) -> HubService {
    let adapter = HubAdapter::init(dir, Backend::Git).unwrap();
    HubService::new(adapter, dir, RPC.into(), HEAD.into()).unwrap()
}

/// Starts `service` answering on `transport`, once it is listening.
async fn serve(service: HubService, transport: Arc<dyn Transport>) {
    let (ready, listening) = tokio::sync::oneshot::channel();
    tokio::task::spawn_local(async move {
        service
            .run(transport, || ready.send(()).unwrap())
            .await
            .unwrap();
    });
    listening.await.unwrap();
}

fn driver(repo: &TestRepo, transport: Arc<dyn Transport>) -> NodeDriver {
    let mut node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
    node.create_join_operation(&format!("musubi: {} joins", repo.machine()))
        .unwrap();
    let blobs = repo.repo_path().join("musubi/blobs");
    let remote = RemoteHub::new(transport, RPC.into(), &blobs, TIMEOUT).unwrap();
    NodeDriver::new(node, remote).unwrap()
}

/// Commits a file of incompressible content, several windows of chunks long.
fn big_commit(repo: &TestRepo, message: &str) {
    let mut bytes = vec![0; 48 * 1024];
    blake3::Hasher::new()
        .update(message.as_bytes())
        .finalize_xof()
        .fill(&mut bytes);
    std::fs::write(repo.path().join(message.replace(' ', "-")), bytes).unwrap();
    repo.jj(&["commit", "-m", message]);
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

fn run_local(future: impl Future<Output = ()>) {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();
    tokio::task::LocalSet::new().block_on(&runtime, future);
}
