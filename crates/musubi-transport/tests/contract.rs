//! The behavior musubi relies on, checked against every transport.

#![allow(clippy::unwrap_used)]

use std::io;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::Duration;

use async_trait::async_trait;
use bytes::Bytes;
use musubi_transport::MemoryNetwork;
use musubi_transport::StreamTransport;
use musubi_transport::Transport;
use musubi_transport::TransportError;
use musubi_transport::stream::Connector;
use musubi_transport::stream::Reader;
use musubi_transport::stream::Writer;

const LIMIT: usize = 64 * 1024;

async fn check_contract(a: &dyn Transport, b: &dyn Transport) {
    assert_eq!(a.max_payload(), LIMIT);

    // Publish reaches subscribers.
    let mut sub = b.subscribe("musubi.test.head").await.unwrap();
    tokio::time::sleep(Duration::from_millis(50)).await;
    a.publish("musubi.test.head", Bytes::from_static(b"head"))
        .await
        .unwrap();
    let message = tokio::time::timeout(Duration::from_secs(5), sub.next())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(message.payload, "head");
    assert_eq!(message.subject, "musubi.test.head");

    // Requests get the responder's reply.
    let mut rpc = b.subscribe("musubi.test.rpc").await.unwrap();
    tokio::time::sleep(Duration::from_millis(50)).await;
    let request = a.request(
        "musubi.test.rpc",
        Bytes::from_static(b"ping"),
        Duration::from_secs(5),
    );
    let respond = async {
        let message = rpc.next().await.unwrap();
        assert_eq!(message.payload, "ping");
        b.publish(&message.reply.unwrap(), Bytes::from_static(b"pong"))
            .await
            .unwrap();
    };
    let (reply, ()) = tokio::join!(request, respond);
    assert_eq!(reply.unwrap(), "pong");

    // Wildcards match one token, or the rest.
    let mut one = b.subscribe("wild.*.rpc").await.unwrap();
    let mut rest = b.subscribe("wild.>").await.unwrap();
    tokio::time::sleep(Duration::from_millis(50)).await;
    a.publish("wild.other.rpc", Bytes::from_static(b"wild"))
        .await
        .unwrap();
    a.publish("wild.other.rpc.deeper", Bytes::from_static(b"deep"))
        .await
        .unwrap();
    let received = tokio::time::timeout(Duration::from_secs(5), one.next())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(received.subject, "wild.other.rpc");
    for expected in ["wild.other.rpc", "wild.other.rpc.deeper"] {
        let received = tokio::time::timeout(Duration::from_secs(5), rest.next())
            .await
            .unwrap()
            .unwrap();
        assert_eq!(received.subject, expected);
    }

    // A request nobody listens to fails promptly rather than timing out.
    let err = a
        .request("musubi.test.nobody", Bytes::new(), Duration::from_secs(30))
        .await
        .unwrap_err();
    assert!(matches!(err, TransportError::NoResponders(_)), "{err:?}");

    // Oversized payloads are refused locally.
    let big = Bytes::from(vec![0; LIMIT + 1]);
    let err = a.publish("musubi.test.head", big).await.unwrap_err();
    assert!(
        matches!(err, TransportError::PayloadTooLarge { .. }),
        "{err:?}"
    );
}

#[tokio::test]
async fn memory_transport_meets_contract() {
    let network = MemoryNetwork::new(1, LIMIT);
    check_contract(&network.connect(), &network.connect()).await;
}

/// Connects to a hub in this process, whose side of each connection relays through the hub's
/// own transport, over an in-memory pipe it can cut.
struct Pipe {
    hub: Arc<dyn Transport>,
    /// What the hub's side says before the hub, as some shells' startup files do over ssh.
    noise: &'static [u8],
    serving: Mutex<Vec<tokio::task::AbortHandle>>,
}

/// What some machines print for every shell, interactive or not.
const GOAT: &[u8] = b"\x1b[1;33m      _))\n     > *\\     _~\n     `;'\\\\__-' \\_\n\
                      Welcome to musubi-linux, home of the goat.\n\x1b[0m\
                      Last login: never (and no newline after this)";

impl Pipe {
    fn new(hub: Arc<dyn Transport>) -> Arc<Self> {
        Self::noisy(hub, b"")
    }

    fn noisy(hub: Arc<dyn Transport>, noise: &'static [u8]) -> Arc<Self> {
        Arc::new(Self {
            hub,
            noise,
            serving: Mutex::new(vec![]),
        })
    }

    /// Ends every connection, as a link failing does.
    fn cut(&self) {
        for task in self.serving.lock().unwrap().drain(..) {
            task.abort();
        }
    }
}

#[async_trait]
impl Connector for Pipe {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        let (ours, theirs) = tokio::io::duplex(64 * 1024);
        let (reader, mut writer) = tokio::io::split(theirs);
        let (hub, noise) = (self.hub.clone(), self.noise);
        let serving = tokio::spawn(async move {
            use tokio::io::AsyncWriteExt as _;
            writer.write_all(noise).await?;
            musubi_transport::stream::serve(hub, reader, writer).await
        });
        self.serving.lock().unwrap().push(serving.abort_handle());
        let (reader, writer) = tokio::io::split(ours);
        Ok((Box::new(reader), Box::new(writer)))
    }
}

#[tokio::test]
async fn stream_transport_meets_contract() {
    let network = MemoryNetwork::new(1, LIMIT);
    let pipe = Pipe::new(Arc::new(network.connect()));
    let a = StreamTransport::connect(pipe.clone()).await.unwrap();
    let b = StreamTransport::connect(pipe).await.unwrap();
    check_contract(&a, &b).await;
}

/// What the hub's machine prints before the hub, as a shell's startup files can over ssh, is
/// passed over.
#[tokio::test]
async fn stream_transport_passes_over_login_noise() {
    let network = MemoryNetwork::new(1, LIMIT);
    let pipe = Pipe::noisy(Arc::new(network.connect()), GOAT);
    let a = StreamTransport::connect(pipe.clone()).await.unwrap();
    let b = StreamTransport::connect(pipe).await.unwrap();
    check_contract(&a, &b).await;
}

/// A connection that ends fails the requests in flight on it at once, and the transport
/// connects again, subscribed as before; requests made meanwhile wait for the connection.
#[tokio::test]
async fn stream_transport_reconnects() {
    let network = MemoryNetwork::new(1, LIMIT);
    let hub = network.connect();
    let pipe = Pipe::new(Arc::new(network.connect()));
    let client = StreamTransport::connect(pipe.clone()).await.unwrap();
    let mut reconnections = client.reconnections();
    let mut heads = client.subscribe("musubi.test.head").await.unwrap();
    // Asked, but never answered.
    let _rpc = hub.subscribe("musubi.test.rpc").await.unwrap();
    tokio::time::sleep(Duration::from_millis(50)).await;
    let request = client.request("musubi.test.rpc", Bytes::new(), Duration::from_secs(30));
    let cut = async {
        tokio::time::sleep(Duration::from_millis(50)).await;
        pipe.cut();
    };
    let (result, ()) = tokio::join!(request, cut);
    assert!(
        matches!(result, Err(TransportError::Disconnected)),
        "{result:?}"
    );
    tokio::time::timeout(Duration::from_secs(5), reconnections.next())
        .await
        .unwrap();
    // The subscription is back once a message on the new connection gets through.
    let mut answering = hub.subscribe("musubi.test.echo").await.unwrap();
    tokio::spawn(async move {
        while let Some(message) = answering.next().await {
            let reply = message.reply.unwrap();
            hub.publish(&reply, message.payload).await.unwrap();
            hub.publish("musubi.test.head", Bytes::from_static(b"head"))
                .await
                .unwrap();
        }
    });
    let reply = client
        .request(
            "musubi.test.echo",
            Bytes::from_static(b"echo"),
            Duration::from_secs(5),
        )
        .await
        .unwrap();
    assert_eq!(reply, "echo");
    let head = tokio::time::timeout(Duration::from_secs(5), heads.next())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(head.payload, "head");
}

/// What answers must greet as a hub of this version, after no more than so much noise, or
/// connecting fails at once rather than retrying, and the connector hears why.
#[tokio::test]
async fn stream_transport_refuses_what_is_not_a_hub() {
    struct Talker(Vec<u8>, Mutex<Option<String>>);
    #[async_trait]
    impl Connector for Talker {
        fn not_hub(&self, why: &io::Error) {
            *self.1.lock().unwrap() = Some(why.to_string());
        }

        async fn connect(&self) -> io::Result<(Reader, Writer)> {
            let (ours, mut theirs) = tokio::io::duplex(1024);
            let said = self.0.clone();
            tokio::spawn(async move {
                use tokio::io::AsyncWriteExt as _;
                theirs.write_all(&said).await.ok();
                tokio::time::sleep(Duration::from_secs(60)).await;
            });
            let (reader, writer) = tokio::io::split(ours);
            Ok((Box::new(reader), Box::new(writer)))
        }
    }
    let banner = "Unauthorized access is prohibited.\n".repeat(2000);
    for (said, expected) in [
        (banner.into_bytes(), "not a musubi hub"),
        (b"motd\n\0musubi2\n\0\0\x10\0".to_vec(), "another version"),
        (b"\0musubi1\n\0\0\0\0".to_vec(), "up to 0 bytes"),
    ] {
        let talker = Arc::new(Talker(said, Mutex::new(None)));
        let err = tokio::time::timeout(
            Duration::from_secs(5),
            StreamTransport::connect(talker.clone()),
        )
        .await
        .unwrap()
        .err()
        .unwrap();
        assert!(err.to_string().contains(expected), "{err}");
        let told = talker.1.lock().unwrap().clone().unwrap_or_default();
        assert!(told.contains(expected), "{told}");
    }
}
