//! The behavior musubi relies on, checked against every transport.

#![allow(clippy::unwrap_used)]

use std::time::Duration;

use bytes::Bytes;
use musubi_testutil::NatsServer;
use musubi_transport::MemoryNetwork;
use musubi_transport::NatsTransport;
use musubi_transport::Transport;
use musubi_transport::TransportError;

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

#[tokio::test]
async fn nats_transport_meets_contract() {
    let server = NatsServer::start(LIMIT);
    let a = NatsTransport::connect(&server.url()).await.unwrap();
    let b = NatsTransport::connect(&server.url()).await.unwrap();
    check_contract(&a, &b).await;
}

#[tokio::test]
async fn memory_partition_cuts_both_directions() {
    let network = MemoryNetwork::new(1, LIMIT);
    let (a, b) = (network.connect(), network.connect());
    let mut sub = b.subscribe("s").await.unwrap();
    network.partition(&a);
    assert!(matches!(
        a.publish("s", Bytes::new()).await,
        Err(TransportError::Disconnected)
    ));
    network.heal(&a);
    network.partition(&b);
    a.publish("s", Bytes::from_static(b"lost")).await.unwrap();
    network.heal(&b);
    a.publish("s", Bytes::from_static(b"kept")).await.unwrap();
    assert_eq!(sub.next().await.unwrap().payload, "kept");
}
