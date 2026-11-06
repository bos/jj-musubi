//! Command-side errors and deadlines, using the same transport as the hub service.

#![allow(clippy::unwrap_used)]

use super::*;

fn connection(network: &MemoryNetwork, dir: &Path) -> Connection {
    Connection {
        transport: Arc::new(network.connect()),
        place: Place::Local(dir.to_owned()),
    }
}

#[tokio::test(start_paused = true)]
async fn a_missing_local_hub_fails_before_waiting_for_a_connection() {
    let dir = musubi_testutil::tempdir();
    // Both a directory that was never a hub and one whose hub has stopped.
    for marked in [false, true] {
        if marked {
            HubSettings::default().save(dir.path()).unwrap();
        }
        let before = tokio::time::Instant::now();
        let result = connect(dir.path().to_str().unwrap(), Duration::from_secs(60)).await;
        assert_eq!(tokio::time::Instant::now(), before);
        let err = result.err().expect("no hub is listening");
        assert_eq!(
            err.to_string(),
            format!("no hub is serving {}", dir.path().display())
        );
        let network = MemoryNetwork::new(0, MAX_PAYLOAD);
        let connection = connection(&network, dir.path());
        assert_eq!(connection.out_of_reach().await, Some(err.to_string()));
    }
}

#[tokio::test(start_paused = true)]
async fn hub_requests_report_missing_responders_and_refusals() {
    let network = MemoryNetwork::new(0, MAX_PAYLOAD);
    let connection = connection(&network, Path::new("/unused"));
    let err = ask_within(
        &connection,
        "test-hub",
        HubWideRequest::List,
        Duration::from_secs(1),
    )
    .await
    .unwrap_err();
    assert_eq!(err.to_string(), "no hub is serving at test-hub");

    let server = network.connect();
    let mut requests = server.subscribe(&rpc_subject(HUB_TOKEN)).await.unwrap();
    let answer = async {
        let request = requests.next().await.unwrap();
        assert!(matches!(
            Envelope::decode(&request.payload).unwrap(),
            HubWideRequest::List
        ));
        server
            .publish(
                &request.reply.unwrap(),
                Envelope::encode(HubWideReply::Error("hub refused the request".to_owned()))
                    .unwrap()
                    .into(),
            )
            .await
            .unwrap();
    };
    let (result, ()) = tokio::time::timeout(Duration::from_secs(2), async {
        tokio::join!(
            ask_within(
                &connection,
                "test-hub",
                HubWideRequest::List,
                Duration::from_secs(1)
            ),
            answer,
        )
    })
    .await
    .expect("the request must reach its responder");
    assert_eq!(result.unwrap_err().to_string(), "hub refused the request");
}

#[tokio::test(start_paused = true)]
async fn hub_requests_obey_the_callers_deadline() {
    let network = MemoryNetwork::new(0, MAX_PAYLOAD);
    let connection = connection(&network, Path::new("/unused"));
    // A listener receives the request but never answers it.
    let _requests = network
        .connect()
        .subscribe(&rpc_subject(HUB_TOKEN))
        .await
        .unwrap();
    let before = tokio::time::Instant::now();
    let limit = Duration::from_secs(7);
    let err = ask_within(&connection, "test-hub", HubWideRequest::List, limit)
        .await
        .unwrap_err();
    assert_eq!(tokio::time::Instant::now() - before, limit);
    assert_eq!(err.to_string(), "asking the hub");
    assert!(matches!(
        err.downcast_ref::<TransportError>(),
        Some(TransportError::Timeout)
    ));
}
