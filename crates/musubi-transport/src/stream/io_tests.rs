//! Faults at the real async byte-stream boundary, independent of the frame codec fuzzer.

use hegel::TestCase;
use hegel::generators as gs;
use tokio_test::assert_pending;

use super::*;

fn runtime() -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new_current_thread()
        .enable_time()
        .start_paused(true)
        .build()
        .unwrap()
}

/// One connection, then an unavailable hub. No reconnect can hide the first one's result.
struct Once(Mutex<Option<tokio::io::DuplexStream>>);

#[async_trait]
impl Connector for Once {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        let stream = self.0.lock().unwrap().take();
        match stream {
            Some(stream) => {
                let (read, write) = tokio::io::split(stream);
                Ok((Box::new(read), Box::new(write)))
            }
            None => std::future::pending().await,
        }
    }
}

async fn connection() -> (StreamTransport, tokio::io::DuplexStream) {
    // A one-byte pipe forces short reads/writes and Pending on both ends, even in greetings.
    let (stream, mut peer) = tokio::io::duplex(1);
    let connector = Arc::new(Once(Mutex::new(Some(stream))));
    let greet = async {
        peer.write_all(GREETING).await.unwrap();
        peer.write_u32(1024).await.unwrap();
        let mut greeting = [0; GREETING.len()];
        peer.read_exact(&mut greeting).await.unwrap();
        assert_eq!(&greeting, GREETING);
    };
    let (client, ()) = tokio::join!(StreamTransport::connect(connector), greet);
    (client.unwrap(), peer)
}

#[hegel::test(test_cases = 80)]
fn requests_release_their_inbox_at_every_end(tc: TestCase) {
    let end = tc.draw(gs::integers::<u8>().max_value(3));
    let payload = Bytes::from(vec![b'x'; tc.draw(gs::integers::<usize>().max_value(32))]);
    // Include cancellation before any bytes are written, inside the length/fields/payload,
    // and after the whole request. The next frame must still start at its own boundary.
    let len = Frame::Req {
        id: 1,
        timeout: Duration::from_secs(60),
        subject: "rpc".into(),
        payload: payload.clone(),
    }
    .encode()
    .len();
    let cut = tc.draw(gs::integers::<usize>().max_value(len));
    runtime().block_on(async {
        let (client, mut peer) = connection().await;
        let mut call = tokio_test::task::spawn(client.request(
            "rpc",
            payload.clone(),
            Duration::from_secs(60),
        ));
        assert_pending!(call.poll());
        assert_eq!(client.shared.lock().pending.len(), 1);
        let mut bytes = vec![0; len];
        peer.read_exact(&mut bytes[..cut]).await.unwrap();
        if end == 0 {
            drop(call);
            assert!(
                client.shared.lock().pending.is_empty(),
                "canceled request retained its inbox"
            );
        } else {
            match end {
                1 => {
                    tokio::time::advance(Duration::from_secs(60)).await;
                    assert!(matches!(call.await, Err(TransportError::Timeout)));
                }
                2 => {
                    drop(peer);
                    assert!(matches!(call.await, Err(TransportError::Disconnected)));
                    assert!(client.shared.lock().pending.is_empty());
                    return;
                }
                _ => {
                    peer.read_exact(&mut bytes[cut..]).await.unwrap();
                    peer.write_all(
                        &Frame::Reply {
                            id: 1,
                            payload: Bytes::from_static(b"answer"),
                        }
                        .encode(),
                    )
                    .await
                    .unwrap();
                    assert_eq!(call.await.unwrap(), "answer");
                }
            }
            assert!(client.shared.lock().pending.is_empty());
        }
        if end != 3 {
            peer.read_exact(&mut bytes[cut..]).await.unwrap();
        }
        let request = Frame::decode(Bytes::copy_from_slice(&bytes[4..])).unwrap();
        assert!(matches!(request, Frame::Req { id: 1, payload: body, .. } if body == payload));
        let mut fresh =
            tokio_test::task::spawn(client.request("rpc", Bytes::new(), Duration::from_secs(60)));
        assert_pending!(fresh.poll());
        assert!(matches!(
            read_frame(&mut peer, 2048).await.unwrap(),
            Some(Frame::Req { id: 2, .. })
        ));
        // Late and duplicate answers must not finish the newer call.
        for _ in 0..2 {
            peer.write_all(
                &Frame::Reply {
                    id: 1,
                    payload: Bytes::from_static(b"obsolete"),
                }
                .encode(),
            )
            .await
            .unwrap();
        }
        assert_pending!(fresh.poll());
        peer.write_all(
            &Frame::Reply {
                id: 2,
                payload: Bytes::from_static(b"fresh"),
            }
            .encode(),
        )
        .await
        .unwrap();
        assert_eq!(fresh.await.unwrap(), "fresh");
        assert!(client.shared.lock().pending.is_empty());
    });
}

/// No arbitrary bytes here: the codec fuzzer already tests those. Split valid consecutive
/// frames at generated byte boundaries, yielding between fragments, then end or fail the I/O.
#[hegel::test(test_cases = 100)]
fn fragmented_reads_deliver_only_complete_frames(tc: TestCase) {
    let frames = [
        Frame::Reply {
            id: 7,
            payload: Bytes::from_static(b"first"),
        },
        Frame::Fail {
            id: 8,
            code: TIMED_OUT,
            message: String::new(),
        },
        Frame::Msg {
            sid: 9,
            subject: "head".into(),
            reply: None,
            payload: Bytes::from_static(b"last"),
        },
    ];
    let encoded: Vec<_> = frames.iter().map(Frame::encode).collect();
    let bytes = encoded.concat();
    let cut = tc.draw(gs::integers::<usize>().max_value(bytes.len()));
    let width = tc.draw(gs::integers::<usize>().min_value(1).max_value(16));
    let error = tc.draw(gs::booleans());
    runtime().block_on(async {
        let mut script = tokio_test::io::Builder::new();
        for chunk in bytes[..cut].chunks(width) {
            script.read(chunk).wait(Duration::from_millis(1));
        }
        if error {
            script.read_error(io::Error::from(io::ErrorKind::ConnectionReset));
        }
        let mut reader = script.build();
        drop(script);
        let mut consumed = 0;
        for (frame, encoded) in frames.iter().zip(&encoded) {
            let result = read_frame(&mut reader, 2048).await;
            if consumed + encoded.len() <= cut {
                assert_eq!(result.unwrap().as_ref(), Some(frame));
                consumed += encoded.len();
            } else {
                match result {
                    Err(err) => assert_eq!(
                        err.kind(),
                        if error {
                            io::ErrorKind::ConnectionReset
                        } else {
                            io::ErrorKind::UnexpectedEof
                        }
                    ),
                    Ok(None) => assert!(!error && cut - consumed < 4),
                    result => panic!("delivered incomplete frame at {cut}: {result:?}"),
                }
                return;
            }
        }
        let result = read_frame(&mut reader, 2048).await;
        if error {
            assert_eq!(result.unwrap_err().kind(), io::ErrorKind::ConnectionReset);
        } else {
            assert!(result.unwrap().is_none());
        }
    });
}

#[hegel::test(test_cases = 80)]
fn fragmented_writes_preserve_frames_or_end_the_connection(tc: TestCase) {
    let frames = [
        Frame::Pub {
            subject: "head".into(),
            payload: Bytes::from(vec![b'x'; tc.draw(gs::integers::<usize>().max_value(9000))]),
        }
        .encode(),
        Frame::Reply {
            id: 2,
            payload: Bytes::from_static(b"reply"),
        }
        .encode(),
    ];
    let bytes = frames.concat();
    let error = tc.draw(gs::booleans());
    let cut = if error {
        tc.draw(gs::integers::<usize>().max_value(bytes.len() - 1))
    } else {
        bytes.len()
    };
    let width = tc.draw(gs::integers::<usize>().min_value(1).max_value(128));
    runtime().block_on(async {
        let mut script = tokio_test::io::Builder::new();
        for chunk in bytes[..cut].chunks(width) {
            script.write(chunk).wait(Duration::from_millis(1));
        }
        if error {
            script.write_error(io::Error::from(io::ErrorKind::BrokenPipe));
        }
        let (out, received) = mpsc::channel(2);
        for frame in frames {
            out.try_send(frame).unwrap();
        }
        drop(out);
        let writer = script.build();
        drop(script);
        let result = write_frames(writer, received).await;
        if error {
            assert_eq!(result.unwrap_err().kind(), io::ErrorKind::BrokenPipe);
        } else {
            result.unwrap();
        }
    });
}

#[tokio::test(start_paused = true)]
async fn a_stalled_writer_disconnects_pending_calls() {
    let (client, mut peer) = connection().await;
    client
        .publish("head", Bytes::from_static(b"blocked"))
        .await
        .unwrap();
    // Leave the writer partway through a frame with the peer no longer reading it.
    peer.read_u8().await.unwrap();
    let mut call =
        tokio_test::task::spawn(client.request("rpc", Bytes::new(), Duration::from_secs(60)));
    assert_pending!(call.poll());
    let mut refused = false;
    for _ in 0..=MAX_QUEUED {
        if matches!(
            client.publish("head", Bytes::new()).await,
            Err(TransportError::Disconnected)
        ) {
            refused = true;
            break;
        }
    }
    assert!(refused, "bounded writer queue accepted every frame");
    assert!(matches!(call.await, Err(TransportError::Disconnected)));
    assert!(!client.connected());
    assert!(client.shared.lock().pending.is_empty());
}

/// Count a real relayed request's lifetime, without replacing what that request does.
struct Observed {
    inner: crate::MemoryTransport,
    ended: mpsc::UnboundedSender<()>,
}

struct Ended(mpsc::UnboundedSender<()>);

impl Drop for Ended {
    fn drop(&mut self) {
        self.0.send(()).unwrap();
    }
}

#[async_trait]
impl Transport for Observed {
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
        let _ended = Ended(self.ended.clone());
        self.inner.request(subject, payload, timeout).await
    }
}

#[hegel::test(test_cases = 50)]
fn serving_a_cut_frame_cancels_relays_without_delivering_it(tc: TestCase) {
    let frame = Frame::Pub {
        subject: "head".into(),
        payload: Bytes::from_static(b"incomplete"),
    }
    .encode();
    let cut = tc.draw(gs::integers::<usize>().max_value(frame.len() - 1));
    let error = tc.draw(gs::booleans());
    runtime().block_on(async {
        let network = crate::MemoryNetwork::new(1, 1024);
        let responder = network.connect();
        let mut rpc = responder.subscribe("rpc").await.unwrap();
        let mut heads = responder.subscribe("head").await.unwrap();
        let (ended, mut endings) = mpsc::unbounded_channel();
        let observed = Arc::new(Observed {
            inner: network.connect(),
            ended,
        });
        let request = Frame::Req {
            id: 1,
            subject: "rpc".into(),
            payload: Bytes::from_static(b"waiting"),
            timeout: Duration::from_secs(60),
        }
        .encode();
        let mut script = tokio_test::io::Builder::new();
        script
            .read(GREETING)
            .read(&request)
            .wait(Duration::from_millis(1));
        if cut > 0 {
            script.read(&frame[..cut]);
        }
        if error {
            script.read_error(io::Error::from(io::ErrorKind::ConnectionReset));
        }
        let reader = script.build();
        drop(script);
        let writer = tokio_test::io::Builder::new()
            .write(GREETING)
            .write(&1024_u32.to_be_bytes())
            .build();
        let result = serve(observed, reader, writer).await;
        if error {
            assert_eq!(result.unwrap_err().kind(), io::ErrorKind::ConnectionReset);
        } else if cut >= 4 {
            assert_eq!(result.unwrap_err().kind(), io::ErrorKind::UnexpectedEof);
        } else {
            result.unwrap();
        }
        // JoinSet aborts its children when the connection ends. Wait for the actual future
        // to be dropped, rather than sleeping or merely checking that abort was requested.
        tokio::time::timeout(Duration::from_secs(1), endings.recv())
            .await
            .unwrap()
            .unwrap();
        assert_eq!(rpc.next().await.unwrap().payload, "waiting");
        let mut no_partial_publish = tokio_test::task::spawn(heads.next());
        assert_pending!(no_partial_publish.poll());
    });
}
