//! Relaying one client's stream to the hub's transport.

use std::io;
use std::sync::Arc;
use std::time::Duration;

use tokio::io::AsyncRead;
use tokio::io::AsyncReadExt as _;
use tokio::io::AsyncWrite;
use tokio::io::AsyncWriteExt as _;
use tokio::io::BufReader;
use tokio::sync::Notify;
use tokio::sync::mpsc;
use tokio::sync::mpsc::error::TrySendError;
use tokio::task::JoinSet;

use super::MAX_QUEUED;
use super::frame::FRAME_OVERHEAD;
use super::frame::Frame;
use super::frame::NO_RESPONDERS;
use super::frame::OTHER;
use super::frame::TIMED_OUT;
use super::frame::invalid;
use super::frame::read_frame;
use super::frame::write_frames;
use super::greeting::GREETING;
use super::greeting::GREETING_TIMEOUT;
use crate::Transport;
use crate::TransportError;

/// The longest a request relayed for a client may take, whatever the client asked for.
const MAX_REQUEST_TIMEOUT: Duration = Duration::from_secs(3600);

/// Serves one connection to the hub, relaying what the other side sends through
/// `transport`, which reaches the hub's service, until either side closes it. Requests are
/// relayed as they come, without waiting for earlier ones' replies.
pub async fn serve(
    transport: Arc<dyn Transport>,
    reader: impl AsyncRead + Send + Unpin,
    mut writer: impl AsyncWrite + Send + Unpin,
) -> io::Result<()> {
    let limit = transport.max_payload();
    writer.write_all(GREETING).await?;
    writer
        .write_u32(u32::try_from(limit).unwrap_or(u32::MAX))
        .await?;
    writer.flush().await?;
    let mut reader = BufReader::new(reader);
    let mut greeting = [0; GREETING.len()];
    tokio::time::timeout(GREETING_TIMEOUT, reader.read_exact(&mut greeting))
        .await
        .map_err(|_| io::Error::new(io::ErrorKind::TimedOut, "the client did not greet"))??;
    if &greeting != GREETING {
        return Err(invalid(
            "what connected is not a musubi client, or speaks another version of its protocol",
        ));
    }
    let (out, frames) = mpsc::channel(MAX_QUEUED);
    let stopped_reading = Arc::new(Notify::new());
    // Subscriptions and requests in progress, which end with the connection.
    let mut tasks = JoinSet::new();
    let relay = async {
        while let Some(frame) = read_frame(&mut reader, limit + FRAME_OVERHEAD).await? {
            while tasks.try_join_next().is_some() {}
            match frame {
                Frame::Sub { sid, subject } => {
                    let mut subscription = transport
                        .subscribe(&subject)
                        .await
                        .map_err(io::Error::other)?;
                    let (out, stopped_reading) = (out.clone(), stopped_reading.clone());
                    tasks.spawn(async move {
                        while let Some(message) = subscription.next().await {
                            let frame = Frame::Msg {
                                sid,
                                subject: message.subject,
                                reply: message.reply,
                                payload: message.payload,
                            };
                            if !queue(&out, &stopped_reading, &frame) {
                                break;
                            }
                        }
                    });
                }
                // Delivery is best effort: what can't be published is lost, as on the way.
                Frame::Pub { subject, payload } => {
                    transport.publish(&subject, payload).await.ok();
                }
                Frame::Req {
                    id,
                    timeout,
                    subject,
                    payload,
                } => {
                    let (transport, out) = (transport.clone(), out.clone());
                    let stopped_reading = stopped_reading.clone();
                    tasks.spawn(async move {
                        let timeout = timeout.min(MAX_REQUEST_TIMEOUT);
                        let frame = match transport.request(&subject, payload, timeout).await {
                            Ok(payload) => Frame::Reply { id, payload },
                            Err(err) => failure(id, err),
                        };
                        queue(&out, &stopped_reading, &frame);
                    });
                }
                frame => {
                    return Err(invalid(format!(
                        "a client sent the hub's frame, {}",
                        frame.kind()
                    )));
                }
            }
        }
        Ok(())
    };
    tokio::select! {
        result = relay => result,
        result = write_frames(writer, frames) => result,
        () = stopped_reading.notified() => Err(io::Error::other(format!(
            "the client fell {MAX_QUEUED} frames behind; it may have vanished"
        ))),
    }
}

/// Queues `frame` for the client, returning whether the connection carries on: it doesn't
/// once it has closed, or once too many frames wait for the client.
fn queue(out: &mpsc::Sender<Vec<u8>>, stopped_reading: &Notify, frame: &Frame) -> bool {
    match out.try_send(frame.encode()) {
        Ok(()) => true,
        Err(TrySendError::Full(_)) => {
            stopped_reading.notify_one();
            false
        }
        Err(TrySendError::Closed(_)) => false,
    }
}

fn failure(id: u64, err: TransportError) -> Frame {
    let (code, message) = match err {
        TransportError::Timeout => (TIMED_OUT, String::new()),
        TransportError::NoResponders(_) => (NO_RESPONDERS, String::new()),
        err => (OTHER, err.to_string()),
    };
    Frame::Fail { id, code, message }
}
