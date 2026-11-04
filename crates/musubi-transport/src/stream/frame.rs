//! The byte-stream frame codec and bounded frame I/O.

use std::io;
use std::time::Duration;

use bytes::Buf as _;
use bytes::Bytes;
use tokio::io::AsyncRead;
use tokio::io::AsyncReadExt as _;
use tokio::io::AsyncWrite;
use tokio::io::AsyncWriteExt as _;
use tokio::io::BufWriter;
use tokio::sync::mpsc;

/// Room in a frame for everything but its payload: two strings and a few integers.
pub(super) const FRAME_OVERHEAD: usize = 2 * (2 + u16::MAX as usize) + 32;

const SUB: u8 = 1;
const PUB: u8 = 2;
const REQ: u8 = 3;
const MSG: u8 = 4;
const REPLY: u8 = 5;
const FAIL: u8 = 6;

/// Why a request failed, in a `FAIL` frame.
pub(super) const TIMED_OUT: u8 = 1;
pub(super) const NO_RESPONDERS: u8 = 2;
pub(super) const OTHER: u8 = 3;

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Frame {
    Sub {
        sid: u64,
        subject: String,
    },
    Pub {
        subject: String,
        payload: Bytes,
    },
    Req {
        id: u64,
        timeout: Duration,
        subject: String,
        payload: Bytes,
    },
    Msg {
        sid: u64,
        subject: String,
        reply: Option<String>,
        payload: Bytes,
    },
    Reply {
        id: u64,
        payload: Bytes,
    },
    Fail {
        id: u64,
        code: u8,
        message: String,
    },
}

impl Frame {
    pub(super) fn kind(&self) -> &'static str {
        match self {
            Self::Sub { .. } => "SUB",
            Self::Pub { .. } => "PUB",
            Self::Req { .. } => "REQ",
            Self::Msg { .. } => "MSG",
            Self::Reply { .. } => "REPLY",
            Self::Fail { .. } => "FAIL",
        }
    }

    /// The frame, with its length in front.
    pub(super) fn encode(&self) -> Vec<u8> {
        let mut out = vec![0; 4];
        let payload = match self {
            Self::Sub { sid, subject } => {
                out.push(SUB);
                put_u64(&mut out, *sid);
                put_str(&mut out, subject);
                None
            }
            Self::Pub { subject, payload } => {
                out.push(PUB);
                put_str(&mut out, subject);
                Some(payload)
            }
            Self::Req {
                id,
                timeout,
                subject,
                payload,
            } => {
                out.push(REQ);
                put_u64(&mut out, *id);
                put_u64(
                    &mut out,
                    u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX),
                );
                put_str(&mut out, subject);
                Some(payload)
            }
            Self::Msg {
                sid,
                subject,
                reply,
                payload,
            } => {
                out.push(MSG);
                put_u64(&mut out, *sid);
                put_str(&mut out, subject);
                put_str(&mut out, reply.as_deref().unwrap_or_default());
                Some(payload)
            }
            Self::Reply { id, payload } => {
                out.push(REPLY);
                put_u64(&mut out, *id);
                Some(payload)
            }
            Self::Fail { id, code, message } => {
                out.push(FAIL);
                put_u64(&mut out, *id);
                out.push(*code);
                put_str(&mut out, message);
                None
            }
        };
        if let Some(payload) = payload {
            out.extend_from_slice(payload);
        }
        let len = u32::try_from(out.len() - 4).unwrap_or(u32::MAX);
        out[..4].copy_from_slice(&len.to_be_bytes());
        out
    }

    /// Reads a frame's body, everything after its length.
    pub(super) fn decode(mut body: Bytes) -> io::Result<Self> {
        Ok(match take_u8(&mut body)? {
            SUB => {
                let sid = take_u64(&mut body)?;
                let subject = take_str(&mut body)?;
                take_end(&body)?;
                Self::Sub { sid, subject }
            }
            PUB => {
                let subject = take_str(&mut body)?;
                Self::Pub {
                    subject,
                    payload: body,
                }
            }
            REQ => {
                let id = take_u64(&mut body)?;
                let timeout = Duration::from_millis(take_u64(&mut body)?);
                let subject = take_str(&mut body)?;
                Self::Req {
                    id,
                    timeout,
                    subject,
                    payload: body,
                }
            }
            MSG => {
                let sid = take_u64(&mut body)?;
                let subject = take_str(&mut body)?;
                let reply = take_str(&mut body)?;
                Self::Msg {
                    sid,
                    subject,
                    reply: (!reply.is_empty()).then_some(reply),
                    payload: body,
                }
            }
            REPLY => {
                let id = take_u64(&mut body)?;
                Self::Reply { id, payload: body }
            }
            FAIL => {
                let id = take_u64(&mut body)?;
                let code = take_u8(&mut body)?;
                let message = take_str(&mut body)?;
                take_end(&body)?;
                Self::Fail { id, code, message }
            }
            kind => return Err(invalid(format!("a frame of unknown kind {kind}"))),
        })
    }
}

fn put_u64(out: &mut Vec<u8>, n: u64) {
    out.extend_from_slice(&n.to_be_bytes());
}

fn put_str(out: &mut Vec<u8>, s: &str) {
    // Subjects are checked before they get this far; only an error's message can be longer.
    let s = &s[..s.floor_char_boundary(usize::from(u16::MAX))];
    out.extend_from_slice(&u16::try_from(s.len()).unwrap_or(u16::MAX).to_be_bytes());
    out.extend_from_slice(s.as_bytes());
}

fn take_u8(body: &mut Bytes) -> io::Result<u8> {
    if body.is_empty() {
        return Err(cut_short());
    }
    Ok(body.get_u8())
}

fn take_u64(body: &mut Bytes) -> io::Result<u64> {
    if body.len() < 8 {
        return Err(cut_short());
    }
    Ok(body.get_u64())
}

fn take_str(body: &mut Bytes) -> io::Result<String> {
    if body.len() < 2 {
        return Err(cut_short());
    }
    let len = usize::from(body.get_u16());
    if body.len() < len {
        return Err(cut_short());
    }
    String::from_utf8(body.split_to(len).to_vec()).map_err(|_| invalid("a string that isn't UTF-8"))
}

/// The end of a frame with no payload, which nothing may follow.
fn take_end(body: &Bytes) -> io::Result<()> {
    if !body.is_empty() {
        return Err(invalid("a frame longer than its fields"));
    }
    Ok(())
}

fn cut_short() -> io::Error {
    invalid("a frame cut short")
}

pub(super) fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

/// Reads the next frame, or `None` at the end of the stream. A frame longer than `limit`
/// is an error.
pub(super) async fn read_frame(
    reader: &mut (impl AsyncRead + Unpin),
    limit: usize,
) -> io::Result<Option<Frame>> {
    let len = match reader.read_u32().await {
        Ok(len) => len as usize,
        Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
        Err(err) => return Err(err),
    };
    if len > limit {
        return Err(invalid(format!(
            "a frame of {len} bytes, more than the {limit} allowed"
        )));
    }
    let mut body = vec![0; len];
    reader.read_exact(&mut body).await?;
    Frame::decode(Bytes::from(body)).map(Some)
}

/// Writes encoded frames as they come, until there are no more.
pub(super) async fn write_frames(
    writer: impl AsyncWrite + Unpin,
    mut frames: mpsc::Receiver<Vec<u8>>,
) -> io::Result<()> {
    let mut writer = BufWriter::new(writer);
    while let Some(frame) = frames.recv().await {
        writer.write_all(&frame).await?;
        while let Ok(frame) = frames.try_recv() {
            writer.write_all(&frame).await?;
        }
        writer.flush().await?;
    }
    writer.shutdown().await
}

/// Entry points for fuzz/, which reach frames without making them public. Tests build them
/// too, so that they're checked and linted with everything else.
#[cfg(any(fuzzing, test))]
pub mod fuzzing {
    use super::read_frame;

    /// Reads frames from `stream` until it ends or one is malformed, checking that each
    /// encodes to exactly the bytes it was read from: a frame has one encoding. Returns how
    /// many it read.
    pub async fn frames(stream: &[u8], limit: usize) -> usize {
        let mut rest = stream;
        let mut read = 0;
        loop {
            let before = rest;
            let Ok(Some(frame)) = read_frame(&mut rest, limit).await else {
                return read;
            };
            assert_eq!(
                frame.encode(),
                &before[..before.len() - rest.len()],
                "{frame:?}"
            );
            read += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trip(frame: Frame) {
        let encoded = frame.encode();
        let len = u32::from_be_bytes([encoded[0], encoded[1], encoded[2], encoded[3]]);
        assert_eq!(len as usize, encoded.len() - 4);
        let decoded = Frame::decode(Bytes::from(encoded[4..].to_vec())).unwrap();
        assert_eq!(decoded, frame);
    }

    #[test]
    fn frames_round_trip() {
        round_trip(Frame::Sub {
            sid: 7,
            subject: "musubi.*.rpc".into(),
        });
        round_trip(Frame::Pub {
            subject: "musubi.hive.head".into(),
            payload: Bytes::from_static(b"head"),
        });
        round_trip(Frame::Req {
            id: u64::MAX,
            timeout: Duration::from_millis(1500),
            subject: "musubi.hive.rpc".into(),
            payload: Bytes::new(),
        });
        round_trip(Frame::Msg {
            sid: 1,
            subject: "musubi.hive.rpc".into(),
            reply: Some("_INBOX.1.2".into()),
            payload: Bytes::from_static(b"request"),
        });
        round_trip(Frame::Msg {
            sid: 1,
            subject: "musubi.hive.head".into(),
            reply: None,
            payload: Bytes::new(),
        });
        round_trip(Frame::Reply {
            id: 3,
            payload: Bytes::from_static(b"reply"),
        });
        round_trip(Frame::Fail {
            id: 4,
            code: OTHER,
            message: "it went wrong".into(),
        });
    }

    /// Frames of every kind, read from a stream, encode to exactly the bytes they were read
    /// from, as the fuzz target checks of any stream.
    #[tokio::test]
    async fn frames_encode_as_they_were_read() {
        let frames = [
            Frame::Sub {
                sid: 7,
                subject: "musubi.*.rpc".into(),
            },
            Frame::Pub {
                subject: "musubi.hive.head".into(),
                payload: Bytes::from_static(b"head"),
            },
            Frame::Req {
                id: u64::MAX,
                timeout: Duration::from_millis(u64::MAX),
                subject: "s".repeat(usize::from(u16::MAX)),
                payload: Bytes::new(),
            },
            Frame::Msg {
                sid: 1,
                subject: "musubi.hive.head".into(),
                reply: None,
                payload: Bytes::from_static(b"notice"),
            },
            Frame::Reply {
                id: 3,
                payload: Bytes::from_static(b"reply"),
            },
            Frame::Fail {
                id: 4,
                code: OTHER,
                message: String::new(),
            },
        ];
        let stream: Vec<u8> = frames.iter().flat_map(Frame::encode).collect();
        assert_eq!(fuzzing::frames(&stream, 1 << 20).await, frames.len());
    }

    #[test]
    fn long_messages_are_cut_to_fit() {
        let message = "é".repeat(40_000);
        let encoded = Frame::Fail {
            id: 1,
            code: OTHER,
            message,
        }
        .encode();
        let Frame::Fail { message, .. } =
            Frame::decode(Bytes::from(encoded[4..].to_vec())).unwrap()
        else {
            panic!("not a FAIL");
        };
        assert_eq!(message.len(), 65534);
    }

    #[test]
    fn malformed_frames_are_errors() {
        let mut encoded = Frame::Sub {
            sid: 7,
            subject: "subject".into(),
        }
        .encode();
        encoded.pop();
        let err = Frame::decode(Bytes::from(encoded[4..].to_vec())).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        let err = Frame::decode(Bytes::from_static(&[99])).unwrap_err();
        assert!(err.to_string().contains("unknown kind 99"), "{err}");
        let err = Frame::decode(Bytes::from_static(&[
            SUB, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0xff,
        ]))
        .unwrap_err();
        assert!(err.to_string().contains("UTF-8"), "{err}");
        // Nothing may follow the fields of a frame without a payload.
        for frame in [
            Frame::Sub {
                sid: 7,
                subject: "subject".into(),
            },
            Frame::Fail {
                id: 4,
                code: OTHER,
                message: "it went wrong".into(),
            },
        ] {
            let mut encoded = frame.encode();
            encoded.push(0);
            let err = Frame::decode(Bytes::from(encoded[4..].to_vec())).unwrap_err();
            assert!(err.to_string().contains("longer than its fields"), "{err}");
        }
    }

    #[tokio::test]
    async fn frames_over_the_limit_are_refused() {
        let frame = Frame::Reply {
            id: 1,
            payload: Bytes::from(vec![0; 100]),
        }
        .encode();
        let err = read_frame(&mut frame.as_slice(), 50).await.unwrap_err();
        assert!(
            err.to_string().contains("more than the 50 allowed"),
            "{err}"
        );
        // A frame the stream ends partway through is never delivered.
        let err = read_frame(&mut &frame[..50], 200).await.unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);
        assert!(read_frame(&mut &[][..], 200).await.unwrap().is_none());
    }
}
