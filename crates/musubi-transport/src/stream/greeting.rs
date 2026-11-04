//! Recognizing the hub's greeting through shell banners and refusing other versions.

use std::io;
use std::time::Duration;

use tokio::io::AsyncBufRead;
use tokio::io::AsyncBufReadExt as _;
use tokio::io::AsyncReadExt as _;

use super::frame::invalid;

/// What each side sends first: the protocol's name and version, after a NUL. A NUL is never
/// part of text, so a banner passes for the greeting, as one naming a host `musubi1` would
/// without it, only by printing it on purpose.
pub const GREETING: &[u8; 9] = b"\0musubi1\n";

/// The payload limits a hub may offer: what it says outside this is more likely to be noise
/// than a hub.
pub const PLAUSIBLE_PAYLOADS: std::ops::RangeInclusive<usize> = 1024..=64 << 20;

/// The most the hub's machine may print before the hub greets: a banner of ASCII art, say,
/// that a shell's startup files print for every shell.
pub const MAX_BEFORE_GREETING: usize = 64 * 1024;

/// How long the other side may take to greet, which over ssh includes logging in, through a
/// tunnel's ProxyCommand perhaps.
pub(super) const GREETING_TIMEOUT: Duration = Duration::from_secs(30);

/// Reads through the hub's greeting, passing over up to [`MAX_BEFORE_GREETING`] bytes of
/// whatever comes before it. Fails with [`io::ErrorKind::InvalidData`] if what answers is
/// not a hub, or speaks another version of the protocol.
pub async fn await_greeting(reader: &mut (impl AsyncBufRead + Unpin)) -> io::Result<()> {
    let mut before = Vec::new();
    loop {
        let room = MAX_BEFORE_GREETING.saturating_sub(before.len()) + GREETING.len();
        let mut line = Vec::new();
        let n = (&mut *reader)
            .take(room as u64)
            .read_until(b'\n', &mut line)
            .await?;
        // Whatever came before on the same line, as when the last thing printed has no
        // newline, is more of the same.
        if line.ends_with(GREETING) {
            return Ok(());
        }
        if is_other_greeting(&line) {
            return Err(invalid(
                "the hub speaks another version of musubi's protocol",
            ));
        }
        if n == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "the connection ended before the hub answered",
            ));
        }
        before.extend_from_slice(&line);
        if before.len() > MAX_BEFORE_GREETING {
            let said = String::from_utf8_lossy(&before);
            let first = said.lines().map(str::trim).find(|line| !line.is_empty());
            let first: String = first.unwrap_or_default().chars().take(80).collect();
            return Err(invalid(format!(
                "what answered is not a musubi hub: it said {first:?}"
            )));
        }
    }
}

/// Whether `line` ends as another version's greeting would, `\0musubi<digits>\n`.
fn is_other_greeting(line: &[u8]) -> bool {
    let Some(line) = line.strip_suffix(b"\n") else {
        return false;
    };
    let digits = line.iter().rev().take_while(|b| b.is_ascii_digit()).count();
    digits > 0 && line[..line.len() - digits].ends_with(b"\0musubi")
}

#[cfg(test)]
mod tests {
    use tokio::io::BufReader;

    use super::*;

    #[tokio::test]
    async fn noise_before_the_greeting_is_passed_over() {
        // On a host named as if it were the greeting, too.
        let goat = b"\x1b[1;33m      _))\n     > *\\     _~\n  Welcome to musubi1\n\x1b[0m\
                     Last login: never";
        let stream = [&goat[..], GREETING, b"rest"].concat();
        let mut reader = BufReader::new(stream.as_slice());
        await_greeting(&mut reader).await.unwrap();
        let mut rest = Vec::new();
        reader.read_to_end(&mut rest).await.unwrap();
        assert_eq!(rest, b"rest");
    }

    #[tokio::test]
    async fn too_much_noise_and_other_versions_are_refused() {
        let noise = "baa\n".repeat(MAX_BEFORE_GREETING);
        let stream = [noise.as_bytes(), GREETING].concat();
        let err = await_greeting(&mut BufReader::new(stream.as_slice()))
            .await
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        assert!(err.to_string().contains("it said \"baa\""), "{err}");
        // Noise with no newline in it at all.
        let stream = [&vec![b'x'; 2 * MAX_BEFORE_GREETING][..], GREETING].concat();
        let err = await_greeting(&mut BufReader::new(stream.as_slice()))
            .await
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
        let err = await_greeting(&mut BufReader::new(&b"motd\n\0musubi2\n"[..]))
            .await
            .unwrap_err();
        assert!(err.to_string().contains("another version"), "{err}");
        let err = await_greeting(&mut BufReader::new(&b"motd\n"[..]))
            .await
            .unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof);
    }
}
