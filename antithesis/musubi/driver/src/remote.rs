//! Running a shell script on a machine over ssh, with a deadline.

use std::io::Read as _;
use std::io::Write as _;
use std::process::Command;
use std::process::Stdio;
use std::time::Duration;
use std::time::Instant;

/// How a remote command went.
#[derive(Debug)]
pub enum Outcome {
    /// It ran and exited 0.
    Ok { stdout: String, stderr: String },
    /// It ran and exited otherwise.
    Failed {
        code: i32,
        stdout: String,
        stderr: String,
    },
    /// ssh failed, or the deadline passed: the command may or may not have run, in part or
    /// in whole.
    Lost { why: String },
}

impl Outcome {
    pub fn describe(&self) -> String {
        match self {
            Outcome::Ok { .. } => "ok".to_owned(),
            Outcome::Failed { code, stderr, .. } => {
                format!("exit {code}: {}", last_lines(stderr, 4))
            }
            Outcome::Lost { why } => format!("lost: {why}"),
        }
    }

    pub fn ok(&self) -> bool {
        matches!(self, Outcome::Ok { .. })
    }

    /// Everything the command said, on both streams.
    pub fn said(&self) -> String {
        match self {
            Outcome::Ok { stdout, stderr } | Outcome::Failed { stdout, stderr, .. } => {
                format!("{stdout}{stderr}")
            }
            Outcome::Lost { why } => why.clone(),
        }
    }
}

pub fn last_lines(text: &str, n: usize) -> String {
    let lines: Vec<&str> = text.trim().lines().collect();
    lines[lines.len().saturating_sub(n)..].join(" | ")
}

/// Where a command run with [`Exclusive::Yes`] takes its lock on the machine.
const LOCK: &str = "/tmp/driver.lock";

/// Where an exclusive command records its sequence number on the machine, under the lock.
const SEQUENCE: &str = "/tmp/driver.sequence";

/// The exit status of an exclusive command that found a later one had already run: it gave up
/// without running, as one the driver gave up on, delivered late, must.
const SUPERSEDED: i32 = 75;

/// Exclusive commands' sequence numbers, across machines: each machine sees them increase.
static NEXT_SEQUENCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

/// The line the remote shell prints last on standard error: the script's exit status. Its
/// absence tells ssh's own failure apart from the script's, since jj, like ssh, exits 255
/// for an internal error.
const STATUS: &str = "__driver_status=";

/// Whether a command waits for every other exclusive command on its machine to end, even one
/// the driver gave up waiting for, which ssh doesn't stop.
#[derive(Clone, Copy, PartialEq)]
pub enum Exclusive {
    Yes,
    No,
}

pub fn run(host: &str, script: &str, deadline: Duration) -> Outcome {
    run_with_input(host, script, None, deadline, Exclusive::No)
}

pub fn run_exclusive(host: &str, script: &str, deadline: Duration) -> Outcome {
    run_with_input(host, script, None, deadline, Exclusive::Yes)
}

/// Runs `script` in `sh` on `host`, as root, giving it `input` on standard input.
pub fn run_with_input(
    host: &str,
    script: &str,
    input: Option<&[u8]>,
    deadline: Duration,
    exclusive: Exclusive,
) -> Outcome {
    // An exclusive command runs only if no later one has: ssh can deliver a command the
    // driver gave up on after the next one, as when a partition heals. `-o` keeps the lock
    // from anything the command leaves running, such as a daemon it starts.
    let (lock, script) = match exclusive {
        Exclusive::Yes => {
            let n = NEXT_SEQUENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            (
                format!("flock -o {LOCK} "),
                format!(
                    "[ \"$(cat {SEQUENCE} 2>/dev/null || echo 0)\" -lt {n} ] || exit {SUPERSEDED}\n\
                     echo {n} > {SEQUENCE}\n{script}"
                ),
            )
        }
        Exclusive::No => (String::new(), script.to_owned()),
    };
    // The script travels in base64, so that no quoting of it can go wrong.
    let wrapped = format!(
        "{lock}sh -c \"$(echo {} | base64 -d)\"; printf '\\n{STATUS}%s\\n' $? >&2",
        base64(script.as_bytes())
    );
    let mut command = Command::new("ssh");
    command
        .args([
            "-o",
            "BatchMode=yes",
            "-o",
            "ConnectTimeout=3",
            "-o",
            "ServerAliveInterval=2",
            "-o",
            "ServerAliveCountMax=3",
            "-T",
            "--",
            host,
            &wrapped,
        ])
        .stdin(if input.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(err) => {
            return Outcome::Lost {
                why: format!("spawning ssh: {err}"),
            };
        }
    };
    if let (Some(input), Some(mut stdin)) = (input, child.stdin.take()) {
        let input = input.to_vec();
        std::thread::spawn(move || {
            let _ = stdin.write_all(&input);
        });
    }
    let mut stdout = child.stdout.take().expect("piped");
    let mut stderr = child.stderr.take().expect("piped");
    let out = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stdout.read_to_end(&mut buf);
        buf
    });
    let err = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = stderr.read_to_end(&mut buf);
        buf
    });
    let start = Instant::now();
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) if start.elapsed() < deadline => std::thread::sleep(Duration::from_millis(5)),
            Ok(None) | Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
        }
    };
    let stdout = String::from_utf8_lossy(&out.join().unwrap_or_default()).into_owned();
    let mut stderr = String::from_utf8_lossy(&err.join().unwrap_or_default()).into_owned();
    // Only the status line itself: ssh can say more after it, as when the connection closes.
    let code = stderr.rfind(STATUS).and_then(|at| {
        let rest = &stderr[at + STATUS.len()..];
        let code = rest.lines().next()?.trim().parse::<i32>().ok()?;
        stderr.truncate(at);
        Some(code)
    });
    match (status, code) {
        (None, _) => Outcome::Lost {
            why: format!(
                "no answer within {deadline:?}; said: {}",
                last_lines(&format!("{stdout}{stderr}"), 3)
            ),
        },
        (Some(_), None) => Outcome::Lost {
            why: format!("ssh failed: {}", last_lines(&stderr, 2)),
        },
        (Some(_), Some(SUPERSEDED)) => Outcome::Lost {
            why: "superseded by a later command".to_owned(),
        },
        (Some(_), Some(0)) => Outcome::Ok { stdout, stderr },
        (Some(_), Some(code)) => Outcome::Failed {
            code,
            stdout,
            stderr,
        },
    }
}

fn base64(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::new();
    for chunk in bytes.chunks(3) {
        let n = chunk
            .iter()
            .enumerate()
            .fold(0u32, |n, (i, &b)| n | u32::from(b) << (16 - 8 * i));
        for i in 0..4 {
            if i <= chunk.len() {
                out.push(ALPHABET[(n >> (18 - 6 * i) & 63) as usize] as char);
            } else {
                out.push('=');
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn base64_matches_the_standard_encoding() {
        assert_eq!(super::base64(b""), "");
        assert_eq!(super::base64(b"a"), "YQ==");
        assert_eq!(super::base64(b"ab"), "YWI=");
        assert_eq!(super::base64(b"abc"), "YWJj");
        assert_eq!(super::base64(b"jj log -r '@'"), "amogbG9nIC1yICdAJw==");
    }
}
