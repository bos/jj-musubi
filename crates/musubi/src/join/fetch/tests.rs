//! A real Git fetch against a server that accepts its request and never answers.

use std::path::Path;
use std::time::Duration;

use musubi_testutil::TestEnv;
use tokio::io::AsyncBufReadExt as _;
use tokio::io::AsyncReadExt as _;
use tokio::io::BufReader;

async fn request(listener: &tokio::net::TcpListener) -> BufReader<tokio::net::TcpStream> {
    let (stream, _) = tokio::time::timeout(Duration::from_secs(10), listener.accept())
        .await
        .unwrap()
        .unwrap();
    let mut stream = BufReader::new(stream);
    tokio::time::timeout(Duration::from_secs(10), async {
        loop {
            let mut line = String::new();
            assert_ne!(stream.read_line(&mut line).await.unwrap(), 0);
            if line == "\r\n" {
                break;
            }
        }
    })
    .await
    .unwrap();
    stream
}

/// Start the deadline check only after the native Git request reaches the server, then
/// advance virtual time. EOF proves Git's socket was closed, not just its waiting jj parent.
#[tokio::test]
async fn a_stalled_fetch_stops_its_git_descendant() {
    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let url = format!("http://{}/repo", listener.local_addr().unwrap());
    repo.jj(&["git", "remote", "add", "origin", &url]);
    let mut command = repo.program(Path::new("jj"));
    command.args([
        "--ignore-working-copy",
        "git",
        "fetch",
        "--remote",
        "origin",
    ]);
    let fetch = tokio::spawn(super::run(command, Duration::from_secs(30)));
    let mut stream = request(&listener).await;
    tokio::time::pause();
    tokio::time::advance(Duration::from_secs(31)).await;
    let error = fetch.await.unwrap().unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::TimedOut);
    tokio::time::resume();
    let mut byte = [0];
    assert_eq!(
        tokio::time::timeout(Duration::from_secs(2), stream.read(&mut byte))
            .await
            .unwrap()
            .unwrap(),
        0
    );
}

/// A subprocess helper: its first interrupt must reap the fetch; its second, after the
/// runtime has ended, must still terminate the command rather than be silently ignored.
#[cfg(unix)]
#[test]
fn interrupt_child() {
    if std::env::var_os("MUSUBI_FETCH_INTERRUPT_CHILD").is_none() {
        return;
    }
    let mut command = std::process::Command::new("jj");
    command.args([
        "--ignore-working-copy",
        "git",
        "fetch",
        "--remote",
        "origin",
    ]);
    let error = crate::block_on(async { Ok(super::run(command, Duration::from_secs(30)).await?) })
        .unwrap_err();
    assert_eq!(
        error.downcast_ref::<std::io::Error>().unwrap().kind(),
        std::io::ErrorKind::Interrupted
    );
    println!("fetch stopped");
    // Model later synchronous work after the short-lived fetch runtime was dropped.
    std::thread::park();
    panic!("the inactive interruption handler did not terminate the command");
}

#[cfg(unix)]
#[tokio::test]
async fn interrupts_stop_the_fetch_and_still_work_afterwards() {
    use rustix::process::{Pid, Signal, kill_process};
    use std::process::Stdio;

    let env = TestEnv::new();
    let repo = env.init_repo("alpha");
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let url = format!("http://{}/repo", listener.local_addr().unwrap());
    repo.jj(&["git", "remote", "add", "origin", &url]);
    let mut command = repo.program(&std::env::current_exe().unwrap());
    command
        .args([
            "--exact",
            "join::fetch::tests::interrupt_child",
            "--nocapture",
        ])
        .env("MUSUBI_FETCH_INTERRUPT_CHILD", "1");
    let mut child = tokio::process::Command::from(command)
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .kill_on_drop(true)
        .spawn()
        .unwrap();
    let pid = Pid::from_raw(i32::try_from(child.id().unwrap()).unwrap()).unwrap();
    let mut stream = request(&listener).await;
    kill_process(pid, Signal::INT).unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    tokio::time::timeout(Duration::from_secs(5), async {
        loop {
            let mut line = String::new();
            assert_ne!(output.read_line(&mut line).await.unwrap(), 0);
            if line.trim() == "fetch stopped" {
                break;
            }
        }
    })
    .await
    .unwrap();
    let mut byte = [0];
    assert_eq!(
        tokio::time::timeout(Duration::from_secs(2), stream.read(&mut byte))
            .await
            .unwrap()
            .unwrap(),
        0
    );
    kill_process(pid, Signal::INT).unwrap();
    let status = tokio::time::timeout(Duration::from_secs(2), child.wait())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(status.code(), Some(130));
}
