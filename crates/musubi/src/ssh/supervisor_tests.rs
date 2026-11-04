//! Real processes and pipes, without ssh, a hub, a repository, or the user's services.

#![allow(clippy::unwrap_used)]

use std::future::Future as _;
use std::io::Read as _;

use musubi_transport::Transport as _;
use rustix::process::Pid;
use rustix::process::WaitOptions;
use tokio::io::AsyncBufReadExt as _;
use tokio::io::BufReader;

use super::*;

const DEADLINE: Duration = Duration::from_secs(5);
const CHILD: &str = "ssh::supervisor_tests::controlled_child";

/// Each child blocks on a pipe or parks; its parent controls every transition.
#[test]
#[ignore = "subprocess helper, invoked with a mode by the supervisor tests"]
fn controlled_child() {
    let Ok(mode) = std::env::var("MUSUBI_SSH_CHILD_MODE") else {
        return;
    };
    match mode.as_str() {
        "stubborn" => {
            println!("READY");
            io::stdout().flush().unwrap();
            io::stdin().read_to_end(&mut vec![]).unwrap();
            println!("EOF");
            io::stdout().flush().unwrap();
            loop {
                std::thread::park();
            }
        }
        "inherited" => {
            let holder = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", CHILD, "--ignored", "--nocapture", "--quiet"])
                .env("MUSUBI_SSH_CHILD_MODE", "holder")
                .stdin(Stdio::inherit())
                .stdout(Stdio::null())
                .stderr(Stdio::inherit())
                .spawn()
                .unwrap();
            eprintln!("proxy still has stderr");
            println!("HOLDER {}", holder.id());
            io::stdout().flush().unwrap();
            std::process::exit(255);
        }
        "holder" => {
            io::stdin().read_to_end(&mut vec![]).unwrap();
        }
        "chatty" => {
            io::stderr().write_all(&vec![b'x'; 1024 * 1024]).unwrap();
            eprintln!("\nlast diagnostic");
            println!("READY");
            io::stdout().flush().unwrap();
            io::stdin().read_to_end(&mut vec![]).unwrap();
            std::process::exit(255);
        }
        "relay" => {
            let runtime = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .unwrap();
            runtime.block_on(async {
                let hub = Arc::new(musubi_transport::MemoryNetwork::new(1, 1 << 20).connect());
                let mut calls = hub.subscribe("echo").await.unwrap();
                let replies = hub.clone();
                tokio::spawn(async move {
                    while let Some(call) = calls.next().await {
                        replies
                            .publish(&call.reply.unwrap(), call.payload)
                            .await
                            .unwrap();
                    }
                });
                musubi_transport::stream::serve(hub, tokio::io::stdin(), tokio::io::stdout())
                    .await
                    .unwrap();
            });
        }
        "greeting" => {
            // A shell banner must not clear ssh's failures; only the hub's greeting does.
            println!("BANNER");
            io::stdout().flush().unwrap();
            let mut go = [0];
            io::stdin().read_exact(&mut go).unwrap();
            for byte in GREETING {
                io::stdout().write_all(&[*byte]).unwrap();
                io::stdout().flush().unwrap();
            }
            io::stdin().read_to_end(&mut vec![]).unwrap();
        }
        _ => panic!("unknown child mode {mode}"),
    }
}

fn child_command(mode: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", CHILD, "--ignored", "--nocapture", "--quiet"])
        .env("MUSUBI_SSH_CHILD_MODE", mode)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true);
    command
}

fn child(mode: &str) -> Child {
    child_command(mode).spawn().unwrap()
}

async fn line<R: AsyncRead + Unpin>(reader: &mut BufReader<R>, prefix: &str) -> String {
    tokio::time::timeout(DEADLINE, async {
        loop {
            let mut line = String::new();
            assert_ne!(
                reader.read_line(&mut line).await.unwrap(),
                0,
                "missing {prefix}"
            );
            if line.starts_with(prefix) {
                return line;
            }
        }
    })
    .await
    .expect("child did not reach the signaled transition")
}

struct Running {
    input: Option<tokio::process::ChildStdin>,
    output: BufReader<ChildStdout>,
    closed: Option<oneshot::Sender<()>>,
    woke: watch::Sender<u64>,
    settled: Arc<AtomicBool>,
    health: Health,
    pid: Pid,
    task: Option<tokio::task::JoinHandle<()>>,
}

impl Running {
    fn new(mode: &str) -> Self {
        let (mut run, ssh) = Self::unstarted(mode);
        run.task = Some(tokio::spawn(supervise(ssh)));
        run
    }

    fn unstarted(mode: &str) -> (Self, Ssh) {
        let mut child = child(mode);
        let input = child.stdin.take();
        let output = BufReader::new(child.stdout.take().unwrap());
        let stderr = child.stderr.take().unwrap();
        let pid = Pid::from_raw(child.id().unwrap() as i32).unwrap();
        let (closed, let_go) = oneshot::channel();
        let (woke, receiver) = watch::channel(0);
        let health = Health::default();
        let settled = Arc::new(AtomicBool::new(false));
        let ssh = Ssh {
            child,
            stderr,
            dest: "controlled-child".into(),
            health: health.clone(),
            settled: settled.clone(),
            woke: receiver,
            let_go,
        };
        (
            Self {
                input,
                output,
                closed: Some(closed),
                woke,
                settled,
                health,
                pid,
                task: None,
            },
            ssh,
        )
    }

    async fn finished(&mut self) {
        tokio::time::timeout(DEADLINE, self.task.as_mut().unwrap())
            .await
            .expect("supervisor did not finish")
            .unwrap();
        assert!(
            matches!(
                rustix::process::waitpid(Some(self.pid), WaitOptions::NOHANG),
                Err(rustix::io::Errno::CHILD)
            ),
            "the supervisor must reap its child, not merely kill it"
        );
        assert!(rustix::process::test_kill_process(self.pid).is_err());
    }
}

impl Drop for Running {
    fn drop(&mut self) {
        if let Some(task) = &self.task {
            task.abort();
        }
    }
}

/// Own only the descendant created by the helper; never signal a process group.
struct Descendant(Pid);

impl Drop for Descendant {
    fn drop(&mut self) {
        rustix::process::kill_process(self.0, rustix::process::Signal::KILL).ok();
    }
}

#[tokio::test]
async fn letting_go_kills_and_reaps_a_child_that_ignores_eof() {
    let mut run = Running::new("stubborn");
    line(&mut run.output, "READY").await;
    run.input.take();
    run.closed.take();
    line(&mut run.output, "EOF").await;
    run.finished().await;
    assert_eq!(run.health.lock().failures, 1);
    assert!(run.health.refusing());
    assert_eq!(
        run.health.problem().unwrap(),
        "ssh to controlled-child did not connect"
    );
}

#[tokio::test]
async fn inherited_stderr_does_not_hold_up_failure_reporting() {
    let mut run = Running::new("inherited");
    let holder = line(&mut run.output, "HOLDER ").await;
    let _holder = Descendant(Pid::from_raw(holder.trim()[7..].parse().unwrap()).unwrap());
    run.finished().await;
    assert_eq!(
        run.health.problem().unwrap(),
        "ssh to controlled-child failed: proxy still has stderr"
    );
    assert!(run.health.refusing());
    assert!(!run.settled.load(Ordering::Relaxed));
}

#[tokio::test]
async fn chatty_stderr_is_drained_and_keeps_the_last_diagnostic() {
    let mut child = child("chatty");
    let said = Arc::new(Mutex::new(vec![]));
    let mut reading = tokio::spawn(read_stderr(child.stderr.take().unwrap(), said.clone()));
    let mut output = BufReader::new(child.stdout.take().unwrap());
    line(&mut output, "READY").await;
    child.stdin.take();
    assert_eq!(child.wait().await.unwrap().code(), Some(255));
    let tail = said_so_far(&mut reading, &said).await;
    assert!(tail.len() <= MAX_SAID);
    assert!(tail.ends_with("\nlast diagnostic\n"));
    assert_eq!(
        describe_failure("controlled-child", child.try_wait().unwrap(), &tail),
        "ssh to controlled-child failed: last diagnostic"
    );
}

#[tokio::test]
async fn waking_during_teardown_does_not_restore_an_old_failure() {
    let (mut run, ssh) = Running::unstarted("stubborn");
    line(&mut run.output, "READY").await;
    run.input.take();
    run.closed.take();
    line(&mut run.output, "EOF").await;
    // Poll the shipping supervisor after let_go closed. The child is parked, so
    // Pending proves it has entered the grace wait, before we publish the wake.
    let mut supervisor = Box::pin(supervise(ssh));
    std::future::poll_fn(|cx| {
        assert!(supervisor.as_mut().poll(cx).is_pending());
        Poll::Ready(())
    })
    .await;
    run.task = Some(tokio::spawn(supervisor));
    run.health.failed("old failure".into());
    run.health.woke(&run.woke);
    run.finished().await;
    assert_eq!(run.health.problem(), None);
    assert!(!run.health.refusing());
}

#[tokio::test]
async fn waking_during_stderr_drain_does_not_restore_an_old_failure() {
    let mut run = Running::new("inherited");
    let holder = line(&mut run.output, "HOLDER ").await;
    let _holder = Descendant(Pid::from_raw(holder.trim()[7..].parse().unwrap()).unwrap());
    // Wait for the real child exit without reaping it ourselves. The supervisor's
    // wait reaps it before entering said_so_far's bounded stderr drain.
    tokio::time::timeout(DEADLINE, async {
        while rustix::process::test_kill_process(run.pid).is_ok() {
            tokio::task::yield_now().await;
        }
    })
    .await
    .unwrap();
    run.health.failed("old failure".into());
    run.health.woke(&run.woke);
    run.finished().await;
    assert_eq!(run.health.problem(), None);
    assert!(!run.health.refusing());
}

fn link() -> Link {
    Link {
        dest: "controlled-child".into(),
        key: PathBuf::from("unused-key"),
        health: Health::default(),
        woke: watch::channel(0).0,
        latest: Mutex::new(None),
        // Wakes are injected rather than changing the machine's wall clock or sleeping it.
        task: tokio::spawn(std::future::pending()),
    }
}

#[test]
fn ssh_backoff_is_bounded_and_a_wake_retires_old_failures() {
    let health = Health::default();
    for (index, seconds) in [1, 2, 4, 8, 16, 32, 60, 60].into_iter().enumerate() {
        let before = Instant::now();
        health.failed("unreachable".into());
        let after = Instant::now();
        let state = health.lock();
        assert_eq!(state.failures, index as u32 + 1);
        let at = state.retry_at.unwrap();
        let backoff = Duration::from_secs(seconds);
        assert!(at >= before + backoff && at <= after + backoff);
    }
    assert!(health.refusing());
    health.lock().retry_at = Some(Instant::now() - Duration::from_secs(1));
    assert!(!health.refusing());
    let (woke, before_wake) = watch::channel(0);
    health.woke(&woke);
    health.failed_unless_woke("obsolete connection failure".into(), &before_wake);
    assert_eq!(health.problem(), None);
    assert_eq!(health.lock().failures, 0);
    assert!(!health.refusing());
    // A connection begun after waking still records genuine failures.
    health.failed_unless_woke("new failure".into(), &woke.subscribe());
    assert_eq!(health.problem().as_deref(), Some("new failure"));
    assert_eq!(health.lock().failures, 1);
}

#[tokio::test]
async fn only_a_greeting_clears_failures() {
    let link = link();
    link.health.failed("previous failure".into());
    assert!(link.connect_using(child_command("greeting")).await.is_err());
    // Expire the backoff without a sleep. A banner alone must not forgive the old failure.
    link.health.lock().retry_at = None;
    let (output, mut input) = link.connect_using(child_command("greeting")).await.unwrap();
    let mut output = BufReader::new(output);
    line(&mut output, "BANNER").await;
    assert_eq!(link.health.problem().as_deref(), Some("previous failure"));
    input.write_all(b"g").await.unwrap();
    tokio::time::timeout(DEADLINE, await_greeting(&mut output))
        .await
        .unwrap()
        .unwrap();
    assert_eq!(link.health.problem(), None);
    assert!(!link.health.refusing());
    drop(input);
    // Read EOF so that the child has exited; then wait for its supervisor to reap it.
    let mut tail = vec![];
    tokio::time::timeout(DEADLINE, output.read_to_end(&mut tail))
        .await
        .unwrap()
        .unwrap();
    drop(output);
    assert_eq!(link.health.problem(), None);
}

struct LocalRelay(Link);

#[async_trait]
impl Connector for LocalRelay {
    async fn connect(&self) -> io::Result<(Reader, Writer)> {
        self.0.connect_using(child_command("relay")).await
    }
}

#[tokio::test]
async fn a_wake_reconnects_the_real_transport_and_notifies_its_users() {
    let connector = Arc::new(LocalRelay(link()));
    let transport = tokio::time::timeout(
        DEADLINE,
        musubi_transport::StreamTransport::connect(connector.clone()),
    )
    .await
    .unwrap()
    .unwrap();
    assert_eq!(
        transport
            .request("echo", "before".into(), DEADLINE)
            .await
            .unwrap(),
        "before"
    );
    let mut reconnections = transport.reconnections();
    connector.0.health.failed("old connection".into());
    connector.0.health.woke(&connector.0.woke);
    tokio::time::timeout(DEADLINE, reconnections.next())
        .await
        .expect("wake did not cause reconnection");
    assert!(transport.connected());
    assert_eq!(connector.0.health.problem(), None);
    assert_eq!(
        transport
            .request("echo", "after".into(), DEADLINE)
            .await
            .unwrap(),
        "after"
    );
}

#[tokio::test]
async fn settled_connections_keep_the_transport_diagnostic() {
    let mut run = Running::new("stubborn");
    line(&mut run.output, "READY").await;
    let mut link = link();
    link.health = run.health.clone();
    link.latest = Mutex::new(Some(run.settled.clone()));
    link.not_hub(&io::Error::other("wrong hub version"));
    run.input.take();
    run.closed.take();
    run.finished().await;
    assert_eq!(run.health.lock().failures, 1);
    assert_eq!(
        run.health.problem().as_deref(),
        Some("ssh to controlled-child worked, but wrong hub version")
    );
}
