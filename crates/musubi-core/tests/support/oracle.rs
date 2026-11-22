//! The Lean model as an oracle: a child process speaking the JSON lines of
//! docs/internals/conformance.md.

use std::cell::Cell;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Child;
use std::process::ChildStdin;
use std::process::ChildStdout;
use std::process::Command;
use std::process::Stdio;
use std::sync::OnceLock;

use serde_json::Value;
use serde_json::json;

pub struct Oracle {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

thread_local! {
    /// The oracle that this thread's last caller gave back, for the next: starting one takes
    /// longer than most generated cases.
    #[cfg_attr(
        any(target_os = "illumos", target_os = "solaris"),
        allow(
            clippy::missing_const_for_thread_local,
            reason = "clippy wrongly reports this on illumos, but only when the \
                      rust-src component is installed, so it's allowed rather than expected"
        )
    )]
    static KEPT: Cell<Option<Oracle>> = const { Cell::new(None) };
}

impl Oracle {
    /// The oracle binary: `$MUSUBI_ORACLE`, or else the one `lake build oracle` writes,
    /// brought up to date with the model first.
    pub fn path() -> PathBuf {
        static BUILT: OnceLock<PathBuf> = OnceLock::new();
        if let Some(path) = std::env::var_os("MUSUBI_ORACLE") {
            return PathBuf::from(path);
        }
        BUILT
            .get_or_init(|| {
                let formal = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../formal");
                build(&formal);
                formal.join(".lake/build/bin/oracle")
            })
            .clone()
    }

    pub fn spawn() -> Self {
        let path = Self::path();
        let mut child = Command::new(&path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap_or_else(|err| panic!("cannot run the Lean oracle at {path:?} ({err})"));
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        Self {
            child,
            stdin,
            stdout,
        }
    }

    /// Calls `f` with this thread's oracle, which it keeps for the next caller, as for
    /// [`Oracle::kept`]. Only for requests that leave the oracle as they found it, such as
    /// `names` or `attempts`, or that start by resetting it.
    pub fn with<R>(f: impl FnOnce(&mut Self) -> R) -> R {
        let mut oracle = Self::kept();
        let result = f(&mut oracle);
        oracle.keep();
        result
    }

    /// The oracle this thread's last caller gave back with [`Oracle::keep`], or else a new
    /// one. A caller that panics, as a failing case does, drops it rather than giving it
    /// back, since its state is then unknown, and the next caller gets a new one.
    pub fn kept() -> Self {
        KEPT.take().unwrap_or_else(Self::spawn)
    }

    /// Gives the oracle back for this thread's next caller of [`Oracle::kept`].
    pub fn keep(self) {
        KEPT.set(Some(self));
    }

    /// Sends one request, and returns the reply.
    pub fn call(&mut self, request: &Value) -> Value {
        writeln!(self.stdin, "{request}").unwrap();
        self.stdin.flush().unwrap();
        let mut line = String::new();
        self.stdout.read_line(&mut line).unwrap();
        serde_json::from_str(&line).unwrap_or_else(|err| panic!("bad oracle reply {line:?}: {err}"))
    }

    pub fn reset(&mut self, nodes: usize) -> Value {
        let reply = self.call(&json!({"op": "reset", "nodes": nodes}));
        assert_eq!(reply["ok"], true, "oracle reset failed: {reply}");
        reply["state"].clone()
    }

    /// Applies an action; the model's new state, or why the model rejects the action.
    pub fn step(&mut self, action: &Value) -> Result<Value, String> {
        let reply = self.call(&json!({"op": "step", "action": action}));
        if reply["ok"] == true {
            Ok(reply["state"].clone())
        } else {
            Err(reply["error"]
                .as_str()
                .unwrap_or("no reason given")
                .to_owned())
        }
    }

    /// The model state's liveness measures and whether it has converged
    /// (docs/internals/conformance.md, "Liveness").
    pub fn measure(&mut self) -> Measure {
        let reply = self.call(&json!({"op": "measure"}));
        assert_eq!(reply["ok"], true, "oracle measure failed: {reply}");
        Measure {
            measure: numbers(&reply, "measure"),
            rmeasure: numbers(&reply, "rmeasure"),
            converged: reply["converged"] == true,
        }
    }

    /// What a policy `Push` of `new` from `node` uploads: `upOps` and `upObjs`, sorted.
    pub fn upload(&mut self, node: usize, new: u64) -> (Vec<u64>, Vec<u64>) {
        let reply = self.call(&json!({"op": "upload", "node": node, "new": new}));
        assert_eq!(reply["ok"], true, "oracle upload failed: {reply}");
        (numbers(&reply, "ops"), numbers(&reply, "objs"))
    }
}

fn numbers(reply: &Value, key: &str) -> Vec<u64> {
    serde_json::from_value(reply[key].clone())
        .unwrap_or_else(|err| panic!("bad {key} in oracle reply {reply}: {err}"))
}

/// The oracle's answer to a `measure` request. Each measure is compared lexicographically,
/// as `Vec`s are.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Measure {
    /// `measure` of `Liveness.lean`, proved to fall only from states the hub reached
    /// without going back.
    pub measure: Vec<u64>,
    /// `rmeasure` of `Regress.lean`, which falls whether or not it has.
    pub rmeasure: Vec<u64>,
    /// `convergedE`.
    pub converged: bool,
}

impl Drop for Oracle {
    fn drop(&mut self) {
        self.child.kill().ok();
        self.child.wait().ok();
    }
}

/// Runs `lake build oracle` in `formal`, which does nothing if the oracle is up to date.
/// nextest runs each test in a process of its own, and two builds at once break each other's
/// files, so a build holds a lock on a file in `formal/.lake` throughout: the others wait, then
/// find the oracle up to date.
fn build(formal: &Path) {
    let lake = formal.join(".lake");
    std::fs::create_dir_all(&lake)
        .unwrap_or_else(|err| panic!("cannot make {lake:?} for the oracle ({err})"));
    let lock = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(lake.join("oracle-build.lock"))
        .unwrap_or_else(|err| panic!("cannot make the oracle's build lock in {lake:?} ({err})"));
    lock.lock()
        .unwrap_or_else(|err| panic!("cannot lock the oracle's build ({err})"));
    let output = Command::new("lake")
        .args(["build", "oracle"])
        .current_dir(formal)
        // Progress, such as elan downloading the toolchain, shows as it happens.
        .stderr(Stdio::inherit())
        .output()
        .unwrap_or_else(|err| {
            panic!("cannot run `lake build oracle` ({err}): put lake on PATH, or set MUSUBI_ORACLE")
        });
    assert!(
        output.status.success(),
        "`lake build oracle` failed:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}
