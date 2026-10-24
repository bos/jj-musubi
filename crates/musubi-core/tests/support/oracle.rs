//! The Lean model as an oracle: a child process speaking the JSON lines of
//! docs/internals/conformance.md.

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

    /// Sends one request, and returns the reply.
    pub fn call(&mut self, request: &Value) -> Value {
        writeln!(self.stdin, "{request}").unwrap();
        self.stdin.flush().unwrap();
        let mut line = String::new();
        self.stdout.read_line(&mut line).unwrap();
        serde_json::from_str(&line).unwrap_or_else(|err| panic!("bad oracle reply {line:?}: {err}"))
    }

    pub fn reset(&mut self, nodes: usize) {
        let reply = self.call(&json!({"op": "reset", "nodes": nodes}));
        assert_eq!(reply["ok"], true, "oracle reset failed: {reply}");
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
    pub converged: bool,
}

impl Drop for Oracle {
    fn drop(&mut self) {
        self.child.kill().ok();
        self.child.wait().ok();
    }
}

/// Runs `lake build oracle` in `formal`, which does nothing if the oracle is up to date.
fn build(formal: &Path) {
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
