//! The Lean model as an oracle: a child process speaking docs/conformance.md's JSON lines.

use std::io;
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

    fn call(&mut self, request: &Value) -> Value {
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
}

impl Drop for Oracle {
    fn drop(&mut self) {
        self.child.kill().ok();
        self.child.wait().ok();
    }
}

/// Runs `lake build oracle` in `formal`, which does nothing if the oracle is up to date.
fn build(formal: &Path) {
    let run = |lake: &Path| {
        Command::new(lake)
            .args(["build", "oracle"])
            .current_dir(formal)
            // Progress, such as elan downloading the toolchain, shows as it happens.
            .stderr(Stdio::inherit())
            .output()
    };
    // elan puts `lake` on the PATH, but not of every shell.
    let output = match run(Path::new("lake")) {
        Err(err) if err.kind() == io::ErrorKind::NotFound => std::env::var_os("HOME")
            .map(|home| run(&Path::new(&home).join(".elan/bin/lake")))
            .unwrap_or(Err(err)),
        output => output,
    }
    .unwrap_or_else(|err| {
        panic!("cannot run `lake build oracle` ({err}): install elan, or set MUSUBI_ORACLE")
    });
    assert!(
        output.status.success(),
        "`lake build oracle` failed:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}
