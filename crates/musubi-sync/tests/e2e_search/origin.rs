//! A shared bare git remote, `origin`, that every machine fetches from and pushes to, and
//! that moves on its own (someone else pushing), as in tests/races/remotes.rs.

use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;

pub struct Origin {
    pub bare: PathBuf,
    seed: PathBuf,
    home: PathBuf,
    pushes: usize,
}

impl Origin {
    /// A bare repository under `root` with one commit on `main`.
    pub fn new(root: &Path) -> Self {
        let origin = Self {
            bare: root.join("origin.git"),
            seed: root.join("seed"),
            home: root.join("home"),
            pushes: 0,
        };
        std::fs::create_dir_all(&origin.seed).unwrap();
        origin.git(
            root,
            &[
                "init",
                "--quiet",
                "--bare",
                "--initial-branch=main",
                origin.bare.to_str().unwrap(),
            ],
        );
        origin.git(&origin.seed, &["init", "--quiet", "--initial-branch=main"]);
        origin
    }

    fn git(&self, dir: &Path, args: &[&str]) -> String {
        let output = Command::new("git")
            .current_dir(dir)
            .args(args)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("HOME", &self.home)
            .env("GIT_AUTHOR_NAME", "Upstream")
            .env("GIT_AUTHOR_EMAIL", "upstream@example.com")
            .env("GIT_COMMITTER_NAME", "Upstream")
            .env("GIT_COMMITTER_EMAIL", "upstream@example.com")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    }

    /// Someone else pushes a new commit on top of origin's `main`. The seed fetches first,
    /// so that the push is a fast-forward of whatever the hive pushed there.
    pub fn advance(&mut self) -> String {
        self.pushes += 1;
        let bare = self.bare.to_str().unwrap().to_owned();
        let has_main = !self
            .git(&self.bare, &["for-each-ref", "refs/heads/main"])
            .is_empty();
        if has_main {
            self.git(&self.seed, &["fetch", "--quiet", &bare, "main"]);
            self.git(&self.seed, &["reset", "--quiet", "--hard", "FETCH_HEAD"]);
        }
        std::fs::write(
            self.seed.join("upstream"),
            format!("upstream {}\n", self.pushes),
        )
        .unwrap();
        self.git(&self.seed, &["add", "upstream"]);
        let message = format!("upstream {}", self.pushes);
        // Written by hand, to give it a change id: jj makes one up from the commit id of a
        // commit without, and this one's parent may be a commit jj pushed, whose id
        // depends on when jj made it.
        let tree = self.git(&self.seed, &["write-tree"]);
        let head = self.git(
            &self.seed,
            &["for-each-ref", "--format=%(objectname)", "refs/heads/main"],
        );
        let parent = match head.trim() {
            "" => String::new(),
            head => format!("parent {head}\n"),
        };
        let when = format!("{} +0000", 1_000_000_000 + self.pushes);
        let commit = format!(
            "tree {}\n{parent}author Upstream <upstream@example.com> {when}\n\
             committer Upstream <upstream@example.com> {when}\nchange-id {}\n\n{message}\n",
            tree.trim(),
            change_id(self.pushes),
        );
        let id = self.git_with_input(
            &self.seed,
            &["hash-object", "-t", "commit", "-w", "--stdin"],
            &commit,
        );
        self.git(&self.seed, &["reset", "--quiet", "--hard", id.trim()]);
        self.git(
            &self.seed,
            &["push", "--quiet", &bare, "HEAD:refs/heads/main"],
        );
        message
    }

    fn git_with_input(&self, dir: &Path, args: &[&str], input: &str) -> String {
        let mut child = Command::new("git")
            .current_dir(dir)
            .args(args)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("HOME", &self.home)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(input.as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).unwrap()
    }
}

/// The change id of origin's `n`th upstream commit, in jj's notation for change ids:
/// hexadecimal with the digits 0 to f written as z to k.
fn change_id(n: usize) -> String {
    format!("{:032x}", 0x0057_ea4d_u128 << 96 | n as u128)
        .chars()
        .map(|digit| char::from(b'z' - u8::try_from(digit.to_digit(16).unwrap()).unwrap()))
        .collect()
}
