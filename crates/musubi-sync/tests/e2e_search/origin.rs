//! A shared bare git remote, `origin`, that every machine fetches from and pushes to, and
//! that moves on its own (someone else pushing), as in tests/races/remotes.rs.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

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
        self.git(&self.seed, &["commit", "--quiet", "-m", &message]);
        self.git(
            &self.seed,
            &["push", "--quiet", &bare, "HEAD:refs/heads/main"],
        );
        message
    }
}
