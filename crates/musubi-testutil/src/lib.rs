//! Hermetic jj repositories for tests, driven through the real `jj` CLI.
//!
//! Each [`TestEnv`] has its own home directory and per-machine jj config, so tests never read
//! the developer's configuration. The `jj` on `PATH` must be the version musubi's jj-lib is
//! pinned to; [`TestEnv::new`] checks.
//!
//! jj makes up a random change id for each new change. Here each command, and each set of
//! [`TestRepo::settings`], gets the next seed from a counter that the environment's
//! repositories share, so that a test that runs the same commands makes the same changes,
//! and a generated test case replays exactly.

// Test helpers fail the test on any unexpected error; that is what unwrap is for here.
#![allow(clippy::unwrap_used)]

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;
use std::sync::Arc;
use std::sync::OnceLock;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::config::StackedConfig;
use jj_lib::settings::UserSettings;
use tempfile::TempDir;

/// The jj version musubi's jj-lib is pinned to.
pub const JJ_VERSION: &str = "0.46.0";

pub struct TestEnv {
    root: TempDir,
    seeds: Arc<AtomicU64>,
}

impl Default for TestEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TestEnv {
    pub fn new() -> Self {
        check_jj_version();
        let mut root = tempfile::Builder::new()
            .prefix("musubi-test-")
            .tempdir()
            .unwrap();
        // For inspecting a failure's repositories afterwards.
        if std::env::var_os("MUSUBI_KEEP_TEST_DIRS").is_some() {
            root.disable_cleanup(true);
        }
        fs::create_dir_all(root.path().join("home/.config")).unwrap();
        Self {
            root,
            seeds: Arc::new(AtomicU64::new(1)),
        }
    }

    pub fn root(&self) -> &Path {
        self.root.path()
    }

    /// Creates a colocated repository for `machine`, whose workspace is named after it.
    pub fn init_repo(&self, machine: &str) -> TestRepo {
        let repo = self.repo_handle(machine);
        fs::write(&repo.config_path, machine_config(machine)).unwrap();
        repo.run_jj_at(self.root(), &["git", "init", "--colocate", machine]);
        repo.jj(&["workspace", "rename", machine]);
        repo
    }

    /// Creates a colocated repository in directory `machine` whose workspace is named
    /// `workspace`, for provoking name collisions.
    pub fn init_repo_with_workspace(&self, machine: &str, workspace: &str) -> TestRepo {
        let repo = self.repo_handle(machine);
        fs::write(&repo.config_path, machine_config(machine)).unwrap();
        repo.run_jj_at(self.root(), &["git", "init", "--colocate", machine]);
        repo.jj(&["workspace", "rename", workspace]);
        repo
    }

    /// Creates a repository using jj's simple backend, whose workspace is named after
    /// `machine`.
    pub fn init_simple_repo(&self, machine: &str) -> TestRepo {
        let repo = self.repo_handle(machine);
        fs::write(&repo.config_path, machine_config(machine)).unwrap();
        repo.run_jj_at(self.root(), &["debug", "init-simple", machine]);
        repo.jj(&["workspace", "rename", machine]);
        repo
    }

    /// A handle for a repository directory that may not exist yet.
    pub fn repo_handle(&self, machine: &str) -> TestRepo {
        TestRepo {
            home: self.root().join("home"),
            config_path: self.root().join(format!("config-{machine}.toml")),
            path: self.root().join(machine),
            machine: machine.to_owned(),
            hostname: machine.to_owned(),
            seeds: self.seeds.clone(),
        }
    }

    /// Creates a colocated repository in directory `machine` whose jj
    /// `operation.hostname` is `hostname`, for provoking machine-name collisions.
    pub fn init_repo_with_hostname(&self, machine: &str, hostname: &str) -> TestRepo {
        let mut repo = self.repo_handle(machine);
        repo.hostname = hostname.to_owned();
        fs::write(&repo.config_path, machine_config(hostname)).unwrap();
        repo.run_jj_at(self.root(), &["git", "init", "--colocate", machine]);
        repo
    }
}

fn machine_config(machine: &str) -> String {
    format!(
        r#"
user.name = "Test User"
user.email = "test@example.com"
operation.hostname = "{machine}"
operation.username = "test"
snapshot.auto-update-stale = true
ui.color = "never"
ui.paginate = "never"
"#
    )
}

fn check_jj_version() {
    static CHECKED: OnceLock<()> = OnceLock::new();
    CHECKED.get_or_init(|| {
        let output = Command::new("jj")
            .arg("--version")
            .output()
            .expect("`jj` is not on PATH");
        let version = String::from_utf8_lossy(&output.stdout);
        // Release builds append the commit they were built from: `jj 0.46.0-7d382314...`.
        let number = version
            .split_whitespace()
            .nth(1)
            .map(|v| v.split_once('-').map_or(v, |(number, _)| number));
        assert!(
            number == Some(JJ_VERSION),
            "tests need jj {JJ_VERSION} on PATH, found {version:?}"
        );
    });
}

pub struct TestRepo {
    home: PathBuf,
    config_path: PathBuf,
    path: PathBuf,
    machine: String,
    /// jj's `operation.hostname`, which musubi takes as the machine's name.
    hostname: String,
    /// The environment's counter of seeds for jj's change ids.
    seeds: Arc<AtomicU64>,
}

impl TestRepo {
    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn machine(&self) -> &str {
        &self.machine
    }

    /// The `.jj/repo` directory.
    pub fn repo_path(&self) -> PathBuf {
        self.path.join(".jj/repo")
    }

    /// Settings equivalent to the ones the `jj` CLI uses in this repository, with a seed of
    /// their own for change ids.
    pub fn settings(&self) -> UserSettings {
        let mut config = StackedConfig::with_defaults();
        let text = format!(
            "{}debug.randomness-seed = {}\n",
            machine_config(&self.hostname),
            self.next_seed()
        );
        config.add_layer(ConfigLayer::parse(ConfigSource::User, &text).unwrap());
        UserSettings::from_config_and_home_dir(config, Some(self.home.clone())).unwrap()
    }

    /// jj's repo config file for this repository (`jj config path --repo`).
    pub fn repo_config_path(&self) -> PathBuf {
        PathBuf::from(self.jj(&["config", "path", "--repo"]).trim())
    }

    pub fn write_file(&self, name: &str, contents: &str) {
        let path = self.path.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }

    /// Runs `jj` in the repository and returns stdout, panicking on failure.
    pub fn jj(&self, args: &[&str]) -> String {
        self.run_jj_at(&self.path, args)
    }

    /// Runs `jj` in the repository and returns the raw output.
    pub fn jj_output(&self, args: &[&str]) -> Output {
        self.command("jj", &self.path).args(args).output().unwrap()
    }

    /// Runs `git` in the repository and returns stdout, panicking on failure.
    pub fn git(&self, args: &[&str]) -> String {
        let output = self.command("git", &self.path).args(args).output().unwrap();
        expect_success("git", args, &output)
    }

    fn run_jj_at(&self, dir: &Path, args: &[&str]) -> String {
        let output = self.command("jj", dir).args(args).output().unwrap();
        expect_success("jj", args, &output)
    }

    /// A command for any program, run in the repository with the same hermetic
    /// environment as `jj`.
    pub fn program(&self, program: &Path) -> Command {
        let mut command = self.command(program.to_str().unwrap(), &self.path);
        command.env(
            "MUSUBI_CONFIG_DIR",
            self.home.join(format!("musubi-{}", self.machine)),
        );
        command
    }

    fn next_seed(&self) -> u64 {
        self.seeds.fetch_add(1, Ordering::Relaxed)
    }

    fn command(&self, program: &str, dir: &Path) -> Command {
        let mut command = Command::new(program);
        command
            .current_dir(dir)
            .env_clear()
            .env("PATH", std::env::var_os("PATH").unwrap_or_default())
            .env("JJ_RANDOMNESS_SEED", self.next_seed().to_string())
            // Windows's equivalents of `HOME`, where jj keeps each repository's config:
            // without them it would use the real user's, which every test would share.
            .env("USERPROFILE", &self.home)
            .env("APPDATA", self.home.join("AppData/Roaming"))
            .env("LOCALAPPDATA", self.home.join("AppData/Local"))
            .env("HOME", &self.home)
            .env("XDG_CONFIG_HOME", self.home.join(".config"))
            .env("JJ_CONFIG", &self.config_path)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_AUTHOR_NAME", "Test User")
            .env("GIT_AUTHOR_EMAIL", "test@example.com")
            .env("GIT_COMMITTER_NAME", "Test User")
            .env("GIT_COMMITTER_EMAIL", "test@example.com");
        // What Windows itself needs: without `SystemRoot`, for one, sockets don't work.
        for name in [
            "SystemRoot",
            "SystemDrive",
            "windir",
            "TEMP",
            "TMP",
            "PATHEXT",
        ] {
            if let Some(value) = std::env::var_os(name) {
                command.env(name, value);
            }
        }
        command
    }
}

fn expect_success(program: &str, args: &[&str], output: &Output) -> String {
    assert!(
        output.status.success(),
        "`{program} {}` failed:\n{}",
        args.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout.clone()).unwrap()
}
