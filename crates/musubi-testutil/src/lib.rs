//! Hermetic jj repositories for tests, driven through the real `jj` CLI.
//!
//! Each [`TestEnv`] has its own home directory and per-machine jj config, so tests never read
//! the developer's configuration. The `jj` on `PATH` must be the version musubi's jj-lib is
//! pinned to; [`TestEnv::new`] checks.

// Test helpers fail the test on any unexpected error; that is what unwrap is for here.
#![allow(clippy::unwrap_used)]

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;
use std::sync::OnceLock;

use jj_lib::config::ConfigLayer;
use jj_lib::config::ConfigSource;
use jj_lib::config::StackedConfig;
use jj_lib::settings::UserSettings;
use tempfile::TempDir;

/// The jj version musubi's jj-lib is pinned to.
pub const JJ_VERSION: &str = "0.46.0";

pub struct TestEnv {
    root: TempDir,
}

impl Default for TestEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TestEnv {
    pub fn new() -> Self {
        check_jj_version();
        let root = tempfile::Builder::new()
            .prefix("musubi-test-")
            .tempdir()
            .unwrap();
        fs::create_dir_all(root.path().join("home/.config")).unwrap();
        Self { root }
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

    /// Settings equivalent to the ones the `jj` CLI uses in this repository.
    pub fn settings(&self) -> UserSettings {
        let mut config = StackedConfig::with_defaults();
        config.add_layer(
            ConfigLayer::parse(ConfigSource::User, &machine_config(&self.hostname)).unwrap(),
        );
        UserSettings::from_config_and_home_dir(config, Some(self.home.clone())).unwrap()
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

    fn command(&self, program: &str, dir: &Path) -> Command {
        let mut command = Command::new(program);
        command
            .current_dir(dir)
            .env_clear()
            .env("PATH", std::env::var_os("PATH").unwrap_or_default())
            .env("HOME", &self.home)
            .env("XDG_CONFIG_HOME", self.home.join(".config"))
            .env("JJ_CONFIG", &self.config_path)
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_AUTHOR_NAME", "Test User")
            .env("GIT_AUTHOR_EMAIL", "test@example.com")
            .env("GIT_COMMITTER_NAME", "Test User")
            .env("GIT_COMMITTER_EMAIL", "test@example.com");
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

/// A `nats-server` on a free local port, killed when dropped.
pub struct NatsServer {
    child: std::process::Child,
    port: u16,
}

impl NatsServer {
    /// Starts `nats-server`, which must be on `PATH`, with the given `max_payload`.
    pub fn start(max_payload: usize) -> Self {
        let port = std::net::TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
            .port();
        let dir = tempfile::tempdir().unwrap();
        let config = dir.path().join("nats.conf");
        fs::write(&config, format!("max_payload: {max_payload}\n")).unwrap();
        let child = Command::new("nats-server")
            .args(["-a", "127.0.0.1", "-p", &port.to_string(), "-c"])
            .arg(&config)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("`nats-server` is not on PATH");
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        while std::net::TcpStream::connect(("127.0.0.1", port)).is_err() {
            assert!(
                std::time::Instant::now() < deadline,
                "nats-server did not start"
            );
            std::thread::sleep(std::time::Duration::from_millis(20));
        }
        // The config file is read at startup; the directory can go.
        drop(dir);
        Self { child, port }
    }

    pub fn url(&self) -> String {
        format!("nats://127.0.0.1:{}", self.port)
    }
}

impl Drop for NatsServer {
    fn drop(&mut self) {
        self.child.kill().ok();
        self.child.wait().ok();
    }
}
