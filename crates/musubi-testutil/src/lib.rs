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
//!
//! The same seed gives each `jj` command its times, as jj's own tests have them: the commits
//! it makes a second later than the last command's, and its operation a millisecond later.
//! jj orders operations by their times, to merge them, as musubi does too, breaking ties by
//! their ids; with the real clock, operations tied or not by how fast a test ran, and a case
//! merged differently from one run to the next. Code that compares operation times with the
//! clock, as expiry does, must ask the environment's [`Clock`] for the time instead.

// Test helpers fail the test on any unexpected error; that is what unwrap is for here.
#![allow(clippy::unwrap_used)]

use std::fs;
use std::hash::Hash as _;
use std::hash::Hasher as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Output;
use std::sync::Arc;
use std::sync::OnceLock;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;
use std::time::Duration;
use std::time::SystemTime;

use jj_lib::backend::MillisSinceEpoch;
use jj_lib::backend::Timestamp;
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
    /// Whether `jj` commands record the real time in their operations, not their seed's.
    real_op_times: bool,
}

impl Default for TestEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TestEnv {
    pub fn new() -> Self {
        check_jj_version();
        let root = tempdir();
        fs::create_dir_all(root.path().join("home/.config")).unwrap();
        Self {
            root,
            seeds: Arc::new(AtomicU64::new(1)),
            real_op_times: false,
        }
    }

    /// An environment whose `jj` commands record the real time in their operations, for
    /// tests that run musubi's own processes, whose daemons judge copies idle by the real
    /// clock. Their commits' times are still their seeds'.
    pub fn with_real_op_times() -> Self {
        Self {
            real_op_times: true,
            ..Self::new()
        }
    }

    /// The clock that agrees with the times this environment's operations record.
    pub fn clock(&self) -> Clock {
        Clock {
            seeds: self.seeds.clone(),
        }
    }

    /// Saves a copy of this environment in `dir`, for [`Self::restore`]: its directory,
    /// with every repository and its home, and where its seeds for change ids have got to.
    pub fn save(&self, dir: &Path) {
        fs::create_dir_all(dir).unwrap();
        copy_tree(self.root(), &dir.join("root"));
        let seed = self.seeds.load(Ordering::Relaxed);
        fs::write(dir.join("seed"), seed.to_string()).unwrap();
    }

    /// An environment of its own with a copy of the one saved in `dir`, its repositories at
    /// the same places in it (see [`Self::repo_handle`]). jj keeps no path of a repository's
    /// in the repository, and takes one whose recorded path is gone for one that moved.
    pub fn restore(dir: &Path) -> Self {
        check_jj_version();
        let root = tempdir();
        // A clone wants a path with nothing there.
        fs::remove_dir(root.path()).unwrap();
        copy_tree(&dir.join("root"), root.path());
        let seed = fs::read_to_string(dir.join("seed")).unwrap();
        Self {
            root,
            seeds: Arc::new(AtomicU64::new(seed.parse().unwrap())),
            real_op_times: false,
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

    /// Creates a repository for `machine` that isn't colocated, whose git store is inside
    /// `.jj` and whose workspace is named after it.
    pub fn init_non_colocated_repo(&self, machine: &str) -> TestRepo {
        let repo = self.repo_handle(machine);
        fs::write(&repo.config_path, machine_config(machine)).unwrap();
        repo.run_jj_at(self.root(), &["git", "init", "--no-colocate", machine]);
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
            real_op_times: self.real_op_times,
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

/// A new directory for a test, kept with `MUSUBI_KEEP_TEST_DIRS` for inspecting a failure's
/// repositories afterwards.
///
/// On Linux it is in `/dev/shm`, in memory, unless `TMPDIR` is set, the directory is to be
/// kept, or `/dev/shm` is mounted `noexec`, as in a Docker container, since some tests run
/// scripts they write. jj syncs what it writes to disk, and on a disk, waiting for that took
/// most of the suite's time. Nothing a test writes needs to survive a power cut. Where
/// `/dev/shm` is too small, as Docker's 64 MB may be for a run on many cores, set `TMPDIR`.
pub fn tempdir() -> TempDir {
    let keep = std::env::var_os("MUSUBI_KEEP_TEST_DIRS").is_some();
    let mut builder = tempfile::Builder::new();
    builder.prefix("musubi-test-");
    let mut root = match in_memory() {
        Some(dir) if !keep => builder
            .tempdir_in(dir)
            .or_else(|_| builder.tempdir())
            .unwrap(),
        _ => builder.tempdir().unwrap(),
    };
    if keep {
        root.disable_cleanup(true);
    }
    root
}

/// `/dev/shm`, on Linux, unless `TMPDIR` is set or it is mounted `noexec`.
fn in_memory() -> Option<&'static Path> {
    static IN_MEMORY: OnceLock<Option<&'static Path>> = OnceLock::new();
    *IN_MEMORY.get_or_init(|| {
        if !cfg!(target_os = "linux") || std::env::var_os("TMPDIR").is_some() {
            return None;
        }
        // Each line: device, mount point, type, options, ...; the last mount there counts.
        let mounts = fs::read_to_string("/proc/self/mounts").ok()?;
        let options = mounts.lines().rev().find_map(|line| {
            let fields: Vec<&str> = line.split(' ').collect();
            (fields.get(1) == Some(&"/dev/shm")).then(|| fields.get(3).copied())?
        })?;
        let exec = !options.split(',').any(|option| option == "noexec");
        exec.then_some(Path::new("/dev/shm"))
    })
}

/// Copies the directory `from` to `to`. On macOS that is one clonefile(2) of the whole
/// tree, when `to` doesn't exist yet: alongside the rest of the suite, making a tree's
/// files one by one takes over ten times longer. Other systems clone only a file at a
/// time, which saves nothing on small files: those it copies.
pub fn copy_tree(from: &Path, to: &Path) {
    if cfg!(target_os = "macos") && reflink_copy::reflink(from, to).is_ok() {
        return;
    }
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let to = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&entry.path(), &to);
        } else {
            fs::copy(entry.path(), to).unwrap();
        }
    }
}

/// How long a recording of another build of a test binary is kept (see [`recorded`]).
const STALE_RECORDING: Duration = Duration::from_secs(3600);

/// A directory under `base`, normally the test binary's `CARGO_TARGET_TMPDIR`, holding what
/// `record` wrote to it, once for each build of the running test binary. nextest runs each
/// test in a process of its own, so each would otherwise make it again, many of them at
/// once in a full run. The first process to ask records it, while the others wait on a
/// file lock; a later run of the same build finds it there.
pub fn recorded(base: &Path, name: &str, record: impl FnOnce(&Path)) -> PathBuf {
    let cache = base.join(name);
    fs::create_dir_all(&cache).unwrap();
    // Not truncated: on Windows that fails while another process holds the lock.
    let lock = fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(cache.join("lock"))
        .unwrap();
    lock.lock().unwrap();
    let dir = cache.join(build());
    if !dir.join("recorded").exists() {
        // One a killed process left half recorded.
        if dir.exists() {
            fs::remove_dir_all(&dir).unwrap();
        }
        // Other builds' recordings, once their tests are long done: a build in another
        // checkout sharing this target directory may still be copying from its own.
        for entry in fs::read_dir(&cache).unwrap() {
            let path = entry.unwrap().path();
            let age = path.metadata().and_then(|metadata| metadata.modified());
            if path.is_dir()
                && age.is_ok_and(|time| time.elapsed().unwrap_or_default() > STALE_RECORDING)
            {
                fs::remove_dir_all(path).ok();
            }
        }
        record(&dir);
        fs::write(dir.join("recorded"), "").unwrap();
    }
    dir
}

/// This build of the running test binary: its path, size, and modification time, hashed.
fn build() -> String {
    let exe = std::env::current_exe().unwrap();
    let metadata = fs::metadata(&exe).unwrap();
    let mut hasher = std::hash::DefaultHasher::new();
    (&exe, metadata.len(), metadata.modified().unwrap()).hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

/// jj's user config for a test machine. It turns on `snapshot.auto-update-stale`, which
/// musubi leaves off, because the tests expect a machine's next `jj` command to update the
/// files another machine's rewrite left stale.
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
    real_op_times: bool,
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
    /// their own for change ids, and for the times of the commits and operations they write
    /// (see [`Clock::retime`]). Those times are in 2001: a node given these settings must
    /// judge copies unused by the environment's [`Clock`], not the system's, or it takes
    /// every copy for unused since then.
    pub fn settings(&self) -> UserSettings {
        let mut config = StackedConfig::with_defaults();
        let seed = self.next_seed();
        let text = format!(
            "{}debug.randomness-seed = {seed}\n",
            machine_config(&self.hostname),
        );
        config.add_layer(ConfigLayer::parse(ConfigSource::User, &text).unwrap());
        if !self.real_op_times {
            config.add_layer(times_layer(seed));
        }
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
        self.jj_command(&self.path).args(args).output().unwrap()
    }

    /// Runs `git` in the repository and returns stdout, panicking on failure.
    pub fn git(&self, args: &[&str]) -> String {
        let output = self.command("git", &self.path).args(args).output().unwrap();
        expect_success("git", args, &output)
    }

    fn run_jj_at(&self, dir: &Path, args: &[&str]) -> String {
        let output = self.jj_command(dir).args(args).output().unwrap();
        expect_success("jj", args, &output)
    }

    fn jj_command(&self, dir: &Path) -> Command {
        let mut command = self.command("jj", dir);
        command
            // Without a terminal, jj asks `tput` for its width: two more processes for each
            // command that writes output.
            .env("COLUMNS", "80")
            // jj starts a thread a core for each command, which on 32 cores nearly doubled
            // the CPU a command took in repositories this small.
            .env("RAYON_NUM_THREADS", "1");
        command
    }

    /// A command for any program, run in the repository with the same hermetic
    /// environment as `jj`.
    pub fn program(&self, program: &Path) -> Command {
        let mut command = self.command(program.to_str().unwrap(), &self.path);
        command
            .env(
                "MUSUBI_STATE_DIR",
                self.home.join(format!("musubi-{}", self.machine)),
            )
            // No test reaches a real machine over ssh, even by a name that resolves, such as
            // this computer's own: one that needs ssh gives a stand-in of its own.
            .env("MUSUBI_SSH", self.home.join("no-ssh"));
        command
    }

    /// Each command's own seed, from which it takes its randomness and, if it is `jj`, the
    /// times its commits and its operation record.
    fn next_seed(&self) -> u64 {
        self.seeds.fetch_add(1, Ordering::Relaxed)
    }

    fn command(&self, program: &str, dir: &Path) -> Command {
        let mut command = Command::new(program);
        let seed = self.next_seed();
        command
            .current_dir(dir)
            .env_clear()
            .env("PATH", std::env::var_os("PATH").unwrap_or_default())
            .env("JJ_RANDOMNESS_SEED", seed.to_string())
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
        if Path::new(program)
            .file_stem()
            .is_some_and(|stem| stem == "jj")
        {
            command.env("JJ_TIMESTAMP", commit_timestamp(seed));
            if !self.real_op_times {
                command.env("JJ_OP_TIMESTAMP", operation_timestamp(seed));
            }
        }
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

/// The time a `jj` command made with `seed` gives its commits, as `JJ_TIMESTAMP`: a second
/// later for each seed. Git records whole seconds, so jj, repeating a rewrite it undid within
/// the same second, would make the very commit it made before, and refuse it as one that
/// exists already; how fast a test ran would decide whether it did. With these, it never does,
/// and every run of a test makes the same commits.
fn commit_timestamp(seed: u64) -> String {
    rfc3339(seed * 1000)
}

/// The time a `jj` command made with `seed` gives its operation, as `JJ_OP_TIMESTAMP`, and
/// what [`Clock::now`] says once it has run: a millisecond later for each seed, the
/// resolution jj records. An hour passes only after millions of commands, so no copy goes
/// unused for its `musubi.forget-after` in a test unless the test says that it did, as a real
/// one wouldn't in the time a test takes.
fn operation_timestamp(seed: u64) -> String {
    rfc3339(seed)
}

/// Milliseconds since the start of 2001, the tests' epoch.
const EPOCH_MILLIS: u64 = 978_307_200_000;

fn rfc3339(millis: u64) -> String {
    let timestamp = Timestamp {
        timestamp: MillisSinceEpoch(i64::try_from(EPOCH_MILLIS + millis).unwrap()),
        tz_offset: 0,
    };
    timestamp.to_datetime().unwrap().to_rfc3339()
}

/// A config layer giving what jj writes the times that a `jj` command with `seed` gives
/// its commits and its operation.
fn times_layer(seed: u64) -> ConfigLayer {
    let text = format!(
        "debug.commit-timestamp = \"{}\"\ndebug.operation-timestamp = \"{}\"\n",
        commit_timestamp(seed),
        operation_timestamp(seed)
    );
    ConfigLayer::parse(ConfigSource::CommandArg, &text).unwrap()
}

/// An environment's clock, which agrees with the times its operations record: the time of
/// the latest seed taken. Code that compares operations' times with the clock takes the time
/// from this one in tests.
#[derive(Clone)]
pub struct Clock {
    seeds: Arc<AtomicU64>,
}

impl Clock {
    /// The time the latest command's operation recorded, or would have.
    pub fn now(&self) -> SystemTime {
        let seed = self.seeds.load(Ordering::Relaxed).saturating_sub(1);
        SystemTime::UNIX_EPOCH + Duration::from_millis(EPOCH_MILLIS + seed)
    }

    /// `settings` with the next seed's times for the commits and operations they write, as
    /// if a `jj` command ran now, keeping their randomness. jj-lib takes these times from the
    /// settings a repository was opened with, so a test hands a node new ones as it acts,
    /// to keep its operations in order with the commands' around them.
    pub fn retime(&self, settings: &UserSettings) -> UserSettings {
        let seed = self.seeds.fetch_add(1, Ordering::Relaxed);
        let mut config = settings.config().clone();
        config.remove_layers(ConfigSource::CommandArg);
        config.add_layer(times_layer(seed));
        settings.with_new_config(config).unwrap()
    }
}
