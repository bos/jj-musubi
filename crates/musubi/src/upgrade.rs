//! The daemon upgrading musubi when a hub runs a newer release: it runs the command
//! `musubi.upgrade-command` names, once for each such release, and once the binary it started
//! from is that release, starts again from it (docs/guides/manage.md, "Upgrade musubi").
//!
//! Only towards the hub: a machine newer than its hub runs nothing, so that the hub's release
//! is the one place to choose, and nothing can go back and forth.

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Child;
use std::process::Command;
use std::process::ExitStatus;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::PoisonError;
use std::time::Duration;
use std::time::Instant;

use anyhow::Context as _;
use musubi_sync::wire::RELEASE;
use semver::Version;

use crate::config;
use crate::config::Settings;

/// How long the upgrade command may run, building musubi from source included.
const TIMEOUT: Duration = Duration::from_secs(60 * 60);

/// The binary the daemon started from, which an upgrade replaces: found before any has.
static EXE: OnceLock<PathBuf> = OnceLock::new();

/// What the daemon has done about newer releases.
static TRIED: Mutex<Tried> = Mutex::new(Tried {
    release: None,
    running: false,
    noted: None,
});

struct Tried {
    /// The newest release the upgrade command was run for.
    release: Option<Version>,
    /// Whether it runs now.
    running: bool,
    /// The newest release logged as having no command to install it.
    noted: Option<Version>,
}

fn lock_tried() -> std::sync::MutexGuard<'static, Tried> {
    TRIED.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Once an upgrade has installed the hub's release, the binary to start again from.
static RESTART: OnceLock<PathBuf> = OnceLock::new();

fn restart_notice() -> &'static tokio::sync::Notify {
    static NOTICE: OnceLock<tokio::sync::Notify> = OnceLock::new();
    NOTICE.get_or_init(tokio::sync::Notify::new)
}

/// Notes the binary the daemon started from, as it starts.
pub fn started() {
    match std::env::current_exe() {
        Ok(exe) => {
            EXE.get_or_init(|| exe);
        }
        Err(err) => tracing::warn!("can't upgrade: can't find this daemon's binary: {err}"),
    }
}

/// Where the upgrade command's output goes.
pub fn log_path() -> anyhow::Result<PathBuf> {
    Ok(config::state_dir()?.join("upgrade.log"))
}

/// Where the daemon records why its latest upgrade failed: the release it was for, on a line
/// of its own, then why.
fn failure_path() -> anyhow::Result<PathBuf> {
    Ok(config::state_dir()?.join("upgrade-failed"))
}

/// Why the daemon's latest upgrade failed, and the release it was for, unless this release
/// is that one or newer, as after upgrading by hand.
pub fn failure() -> Option<(String, String)> {
    let text = fs::read_to_string(failure_path().ok()?).ok()?;
    let (release, why) = text.split_once('\n')?;
    newer(release)?;
    Some((release.to_owned(), why.trim().to_owned()))
}

/// `release`, if it is newer than this one.
fn newer(release: &str) -> Option<Version> {
    let release = Version::parse(release).ok()?;
    (release > Version::parse(RELEASE).ok()?).then_some(release)
}

/// Upgrades musubi, in the background, if a hub that answered runs `release`, a newer one,
/// and no upgrade has been tried for it or a newer one.
pub fn consider(release: &str) {
    let Some(release) = newer(release) else {
        return;
    };
    let mut tried = lock_tried();
    if tried.running
        || tried
            .release
            .as_ref()
            .is_some_and(|tried| *tried >= release)
    {
        return;
    }
    // Read afresh each time, so that a command set meanwhile runs without a restart.
    let command = match Settings::load() {
        Ok(settings) => settings.upgrade_command,
        Err(err) => {
            tracing::warn!("can't upgrade: reading musubi.upgrade-command: {err:#}");
            return;
        }
    };
    let Some(command) = command else {
        if tried.noted.as_ref() != Some(&release) {
            tracing::info!(
                "a hub runs musubi {release}, newer than this, {RELEASE}; set \
                 musubi.upgrade-command for the daemon to upgrade"
            );
            tried.noted = Some(release);
        }
        return;
    };
    tried.release = Some(release.clone());
    tried.running = true;
    drop(tried);
    let spawned = std::thread::Builder::new()
        .name("upgrade".to_owned())
        .spawn(move || {
            if let Err(err) = upgrade(&release, &command) {
                let why = format!("{err:#}");
                tracing::warn!("upgrading to musubi {release}: {why}");
                if let Ok(path) = failure_path()
                    && let Err(err) = fs::write(&path, format!("{release}\n{why}\n"))
                {
                    tracing::warn!("recording that in {}: {err}", path.display());
                }
            }
            lock_tried().running = false;
        });
    if let Err(err) = spawned {
        tracing::warn!("starting to upgrade: {err}");
        lock_tried().running = false;
    }
}

/// Runs the upgrade command for `release`, and once the binary the daemon started from is
/// that release, has the daemon stop to start again from it.
fn upgrade(release: &Version, command: &str) -> anyhow::Result<()> {
    let exe = EXE.get().context("this daemon's binary is unknown")?;
    // The command holds it, as its standard input, until it and whatever it starts exit: a
    // daemon stopped meanwhile leaves the command running, and the next must not start
    // another beside it.
    let state = config::state_dir()?;
    let Some(lock) = crate::lock::try_lock(&state.join("upgrade.lock"))? else {
        tracing::info!("an earlier daemon's upgrade command still runs");
        // For the next sync to try again.
        lock_tried().release = None;
        return Ok(());
    };
    fs::remove_file(failure_path()?).ok();
    tracing::info!("a hub runs musubi {release}; running musubi.upgrade-command");
    let log = log_path()?;
    let output = fs::File::create(&log).with_context(|| format!("creating {}", log.display()))?;
    let mut child = shell(command)
        .env("MUSUBI_UPGRADE_TO", release.to_string())
        .current_dir(&state)
        .stdin(lock.into_file())
        .stdout(output.try_clone()?)
        .stderr(output)
        .spawn()
        .context("starting musubi.upgrade-command")?;
    let status = wait(&mut child, TIMEOUT)?;
    anyhow::ensure!(
        status.success(),
        "musubi.upgrade-command failed ({status}); its output is in {}",
        log.display()
    );
    let want = format!("musubi {release}");
    let found = Command::new(exe)
        .arg("--version")
        .output()
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
        .unwrap_or_default();
    anyhow::ensure!(
        found == want,
        "musubi.upgrade-command succeeded, but {} is {}, not {want}",
        exe.display(),
        if found.is_empty() {
            "no musubi"
        } else {
            &found
        }
    );
    tracing::info!("upgraded to {want}; starting again");
    RESTART.get_or_init(|| exe.clone());
    restart_notice().notify_one();
    Ok(())
}

/// `command` run by the shell.
fn shell(command: &str) -> Command {
    let mut shell = if cfg!(windows) {
        let mut shell = Command::new("cmd");
        shell.arg("/C");
        shell
    } else {
        let mut shell = Command::new("sh");
        shell.arg("-c");
        shell
    };
    shell.arg(command);
    shell
}

/// Waits for `child` to exit, killing it if it runs for longer than `timeout`.
fn wait(child: &mut Child, timeout: Duration) -> anyhow::Result<ExitStatus> {
    let deadline = Instant::now() + timeout;
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(status);
        }
        if Instant::now() >= deadline {
            child.kill().ok();
            child.wait().ok();
            anyhow::bail!(
                "musubi.upgrade-command ran for over {} minutes, so it was stopped",
                timeout.as_secs() / 60
            );
        }
        std::thread::sleep(Duration::from_millis(500));
    }
}

/// Waits until an upgrade has installed the hub's release, for the daemon to stop and start
/// again from the binary this returns.
pub async fn installed() -> &'static Path {
    loop {
        restart_notice().notified().await;
        if let Some(exe) = RESTART.get() {
            return exe;
        }
    }
}

/// Starts the daemon again from `exe`, with the arguments it was started with: in place of
/// this process, so that whatever started it, such as launchd, goes on seeing it.
pub fn restart(exe: &Path) -> anyhow::Result<()> {
    let mut command = Command::new(exe);
    command.args(std::env::args_os().skip(1));
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt as _;
        let err = command.exec();
        Err(err).with_context(|| format!("starting {}", exe.display()))
    }
    #[cfg(windows)]
    {
        crate::daemon::detach(&mut command);
        command
            .spawn()
            .with_context(|| format!("starting {}", exe.display()))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

    /// Only a release newer than this one, read as semver, calls for an upgrade: not this
    /// one, as every unreleased build is, nor an older one, nor what isn't a version, which
    /// would otherwise reach the upgrade command's environment.
    #[test]
    fn only_a_newer_release_calls_for_an_upgrade() {
        let this = Version::parse(RELEASE).unwrap();
        let next = Version::new(this.major, this.minor, this.patch + 1);
        assert_eq!(newer(&next.to_string()), Some(next));
        assert_eq!(newer(RELEASE), None);
        assert_eq!(newer("0.0.0"), None);
        assert_eq!(newer("99.0.0; rm -rf ~"), None);
        assert_eq!(newer(""), None);
    }
}
