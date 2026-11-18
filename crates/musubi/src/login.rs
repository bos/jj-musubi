//! Starting the daemon, or a hub, at login, as the platform's own service manager does it:
//!
//! - macOS: a launchd agent, `~/Library/LaunchAgents/io.github.bos.musubi.plist` (or
//!   `io.github.bos.musubi.hub.plist`);
//! - Linux: a systemd user unit, `~/.config/systemd/user/musubi.service` (or
//!   `musubi-hub.service`);
//! - Windows, for the daemon only: an entry in the current user's `Run` registry key, which
//!   runs `musubi daemon start` at login.
//! - illumos and Solaris: an instance of an SMF service for each user,
//!   `svc:/site/musubi/daemon:<user>` (or `svc:/site/musubi/hub:<user>`), which starts at boot
//!   rather than at login, and which musubi sets up, starts and stops through `pfexec`.
//!
//! The hub's service runs `musubi hub` in the hub's directory, as the user's one hub.
//! With `hub install --at-boot`, a system service runs it as that user (see `boot`).
//!
//! Where a service manager runs the daemon, commands that need it ask the service manager to
//! start it rather than starting one themselves, so there is only ever one, and it restarts
//! after a crash but not after `musubi daemon stop`. SMF starts a daemon again even when it
//! exits cleanly, so there `musubi daemon stop` asks SMF to stop it (`svcadm disable -t`). The
//! service carries the `PATH` (the daemon and the hub run `git`) of the shell that installed
//! it, and what there says where jj's config, which holds the daemon's own settings too, and
//! musubi's state are: `JJ_CONFIG`, `XDG_CONFIG_HOME`, `XDG_STATE_HOME`, and any `MUSUBI_*`
//! settings. SMF's service also gets `HOME`, `USER` and `LOGNAME`, which SMF doesn't set.
//!
//! A marker in the state directory records each installation, so that a command run with
//! another `MUSUBI_STATE_DIR`, as tests do, never mistakes this one for its own.

#![cfg_attr(
    not(any(
        target_os = "macos",
        target_os = "linux",
        target_os = "illumos",
        target_os = "solaris",
        windows
    )),
    allow(
        dead_code,
        reason = "musubi has no service manager integration on this platform"
    )
)]

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use anyhow::Context as _;

use crate::config;

#[cfg(any(target_os = "macos", target_os = "linux"))]
mod boot;

// SMF's names, paths and manifest. They build on every platform so that their tests run
// everywhere.
#[cfg_attr(
    not(any(target_os = "illumos", target_os = "solaris")),
    allow(dead_code, reason = "illumos and Solaris only")
)]
mod smf;

/// Whether this hub has a system service, rather than a login service.
pub fn hub_at_boot() -> bool {
    Service::Hub
        .marker()
        .ok()
        .and_then(|path| fs::read_to_string(path).ok())
        .is_some_and(|text| text.starts_with("boot\n"))
}

/// Obtain privileges before replacing an installed hub. The main process stays the user
/// whose home, state and executable the service must use.
pub fn prepare_hub_install(at_boot: bool) -> anyhow::Result<()> {
    // SMF starts the hub it runs for a user at boot already, so a hub at boot needs nothing more
    // there.
    if !SMF && (at_boot || hub_at_boot()) {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            boot::authorize()?;
            if at_boot && !hub_at_boot() {
                boot::check_available()?;
            }
            return Ok(());
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        anyhow::bail!("musubi can't start a hub at boot on this system");
    }
    Ok(())
}

pub fn install_hub(dir: &Path, at_boot: bool) -> anyhow::Result<String> {
    // Under SMF, the hub's own service starts at boot.
    if !at_boot || SMF {
        return install(Service::Hub, Some(dir));
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        let exe = std::env::current_exe()?;
        let marker = Service::Hub.marker()?;
        fs::write(&marker, "boot\n")?;
        // The marker is already complete: never truncate it while a boot service runs.
        let result = boot::install(&exe, dir);
        if result.is_err() {
            // Keep the marker if cleanup fails, so uninstall can retry it.
            boot::uninstall()
                .context("removing the failed boot service; retry `musubi hub uninstall`")?;
            fs::remove_file(marker)?;
        }
        result
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    anyhow::bail!("musubi can't start a hub at boot on this system")
}

/// What starts at login.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Service {
    Daemon,
    Hub,
}

impl Service {
    /// launchd's label for the agent.
    #[cfg_attr(not(target_os = "macos"), allow(dead_code, reason = "macOS only"))]
    fn label(self) -> &'static str {
        match self {
            Self::Daemon => "io.github.bos.musubi",
            Self::Hub => "io.github.bos.musubi.hub",
        }
    }

    /// systemd's name for the unit.
    #[cfg_attr(not(target_os = "linux"), allow(dead_code, reason = "Linux only"))]
    fn unit(self) -> &'static str {
        match self {
            Self::Daemon => "musubi.service",
            Self::Hub => "musubi-hub.service",
        }
    }

    /// The musubi command the service runs.
    #[cfg_attr(windows, allow(dead_code, reason = "not Windows"))]
    fn command(self) -> &'static str {
        match self {
            Self::Daemon => "daemon",
            Self::Hub => "hub",
        }
    }

    #[cfg_attr(
        not(any(target_os = "linux", target_os = "illumos", target_os = "solaris")),
        allow(dead_code, reason = "Linux, illumos and Solaris only")
    )]
    fn description(self) -> &'static str {
        match self {
            Self::Daemon => "musubi: keeps jj repositories in sync across machines",
            Self::Hub => "musubi hub: stores hives and orders their updates",
        }
    }

    fn marker(self) -> anyhow::Result<PathBuf> {
        let name = match self {
            Self::Daemon => "login-service",
            Self::Hub => "hub-login-service",
        };
        Ok(config::state_dir()?.join(name))
    }

    /// Where the service logs, where it logs to a file.
    #[cfg_attr(
        any(target_os = "linux", target_os = "illumos", target_os = "solaris"),
        allow(dead_code, reason = "not Linux, illumos or Solaris")
    )]
    fn log(self) -> anyhow::Result<PathBuf> {
        match self {
            Self::Daemon => config::daemon_log(),
            Self::Hub => config::hub_log(),
        }
    }

    #[cfg_attr(
        any(target_os = "linux", target_os = "illumos", target_os = "solaris"),
        allow(dead_code, reason = "not Linux, illumos or Solaris")
    )]
    fn name(self) -> &'static str {
        match self {
            Self::Daemon => "the daemon",
            Self::Hub => "the hub",
        }
    }
}

/// The name of the value in the `Run` registry key.
#[cfg_attr(not(windows), allow(dead_code, reason = "Windows only"))]
const RUN_VALUE: &str = "musubi";

/// Points the daemon's service at the latest ssh agent, through the link that commands keep:
/// a user's service manager rarely has an agent of its own. The hub ssh-es nowhere.
#[cfg_attr(
    not(any(target_os = "linux", target_os = "illumos", target_os = "solaris")),
    allow(dead_code, reason = "Linux, illumos and Solaris only")
)]
fn push_agent_link(
    service: Service,
    environment: &mut Vec<(String, String)>,
) -> anyhow::Result<()> {
    if service == Service::Daemon
        && let Some(link) = crate::agent::link()?
    {
        environment.push(("SSH_AUTH_SOCK".to_owned(), link.display().to_string()));
    }
    Ok(())
}

/// The environment the daemon needs from the shell that installed it.
#[cfg_attr(windows, allow(dead_code, reason = "not Windows"))]
fn environment() -> Vec<(String, String)> {
    std::env::vars()
        .filter(|(name, _)| {
            ["PATH", "JJ_CONFIG", "XDG_CONFIG_HOME", "XDG_STATE_HOME"].contains(&name.as_str())
                || name.starts_with("MUSUBI_")
        })
        .collect()
}

/// Whether `musubi daemon install`, or `musubi hub install`, set up this user's daemon, or
/// hub, to start at login.
pub fn installed(service: Service) -> bool {
    service.marker().is_ok_and(|path| path.exists())
}

/// Whether the service manager runs the daemon, so that commands must ask it to start the
/// daemon rather than starting it themselves.
pub fn managed() -> bool {
    installed(Service::Daemon) && !cfg!(windows)
}

#[cfg_attr(
    any(target_os = "illumos", target_os = "solaris"),
    allow(
        dead_code,
        reason = "SMF's commands set a locale, so go through output"
    )
)]
fn run(program: &str, args: &[&str]) -> anyhow::Result<()> {
    output(Command::new(program).args(args)).map(drop)
}

/// Runs `command` and returns its output, or an error with what it wrote to stderr if it fails.
fn output(command: &mut Command) -> anyhow::Result<std::process::Output> {
    let program = command.get_program().to_string_lossy().into_owned();
    let output = command
        .output()
        .with_context(|| format!("running {program}"))?;
    anyhow::ensure!(
        output.status.success(),
        "`{program} {}` failed: {}",
        command
            .get_args()
            .map(|arg| arg.to_string_lossy())
            .collect::<Vec<_>>()
            .join(" "),
        String::from_utf8_lossy(&output.stderr).trim()
    );
    Ok(output)
}

/// Sets `service` up to start at login (at boot under SMF), run in `dir` if given, and starts
/// it now. The caller has stopped any it started itself. If that fails, and it wasn't
/// installed before, it removes what it wrote, which [`uninstall`], finding no marker, would
/// leave; under SMF, where removing it can fail too, the error says so.
pub fn install(service: Service, dir: Option<&Path>) -> anyhow::Result<String> {
    let exe = std::env::current_exe()?;
    config::create_state_dir()?;
    // Under SMF, an instance can be set up without this state directory's marker (installed
    // with another `MUSUBI_STATE_DIR`, say), and a failed install must leave it be.
    let before = installed(service) || smf_has_instance(service)?;
    let result = platform::install(service, &exe, dir).and_then(|described| {
        fs::write(service.marker()?, &described)?;
        Ok(described)
    });
    match result {
        Err(err) if !before => match platform::uninstall(service) {
            // Under SMF, an undo that fails can leave an instance set up. A marker keeps it
            // where `uninstall` can retry and `daemon stop` asks SMF; the error says so, as
            // context, so that the install's own error, and any hint on it, still shows. With
            // no instance left, nothing runs (an empty shared service starts nothing), and a
            // marker would only have commands ask SMF for an instance that isn't there.
            // If svcs can't say, assume one is.
            Err(cleanup) if SMF && smf_has_instance(service).unwrap_or(true) => {
                let recorded = service
                    .marker()
                    .and_then(|marker| fs::write(marker, "").map_err(anyhow::Error::from));
                let retry = match recorded {
                    Ok(()) => format!(
                        "; `musubi {} uninstall` removes what's left",
                        service.command()
                    ),
                    Err(marker) => format!(
                        ", and recording that it's left failed too ({marker:#}); `pfexec svcadm \
                         disable {fmri}`, then once `svcs {fmri}` says it's disabled, `pfexec \
                         svccfg delete {fmri}`, removes it",
                        fmri = smf::fmri(service)
                            .unwrap_or_else(|_| format!("{}:<you>", smf::service_fmri(service)))
                    ),
                };
                Err(err.context(format!(
                    "installing failed, and undoing it failed too ({cleanup:#}){retry}"
                )))
            }
            // Otherwise nothing is left: under SMF, no instance; elsewhere, undoing fails for the
            // reason installing did (no systemd user manager, no `Run` value to delete) once
            // nothing is left, so saying it failed would mislead.
            Ok(()) | Err(_) => Err(err),
        },
        result => result,
    }
}

/// Whether SMF has an instance of `service` for this user; never, without SMF.
fn smf_has_instance(service: Service) -> anyhow::Result<bool> {
    #[cfg(any(target_os = "illumos", target_os = "solaris"))]
    return platform::has_instance(service);
    #[cfg(not(any(target_os = "illumos", target_os = "solaris")))]
    {
        let _ = service;
        Ok(false)
    }
}

/// Removes the file at `path`, which may be gone already, as when a user removed a unit file
/// before uninstalling.
#[cfg_attr(windows, allow(dead_code, reason = "not Windows"))]
fn remove_if_present(path: &Path) -> anyhow::Result<()> {
    match fs::remove_file(path) {
        Err(err) if err.kind() != std::io::ErrorKind::NotFound => Err(err.into()),
        _ => Ok(()),
    }
}

/// Whether svcadm's or svccfg's message says the account lacks an authorization: svcadm says
/// "Permission denied.", and svccfg's import "(permission denied)".
#[cfg_attr(
    not(any(target_os = "illumos", target_os = "solaris")),
    allow(dead_code, reason = "illumos and Solaris only")
)]
fn lacks_rights(message: &str) -> bool {
    message.to_ascii_lowercase().contains("permission denied")
}

const SMF: bool = cfg!(any(target_os = "illumos", target_os = "solaris"));

/// When the service manager starts what [`install`] sets up: SMF starts services at boot, the
/// others at login.
pub const STARTS: &str = if SMF { "at boot" } else { "at login" };

/// Undoes [`install`], stopping what the service manager runs. Returns whether it was
/// installed.
pub fn uninstall(service: Service) -> anyhow::Result<bool> {
    if !installed(service) {
        return Ok(false);
    }
    if service == Service::Hub && hub_at_boot() {
        #[cfg(any(target_os = "macos", target_os = "linux"))]
        {
            boot::authorize()?;
            boot::uninstall()?;
        }
    } else {
        platform::uninstall(service)?;
    }
    fs::remove_file(service.marker()?)?;
    Ok(true)
}

/// Asks the service manager to start the daemon now.
pub fn start() -> anyhow::Result<()> {
    platform::start(Service::Daemon)
}

/// Asks SMF, which would otherwise start again a daemon that exits, to stop the daemon until
/// something starts it again. Returns whether SMF was running it; if not, the caller stops any
/// daemon itself.
#[cfg(any(target_os = "illumos", target_os = "solaris"))]
pub fn stop() -> anyhow::Result<bool> {
    if !installed(Service::Daemon) {
        return Ok(false);
    }
    platform::stop(Service::Daemon)
}

/// launchd (`KeepAlive`'s `SuccessfulExit=false`) and systemd (`Restart=on-failure`) leave a
/// daemon that exits cleanly stopped, and Windows runs none, so the caller stops it.
#[cfg(not(any(target_os = "illumos", target_os = "solaris")))]
pub fn stop() -> anyhow::Result<bool> {
    Ok(false)
}

/// Where the service manager logs the output of `service`.
pub fn log_hint(service: Service) -> String {
    #[cfg(target_os = "linux")]
    if service == Service::Hub && hub_at_boot() {
        return format!("`sudo journalctl -u {}`", boot::unit_name());
    }
    platform::log_hint(service)
}

/// Where `service` logs, where it logs to a file.
#[cfg(any(target_os = "macos", windows))]
fn file_log_hint(service: Service) -> String {
    service.log().map_or_else(
        |_| format!("{}'s log", service.name()),
        |log| log.display().to_string(),
    )
}

#[cfg(target_os = "macos")]
mod platform {
    use super::*;

    fn plist_path(service: Service) -> anyhow::Result<PathBuf> {
        let home = std::env::var_os("HOME").context("HOME is not set")?;
        Ok(PathBuf::from(home).join(format!("Library/LaunchAgents/{}.plist", service.label())))
    }

    /// The login session's domain, or with nobody logged in at the screen (a Mac reached
    /// over SSH), the user's background domain, which launchd keeps while they have any
    /// session. The agent may load in either (`LimitLoadToSessionType`).
    fn domain() -> anyhow::Result<String> {
        let uid = crate::socket::uid()?;
        let gui = format!("gui/{uid}");
        let has_gui = Command::new("launchctl")
            .args(["print", &gui])
            .output()
            .is_ok_and(|output| output.status.success());
        Ok(if has_gui { gui } else { format!("user/{uid}") })
    }

    pub fn install(service: Service, exe: &Path, dir: Option<&Path>) -> anyhow::Result<String> {
        let path = plist_path(service)?;
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let log = service.log()?;
        fs::write(&path, plist(service, exe, dir, &log, &environment(), None))?;
        // Replace any earlier version of the agent.
        let label = service.label();
        run("launchctl", &["bootout", &format!("{}/{label}", domain()?)]).ok();
        run(
            "launchctl",
            &[
                "bootstrap",
                &domain()?,
                path.to_str().context("non-UTF-8 path")?,
            ],
        )?;
        Ok(format!("a launchd agent, {}", path.display()))
    }

    pub fn uninstall(service: Service) -> anyhow::Result<()> {
        // Stops what it runs too.
        let label = service.label();
        run("launchctl", &["bootout", &format!("{}/{label}", domain()?)]).ok();
        remove_if_present(&plist_path(service)?)
    }

    pub fn start(service: Service) -> anyhow::Result<()> {
        let label = service.label();
        run(
            "launchctl",
            &["kickstart", &format!("{}/{label}", domain()?)],
        )
    }

    pub fn log_hint(service: Service) -> String {
        file_log_hint(service)
    }
}

#[cfg(target_os = "linux")]
mod platform {
    use etcetera::BaseStrategy as _;

    use super::*;

    fn unit_path(service: Service) -> anyhow::Result<PathBuf> {
        let base = etcetera::choose_base_strategy().context("no config directory")?;
        Ok(base.config_dir().join("systemd/user").join(service.unit()))
    }

    pub fn install(service: Service, exe: &Path, dir: Option<&Path>) -> anyhow::Result<String> {
        let path = unit_path(service)?;
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut environment = environment();
        push_agent_link(service, &mut environment)?;
        fs::write(&path, unit(service, exe, dir, &environment, None))?;
        run("systemctl", &["--user", "daemon-reload"])?;
        run("systemctl", &["--user", "enable", "--now", service.unit()])?;
        Ok(format!("a systemd user unit, {}", path.display()))
    }

    pub fn uninstall(service: Service) -> anyhow::Result<()> {
        run("systemctl", &["--user", "disable", "--now", service.unit()]).ok();
        remove_if_present(&unit_path(service)?)?;
        run("systemctl", &["--user", "daemon-reload"])
    }

    pub fn start(service: Service) -> anyhow::Result<()> {
        run("systemctl", &["--user", "start", service.unit()])
    }

    pub fn log_hint(service: Service) -> String {
        format!("`journalctl --user -u {}`", service.unit())
    }
}

#[cfg(windows)]
mod platform {
    use super::Path;
    use super::RUN_VALUE;
    use super::Service;
    use super::file_log_hint;
    use super::run;

    const KEY: &str = r"HKCU\Software\Microsoft\Windows\CurrentVersion\Run";

    pub fn install(service: Service, exe: &Path, _dir: Option<&Path>) -> anyhow::Result<String> {
        anyhow::ensure!(
            service == Service::Daemon,
            "musubi can't start a hub at login on Windows"
        );
        // `daemon start` starts the daemon detached and returns.
        let command = format!("\"{}\" daemon start", exe.display());
        run(
            "reg",
            &[
                "add", KEY, "/v", RUN_VALUE, "/t", "REG_SZ", "/d", &command, "/f",
            ],
        )?;
        Ok(format!(r"the {RUN_VALUE} entry in {KEY}"))
    }

    pub fn uninstall(_: Service) -> anyhow::Result<()> {
        run("reg", &["delete", KEY, "/v", RUN_VALUE, "/f"])
    }

    pub fn start(_: Service) -> anyhow::Result<()> {
        anyhow::bail!("Windows has no service manager running the daemon")
    }

    pub fn log_hint(service: Service) -> String {
        file_log_hint(service)
    }
}

#[cfg(any(target_os = "illumos", target_os = "solaris"))]
mod platform {
    use super::*;

    // By path, as profiles name them, so that a `PATH` without /usr/sbin, as cron's or a
    // non-interactive ssh's may be, still finds them. svcs is in /usr/bin, which every `PATH`
    // has, and is found there, so that tests can stand in for it.
    const SVCADM: &str = "/usr/sbin/svcadm";
    const SVCCFG: &str = "/usr/sbin/svccfg";

    /// How svcs and svccfg say that nothing matched a pattern: "doesn't match any instances" (or
    /// "... or services").
    const NO_MATCH: &str = "doesn't match any";

    /// Whether an SMF instance in `state` runs its process: a degraded one does, and one in
    /// maintenance or disabled doesn't.
    fn runs_daemon(state: &str) -> bool {
        state == "online" || state == "degraded"
    }

    /// The state svcs gives without its trailing `*`, which marks an instance in transition
    /// (`online*`, `offline*`) and doesn't say where it's going.
    fn settled(state: &str) -> &str {
        state.trim_end_matches('*')
    }

    pub fn has_instance(service: Service) -> anyhow::Result<bool> {
        Ok(state(&smf::fmri(service)?)?.is_some())
    }

    /// The state of the instance `fmri` names, as svcs gives it, or `None` only for svcs's own
    /// "doesn't match any instances". Any other failure (no svcs, svc.configd down) is an error,
    /// so that `uninstall` can't report success while the instance stays enabled.
    fn state(fmri: &str) -> anyhow::Result<Option<String>> {
        match output(
            Command::new("svcs")
                .args(["-H", "-o", "state", fmri])
                .env("LC_ALL", "C"),
        ) {
            Ok(output) => Ok(Some(
                String::from_utf8_lossy(&output.stdout).trim().to_owned(),
            )),
            Err(err) if err.to_string().contains(NO_MATCH) => Ok(None),
            Err(err) => Err(err),
        }
    }

    /// SMF stops restarting an instance that exits too soon after starting and leaves it in
    /// maintenance, where `enable` and `enable -t` do nothing until it is cleared. `current` is
    /// the state the caller has just read, so this asks svcs nothing more unless the clear fails.
    fn clear_maintenance(fmri: &str, current: &str) -> anyhow::Result<()> {
        if settled(current) != "maintenance" {
            return Ok(());
        }
        let Err(err) = admin(&[SVCADM, "clear", fmri]) else {
            return Ok(());
        };
        // Another command may have cleared it first, which is fine: ask svcs again rather than
        // read svcadm's message. If asking fails too, the clear's error, and any hint on it,
        // still shows.
        match state(fmri) {
            Ok(Some(now)) if settled(&now) != "maintenance" => Ok(()),
            Ok(_) => Err(err),
            Err(query) => Err(err.context(format!(
                "clearing maintenance on {fmri} failed, and asking svcs whether it still was \
                 failed too: {query:#}"
            ))),
        }
    }

    /// Runs an SMF administration command through pfexec, so that a profile that runs svccfg and
    /// svcadm with privileges (Primary Administrator) works. The `solaris.smf.*` authorizations
    /// come from the account's profiles either way, and with none, pfexec runs the command as it
    /// is. A missing authorization is recognized by its message, since svccfg's and svcadm's exit
    /// status doesn't tell it from any other failure.
    fn admin(command: &[&str]) -> anyhow::Result<()> {
        // The C locale, so that the messages matched here and in `uninstall` (`NO_MATCH`) are the
        // English ones.
        output(Command::new("pfexec").args(command).env("LC_ALL", "C"))
            .map(drop)
            .map_err(|err| {
                if lacks_rights(&err.to_string()) {
                    crate::ui::with_hint(
                        err,
                        "If `profiles` doesn't list Service Management (or Primary \
                         Administrator), an administrator adds it with `usermod -P`, as \
                         musubi's setup guide says under illumos",
                    )
                } else {
                    err
                }
            })
    }

    pub fn install(service: Service, exe: &Path, dir: Option<&Path>) -> anyhow::Result<String> {
        let (user, instance) = smf::user_and_instance()?;
        let fmri = smf::fmri_of(service, &instance);
        let home = std::env::var("HOME").context("HOME is not set")?;
        anyhow::ensure!(
            Path::new(&home).is_absolute(),
            "HOME must be an absolute path"
        );
        let mut environment = environment();
        // SMF builds a method's environment from scratch, with no `HOME`, without which musubi
        // couldn't find its state directory.
        environment.extend([
            ("HOME".to_owned(), home),
            ("USER".to_owned(), user.clone()),
            ("LOGNAME".to_owned(), user.clone()),
        ]);
        push_agent_link(service, &mut environment)?;
        let path = smf::manifest_path(service)?;
        fs::write(
            &path,
            smf::manifest(service, &instance, &user, exe, dir, &environment),
        )
        .with_context(|| format!("writing the SMF manifest {}", path.display()))?;
        let path = path
            .to_str()
            .with_context(|| format!("the SMF manifest's path, {}, isn't UTF-8", path.display()))?;
        // The manifest imports a new instance disabled, so it runs nothing until the refresh
        // and enable below have succeeded. An existing one keeps running, with what the import
        // stored taking effect at its next restart.
        admin(&[SVCCFG, "import", path])?;
        // Refresh so that a reinstall's new settings apply. A plain `enable` also lifts a
        // `disable -t` left by `musubi daemon stop`.
        admin(&[SVCADM, "refresh", &fmri])?;
        let current = state(&fmri)?;
        if let Some(current) = &current {
            clear_maintenance(&fmri, current)?;
        }
        admin(&[SVCADM, "enable", &fmri])?;
        // The caller stops a daemon the service manager runs, but only where this state
        // directory's marker says it's installed. An instance running without that marker
        // (installed with another `MUSUBI_STATE_DIR`, or left by an install whose undo failed)
        // is still online, and neither a refresh nor an enable restarts it, so it would go on
        // running its old settings.
        if current.as_deref().map(settled).is_some_and(runs_daemon) {
            admin(&[SVCADM, "restart", &fmri])?;
        }
        Ok(format!("the SMF service {fmri}"))
    }

    pub fn uninstall(service: Service) -> anyhow::Result<()> {
        let fmri = smf::fmri(service)?;
        // There may be no instance: after a failed install, or once an administrator deleted it.
        if let Some(current) = state(&fmri)? {
            let stopped = disable(&fmri, Until::Deleted)?;
            warn_if_killed(&fmri, &current, stopped);
            admin(&[SVCCFG, "delete", &fmri])?;
        }
        // Every user's instance shares the service, so delete it only once none is left.
        let service_fmri = smf::service_fmri(service);
        if state(&format!("{service_fmri}:*"))?.is_none() {
            match admin(&[SVCCFG, "delete", &service_fmri]) {
                // Never imported, as after an install that failed early.
                Err(err) if err.to_string().contains(NO_MATCH) => {}
                result => result?,
            }
        }
        let path = smf::manifest_path(service)?;
        remove_if_present(&path)
            .with_context(|| format!("removing the SMF manifest {}", path.display()))
    }

    // Temporarily, leaving whether it starts at boot as `install`, or an administrator, set it.
    pub fn start(service: Service) -> anyhow::Result<()> {
        let fmri = smf::fmri(service)?;
        // The marker says it's installed, but an administrator deleted the instance: say how to
        // set it up again rather than pass on svcadm's "doesn't match".
        let Some(current) = state(&fmri)? else {
            return Err(crate::ui::with_hint(
                anyhow::anyhow!("SMF has no instance {fmri}"),
                "`musubi daemon install` sets it up again",
            ));
        };
        clear_maintenance(&fmri, &current)?;
        admin(&[SVCADM, "enable", "-t", &fmri])
    }

    // SMF starts a wait-style service again whenever its process exits, even with status 0
    // (svc.startd's `wait_remove`), so the daemon can't stop itself: disable it until the next
    // start or boot. A degraded instance runs the daemon too, and one in maintenance doesn't.
    // With no instance, deleted by an administrator, the caller stops the daemon itself.
    pub fn stop(service: Service) -> anyhow::Result<bool> {
        let fmri = smf::fmri(service)?;
        let Some(current) = state(&fmri)? else {
            return Ok(false);
        };
        // Even one that reads disabled: a concurrent `enable -t` may not have shown yet.
        let stopped = disable(&fmri, Until::NextStart)?;
        warn_if_killed(&fmri, &current, stopped);
        Ok(ran(&current))
    }

    /// Whether an instance svcs said was in `state` ran its process: one in transition may be
    /// on its way to running it, or still running it.
    fn ran(state: &str) -> bool {
        runs_daemon(settled(state)) || state.ends_with('*')
    }

    /// Says so when SMF had to kill what an instance that was in `before` ran, since its log is
    /// then the only record of why it didn't stop.
    fn warn_if_killed(fmri: &str, before: &str, stopped: Stopped) {
        match stopped {
            Stopped::Killed if ran(before) => tracing::warn!(
                "{fmri} didn't stop within {} seconds, so SMF killed what it ran; see {}",
                smf::STOP_TIMEOUT_SECONDS,
                smf::log_path(fmri)
            ),
            Stopped::Killed | Stopped::Disabled => {}
        }
    }

    /// How long a disabled instance stays so.
    enum Until {
        /// The next start or boot (`svcadm disable -t`).
        NextStart,
        /// For good, as before deleting it.
        Deleted,
    }

    /// How an instance that [`disable`] waited for ended up running nothing.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum Stopped {
        /// Disabled, or gone.
        Disabled,
        /// Its stop method timed out, so SMF killed what was left and put it in maintenance.
        Killed,
    }

    /// Disables `fmri` and waits until it runs nothing: SMF moves it to `disabled`, or, if its
    /// stop method times out, kills what's left and puts it in `maintenance`, where `svcadm
    /// disable -s` would wait forever.
    fn disable(fmri: &str, until: Until) -> anyhow::Result<Stopped> {
        use std::time::Duration;
        use std::time::Instant;

        let flags: &[&str] = match until {
            Until::NextStart => &["-t"],
            Until::Deleted => &[],
        };
        admin(&[&[SVCADM, "disable"][..], flags, &[fmri]].concat())?;
        // Past the stop method's own timeout, by which SMF has killed what's left.
        let wait = Duration::from_secs(smf::STOP_TIMEOUT_SECONDS + 30);
        let deadline = Instant::now() + wait;
        let mut pause =
            crate::backoff::Backoff::new(Duration::from_millis(10), Duration::from_secs(1));
        loop {
            let now = state(fmri).with_context(|| {
                format!(
                    "asked SMF to disable {fmri}, but asking svcs whether it had stopped failed; \
                     running the command again finishes it"
                )
            })?;
            match now.as_deref() {
                None | Some("disabled") => return Ok(Stopped::Disabled),
                Some("maintenance") => return Ok(Stopped::Killed),
                Some(now) if Instant::now() >= deadline => {
                    return Err(crate::ui::with_hint(
                        anyhow::anyhow!(
                            "SMF didn't stop {fmri} in {} seconds; it is {now}",
                            wait.as_secs()
                        ),
                        format!(
                            "`svcs -p {fmri}` lists what still runs, and {} says why; running \
                             the command again finishes it once it has stopped",
                            smf::log_path(fmri)
                        ),
                    ));
                }
                Some(_) => std::thread::sleep(pause.next()),
            }
        }
    }

    pub fn log_hint(service: Service) -> String {
        match smf::fmri(service) {
            Ok(fmri) => smf::log_path(&fmri),
            Err(_) => format!("`svcs -L {}`", smf::service_fmri(service)),
        }
    }
}

#[cfg(not(any(
    target_os = "macos",
    target_os = "linux",
    target_os = "illumos",
    target_os = "solaris",
    windows
)))]
mod platform {
    use super::Path;
    use super::Service;

    pub fn install(service: Service, _: &Path, _: Option<&Path>) -> anyhow::Result<String> {
        anyhow::bail!(
            "musubi can't start {} at login on this system",
            service.name()
        )
    }

    pub fn uninstall(_: Service) -> anyhow::Result<()> {
        Ok(())
    }

    pub fn start(service: Service) -> anyhow::Result<()> {
        anyhow::bail!(
            "musubi can't start {} at login on this system",
            service.name()
        )
    }

    pub fn log_hint(service: Service) -> String {
        format!("{}'s log", service.name())
    }
}

/// A launchd agent that runs `exe daemon` (or `exe hub`) at login, in `dir` if given, and
/// again if it fails, but not after it stops cleanly.
#[cfg_attr(not(target_os = "macos"), allow(dead_code, reason = "macOS only"))]
fn plist(
    service: Service,
    exe: &Path,
    dir: Option<&Path>,
    log: &Path,
    environment: &[(String, String)],
    boot_user: Option<(&str, &str)>,
) -> String {
    let string = |text: &str| format!("<string>{}</string>", xml_escape(text));
    let mut variables = String::new();
    for (name, value) in environment {
        writeln!(
            variables,
            "\t\t<key>{}</key>\n\t\t{}",
            xml_escape(name),
            string(value)
        )
        .expect("writing to a String");
    }
    let exe = string(&exe.to_string_lossy());
    let command = service.command();
    let working = dir.map_or_else(String::new, |dir| {
        format!(
            "\t<key>WorkingDirectory</key>\n\t{}\n",
            string(&dir.to_string_lossy())
        )
    });
    let log = string(&log.to_string_lossy());
    let (label, identity, session) = if let Some((label, user)) = boot_user {
        (
            label,
            format!("\t<key>UserName</key>\n\t{}\n", string(user)),
            String::new(),
        )
    } else {
        (
            service.label(),
            String::new(),
            concat!(
                "\t<key>LimitLoadToSessionType</key>\n\t<array>\n",
                "\t\t<string>Aqua</string>\n\t\t<string>Background</string>\n\t</array>\n"
            )
            .to_owned(),
        )
    };
    format!(
        r#"<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
	<key>Label</key>
	<string>{label}</string>
	<key>ProgramArguments</key>
	<array>
		{exe}
		<string>{command}</string>
	</array>
{identity}{working}	<key>EnvironmentVariables</key>
	<dict>
{variables}	</dict>
	<key>RunAtLoad</key>
	<true/>
	<key>KeepAlive</key>
	<dict>
		<key>SuccessfulExit</key>
		<false/>
	</dict>
{session}	<key>ProcessType</key>
	<string>Background</string>
	<key>StandardOutPath</key>
	{log}
	<key>StandardErrorPath</key>
	{log}
</dict>
</plist>
"#
    )
}

fn xml_escape(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// A systemd user unit that runs `exe daemon` (or `exe hub`) from login, in `dir` if given,
/// and again if it fails, but not after it stops cleanly.
#[cfg_attr(not(target_os = "linux"), allow(dead_code, reason = "Linux only"))]
fn unit(
    service: Service,
    exe: &Path,
    dir: Option<&Path>,
    environment: &[(String, String)],
    boot_user: Option<u32>,
) -> String {
    let mut text = format!(
        "[Unit]\nDescription={}\n\n[Service]\nExecStart={} {}\n",
        service.description(),
        systemd_quote(&exe.to_string_lossy()),
        service.command()
    );
    if let Some(uid) = boot_user {
        writeln!(text, "User={uid}").expect("writing to a String");
    }
    if let Some(dir) = dir {
        // A path, not a word: systemd doesn't unquote it, but expands `%` specifiers in it.
        writeln!(
            text,
            "WorkingDirectory={}",
            dir.to_string_lossy().replace('%', "%%")
        )
        .expect("writing to a String");
    }
    for (name, value) in environment {
        writeln!(
            text,
            "Environment={}",
            systemd_quote(&format!("{name}={value}"))
        )
        .expect("writing to a String");
    }
    let target = if boot_user.is_some() {
        "multi-user.target"
    } else {
        "default.target"
    };
    write!(
        text,
        "Restart=on-failure\nRestartSec=5\n\n[Install]\nWantedBy={target}\n"
    )
    .expect("writing to a String");
    text
}

/// A double-quoted systemd word: `\` and `"` escaped, and `%` doubled, since systemd
/// expands `%` specifiers even inside quotes.
fn systemd_quote(text: &str) -> String {
    let escaped = text
        .replace('\\', r"\\")
        .replace('"', "\\\"")
        .replace('%', "%%");
    format!("\"{escaped}\"")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn environment() -> Vec<(String, String)> {
        vec![
            ("PATH".to_owned(), "/usr/bin:/opt/my tools/bin".to_owned()),
            ("MUSUBI_SOCKET".to_owned(), "/tmp/a&b%\"c\".sock".to_owned()),
        ]
    }

    #[test]
    fn launchd_agent() {
        let text = plist(
            Service::Daemon,
            Path::new("/opt/bin/mu<s>ubi"),
            None,
            Path::new("/l/daemon.log"),
            &environment(),
            None,
        );
        assert!(
            text.contains("<string>/opt/bin/mu&lt;s&gt;ubi</string>\n\t\t<string>daemon</string>")
        );
        assert!(text.contains("<key>PATH</key>\n\t\t<string>/usr/bin:/opt/my tools/bin</string>"));
        assert!(text.contains("<string>/tmp/a&amp;b%&quot;c&quot;.sock</string>"));
        assert!(text.contains("<key>SuccessfulExit</key>\n\t\t<false/>"));
        assert!(!text.contains("WorkingDirectory"), "{text}");
    }

    #[test]
    fn launchd_hub_agent() {
        let text = plist(
            Service::Hub,
            Path::new("/opt/bin/musubi"),
            Some(Path::new("/srv/my hub")),
            Path::new("/l/hub.log"),
            &environment(),
            None,
        );
        assert!(
            text.contains("<string>io.github.bos.musubi.hub</string>"),
            "{text}"
        );
        assert!(
            text.contains("<string>/opt/bin/musubi</string>\n\t\t<string>hub</string>"),
            "{text}"
        );
        assert!(
            text.contains("<key>WorkingDirectory</key>\n\t<string>/srv/my hub</string>"),
            "{text}"
        );
    }

    #[test]
    fn systemd_unit() {
        let text = unit(
            Service::Daemon,
            Path::new("/opt/my bin/musubi"),
            None,
            &environment(),
            None,
        );
        assert!(
            text.contains("ExecStart=\"/opt/my bin/musubi\" daemon\n"),
            "{text}"
        );
        assert!(
            text.contains("Environment=\"PATH=/usr/bin:/opt/my tools/bin\"\n"),
            "{text}"
        );
        assert!(
            text.contains(r#"Environment="MUSUBI_SOCKET=/tmp/a&b%%\"c\".sock""#),
            "{text}"
        );
        assert!(text.contains("Restart=on-failure\n"));
        assert!(text.contains("WantedBy=default.target\n"));
        assert!(!text.contains("WorkingDirectory"), "{text}");
    }

    #[test]
    fn systemd_hub_unit() {
        let text = unit(
            Service::Hub,
            Path::new("/opt/bin/musubi"),
            Some(Path::new("/srv/100% hub")),
            &environment(),
            None,
        );
        assert!(
            text.contains("ExecStart=\"/opt/bin/musubi\" hub\n"),
            "{text}"
        );
        assert!(text.contains("WorkingDirectory=/srv/100%% hub\n"), "{text}");
    }

    #[test]
    fn smf_daemon_manifest() {
        let text = smf::manifest(
            Service::Daemon,
            "rain",
            "rain",
            Path::new("/opt/it's 100%/musubi"),
            None,
            &environment(),
        );
        assert!(
            text.contains(r#"<service name="site/musubi/daemon" type="service""#),
            "{text}"
        );
        assert!(
            text.contains(r#"exec="'/opt/it'\''s 100%%/musubi' daemon""#),
            "{text}"
        );
        assert!(
            text.contains(r#"<instance name="rain" enabled="false">"#),
            "{text}"
        );
        // Each user's instance carries its own methods and startd settings.
        let instance = text.find("<instance ").unwrap();
        for part in [
            r#"<exec_method type="method" name="start""#,
            r#"<exec_method type="method" name="stop" exec=":kill""#,
            r#"<propval name="duration" type="astring" value="child"/>"#,
        ] {
            assert!(
                text.find(part).is_some_and(|at| at > instance),
                "{part} isn't in the instance: {text}"
            );
        }
        assert!(
            text.contains(r#"<method_context working_directory=":default">"#),
            "{text}"
        );
        assert!(
            text.contains(r#"<method_credential user="rain" group=":default"/>"#),
            "{text}"
        );
        assert!(
            text.contains(r#"<envvar name="PATH" value="/usr/bin:/opt/my tools/bin"/>"#),
            "{text}"
        );
        assert!(
            text.contains(
                r#"<envvar name="MUSUBI_SOCKET" value="/tmp/a&amp;b%&quot;c&quot;.sock"/>"#
            ),
            "{text}"
        );
    }

    #[test]
    fn smf_hub_manifest() {
        let text = smf::manifest(
            Service::Hub,
            "uid1000",
            "first.last",
            Path::new("/opt/bin/musubi"),
            Some(Path::new("/srv/a&b hub")),
            &environment(),
        );
        assert!(
            text.contains(r#"<service name="site/musubi/hub" type="service""#),
            "{text}"
        );
        assert!(text.contains(r#"exec="/opt/bin/musubi hub""#), "{text}");
        assert!(
            text.contains(r#"<instance name="uid1000" enabled="false">"#),
            "{text}"
        );
        assert!(
            text.contains(r#"<method_context working_directory="/srv/a&amp;b hub">"#),
            "{text}"
        );
        assert!(
            text.contains(r#"<method_credential user="first.last" group=":default"/>"#),
            "{text}"
        );
    }

    #[test]
    fn smf_instance_names() {
        assert_eq!(smf::instance("rain", 1000), "rain");
        assert_eq!(smf::instance("a-b_c9", 1000), "a-b_c9");
        assert_eq!(smf::instance("first.last", 1000), "uid1000");
        assert_eq!(smf::instance("9lives", 1000), "uid1000");
        assert_eq!(smf::instance("", 1000), "uid1000");
        assert_eq!(smf::instance("-rain", 1000), "uid1000");
        assert_eq!(smf::instance("rainé", 1000), "uid1000");
        assert_eq!(smf::instance(&"a".repeat(119), 1000), "a".repeat(119));
        assert_eq!(smf::instance(&"a".repeat(120), 1000), "uid1000");
    }

    #[test]
    fn smf_refusals_in_svcadm_and_svccfg_words_lack_rights() {
        assert!(lacks_rights(
            "`pfexec /usr/sbin/svcadm enable -t svc:/site/musubi/daemon:rain` failed: svcadm: \
             svc:/site/musubi/daemon:rain: Permission denied."
        ));
        assert!(lacks_rights(
            "`pfexec /usr/sbin/svccfg import smf-daemon.xml` failed: svccfg: Could not create \
             temporary service \"TEMP/site/musubi/daemon\" (permission denied)."
        ));
        assert!(!lacks_rights(
            "`pfexec /usr/sbin/svcadm enable svc:/site/musubi/daemon:rain` failed: svcadm: \
             Pattern 'svc:/site/musubi/daemon:rain' doesn't match any instances"
        ));
    }

    #[test]
    fn smf_manifest_without_environment() {
        let text = smf::manifest(
            Service::Daemon,
            "rain",
            "rain",
            Path::new("/opt/bin/musubi"),
            None,
            &[],
        );
        assert!(!text.contains("method_environment"), "{text}");
    }

    // SMF's own check of the manifests against `service_bundle.dtd.1`, which the substring tests
    // above can't make: the order of elements, required attributes, an empty
    // `method_environment`. `svccfg validate` only reads the file, so it needs no authorization
    // and changes nothing.
    #[cfg(any(target_os = "illumos", target_os = "solaris"))]
    #[test]
    fn smf_manifests_validate() {
        let dir = musubi_testutil::tempdir();
        let cases = [
            (Service::Daemon, None, environment()),
            (Service::Hub, Some(Path::new("/srv/a&b hub")), environment()),
            (Service::Daemon, None, Vec::new()),
        ];
        for (index, (service, working, variables)) in cases.into_iter().enumerate() {
            let path = dir.path().join(format!("manifest-{index}.xml"));
            fs::write(
                &path,
                smf::manifest(
                    service,
                    "rain",
                    "rain",
                    Path::new("/opt/it's 100%/musubi"),
                    working,
                    &variables,
                ),
            )
            .unwrap();
            let output = Command::new("/usr/sbin/svccfg")
                .arg("validate")
                .arg(&path)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}: {}",
                path.display(),
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }

    // svc.startd turns `%%` back into `%`, then runs the method with `/sbin/sh -c "exec
    // <method>"` (here `/bin/sh`, which every Unix has): the shell, not the quoting code, is the
    // oracle for what argument it gets.
    #[cfg(unix)]
    #[test]
    fn smf_exec_quote_survives_startd_and_sh() {
        for path in [
            "/opt/bin/musubi",
            "/opt/my bin/musubi",
            "/it's/musubi",
            "''",
            "a'",
            "'b",
            "/100%/musubi",
            "%%",
            "%'%",
            "/a$HOME/`x`/\\/\"q\"",
        ] {
            let quoted = smf::exec_quote(path);
            assert!(
                !quoted.replace("%%", "").contains('%'),
                "a lone % startd would read as a token: {quoted}"
            );
            let expanded = quoted.replace("%%", "%");
            let output = Command::new("/bin/sh")
                .args(["-c", &format!("exec printf '%s\\n' {expanded}")])
                .output()
                .unwrap();
            assert!(output.status.success(), "{expanded}");
            assert_eq!(
                String::from_utf8(output.stdout).unwrap(),
                format!("{path}\n")
            );
        }
    }

    #[test]
    fn smf_log_paths() {
        assert_eq!(
            smf::log_path("svc:/site/musubi/daemon:rain"),
            "/var/svc/log/site-musubi-daemon:rain.log"
        );
    }
}

#[cfg(all(
    test,
    any(
        target_os = "macos",
        target_os = "linux",
        target_os = "illumos",
        target_os = "solaris"
    )
))]
mod process_tests;
