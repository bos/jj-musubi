//! Starting the daemon, or a hub, at login, as the platform's own service manager does it:
//!
//! - macOS: a launchd agent, `~/Library/LaunchAgents/io.github.bos.musubi.plist` (or
//!   `io.github.bos.musubi.hub.plist`);
//! - Linux: a systemd user unit, `~/.config/systemd/user/musubi.service` (or
//!   `musubi-hub.service`);
//! - Windows, for the daemon only: an entry in the current user's `Run` registry key, which
//!   runs `musubi daemon start` at login.
//!
//! The hub's service runs `musubi hub` in the hub's directory, as the user's one hub.
//!
//! Where launchd or systemd runs the daemon, commands that need it ask the service manager to
//! start it rather than starting one themselves, so there is only ever one, and it restarts
//! after a crash but not after `musubi daemon stop`. The service carries the `PATH` (the
//! daemon and the hub run `git`) of the shell that installed it, and what there says where
//! jj's config, which holds the daemon's own settings too, and musubi's state are:
//! `JJ_CONFIG`, `XDG_CONFIG_HOME`, `XDG_STATE_HOME`, and any `MUSUBI_*` settings.
//!
//! A marker in the state directory records each installation, so that a command run with
//! another `MUSUBI_STATE_DIR`, as tests do, never mistakes this one for its own.

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use anyhow::Context as _;

use crate::config;

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
    #[cfg_attr(windows, allow(dead_code, reason = "macOS and Linux only"))]
    fn command(self) -> &'static str {
        match self {
            Self::Daemon => "daemon",
            Self::Hub => "hub",
        }
    }

    #[cfg_attr(not(target_os = "linux"), allow(dead_code, reason = "Linux only"))]
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
    #[cfg_attr(target_os = "linux", allow(dead_code, reason = "not Linux"))]
    fn log(self) -> anyhow::Result<PathBuf> {
        match self {
            Self::Daemon => config::daemon_log(),
            Self::Hub => config::hub_log(),
        }
    }

    #[cfg_attr(target_os = "linux", allow(dead_code, reason = "not Linux"))]
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

/// The environment the daemon needs from the shell that installed it.
#[cfg_attr(windows, allow(dead_code, reason = "macOS and Linux only"))]
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

fn run(program: &str, args: &[&str]) -> anyhow::Result<()> {
    let output = Command::new(program)
        .args(args)
        .output()
        .with_context(|| format!("running {program}"))?;
    anyhow::ensure!(
        output.status.success(),
        "`{program} {}` failed: {}",
        args.join(" "),
        String::from_utf8_lossy(&output.stderr).trim()
    );
    Ok(())
}

/// Sets `service` up to start at login, run in `dir` if given, and starts it now. The caller
/// has stopped any it started itself.
pub fn install(service: Service, dir: Option<&Path>) -> anyhow::Result<String> {
    let exe = std::env::current_exe()?;
    fs::create_dir_all(config::state_dir()?)?;
    let described = platform::install(service, &exe, dir)?;
    fs::write(service.marker()?, &described)?;
    Ok(described)
}

/// Undoes [`install`], stopping what the service manager runs. Returns whether it was
/// installed.
pub fn uninstall(service: Service) -> anyhow::Result<bool> {
    if !installed(service) {
        return Ok(false);
    }
    platform::uninstall(service)?;
    fs::remove_file(service.marker()?)?;
    Ok(true)
}

/// Asks the service manager to start the daemon now.
pub fn start() -> anyhow::Result<()> {
    platform::start(Service::Daemon)
}

/// Where the service manager logs the output of `service`.
pub fn log_hint(service: Service) -> String {
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
        fs::write(&path, plist(service, exe, dir, &log, &environment()))?;
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
        match fs::remove_file(plist_path(service)?) {
            Err(err) if err.kind() != std::io::ErrorKind::NotFound => Err(err.into()),
            _ => Ok(()),
        }
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
        // A user's service manager rarely has an ssh agent: reach commands' agents instead.
        // The hub ssh-es nowhere.
        if service == Service::Daemon
            && let Some(link) = crate::agent::link()?
        {
            environment.push(("SSH_AUTH_SOCK".to_owned(), link.display().to_string()));
        }
        fs::write(&path, unit(service, exe, dir, &environment))?;
        run("systemctl", &["--user", "daemon-reload"])?;
        run("systemctl", &["--user", "enable", "--now", service.unit()])?;
        Ok(format!("a systemd user unit, {}", path.display()))
    }

    pub fn uninstall(service: Service) -> anyhow::Result<()> {
        run("systemctl", &["--user", "disable", "--now", service.unit()]).ok();
        match fs::remove_file(unit_path(service)?) {
            Err(err) if err.kind() != std::io::ErrorKind::NotFound => return Err(err.into()),
            _ => {}
        }
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

#[cfg(not(any(target_os = "macos", target_os = "linux", windows)))]
mod platform {
    use super::*;

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
    let label = service.label();
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
{working}	<key>EnvironmentVariables</key>
	<dict>
{variables}	</dict>
	<key>RunAtLoad</key>
	<true/>
	<key>KeepAlive</key>
	<dict>
		<key>SuccessfulExit</key>
		<false/>
	</dict>
	<key>LimitLoadToSessionType</key>
	<array>
		<string>Aqua</string>
		<string>Background</string>
	</array>
	<key>ProcessType</key>
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
) -> String {
    let mut text = format!(
        "[Unit]\nDescription={}\n\n[Service]\nExecStart={} {}\n",
        service.description(),
        systemd_quote(&exe.to_string_lossy()),
        service.command()
    );
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
    text.push_str("Restart=on-failure\nRestartSec=5\n\n[Install]\nWantedBy=default.target\n");
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
        );
        assert!(
            text.contains("ExecStart=\"/opt/bin/musubi\" hub\n"),
            "{text}"
        );
        assert!(text.contains("WorkingDirectory=/srv/100%% hub\n"), "{text}");
    }
}
