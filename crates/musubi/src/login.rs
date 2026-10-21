//! Starting the daemon at login, as the platform's own service manager does it:
//!
//! - macOS: a launchd agent, `~/Library/LaunchAgents/io.github.bos.musubi.plist`;
//! - Linux: a systemd user unit, `~/.config/systemd/user/musubi.service`;
//! - Windows: an entry in the current user's `Run` registry key, which runs
//!   `musubi daemon start` at login.
//!
//! Where launchd or systemd runs the daemon, commands that need it ask the service manager to
//! start it rather than starting one themselves, so there is only ever one, and it restarts
//! after a crash but not after `musubi daemon stop`. The service carries the `PATH` (the
//! daemon runs `git`) and any `MUSUBI_*` settings of the shell that installed it.
//!
//! A marker in the state directory records the installation, so that a command run with
//! another `MUSUBI_CONFIG_DIR`, as tests do, never mistakes this one for its own.

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use anyhow::Context as _;

use crate::config;

/// launchd's label for the agent.
#[cfg_attr(not(target_os = "macos"), allow(dead_code, reason = "macOS only"))]
const LABEL: &str = "io.github.bos.musubi";

/// systemd's name for the unit.
#[cfg_attr(not(target_os = "linux"), allow(dead_code, reason = "Linux only"))]
const UNIT: &str = "musubi.service";

/// The name of the value in the `Run` registry key.
#[cfg_attr(not(windows), allow(dead_code, reason = "Windows only"))]
const RUN_VALUE: &str = "musubi";

/// The environment the daemon needs from the shell that installed it.
fn environment() -> Vec<(String, String)> {
    std::env::vars()
        .filter(|(name, _)| name == "PATH" || name.starts_with("MUSUBI_"))
        .collect()
}

fn marker() -> anyhow::Result<PathBuf> {
    Ok(config::state_dir()?.join("login-service"))
}

/// Whether `musubi daemon install` set up this user's daemon to start at login.
pub fn installed() -> bool {
    marker().is_ok_and(|path| path.exists())
}

/// Whether the service manager runs the daemon, so that commands must ask it to start the
/// daemon rather than starting it themselves.
pub fn managed() -> bool {
    installed() && !cfg!(windows)
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

/// Sets the daemon up to start at login, and starts it now. The caller has stopped any
/// daemon it started itself.
pub fn install() -> anyhow::Result<String> {
    let exe = std::env::current_exe()?;
    let log = config::state_dir()?.join("daemon.log");
    fs::create_dir_all(config::state_dir()?)?;
    let described = platform::install(&exe, &log)?;
    fs::write(marker()?, &described)?;
    Ok(described)
}

/// Undoes [`install`], stopping a daemon the service manager runs. Returns whether it was
/// installed.
pub fn uninstall() -> anyhow::Result<bool> {
    if !installed() {
        return Ok(false);
    }
    platform::uninstall()?;
    fs::remove_file(marker()?)?;
    Ok(true)
}

/// Asks the service manager to start the daemon now.
pub fn start() -> anyhow::Result<()> {
    platform::start()
}

/// Where the service manager logs the daemon's output.
pub fn log_hint() -> String {
    platform::log_hint()
}

#[cfg(target_os = "macos")]
mod platform {
    use super::*;

    fn plist_path() -> anyhow::Result<PathBuf> {
        let home = std::env::var_os("HOME").context("HOME is not set")?;
        Ok(PathBuf::from(home).join(format!("Library/LaunchAgents/{LABEL}.plist")))
    }

    /// The login session's domain, or with nobody logged in at the screen (a Mac reached
    /// over SSH), the user's background domain, which launchd keeps while they have any
    /// session. The agent may load in either (`LimitLoadToSessionType`).
    fn domain() -> anyhow::Result<String> {
        let uid = crate::control::uid()?;
        let gui = format!("gui/{uid}");
        let has_gui = Command::new("launchctl")
            .args(["print", &gui])
            .output()
            .is_ok_and(|output| output.status.success());
        Ok(if has_gui { gui } else { format!("user/{uid}") })
    }

    pub fn install(exe: &Path, log: &Path) -> anyhow::Result<String> {
        let path = plist_path()?;
        if let Some(dir) = path.parent() {
            fs::create_dir_all(dir)?;
        }
        fs::write(&path, plist(exe, log, &environment()))?;
        // Replace any earlier version of the agent.
        run("launchctl", &["bootout", &format!("{}/{LABEL}", domain()?)]).ok();
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

    pub fn uninstall() -> anyhow::Result<()> {
        // Stops the daemon too.
        run("launchctl", &["bootout", &format!("{}/{LABEL}", domain()?)]).ok();
        match fs::remove_file(plist_path()?) {
            Err(err) if err.kind() != std::io::ErrorKind::NotFound => Err(err.into()),
            _ => Ok(()),
        }
    }

    pub fn start() -> anyhow::Result<()> {
        run(
            "launchctl",
            &["kickstart", &format!("{}/{LABEL}", domain()?)],
        )
    }

    pub fn log_hint() -> String {
        config::state_dir().map_or_else(
            |_| "the daemon's log".to_owned(),
            |dir| dir.join("daemon.log").display().to_string(),
        )
    }
}

#[cfg(target_os = "linux")]
mod platform {
    use etcetera::BaseStrategy as _;

    use super::*;

    fn unit_path() -> anyhow::Result<PathBuf> {
        let base = etcetera::choose_base_strategy().context("no config directory")?;
        Ok(base.config_dir().join("systemd/user").join(UNIT))
    }

    pub fn install(exe: &Path, _log: &Path) -> anyhow::Result<String> {
        let path = unit_path()?;
        if let Some(dir) = path.parent() {
            fs::create_dir_all(dir)?;
        }
        fs::write(&path, unit(exe, &environment()))?;
        run("systemctl", &["--user", "daemon-reload"])?;
        run("systemctl", &["--user", "enable", "--now", UNIT])?;
        Ok(format!("a systemd user unit, {}", path.display()))
    }

    pub fn uninstall() -> anyhow::Result<()> {
        run("systemctl", &["--user", "disable", "--now", UNIT]).ok();
        match fs::remove_file(unit_path()?) {
            Err(err) if err.kind() != std::io::ErrorKind::NotFound => return Err(err.into()),
            _ => {}
        }
        run("systemctl", &["--user", "daemon-reload"])
    }

    pub fn start() -> anyhow::Result<()> {
        run("systemctl", &["--user", "start", UNIT])
    }

    pub fn log_hint() -> String {
        format!("`journalctl --user -u {UNIT}`")
    }
}

#[cfg(windows)]
mod platform {
    use super::*;

    const KEY: &str = r"HKCU\Software\Microsoft\Windows\CurrentVersion\Run";

    pub fn install(exe: &Path, _log: &Path) -> anyhow::Result<String> {
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

    pub fn uninstall() -> anyhow::Result<()> {
        run("reg", &["delete", KEY, "/v", RUN_VALUE, "/f"])
    }

    pub fn start() -> anyhow::Result<()> {
        anyhow::bail!("Windows has no service manager running the daemon")
    }

    pub fn log_hint() -> String {
        config::state_dir().map_or_else(
            |_| "the daemon's log".to_owned(),
            |dir| dir.join("daemon.log").display().to_string(),
        )
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux", windows)))]
mod platform {
    use super::*;

    pub fn install(_: &Path, _: &Path) -> anyhow::Result<String> {
        anyhow::bail!("musubi can't start the daemon at login on this system")
    }

    pub fn uninstall() -> anyhow::Result<()> {
        Ok(())
    }

    pub fn start() -> anyhow::Result<()> {
        anyhow::bail!("musubi can't start the daemon at login on this system")
    }

    pub fn log_hint() -> String {
        "the daemon's log".to_owned()
    }
}

/// A launchd agent that runs `exe daemon` at login, and again if it fails, but not after
/// it stops cleanly.
#[cfg_attr(not(target_os = "macos"), allow(dead_code, reason = "macOS only"))]
fn plist(exe: &Path, log: &Path, environment: &[(String, String)]) -> String {
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
    let log = string(&log.to_string_lossy());
    format!(
        r#"<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
	<key>Label</key>
	<string>{LABEL}</string>
	<key>ProgramArguments</key>
	<array>
		{exe}
		<string>daemon</string>
	</array>
	<key>EnvironmentVariables</key>
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

/// A systemd user unit that runs `exe daemon` from login, and again if it fails, but not
/// after it stops cleanly.
#[cfg_attr(not(target_os = "linux"), allow(dead_code, reason = "Linux only"))]
fn unit(exe: &Path, environment: &[(String, String)]) -> String {
    let mut text = format!(
        "[Unit]\nDescription=musubi: keeps jj repositories in sync across machines\n\n\
         [Service]\nExecStart={} daemon\n",
        systemd_quote(&exe.to_string_lossy())
    );
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
            Path::new("/opt/bin/mu<s>ubi"),
            Path::new("/l/daemon.log"),
            &environment(),
        );
        assert!(
            text.contains("<string>/opt/bin/mu&lt;s&gt;ubi</string>\n\t\t<string>daemon</string>")
        );
        assert!(text.contains("<key>PATH</key>\n\t\t<string>/usr/bin:/opt/my tools/bin</string>"));
        assert!(text.contains("<string>/tmp/a&amp;b%&quot;c&quot;.sock</string>"));
        assert!(text.contains("<key>SuccessfulExit</key>\n\t\t<false/>"));
    }

    #[test]
    fn systemd_unit() {
        let text = unit(Path::new("/opt/my bin/musubi"), &environment());
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
    }
}
