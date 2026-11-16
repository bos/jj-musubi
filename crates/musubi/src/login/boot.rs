//! A hub started by the system service manager, with the installing user's identity.
//! Only installation and service-manager calls use sudo; hub setup never runs as root.

use std::io::Write as _;

use super::*;

fn uid() -> u32 {
    rustix::process::getuid().as_raw()
}

pub(super) fn authorize() -> anyhow::Result<()> {
    anyhow::ensure!(
        uid() != 0 || std::env::var_os("SUDO_UID").is_none(),
        "run `musubi hub install --at-boot` without sudo; musubi requests it when needed"
    );
    if uid() != 0 {
        let status = Command::new("sudo")
            // Unlike `sudo -v`, a command honors a matching NOPASSWD rule even when
            // other sudoers entries require a password (the default verifypw=all).
            .args(["--", "/usr/bin/true"])
            .status()
            .context("running sudo")?;
        anyhow::ensure!(
            status.success(),
            "sudo refused permission to manage the hub's boot service"
        );
    }
    Ok(())
}

fn privileged_command(program: &str, args: &[&str]) -> Command {
    if uid() == 0 {
        let mut command = Command::new(program);
        command.args(args);
        command
    } else {
        let mut command = Command::new("sudo");
        command.args(["--", program]).args(args);
        command
    }
}

fn privileged(program: &str, args: &[&str]) -> anyhow::Result<()> {
    let output = privileged_command(program, args)
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

#[cfg(target_os = "macos")]
fn label() -> String {
    format!("io.github.bos.musubi.hub.{}", uid())
}

#[cfg(target_os = "linux")]
pub(super) fn unit_name() -> String {
    format!("musubi-hub-{}.service", uid())
}

fn service_path() -> PathBuf {
    #[cfg(target_os = "macos")]
    {
        PathBuf::from(format!("/Library/LaunchDaemons/{}.plist", label()))
    }
    #[cfg(target_os = "linux")]
    {
        PathBuf::from("/etc/systemd/system").join(unit_name())
    }
}

/// The system-service name is per user, while installation markers are per state
/// directory. A different state directory must not replace a service it cannot uninstall.
pub(super) fn check_available() -> anyhow::Result<()> {
    let exists = if service_file_exists()? {
        true
    } else {
        #[cfg(target_os = "macos")]
        {
            Command::new("launchctl")
                .args(["print", &format!("system/{}", label())])
                .output()
                .context("checking the hub's boot service")?
                .status
                .success()
        }
        #[cfg(target_os = "linux")]
        {
            let output = Command::new("systemctl")
                .args(["show", "--property=LoadState", "--value", &unit_name()])
                .output()
                .context("checking the hub's boot service")?;
            anyhow::ensure!(
                output.status.success(),
                "can't inspect the hub's boot service: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            );
            output.stdout != b"not-found\n"
        }
    };
    anyhow::ensure!(
        !exists,
        "a boot hub service is already installed for this user; uninstall it with its original state directory first"
    );
    Ok(())
}

fn service_file_exists() -> anyhow::Result<bool> {
    let path = service_path();
    let output = privileged_command(
        "/bin/test",
        &["-e", path.to_str().context("non-UTF-8 path")?],
    )
    .output()
    .context("checking the hub's boot service file")?;
    match output.status.code() {
        Some(0) => Ok(true),
        Some(1) if output.stderr.is_empty() => Ok(false),
        _ => anyhow::bail!(
            "can't inspect the hub's boot service file: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ),
    }
}

pub(super) fn install(exe: &Path, dir: &Path) -> anyhow::Result<String> {
    let home = std::env::var("HOME").context("HOME is not set")?;
    anyhow::ensure!(
        Path::new(&home).is_absolute(),
        "HOME must be an absolute path"
    );
    let mut environment = environment();
    environment.push(("HOME".to_owned(), home));
    // Keep relative shell overrides from acquiring a different meaning in the hub's cwd.
    environment.retain(|(key, _)| key != "MUSUBI_STATE_DIR");
    environment.push((
        "MUSUBI_STATE_DIR".to_owned(),
        config::state_dir()?.display().to_string(),
    ));
    let text = service_text(exe, dir, &environment)?;
    let path = service_path();
    // Write through the tempfile's handle; install gives the system copy root ownership.
    let mut staged = tempfile::NamedTempFile::new()?;
    staged.write_all(text.as_bytes())?;
    privileged(
        "/usr/bin/install",
        &[
            "-o",
            "root",
            "-g",
            "0",
            "-m",
            "644",
            staged.path().to_str().context("non-UTF-8 path")?,
            path.to_str().context("non-UTF-8 path")?,
        ],
    )?;
    #[cfg(target_os = "macos")]
    {
        privileged(
            "/bin/launchctl",
            &[
                "bootstrap",
                "system",
                path.to_str().context("non-UTF-8 path")?,
            ],
        )?;
        Ok(format!("a launchd daemon, {}", path.display()))
    }
    #[cfg(target_os = "linux")]
    {
        privileged("/usr/bin/systemctl", &["daemon-reload"])?;
        privileged("/usr/bin/systemctl", &["enable", "--now", &unit_name()])?;
        Ok(format!("a systemd system unit, {}", path.display()))
    }
}

fn service_text(
    exe: &Path,
    dir: &Path,
    environment: &[(String, String)],
) -> anyhow::Result<String> {
    #[cfg(target_os = "macos")]
    {
        let user = whoami::username()?;
        Ok(plist(
            Service::Hub,
            exe,
            Some(dir),
            &Service::Hub.log()?,
            environment,
            Some((&label(), &user)),
        ))
    }
    #[cfg(target_os = "linux")]
    {
        Ok(unit(Service::Hub, exe, Some(dir), environment, Some(uid())))
    }
}

pub(super) fn uninstall() -> anyhow::Result<()> {
    let path = service_path();
    #[cfg(target_os = "macos")]
    {
        let target = format!("system/{}", label());
        if let Err(err) = privileged("/bin/launchctl", &["bootout", &target]) {
            // Already stopped is fine, including cleanup after a refused bootstrap. A
            // failed bootout of a still-loaded job must leave its marker for another try.
            if privileged("/bin/launchctl", &["print", &target]).is_ok() {
                return Err(err);
            }
        }
    }
    #[cfg(target_os = "linux")]
    {
        let unit = unit_name();
        if let Err(err) = privileged("/usr/bin/systemctl", &["disable", "--now", &unit]) {
            if service_file_exists()? {
                return Err(err);
            }
            // A removed unit file can make disable fail even though the manager still
            // has the running service loaded. Stop it before forgetting the installation.
            if let Err(stop) = privileged("/usr/bin/systemctl", &["stop", &unit]) {
                let state = privileged_command(
                    "/usr/bin/systemctl",
                    &["show", "--property=LoadState", "--value", &unit],
                )
                .output()?;
                if !state.status.success() || state.stdout != b"not-found\n" {
                    return Err(stop);
                }
            }
        }
    }
    privileged("/bin/rm", &["-f", path.to_str().context("non-UTF-8 path")?])?;
    #[cfg(target_os = "linux")]
    privileged("/usr/bin/systemctl", &["daemon-reload"])?;
    Ok(())
}
