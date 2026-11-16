//! Run the real installation code with private state and stand-in service managers. A child
//! test process owns the environment; nothing invokes the machine's launchctl or systemctl.

#![allow(clippy::unwrap_used)]

use std::os::unix::fs::PermissionsExt as _;

use super::*;

#[test]
fn service_installation_tracks_success_and_keeps_services_separate() {
    let dir = musubi_testutil::tempdir();
    let bin = dir.path().join("bin");
    fs::create_dir(&bin).unwrap();
    let program = if cfg!(target_os = "macos") {
        "launchctl"
    } else {
        "systemctl"
    };
    let manager = bin.join(program);
    fs::write(
        &manager,
        r#"#!/bin/sh
printf '%s\n' "$*" >> "$HOME/calls"
case "$*" in
    'print system/'*) test -f "$HOME/system/${2##*/}.plist"; exit $? ;;
    'show --property=LoadState --value '*)
        if test -f "$HOME/system/$4"; then echo loaded; else echo not-found; fi
        exit 0 ;;
    'print '*) test "$MUSUBI_TEST_GUI" = yes; exit $? ;;
    'bootstrap '*|'--user enable --now '*|'enable --now '*)
        if test -f "$HOME/fail-install"; then
            echo 'installation refused' >&2
            exit 1
        fi ;;
    'bootout system/'*|'disable --now '*|'stop musubi-hub-'*)
        if test -f "$HOME/fail-stop"; then exit 1; fi ;;
esac
"#,
    )
    .unwrap();
    fs::set_permissions(manager, fs::Permissions::from_mode(0o755)).unwrap();
    // Redirect every privileged effect into the private home. No invocation reaches sudo
    // or a system service manager, even when the code uses an absolute program path.
    let sudo = bin.join("sudo");
    fs::write(
        &sudo,
        r#"#!/bin/sh
printf 'sudo %s\n' "$*" >> "$HOME/calls"
if test "$*" = '-- /usr/bin/true'; then
    test ! -f "$HOME/fail-authorize"
    exit $?
fi
program=$2
shift 2
case "$program" in
    /usr/bin/install)
        /bin/mkdir -p "$HOME/system"
        while test "$#" -gt 2; do shift; done
        /bin/cp "$1" "$HOME/system/${2##*/}" ;;
    /bin/rm) /bin/rm -f "$HOME/system/${2##*/}" ;;
    /bin/test) test -e "$HOME/system/${2##*/}" ;;
    *) exec "$HOME/bin/${program##*/}" "$@" ;;
esac
"#,
    )
    .unwrap();
    fs::set_permissions(sudo, fs::Permissions::from_mode(0o755)).unwrap();

    // Both launchd domains matter: a Mac reached only over ssh has no GUI domain.
    for gui in ["yes", "no"] {
        let output = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "login::process_tests::installation_process",
                "--ignored",
                "--nocapture",
            ])
            .env_clear()
            .env("HOME", dir.path())
            .env("PATH", &bin)
            .env("XDG_CONFIG_HOME", dir.path().join("config"))
            .env("MUSUBI_STATE_DIR", dir.path().join("state"))
            .env("MUSUBI_TEST_LOGIN_ROOT", dir.path())
            .env("MUSUBI_TEST_GUI", gui)
            .env("UNRELATED_SECRET", "must not enter the service")
            // Preserve per-test coverage when this helper is run by the collector.
            .envs(std::env::vars().filter(|(key, _)| key.starts_with("LLVM_PROFILE_")))
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
#[ignore = "run by service_installation_tracks_success_and_keeps_services_separate"]
fn installation_process() {
    // `cargo test -- --ignored` must never install a real service either.
    let Some(root) = std::env::var_os("MUSUBI_TEST_LOGIN_ROOT") else {
        return;
    };
    let home = PathBuf::from(root);
    assert_eq!(std::env::var_os("HOME").unwrap(), home.as_os_str());
    assert_eq!(
        std::env::var_os("PATH").unwrap(),
        home.join("bin").as_os_str()
    );
    assert_eq!(
        std::env::var_os("MUSUBI_STATE_DIR").unwrap(),
        home.join("state").as_os_str()
    );
    let calls = home.join("calls");
    fs::write(&calls, "").unwrap();
    for service in [Service::Daemon, Service::Hub] {
        assert!(!installed(service));
        assert!(!uninstall(service).unwrap());
    }
    assert_eq!(fs::read_to_string(&calls).unwrap(), "");

    for service in [Service::Daemon, Service::Hub] {
        fs::write(home.join("fail-install"), "").unwrap();
        let err = install(service, Some(&home)).unwrap_err();
        assert!(err.to_string().contains("installation refused"), "{err:#}");
        assert!(
            !installed(service),
            "a failed install must not leave a marker"
        );
        // Nor anything else, which uninstalling, finding no marker, would leave.
        assert!(!service_file(&home, service).exists());
        fs::remove_file(home.join("fail-install")).unwrap();
        let description = install(service, Some(&home)).unwrap();
        assert_eq!(
            fs::read_to_string(service.marker().unwrap()).unwrap(),
            description
        );
        assert!(installed(service));
    }
    assert!(managed());
    start().unwrap();

    for service in [Service::Daemon, Service::Hub] {
        let path = service_file(&home, service);
        let text = fs::read_to_string(&path).unwrap();
        assert!(text.contains("MUSUBI_TEST_GUI"), "{text}");
        assert!(
            text.contains(&home.join("bin").display().to_string()),
            "{text}"
        );
        assert!(!text.contains("UNRELATED_SECRET"), "{text}");
        assert!(!text.contains("must not enter the service"), "{text}");
        assert!(log_hint(service).contains(if cfg!(target_os = "macos") {
            if service == Service::Daemon {
                "daemon.log"
            } else {
                "hub.log"
            }
        } else {
            service.unit()
        }));
        // A user can remove the unit file before uninstalling. The marker still needs to go.
        fs::remove_file(&path).unwrap();
        assert!(uninstall(service).unwrap());
        assert!(!installed(service));
        assert!(!uninstall(service).unwrap());
        if service == Service::Daemon {
            assert!(!managed());
            assert!(installed(Service::Hub));
        }
    }
    let calls = fs::read_to_string(calls).unwrap();
    if cfg!(target_os = "macos") {
        let domain = if std::env::var("MUSUBI_TEST_GUI").unwrap() == "yes" {
            "gui"
        } else {
            "user"
        };
        let domain = format!("{domain}/{}", crate::socket::uid().unwrap());
        for service in [Service::Daemon, Service::Hub] {
            assert!(
                calls.contains(&format!("bootout {domain}/{}", service.label())),
                "{calls}"
            );
        }
        assert!(
            calls.contains(&format!("kickstart {domain}/io.github.bos.musubi\n")),
            "{calls}"
        );
        assert!(calls.contains(&format!("bootstrap {domain} ")), "{calls}");
    } else {
        for service in [Service::Daemon, Service::Hub] {
            assert!(
                calls.contains(&format!("--user enable --now {}\n", service.unit())),
                "{calls}"
            );
            assert!(
                calls.contains(&format!("--user disable --now {}\n", service.unit())),
                "{calls}"
            );
        }
        assert!(calls.contains("--user daemon-reload\n"), "{calls}");
        assert!(calls.contains("--user start musubi.service\n"), "{calls}");
    }

    // Root bypasses sudo in production; don't run this part where our stand-in cannot
    // intercept it. The boot-service tests normally run as an unprivileged user.
    if rustix::process::getuid().is_root() {
        return;
    }
    fs::write(home.join("fail-authorize"), "").unwrap();
    assert!(prepare_hub_install(true).is_err());
    assert!(!installed(Service::Hub));
    fs::remove_file(home.join("fail-authorize")).unwrap();
    prepare_hub_install(true).unwrap();
    let uid = rustix::process::getuid().as_raw();
    let file = home.join("system").join(if cfg!(target_os = "macos") {
        format!("io.github.bos.musubi.hub.{uid}.plist")
    } else {
        format!("musubi-hub-{uid}.service")
    });
    fs::write(home.join("fail-install"), "").unwrap();
    assert!(install_hub(&home, true).is_err());
    assert!(!installed(Service::Hub));
    assert!(!file.exists());
    fs::remove_file(home.join("fail-install")).unwrap();
    install_hub(&home, true).unwrap();
    assert!(hub_at_boot());
    assert!(!managed());
    let text = fs::read_to_string(&file).unwrap();
    assert!(text.contains("HOME"), "{text}");
    assert!(
        text.contains(&home.join("state").display().to_string()),
        "{text}"
    );
    assert!(!text.contains("UNRELATED_SECRET"), "{text}");
    if cfg!(target_os = "macos") {
        assert!(text.contains("<key>UserName</key>"), "{text}");
        assert!(!text.contains("LimitLoadToSessionType"), "{text}");
    } else {
        assert!(text.contains(&format!("User={uid}\n")), "{text}");
        assert!(text.contains("WantedBy=multi-user.target"), "{text}");
        assert!(log_hint(Service::Hub).contains(&format!("musubi-hub-{uid}.service")));
    }
    fs::write(home.join("fail-stop"), "").unwrap();
    assert!(uninstall(Service::Hub).is_err());
    assert!(
        hub_at_boot(),
        "a failed stop must retain the installation marker"
    );
    assert!(file.exists());
    fs::remove_file(home.join("fail-stop")).unwrap();
    assert!(uninstall(Service::Hub).unwrap());
    assert!(!hub_at_boot());
    assert!(!file.exists());
    // A partial installation whose cleanup also fails must remain removable.
    fs::write(home.join("fail-install"), "").unwrap();
    fs::write(home.join("fail-stop"), "").unwrap();
    assert!(install_hub(&home, true).is_err());
    assert!(hub_at_boot());
    fs::remove_file(home.join("fail-install")).unwrap();
    fs::remove_file(home.join("fail-stop")).unwrap();
    assert!(uninstall(Service::Hub).unwrap());
    install_hub(&home, false).unwrap();
    assert!(!hub_at_boot());
    assert!(uninstall(Service::Hub).unwrap());
}

/// The unit file or agent that installing `service` writes.
fn service_file(home: &Path, service: Service) -> PathBuf {
    if cfg!(target_os = "macos") {
        home.join(format!("Library/LaunchAgents/{}.plist", service.label()))
    } else {
        home.join("config/systemd/user").join(service.unit())
    }
}
