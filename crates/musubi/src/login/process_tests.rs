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
    'print '*) test "$MUSUBI_TEST_GUI" = yes; exit $? ;;
    'bootstrap '*|'--user enable --now '*)
        if test -f "$HOME/fail-install"; then
            echo 'installation refused' >&2
            exit 1
        fi ;;
esac
"#,
    )
    .unwrap();
    fs::set_permissions(manager, fs::Permissions::from_mode(0o755)).unwrap();

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
        let path = if cfg!(target_os = "macos") {
            home.join(format!("Library/LaunchAgents/{}.plist", service.label()))
        } else {
            home.join("config/systemd/user").join(service.unit())
        };
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
}
