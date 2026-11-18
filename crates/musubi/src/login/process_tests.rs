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
    let systemd_or_launchd = r#"#!/bin/sh
printf '%s\n' "$*" >> "$HOME/service-calls"
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
    '--user daemon-reload')
        if test -f "$HOME/fail-reload"; then
            echo 'reload refused' >&2
            exit 1
        fi ;;
esac
"#;
    let stand_ins: &[(&str, &str)] = if cfg!(target_os = "macos") {
        &[("launchctl", systemd_or_launchd)]
    } else if cfg!(target_os = "linux") {
        &[("systemctl", systemd_or_launchd)]
    } else {
        &[
            ("pfexec", musubi_testutil::PFEXEC_STAND_IN),
            ("svcs", musubi_testutil::SVCS_STAND_IN),
        ]
    };
    for (program, script) in stand_ins {
        let path = bin.join(program);
        fs::write(&path, script).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
    }
    // Redirect every privileged effect into the private home. No invocation reaches sudo
    // or a system service manager, even when the code uses an absolute program path.
    let sudo = bin.join("sudo");
    fs::write(
        &sudo,
        r#"#!/bin/sh
printf 'sudo %s\n' "$*" >> "$HOME/service-calls"
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
    let calls = home.join("service-calls");
    fs::write(&calls, "").unwrap();
    for service in [Service::Daemon, Service::Hub] {
        assert!(!installed(service));
        assert!(!uninstall(service).unwrap());
    }
    // The SMF instance is named after the user, not the state directory, so only the marker keeps
    // a test's stop away from the developer's own daemon.
    assert!(!stop().unwrap());
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
        if SMF {
            // Failing after the import, the undo removes the instance and, with no other user's
            // left, the service.
            fs::write(home.join("fail-enable"), "").unwrap();
            let err = install(service, Some(&home)).unwrap_err();
            assert!(err.to_string().contains("enabling refused"), "{err:#}");
            assert!(!installed(service));
            let fmri = smf::fmri(service).unwrap();
            assert!(!smf_state(&home, &fmri).exists());
            let shared = smf_state(&home, &smf::service_fmri(service));
            assert!(!PathBuf::from(format!("{}.service", shared.display())).exists());
            assert!(!service_file(&home, service).exists());
            fs::remove_file(home.join("fail-enable")).unwrap();
        }
        let description = install(service, Some(&home)).unwrap();
        assert_eq!(
            fs::read_to_string(service.marker().unwrap()).unwrap(),
            description
        );
        assert!(installed(service));
    }
    assert!(managed());
    start().unwrap();
    if SMF {
        smf_failure_paths(&home);
    } else {
        // launchd and systemd leave a daemon that exits cleanly stopped, so stopping asks them
        // nothing.
        let before = fs::read_to_string(&calls).unwrap();
        assert!(!stop().unwrap());
        assert_eq!(fs::read_to_string(&calls).unwrap(), before);
    }

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
        let hint = log_hint(service);
        if cfg!(target_os = "macos") {
            let log = match service {
                Service::Daemon => "daemon.log",
                Service::Hub => "hub.log",
            };
            assert!(hint.contains(log), "{hint}");
        } else if cfg!(target_os = "linux") {
            assert!(hint.contains(service.unit()), "{hint}");
        } else {
            assert!(
                hint.starts_with(&format!("/var/svc/log/site-musubi-{}:", service.command())),
                "{hint}"
            );
        }
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
    // Undoing a failed install can fail too. Under SMF, which can be left set up, the error says
    // so; under systemd, where undoing fails as installing did once the unit file is gone, only
    // the install's error shows. Either way it keeps the install's error and leaves no marker.
    // Each platform names the file that makes both installing and undoing fail, and what its
    // stand-in then says; launchd has no undo that can fail.
    let undo_failure: Option<(&[&str], &str)> = if SMF {
        Some((&["fail-enable", "fail-disable"], "enabling refused"))
    } else if cfg!(target_os = "linux") {
        Some((&["fail-reload"], "reload refused"))
    } else {
        None
    };
    if let Some((blockers, cause)) = undo_failure {
        for blocker in blockers {
            fs::write(home.join(blocker), "").unwrap();
        }
        let err = install(Service::Daemon, None).unwrap_err();
        let text = format!("{err:#}");
        assert_eq!(text.contains("undoing it failed too"), SMF, "{text}");
        assert!(text.contains(cause), "{text}");
        assert_eq!(text.contains("disabling refused"), SMF, "{text}");
        // Under SMF, the instance left stays installed, for uninstalling to remove.
        assert_eq!(installed(Service::Daemon), SMF);
        for blocker in blockers {
            fs::remove_file(home.join(blocker)).unwrap();
        }
        if SMF {
            assert!(
                text.contains("`musubi daemon uninstall` removes what's left"),
                "{text}"
            );
            assert!(uninstall(Service::Daemon).unwrap());
        }
    }
    // Refused at the import, an SMF install leaves no instance, so an undo that fails too needs
    // no marker: a marker would only have commands ask SMF for an instance that isn't there.
    // (The CLI tests check the hint.)
    if SMF {
        fs::write(home.join("deny"), "").unwrap();
        let err = install(Service::Daemon, None).unwrap_err();
        let text = format!("{err:#}");
        assert!(text.contains("(permission denied)"), "{text}");
        assert!(!text.contains("undoing it failed too"), "{text}");
        assert!(!installed(Service::Daemon));
        fs::remove_file(home.join("deny")).unwrap();
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
    } else if SMF {
        for service in [Service::Daemon, Service::Hub] {
            let fmri = smf::fmri(service).unwrap();
            let manifest = service_file(&home, service);
            for call in [
                format!("svccfg import {}\n", manifest.display()),
                format!("svcadm refresh {fmri}\n"),
                format!("svcadm enable {fmri}\n"),
                format!("svcadm disable {fmri}\n"),
                format!("svccfg delete {fmri}\n"),
                format!("svccfg delete {}\n", smf::service_fmri(service)),
            ] {
                assert!(calls.contains(&call), "no `{}` in {calls}", call.trim());
            }
        }
        let daemon = smf::fmri(Service::Daemon).unwrap();
        assert!(
            calls.contains(&format!("svcadm enable -t {daemon}\n")),
            "{calls}"
        );
        assert!(
            calls.contains(&format!("svcadm disable -t {daemon}\n")),
            "{calls}"
        );
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

    // SMF starts the hub it runs at boot already, so `--at-boot` needs no more rights there and
    // installs the same service, with no boot marker.
    if SMF {
        prepare_hub_install(true).unwrap();
        let described = install_hub(&home, true).unwrap();
        assert_eq!(
            described,
            format!("the SMF service {}", smf::fmri(Service::Hub).unwrap())
        );
        assert!(installed(Service::Hub));
        assert!(!hub_at_boot());
        assert!(uninstall(Service::Hub).unwrap());
        return;
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

/// The failure paths only SMF has: maintenance, a missing authorization, and an instance deleted
/// behind musubi's back, which installing again repairs.
fn smf_failure_paths(home: &Path) {
    let daemon = smf::fmri(Service::Daemon).unwrap();
    let state = smf_state(home, &daemon);
    let calls = || fs::read_to_string(home.join("service-calls")).unwrap();
    assert_eq!(fs::read_to_string(&state).unwrap(), "online\n");

    fs::write(&state, "maintenance\n").unwrap();
    start().unwrap();
    assert!(
        calls().contains(&format!("svcadm clear {daemon}\n")),
        "{}",
        calls()
    );
    assert_eq!(fs::read_to_string(&state).unwrap(), "online\n");

    assert!(stop().unwrap());
    assert_eq!(fs::read_to_string(&state).unwrap(), "disabled\n");
    assert!(!stop().unwrap(), "a disabled instance runs nothing");

    // svcs marks a state in transition with `*`, whichever way it's going: an instance in one may
    // run the daemon, still or soon, and one in maintenance doesn't.
    fs::write(&state, "online*\n").unwrap();
    assert!(stop().unwrap());
    fs::write(&state, "offline*\n").unwrap();
    assert!(stop().unwrap());
    fs::write(&state, "degraded\n").unwrap();
    assert!(stop().unwrap());
    fs::write(&state, "maintenance\n").unwrap();
    assert!(!stop().unwrap());

    fs::write(home.join("deny"), "").unwrap();
    let err = start().unwrap_err();
    assert!(err.to_string().contains("Permission denied"), "{err:#}");
    // A clear SMF refuses, of an instance still in maintenance, is the start's error.
    let before_maintenance = fs::read_to_string(&state).unwrap();
    fs::write(&state, "maintenance\n").unwrap();
    let err = start().unwrap_err();
    assert!(err.to_string().contains("Permission denied"), "{err:#}");
    assert!(err.to_string().contains("svcadm clear"), "{err:#}");
    fs::write(&state, before_maintenance).unwrap();
    // An uninstall SMF refuses keeps the marker and the instance, for another try.
    let err = uninstall(Service::Daemon).unwrap_err();
    assert!(err.to_string().contains("Permission denied"), "{err:#}");
    assert!(installed(Service::Daemon));
    assert!(state.exists());
    fs::remove_file(home.join("deny")).unwrap();

    fs::remove_file(&state).unwrap();
    let err = start().unwrap_err();
    assert!(err.to_string().contains("SMF has no instance"), "{err:#}");
    let before = calls();
    assert!(!stop().unwrap(), "no instance: the caller stops the daemon");
    assert!(!calls()[before.len()..].contains("disable"), "{}", calls());
    let restart = format!("svcadm restart {daemon}\n");
    let before = calls();
    install(Service::Daemon, None).unwrap();
    assert_eq!(fs::read_to_string(&state).unwrap(), "online\n");
    assert!(!calls()[before.len()..].contains(&restart), "{}", calls());

    // An instance this state directory has no marker for, as one installed with another, stays
    // when an install over it fails: undoing that install would delete someone's service.
    let marker = Service::Daemon.marker().unwrap();
    fs::remove_file(&marker).unwrap();
    fs::write(home.join("fail-install"), "").unwrap();
    let before = calls();
    install(Service::Daemon, None).unwrap_err();
    assert!(
        !calls()[before.len()..].contains("svccfg delete"),
        "{}",
        calls()
    );
    assert_eq!(fs::read_to_string(&state).unwrap(), "online\n");
    fs::remove_file(home.join("fail-install")).unwrap();
    install(Service::Daemon, None).unwrap();

    // Installing over a disabled instance, as after `musubi daemon stop`, enables it without a
    // restart; over one in maintenance, clears it first.
    for (left, cleared) in [("disabled", false), ("maintenance", true)] {
        fs::write(&state, format!("{left}\n")).unwrap();
        let before = calls();
        install(Service::Daemon, None).unwrap();
        let made = &calls()[before.len()..];
        assert!(!made.contains("svcadm restart"), "{made}");
        assert_eq!(made.contains("svcadm clear"), cleared, "{made}");
        assert_eq!(fs::read_to_string(&state).unwrap(), "online\n");
    }

    // Installing over an instance that's running, as one installed with another state
    // directory is, restarts it, since neither a refresh nor an enable would apply its new
    // settings.
    let before = calls();
    install(Service::Daemon, None).unwrap();
    assert!(calls()[before.len()..].contains(&restart), "{}", calls());
    assert_eq!(fs::read_to_string(&state).unwrap(), "online\n");
    // So does one svcs shows in transition (`online*`), which still runs it.
    fs::write(&state, "online*\n").unwrap();
    let before = calls();
    install(Service::Daemon, None).unwrap();
    assert!(calls()[before.len()..].contains(&restart), "{}", calls());

    // The service is shared: uninstalling keeps it while another user's instance is left, and
    // deletes it once none is.
    let other = smf_state(home, &smf::fmri_of(Service::Daemon, "someone-else"));
    fs::write(&other, "online\n").unwrap();
    let before = calls();
    assert!(uninstall(Service::Daemon).unwrap());
    let delete_service = format!("svccfg delete {}\n", smf::service_fmri(Service::Daemon));
    assert!(
        !calls()[before.len()..].contains(&delete_service),
        "{}",
        calls()
    );
    assert!(other.exists());
    fs::remove_file(&other).unwrap();
    install(Service::Daemon, None).unwrap();

    // A stop method that times out leaves the instance in maintenance, with nothing running:
    // stopping counts it stopped, and uninstalling deletes it, rather than waiting for a
    // `disabled` that never comes.
    fs::write(home.join("stop-times-out"), "").unwrap();
    let (stopped, warned) = logged(stop);
    assert!(stopped.unwrap());
    assert_eq!(fs::read_to_string(&state).unwrap(), "maintenance\n");
    // It says so, since the daemon was killed rather than stopping; stopping it again, in
    // maintenance already, says nothing.
    assert!(warned.contains("SMF killed what it ran"), "{warned}");
    let (stopped, warned) = logged(stop);
    assert!(!stopped.unwrap());
    assert_eq!(warned, "");
    start().unwrap();
    assert!(uninstall(Service::Daemon).unwrap());
    assert!(!state.exists());
    fs::remove_file(home.join("stop-times-out")).unwrap();
    install(Service::Daemon, None).unwrap();
}

/// What `f` returns, and the warnings it logs.
fn logged<T>(f: impl FnOnce() -> T) -> (T, String) {
    let log = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let writer = log.clone();
    let subscriber = tracing_subscriber::fmt()
        .with_max_level(tracing::Level::WARN)
        .with_ansi(false)
        .with_writer(move || Writer(writer.clone()))
        .finish();
    let result = tracing::subscriber::with_default(subscriber, f);
    let text = String::from_utf8(log.lock().unwrap().clone()).unwrap();
    (result, text)
}

/// A writer into the buffer [`logged`] reads.
struct Writer(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);

impl std::io::Write for Writer {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// The file the SMF stand-ins keep `fmri`'s state in: `~/smf/<fmri with / and : as _>`, as
/// musubi_testutil's scripts name it.
fn smf_state(home: &Path, fmri: &str) -> PathBuf {
    home.join("smf").join(fmri.replace(['/', ':'], "_"))
}

/// The unit file or agent that installing `service` writes.
fn service_file(home: &Path, service: Service) -> PathBuf {
    if cfg!(target_os = "macos") {
        home.join(format!("Library/LaunchAgents/{}.plist", service.label()))
    } else if SMF {
        smf::manifest_path(service).unwrap()
    } else {
        home.join("config/systemd/user").join(service.unit())
    }
}
