# Upgrade jj-musubi

Upgrading jj-musubi means replacing the `musubi` executable and restarting the processes that
use it. The hub passes work between your copies, so it and the daemons that sync those copies
should run the same release.

You can upgrade each machine by hand, or [set up automatic upgrades](#automatic-upgrades) so
that the machines follow the hub. With an installer in place, you only need to upgrade the
hub; sleeping machines catch up when they reconnect.

## Upgrade by hand

[Download the new release](setup.md#install-jj-musubi). Before replacing the installed
executables, stop the daemon on each machine you are upgrading by hand:

```sh
musubi daemon stop
```

Stop the hub with Ctrl-C, or run `musubi hub uninstall` if it runs as a service. Then replace
the executables. Stopping first lets you replace a binary that the operating system would
otherwise keep locked while it runs.

Start the hub with the same directory and options. If it runs as a service, rerun
`musubi hub install` with `--dir <hub-directory>` pointing to its existing directory. Keep
`--at-boot` if the service starts at boot.

If a daemon service's executable moved, use the new executable to run `musubi daemon install`.
This updates the service and starts it. For other machines upgraded by hand, restart the daemon:

```sh
musubi daemon restart
```

A new command may refuse an older daemon's control protocol until the daemon restarts.

Run `musubi sync` in a joined repo to check that it can sync with the hub. `musubi top` shows
the release each machine is running. If you use automatic upgrades, wait for those machines to
show the new release; their daemons restart automatically.

## Automatic upgrades

The daemon can run an installer whenever it finds that the hub has a newer release. It tells the
installer which version to install through `MUSUBI_UPGRADE_TO`, then restarts from the upgraded
executable. You choose how to install it.

For example, save this cargo installer as `~/bin/upgrade-musubi` and make it executable:

```sh
#!/bin/sh
set -e
cargo install --locked --version "$MUSUBI_UPGRADE_TO" jj-musubi
```

On each working machine, tell the daemon to use it:

```sh
jj config set --user musubi.upgrade-command ~/bin/upgrade-musubi
```

This script needs cargo on the daemon's `PATH` and must install over the `musubi` executable
the daemon runs. Once configured, install the new release on the hub and restart it as described
[above](#upgrade-by-hand). The machines follow it automatically, including when a protocol
change prevents them from syncing until upgraded. Watch their releases in `musubi top`.

### Build a release from source

If you prefer to build from a local source clone made with `jj git clone`, use
[contrib/upgrade-from-source](../../contrib/upgrade-from-source). It builds the requested
release's `v<version>` tag in a separate copy, leaving your working copy and edits untouched.

Save the script as `~/bin/upgrade-from-source`, make it executable, and configure it on each
working machine, passing the path to that machine's source repo:

```sh
jj config set --user musubi.upgrade-command '~/bin/upgrade-from-source ~/dev/jj-musubi'
```

The script needs `jj`, `git` and `cargo` on the daemon's `PATH`, and fetches missing tags from
the source repo's remotes. It installs into Cargo's bin directory, normally `~/.cargo/bin`.
If your executable is elsewhere, put `CARGO_INSTALL_ROOT=/installation/root` before the
script path in the configured command. Cargo installs into that root's `bin` directory;
it must replace the executable the daemon runs.

To install a release by hand, replace `<target-version>` below with its version:

```sh
MUSUBI_UPGRADE_TO='<target-version>' ~/bin/upgrade-from-source ~/dev/jj-musubi
```

## If an upgrade fails

The daemon keeps running if its installer fails or installs the wrong version. Run
`musubi status` on that machine for the locally recorded failure and daemon log's location.
If the failure isn't shown, check that log. The installer's own output is in `upgrade.log`
in the [state directory](../reference/configuration.md#files-and-directories).
Fix the installer, then run `musubi daemon restart` to retry.

You can also run the installer by hand with `MUSUBI_UPGRADE_TO` set to the requested release,
then restart the daemon. For a missing release tag, check that the source clone fetches from
a remote that has it. Automatic upgrades only follow newer releases; install an older release
by hand if you need to go back.

## Writing your own installer

The installer must replace the executable the daemon started from with the release named by
`MUSUBI_UPGRADE_TO`. The daemon checks that this executable's `musubi --version` reports the
requested version before restarting. If you change the executable's path, run
`musubi daemon install` again.

The command runs through `sh -c` (`cmd /C` on Windows), in the state directory, without a
terminal. It inherits the daemon's environment; under launchd or systemd, its `PATH` is the
one seen by `musubi daemon install`. Output goes to `upgrade.log`. The daemon attempts the
command once for each newer release; restart the daemon to retry a failure.

Keep the installer in the foreground and preserve its standard input, which holds the Unix
upgrade lock. If the daemon restarts while the installer is running, the installer continues
and the new daemon waits for its lock. Leave `upgrade.lock` in place.

While the daemon that launched it is running, the installer has a one-hour timeout. On Unix,
a timeout stops its process group; on Windows, it stops only the command process. An installer
that outlives its daemon has no timeout monitor, so inspect `upgrade.log` and stop a stalled
installer before retrying. Do not detach installers or start them in the background.
