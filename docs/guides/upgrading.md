# Upgrade jj-musubi

Choose the migration your existing state needs, then install the target release or build on
the hub and working machines. Read its [changelog](../../CHANGELOG.md) before replacing
processes; before 1.0, protocol changes can make different builds refuse to sync.

## Choose the migration

A new installation needs no migration; follow [setup](setup.md). For existing hives, the
unreleased changelog includes an operation-identity change and new hub metadata:

- If you have not recreated both hives and local jj-musubi state for the operation-identity
  change, [recreate both](#recreate-hives-and-local-state).
- If that reset is done but your hub predates the remote-name or clone-default metadata,
  [recreate only the hub state](#recreate-hub-state).
- If neither reset applies, [upgrade together](#upgrade-together), following any other
  instructions in the target build's changelog.

If you are unsure which resets you've already applied, use [Recreate hives and local
state](#recreate-hives-and-local-state). It preserves your jj repositories and their work,
archives the old jj-musubi state, and starts fresh hives.

Both reset procedures install the target build directly. No intermediate release is needed.
Your jj repos keep their work and local configuration.

Remove the obsolete `musubi.shared-config` and `musubi.share-credentials` settings if present.
To keep defaults for future clones, move the desired key selection from `musubi.shared-config`
to `musubi.clone-config` before recreating a hive. This now supplies clone defaults only;
configuration stays local.

### Recreate hives and local state

1. With the old build, sync every copy and note its [machine name](setup.md#name-machines)
   from `musubi status`. In each copy, run `musubi leave`, or `musubi leave --force` if its hub
   is gone, then stop the daemon with `musubi daemon stop`.
2. Back up every repo. Run `jj workspace list` in each copy, then
   `jj workspace forget <name>` for each workspace belonging to another machine. Keep this
   machine's own workspaces, including linked workspaces. A local name can contain `/`;
   `jj workspace root --name <name>` shows its recorded directory. Remove foreign workspace
   names before the next step so the new hive does not treat them as this machine's own.
3. Archive each repo's `musubi` directory (normally `.jj/repo/musubi`) outside the jj
   repo directory. It holds the old membership and operation-id records. For linked
   workspaces, archive the shared repo's directory once.
4. Stop the old hub and archive its directory. Install the target build on the hub and every
   machine, then start the hub with an empty directory, as in [setup](setup.md#start-the-hub).
5. In one preserved repo, run `musubi create --machine <machine>`. In each other copy,
   run `musubi join --machine <machine>`, using the names you noted. Joining starts its daemon.
   Share the present view; do not use `--full-history` to bring the old operation history into
   the new hive.
6. Check each copy with `musubi status` and the hub with `musubi top`. Restore services as in
   [setup](setup.md#keep-the-hub-running), keeping `--at-boot` when reinstalling a boot service.

The old operation history remains in the jj repos. Inspect work on every copy before
discarding archives. Before creating the hive, [choose clone defaults](setup.md#choose-clone-defaults)
if you want different ones. Remote names must identify the same fetch and push destinations;
[use distinct names for different destinations](working-across-machines.md#fetch-and-push).

### Recreate hub state

Use this route only when local state already has the new operation identities.

1. Stop the hub and every machine's daemon, then install the target build everywhere.
2. Archive the old default hub directory. Run `musubi hub` without `--dir` to create a fresh
   default directory, so ssh connections reach it.
3. Run `musubi join --hub <hub-host>` in each existing copy. The first copy recreating a hive
   supplies its [clone defaults](setup.md#choose-clone-defaults); set them before joining.
4. Check each copy with `musubi status` and the hub with `musubi top`. Restore services as in
   [setup](setup.md#keep-the-hub-running), keeping `--at-boot` for a boot service.

Local work and jj config remain intact. Before rejoining, give different destinations
[distinct remote names](working-across-machines.md#fetch-and-push).

## Upgrade together

If no reset is needed:

1. Install the same target build on the hub and each working machine.
2. Stop `musubi hub` and start it again, or reinstall its service with `musubi hub install`,
   keeping `--at-boot` if it starts at boot.
3. Run `musubi daemon restart` on each working machine. A new command may refuse an older
   daemon's control protocol until it restarts. If the executable path changed, run
   `musubi daemon install` again.
4. Check `musubi status` in the copies and `musubi top` for the hive.

## Automatic upgrades

Complete any required state migration above before relying on automatic upgrades.

To have machines upgrade with the hub, configure an installer:

```sh
jj config set --user musubi.upgrade-command ~/bin/upgrade-musubi
```

When the daemon reaches a newer hub, it runs the command once for that release, setting
`MUSUBI_UPGRADE_TO` to the release version or
[deployed build name](#deploy-a-build-from-source). It restarts once `musubi --version` at its
startup path reports the requested version. Sleeping machines upgrade when they reconnect.

After configuring installers, upgrade the hub as in [Upgrade together](#upgrade-together).
Machines with this setting follow it; install and restart other machines by hand.

The command runs through `sh -c` (`cmd /C` on Windows), in the state directory, without a
terminal and with the daemon's environment. Under launchd or systemd, that includes the
`PATH` seen by `musubi daemon install`. Output goes to `upgrade.log`.
Install the release or build named by `$MUSUBI_UPGRADE_TO` at the daemon's existing `musubi`
path. If the path changes, run `musubi daemon install` again.

Keep the installer in the foreground and preserve its standard input, which holds the Unix
upgrade lock. A restarted daemon leaves the installer running and waits for the lock before
trying again.

The command has a one-hour timeout while its daemon runs. On Unix, the timeout stops its
process group; on Windows, only the command process. Do not detach or start background
installers. A command that survives its daemon has no timeout monitor;
see [troubleshooting](../troubleshooting.md#upgrade-upgrading-to-musubi--failed-) if it stalls.

A script that builds jj-musubi with cargo:

```sh
#!/bin/sh
set -e
cargo install --locked --version "$MUSUBI_UPGRADE_TO" jj-musubi
```

For upgrades from a source repo made with `jj git clone`, copy
[contrib/upgrade-from-source](../../contrib/upgrade-from-source) into your
dotfiles and pass the repo:

```sh
jj config set --user musubi.upgrade-command '~/bin/upgrade-from-source ~/dev/jj-musubi'
```

The script builds a release's tag, named `v<version>`, or a deployed build's commit. It fetches
missing revisions and fails if it cannot find them. It builds a copy, leaving the source
repo and your edits untouched. It needs `jj`, `git` and `cargo` on the daemon's `PATH`.
Replace `<target-version>` with a release version to install it:

```sh
MUSUBI_UPGRADE_TO='<target-version>' ~/bin/upgrade-from-source ~/dev/jj-musubi
```

If installation fails or installs another release, the daemon keeps running and
`musubi status` says why. Fix the installer, then use `musubi daemon restart` to retry.

Only a newer release or later deployment starts the command. An undeployed source build,
such as `cargo install --path`, reports only its release and starts nothing. Nor does
putting the hub on an older release: install those versions by hand.

## Deploy a build from source

Deploy a build between releases from the hub machine with `upgrade-from-source --deploy`:

1. Push the revision where the machines' clones of the source fetch from, as by pushing
   `main`.
2. On the hub's machine, deploy it, `main` unless you name another revision. It fetches
   first, and refuses a revision that no remote has, which the machines couldn't fetch:

   ```sh
   ~/bin/upgrade-from-source --deploy ~/dev/jj-musubi main
   ```

   This installs it with `cargo install`, into `~/.cargo/bin` or `CARGO_INSTALL_ROOT`, which
   must be where the hub runs `musubi` from, as a build named for the release it follows (the
   `version` in its `Cargo.toml`), the time in UTC, and its commit, such as
   `musubi 0.3.0+20261102153012.4a0db205e1f0`. `musubi --version` prints that name.
3. Stop `musubi hub` and start it again, or reinstall its service with `musubi hub install`,
   keeping `--at-boot` if it starts at boot.

Machines using `upgrade-from-source` build that commit, fetching it if needed, even across
protocol changes. [`musubi top`](../reference/commands.md#read-musubi-top) shows each machine's build.
Other installers, such as the cargo example above, cannot install deployed builds; `musubi status`
reports this. If a machine tried before the commit was pushed, retry with
`musubi daemon restart` or another deployment.

Deployments following the same release are ordered by the deploying machine's clock, regardless
of commit order: redeploying an older revision takes machines back to it. A deployed build falls
between its release and the next, so a revision preceding the installed release starts no
upgrade.

