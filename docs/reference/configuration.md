# Configuration

Settings, environment variables, logging, and where jj-musubi keeps its files.

`musubi hub`, `create`, `join`, and `clone` write the configuration needed for setup.

## Settings

Settings live under `musubi` in jj's config files. Use `jj config`:

```sh
jj config list musubi
jj config set --user musubi.daemon.log 'info,musubi_sync=debug'
```

System, user, repository and workspace config apply as in `jj`. Merge commits use your identity
and signing settings.

The daemon reloads changes before each repo's next sync, including signing settings
and `musubi.forget-after`. An ongoing sync uses its previous settings; `musubi sync` waits
for one using the new settings.

### This machine's

These use jj's config outside repos, excluding repo and workspace settings. Set them
with `--user`.

| Key | Effect |
| --- | --- |
| `musubi.hub` | The hub to use without `--hub`, overriding the saved default: the first hub used, or the local hub's directory. Takes an ssh host name or, on the hub's machine, its directory (which may start with `~/`). That machine's own name or `localhost` reaches the hub served by `musubi hub` without `--dir`, without ssh. |
| `musubi.daemon.log` | What the daemon logs, unless `--log` or `RUST_LOG` says. See [Logging](#logging). |
| `musubi.daemon.socket` | Override the daemon's control socket with an absolute path or one starting with `~/`. See [Files and directories](#files-and-directories). |
| `musubi.daemon.connections` | `as-needed` (default): share one connection per hub across repos, adding a connection for each transfer of 16 MiB or more until it finishes. `one`: use one connection per hub even for large transfers, useful when each ssh connection is costly or asks you to log in. |
| `musubi.upgrade-command` | Installs the jj-musubi release or deployed build named by `$MUSUBI_UPGRADE_TO`. The daemon runs it on finding a newer hub, then restarts from the installed version. Unset by default: no automatic upgrades. See [Upgrade jj-musubi](../guides/upgrading.md) for installer requirements. |
| `musubi.templates.list` | The jj template for hubs, hives and copies in `musubi list`, unless overridden by `-T`. `musubi list --help` lists keywords. |

The daemon reads `musubi.daemon.*` when it starts, so run `musubi daemon restart` after
changing them.

### Each repo's

Any jj config level can set these for the repo.

| Key | Effect |
| --- | --- |
| `musubi.forget-after` | Inactivity before forgetting this copy: `never`, or at least a second, such as `30m`, `6h`, `1h 30m`, or `2 days`. Units include `s`, `min` or `m`, `h` or `hours`, `d` or `days`, `w` or `weeks` (`M` means months). `musubi create`, `join`, and `clone` keep any configured value, otherwise set `never`, whether run by a person or agent. `--lease 6h` replaces this copy's repo value. The setting stays local. See [Take a repo or machine out](../guides/manage.md#take-a-repo-or-machine-out). |
| `musubi.publication.max-files` | Maximum distinct extra file paths across all outgoing snapshots: `100` by default, including current uncommitted work and older snapshots. Explicit change history and already shared content are exempt. `0` disables this limit. Sending pauses above either publication limit; receiving continues. See [snapshot cleanup](../guides/snapshots.md). |
| `musubi.publication.max-bytes` | Maximum extra content bytes retained by outgoing snapshots: `8 MiB` by default. Accepts jj byte sizes such as `16 MiB`, or a number of bytes. Identical content is counted once across paths and snapshots. `0` disables this limit. |
| `musubi.clone-config` | Keys whose effective values are recorded at hive creation or recreation after hub loss as defaults for future clones. Default: `["user.name", "user.email"]`; `[]` records none. Clone writes those values to its repo config only if absent from the destination's explicit config; built-in jj defaults do not count. Existing values win. Later edits and joins do not update the recorded defaults. `musubi.forget-after` cannot be selected. |
| `operation.hostname` | This machine's name in a hive, unless `--machine` gives another. |
| `git.executable-path` | The `git` jj-musubi runs, as jj does. |
| `snapshot.auto-update-stale` | jj's own: `true` makes every `jj` command update a working copy that another machine made stale. |

jj config stays local, including `trunk()`, `immutable_heads()`, `git.private-commits`, and
signing settings. Set protections on each copy that needs them; see
[Configure each machine](../guides/working-across-machines.md#configure-each-machine).

## Environment variables

| Variable | Effect |
| --- | --- |
| `RUST_LOG` | What a command logs, unless `--log` says. See [Logging](#logging). |
| `NO_COLOR` | Disable colour unless `--color` or `ui.color` requests it. See [Colours](#colours). |
| `MUSUBI_SSH` | Run this ssh program instead of `ssh`. |
| `MUSUBI_SOCKET` | Override the daemon's control socket with an absolute path or one starting with `~/`. Same as `--socket`. |
| `MUSUBI_STATE_DIR` | Overrides the state and daemon socket directories. Use with `JJ_CONFIG` to run a separate instance of `musubi`. If creating the directory yourself, make it writable by you alone (`chmod 700`). |
| `MUSUBI_UPGRADE_TO` | The daemon sets this for `musubi.upgrade-command`: the release or build to install, as printed by `musubi --version`, such as `0.3.0` or `0.3.0+20261102153012.4a0db205e1f0`. |
| `MUSUBI_BUILD` | A build-time variable for builds deployed from source. `contrib/upgrade-from-source` sets it to the deployment time and commit, such as `20261102153012.4a0db205e1f0`. It follows the release in `musubi --version`. See [Deploy a build from source](../guides/upgrading.md#deploy-a-build-from-source). |
| `COMPLETE` | Set by your shell to have `musubi` complete what you type. See [Complete commands in your shell](commands.md#complete-commands-in-your-shell). |

On macOS and Linux, `musubi daemon install` and `musubi hub install` pass their `PATH`,
`MUSUBI_*`, `JJ_CONFIG`, `XDG_CONFIG_HOME`, and `XDG_STATE_HOME` to the service. Run the install
command again after changing them. On Windows, the login daemon gets the login's environment.

## SSH

Each machine keeps `hub_key` and `hub_key.pub` in its
[state directory](#on-every-machine). On Linux and macOS this is `~/.local/state/musubi` unless
overridden. The public key's entry on each hub is restricted to its connection command:

```text
restrict,command="musubi hub connect" ssh-ed25519 AAAA... musubi@laptop
```

Concurrent joins reuse the same completed key pair; each hub may ask you to authorize it.
The daemon uses this key without prompting. It needs an ssh agent only for a `ProxyJump` host,
or to sign commits with a key the agent holds. On Unix, a daemon started by a command uses the
latest responsive agent supplied by a `musubi` command. Commands inheriting that agent keep
using it, including through symbolic links.

If changing the hub's non-interactive `PATH` isn't practical, use the executable's absolute
path in its `~/.ssh/authorized_keys` entry:
`command="/opt/musubi/bin/musubi hub connect"`.
For a hub serving another directory, add `--dir <dir>` to that command.

For key-file errors, see
[key repair](../troubleshooting.md#ssh-keygen-could-not-derive-the-missing-public-key).

## Logging

The hub and daemon log at `info`, with only warnings from jj's crates (`jj_lib`, `jj_local_util`
and others). Other commands log only warnings.

- `musubi hub` logs to its terminal; installed by `musubi hub install`, to `hub.log` in the
  state directory on macOS. On Linux, use `journalctl --user -u musubi-hub` for login startup,
  or `sudo journalctl -u musubi-hub-$(id -u).service` for boot startup.
- `musubi daemon`, run in the foreground, logs to its terminal.
- A background daemon logs to `daemon.log` in the state directory, or under systemd to
  `journalctl --user -u musubi`.

The file logs start afresh on startup if larger than 10 MiB.

Terminal logs follow the [colour settings](#colours). The hub and daemon write their logs and
command output to files without colour codes.

Choose a filter with `--log` or `RUST_LOG`, using [`RUST_LOG`'s syntax][filter]; `--log` wins:

```sh
musubi --log debug hub
musubi --log musubi_sync=debug sync   # each request a sync makes, without a daemon
```

To watch a serving daemon's requests, run `musubi daemon stop`, then
`musubi --log musubi_sync=debug daemon`.

A daemon started for you uses `musubi.daemon.log`: set it and run `musubi daemon restart`.
If another command starts the daemon directly, it inherits that command's `RUST_LOG`, which
overrides the setting. Daemons started through launchd or systemd use the service's environment.

[filter]: https://docs.rs/tracing-subscriber/latest/tracing_subscriber/filter/struct.EnvFilter.html#directives

## Colours

jj-musubi reads colour settings from jj's system and user config. `--color` (`always`, `never`,
`debug`, or `auto`) overrides `ui.color`. The default is `auto` (terminals only), or `never`
when `NO_COLOR` is set without a configured `ui.color`. jj's `colors` table styles each label;
`--color=debug` shows them. Besides jj's labels (`commit_id`, `working_copies`, `warning`,
`hint`), jj-musubi adds:

| Label | Text | Default |
| --- | --- | --- |
| `heading` | a heading, such as `musubi list`'s `This repository:` | bold |
| `hive` | a hive's name | bold |
| `machine` | a machine's name | green |
| `problem` | what's wrong, such as a sync that fails | red |

```sh
jj config set --user 'colors.machine' yellow
```

## Files and directories

To remove jj-musubi's files from a machine, see [Take a repo or
machine out](../guides/manage.md#take-a-repo-or-machine-out).

### On every machine

| Path | Holds |
| --- | --- |
| The state directory: `$XDG_STATE_HOME/musubi`, so `~/.local/state/musubi` on Linux and macOS unless you set `XDG_STATE_HOME`; `%APPDATA%\musubi` on Windows; or `$MUSUBI_STATE_DIR` | `state.toml`: copies the daemon syncs, their machine keys and paths, and the default hub. `daemon.log`: daemon log. `hub_key` and `hub_key.pub`: ssh key for reaching hubs. `ssh-agent`: link to the latest agent for the daemon. `upgrade.log` and `upgrade-failed`: last upgrade command's output and failure. `login-service`: present while `musubi daemon install` enables login startup. On the hub's machine, `hub.path`: directory served without `--dir`; `hub.log`: launchd hub log; `hub-login-service`: records whether `musubi hub install` enables login or boot startup. `daemon.pid`: daemon process id and socket. `daemon.lock`: prevents a second daemon serving the copies; other locks coordinate updates. The directory is readable and writable by you alone. |
| `.jj/repo/musubi/` in each repo | `hive.toml`: hive, jj config id and membership (joined, left or hive removed). `machine`: this copy's identity. `status.json`: last sync. `gc` and `gc.lock`: last jj cleanup and its lock. `hive.lock` and `join.lock`: membership locks. `publication.lock`: publication lock. `publication-approval`: approval for inspected outgoing history. `publication-offers.json`: attempted publications. Also holds the hive's operation records and those `jj op abandon` removed. `musubi leave` marks the copy left in `hive.toml`, removes `status.json`, and keeps the rest. Do not delete these files from a syncing copy or copy them to another repo; use `musubi leave` and `musubi clone`. |
| Each repo's jj repo config | Explicit `musubi join`, `create` and `clone` commands set a default `musubi.forget-after` unless jj's config sets it already. Clone also fills missing defaults once. Sync never copies Git remote definitions or jj config from another machine. jj keeps repo config outside the repo; `jj config path --repo` prints where. |
| What `musubi daemon install` adds | On macOS, `~/Library/LaunchAgents/io.github.bos.musubi.plist`; on Linux, `~/.config/systemd/user/musubi.service` (in `$XDG_CONFIG_HOME` if set); on Windows, the value `musubi` under `HKCU\Software\Microsoft\Windows\CurrentVersion\Run`. `musubi daemon uninstall` removes it. |
| What `musubi hub install` adds | On macOS, `~/Library/LaunchAgents/io.github.bos.musubi.hub.plist`; on Linux, `~/.config/systemd/user/musubi-hub.service` (in `$XDG_CONFIG_HOME` if set). With `--at-boot`, `/Library/LaunchDaemons/io.github.bos.musubi.hub.<uid>.plist` on macOS, or `/etc/systemd/system/musubi-hub-<uid>.service` on Linux, owned by root and running the hub as the installing user. `musubi hub uninstall` removes either kind. |

The default daemon control socket is:

- Linux: `$XDG_RUNTIME_DIR/musubi/daemon.sock`; without `XDG_RUNTIME_DIR`,
  `musubi-<uid>/daemon.sock` in `$TMPDIR` or `/tmp`.
- macOS: `$TMPDIR/musubi/daemon.sock`.
- Windows: the named pipe `\\.\pipe\musubi-<user>`.

With `MUSUBI_STATE_DIR`, it is `daemon.sock` in that directory (a pipe named after it on
Windows). The directory must belong to you and be writable by no one else. Override the socket
with `--socket`, `MUSUBI_SOCKET`, or `musubi.daemon.socket`, using an absolute path or one
starting with `~/`.

Commands without a socket override use the running daemon's socket, even under cron, after
`sudo -u`, or with a different `XDG_RUNTIME_DIR`. A second daemon cannot serve the same state
directory. If a temp cleaner deletes the socket, the daemon restores it within seconds.

### On the hub's machine

The hub's directory, `~/musubi-hub` by default, holds:

| Path | Holds |
| --- | --- |
| `hub.toml` | The hub's settings: the name `--advertise` gave it. |
| `<hive id>/` | One directory per hive: its name, in `hive.toml`, and its operations and objects. |
| `removed/` | Hives removed by `musubi hub remove`, emptied after a day; the empty directories prevent their recreation. Also holds corrupt stores for about a day after the hub replaces them. |
| `run/hub.sock` | The socket the hub listens on, which only you can reach. |
| `hub.lock` | A lock that keeps a second hub from serving the directory. |

Outside it, each machine that reaches the hub over ssh adds a line to
`~/.ssh/authorized_keys`, ending in `musubi@<host>`, that lets its `hub_key` run only
`musubi hub connect`. See [SSH configuration](#ssh).

The hub's directory can be rebuilt from surviving repo copies and the work they retained.
Keep your usual backups of working repos, including any on the hub's machine. See
[Replace or move a hub](../guides/manage.md#replace-or-move-a-hub).
