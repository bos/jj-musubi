# Configuration

Most setups need no configuration: `musubi hub`, `create`, `join`, and `clone` write what
musubi needs. This page lists what you can set, and where musubi keeps its files.

## Settings

musubi's settings are jj's, under `musubi`; it has no config file of its own. See and change
them with `jj config`:

```sh
jj config list musubi
jj config set --user musubi.daemon.log 'info,musubi_sync=debug'
```

musubi loads jj's config files as `jj` does (system, user, repo, and workspace), so the
commits it makes when it merges concurrent work carry your identity, and are signed if you
sign commits.

### This machine's

musubi reads these as `jj` would outside any repository, so a repository's config doesn't
change them. Set them with `--user`.

| Key | Effect |
| --- | --- |
| `musubi.hub` | The hub commands use without `--hub`, in place of the default this machine saved (the first hub it used, or on the hub's own machine, that hub's directory). Give it as `--hub` takes it: the name you ssh to the hub's machine by, or on that machine, the hub's directory, which may start with `~/`. |
| `musubi.daemon.log` | What the daemon logs, unless `--log` or `RUST_LOG` says. See [Logging](#logging). |
| `musubi.daemon.socket` | The path of the daemon's control socket, in place of the usual one. See [Files and directories](#files-and-directories). |

The daemon reads `musubi.daemon.*` when it starts, so run `musubi daemon restart` after
changing them.

### Each repository's

musubi reads these as `jj` would in the repository, so any of jj's config files can set them.

| Key | Effect |
| --- | --- |
| `musubi.forget-after` | How long this copy may go unused before the hive forgets it: `never`, or a duration of at least a second, such as `30m`, `6h`, `1h 30m`, or `2 days`: numbers with units from `s`, `min` or `m`, `h` or `hours`, `d` or `days`, `w` or `weeks`, and so on (`M` is months, not minutes). `musubi create`, `join`, and `clone` set it unless jj's config sets it already: `6h` when a coding agent (Claude Code or Codex) runs them, `never` otherwise. Not shared across a hive. See [Take a repository or machine out](../guides/manage.md#take-a-repository-or-machine-out). |
| `musubi.shared-config` | A list of further repo config keys for the hive to share, such as `["aliases.l"]`. See [Share settings](../guides/working-across-machines.md#share-settings). |
| `musubi.share-credentials` | `true` to share the user and password an https remote URL may carry. Off by default; set it per machine. |
| `operation.hostname` | This machine's name in a hive, unless `--machine` gives another. |
| `git.executable-path` | The `git` musubi runs, as jj does. |
| `snapshot.auto-update-stale` | jj's own: `true` makes every `jj` command update a working copy that another machine made stale. |

A hive always shares these repo config keys, whatever `musubi.shared-config` says:
`revset-aliases."immutable_heads()"`, `revset-aliases."trunk()"`, `git.private-commits`, and
`musubi.shared-config` itself.

## Environment variables

| Variable | Effect |
| --- | --- |
| `RUST_LOG` | What a command logs, unless `--log` says. See [Logging](#logging). |
| `NO_COLOR` | No colour, unless `--color` or your config's `ui.color` asks for it, as for jj. See [Colours](#colours). |
| `MUSUBI_SSH` | The ssh program to run, in place of `ssh`. |
| `MUSUBI_SOCKET` | The daemon's control socket, in place of the usual one. Same as `--socket`. |
| `MUSUBI_STATE_DIR` | One directory for musubi's state and the daemon's socket, in place of the usual ones. With `JJ_CONFIG` for its settings, this runs a second, separate musubi. |
| `COMPLETE` | Set by your shell to have musubi complete what you type. See [Complete commands in your shell](commands.md#complete-commands-in-your-shell). |

On macOS and Linux, `musubi daemon install` passes your `PATH`, and any `MUSUBI_*`,
`JJ_CONFIG`, `XDG_CONFIG_HOME`, and `XDG_STATE_HOME` variables set when you run it, to the
service that starts the daemon: run it again after changing them. On Windows, the daemon
started at login gets the login's environment.

## Logging

The hub and the daemon log what they do, at `info`. Other commands log only warnings, since
they report what they did themselves.

- `musubi hub` logs to its terminal, or under systemd to the journal:
  `journalctl --user -u musubi-hub`.
- `musubi daemon`, run in the foreground, logs to its terminal.
- A daemon started in the background, by a command or at login, logs to `daemon.log` in
  musubi's state directory, starting the log afresh when it starts if it has passed 10 MiB.
  Under systemd, it logs to the journal instead: `journalctl --user -u musubi`.

Logs are in colour only on a terminal, and then as for the rest of what musubi prints (see
[Colours](#colours)). A log file never is, nor is anything else the hub or the daemon writes
to one.

To choose what a command logs, pass `--log` with a filter in [`RUST_LOG`'s syntax][filter],
or set `RUST_LOG`; `--log` wins:

```sh
musubi --log debug hub
musubi --log musubi_sync=debug sync   # each request a sync makes, without a daemon
```

When a daemon serves the repository, `musubi sync` asks it to sync, so the requests are the
daemon's to log. To watch them, run the daemon in the foreground: `musubi daemon stop`, then
`musubi --log musubi_sync=debug daemon`.

A daemon started for you isn't given `--log`: set `musubi.daemon.log` and run `musubi daemon
restart`. One started by another command itself, rather than through launchd or systemd,
inherits that command's `RUST_LOG`, which then takes the setting's place.

[filter]: https://docs.rs/tracing-subscriber/latest/tracing_subscriber/filter/struct.EnvFilter.html#directives

## Colours

musubi prints as jj does, through jj's own formatting, reading jj's config for it as `jj`
does outside any repository: the system's and yours, not a repository's.
`--color` (`always`, `never`, `debug`, or `auto`) or else jj's `ui.color` says when to colour
what it prints: by default, `auto`, only on a terminal, and `never` if `NO_COLOR` is set and your
config doesn't set `ui.color`. jj's `colors` table says how, by label; `--color=debug` shows
each label. Besides jj's own labels, such as `commit_id`, `working_copies`, `warning`, and
`hint`, musubi gives these:

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

### On every machine

| Path | Holds |
| --- | --- |
| State directory: `~/.local/state/musubi` (`$XDG_STATE_HOME/musubi`; `%APPDATA%\musubi` on Windows) | `state.toml`, which lists the repositories the daemon serves and this machine's default hub; `daemon.log`; `hub_key`, the machine's ssh key for reaching hubs; `ssh-agent`, a link to the latest ssh agent, for the daemon; locks. |
| `.jj/repo/musubi/` in each repository | The repository's hive (`hive.toml`), this machine's identity in it (`machine`), its last sync (`status.json`), when the daemon last cleaned up after jj in it (`gc`, and `gc.lock` while it does), and musubi's own record of the hive's operations. Removing it, or copying it into another repository, confuses musubi: use `musubi leave` and `musubi clone`. |

The daemon's control socket is `$XDG_RUNTIME_DIR/musubi/daemon.sock` on Linux (without
`XDG_RUNTIME_DIR`, `musubi-<uid>/daemon.sock` in `$TMPDIR` or `/tmp`),
`$TMPDIR/musubi/daemon.sock` on macOS, and the named pipe `\\.\pipe\musubi-<user>` on Windows. Its
directory must belong to you and be writable by no one else, or musubi won't use it. `--socket`,
`MUSUBI_SOCKET`, or `musubi.daemon.socket` choose another.

### On the hub's machine

The hub's directory, `musubi-hub` by default, holds:

| Path | Holds |
| --- | --- |
| `hub.toml` | The hub's settings: the name `--advertise` gave it. |
| `<hive id>/` | One directory per hive: its name, in `hive.toml`, and its operations and objects. |
| `removed/` | Hives that `musubi hub remove` removed, each emptied a day later and kept, empty, as the record that it was removed. Also, for a day or so, stores the hub found corrupt and made again. |
| `run/hub.sock` | The socket the hub listens on, which only you can reach. |

Nothing in the hub's directory needs backing up: every machine keeps what it synced, so losing
the directory loses no work. See
[Replace or move a hub](../guides/manage.md#replace-or-move-a-hub).
