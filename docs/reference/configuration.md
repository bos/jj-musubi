# Configuration

Most setups need no configuration: `musubi hub`, `create`, `join`, and `clone` write what
musubi needs. This page lists what you can set, and where musubi keeps its files.

## Settings

musubi has no config file of its own: its settings are jj's, under `musubi`, and you see and
change them with `jj config` as you would any of jj's.

```sh
jj config list musubi
jj config set --user musubi.daemon.log 'info,musubi_sync=debug'
```

musubi loads jj's config as `jj` does, system, user, repo and workspace, so the commits it
makes when it merges concurrent work carry your identity and are signed if you sign commits.

### This machine's

These are the machine's, not a repository's, so musubi reads them as `jj` would outside any
repository, and a repository's config doesn't change them: set them with `--user`.

| Key | Effect |
| --- | --- |
| `musubi.hub` | The hub that commands use when not given `--hub`, in place of the one this machine saved: the first it used, or on the hub's own machine, that hub's directory. Give it as `--hub` takes it: the name you ssh to the hub's machine by, or on that machine, the hub's directory, which may start with `~/`. |
| `musubi.daemon.log` | What a daemon started in the background logs, as a filter in `RUST_LOG`'s syntax. See [Logging](#logging). |
| `musubi.daemon.socket` | The path of the daemon's control socket, in place of the usual one. See [Files and directories](#files-and-directories). |

The daemon reads `musubi.daemon` when it starts, so restart it (`musubi daemon restart`)
after changing it.

### Each repository's

musubi reads these as `jj` would in the repository, so any of jj's config files can set them.

| Key | Effect |
| --- | --- |
| `musubi.forget-after` | How long this copy may go unused before the hive forgets it: `never`, or a duration such as `6h`, `1h 30m` or `2 days`: numbers with units from `s`, `min` or `m`, `h` or `hours`, `d` or `days`, `w` or `weeks`, and so on, at least a second. `M` is months, not minutes. `musubi join`, `create` and `clone` set it, unless jj's config sets it already: `6h` when an agent runs them, `never` otherwise. Never shared across a hive. See [Take a repository or machine out](../guides/manage.md#take-a-repository-or-machine-out). |
| `musubi.shared-config` | A list of more repo config keys for the hive to share, such as `["aliases.l"]`. It is shared itself. See [Share settings](../guides/working-across-machines.md#share-settings). |
| `musubi.share-credentials` | `true` to share the user and password an https remote URL may carry. Off by default; set it per machine. |
| `operation.hostname` | This machine's name in a hive, unless `--machine` gives another. |
| `git.executable-path` | The `git` musubi runs, as jj does. |
| `snapshot.auto-update-stale` | jj's own: `true` makes every `jj` command update a working copy that another machine made stale. |

These repo config keys are shared across a hive whatever `musubi.shared-config` says:
`revset-aliases."immutable_heads()"`, `revset-aliases."trunk()"`, `git.private-commits`, and
`musubi.shared-config` itself.

## Environment variables

| Variable | Effect |
| --- | --- |
| `RUST_LOG` | What a command logs, unless `--log` says. A daemon that a command starts itself, rather than through launchd or systemd, inherits it. |
| `MUSUBI_SSH` | The ssh program to run, in place of `ssh`. |
| `MUSUBI_SOCKET` | The daemon's control socket, in place of the usual one. Same as `--socket`. |
| `MUSUBI_STATE_DIR` | One directory for musubi's state and daemon socket, in place of the usual ones. Useful for running a second, separate musubi, as tests do, with `JJ_CONFIG` for its settings. |
| `COMPLETE` | Set by your shell to have musubi complete what you type. See [Complete commands in your shell](commands.md#complete-commands-in-your-shell). |

On macOS and Linux, `musubi daemon install` passes the `MUSUBI_*` variables, `JJ_CONFIG`,
`XDG_CONFIG_HOME`, and `XDG_STATE_HOME` set when you run it, and your `PATH`, to the service
that starts the daemon: run it again after changing them. On Windows, the daemon started at
login gets the login's environment.

## Logging

The hub and the daemon log what they do, at `info`. Other commands log only warnings, since
they say what they did themselves.

- `musubi hub` logs to its terminal.
- A daemon started in the background, by a command or at login, logs to `daemon.log` in
  musubi's state directory. When a daemon starts, it starts the log over if it has
  passed 10 MiB. Under systemd, it logs to the journal instead: `journalctl --user -u
  musubi`.
- `musubi daemon`, run in the foreground, logs to its terminal.

To choose what a command logs, pass `--log` with a filter in [`RUST_LOG`'s syntax][filter]:

```sh
musubi --log debug hub
musubi --log musubi_sync=debug sync   # each request a sync makes, without a daemon
```

`musubi sync` asks the daemon to sync, when one serves the repository, and then the
requests are the daemon's to log. To watch them, stop the daemon and run it in the
foreground: `musubi daemon stop`, then `musubi --log musubi_sync=debug daemon`.

Without `--log`, `RUST_LOG` does the same. A daemon started for you, at login or by another
command, isn't given `--log`: set `musubi.daemon.log` and run `musubi daemon restart`. A
daemon that another command starts itself, rather than through launchd or systemd, also
inherits that command's `RUST_LOG`, which takes the setting's place.

[filter]: https://docs.rs/tracing-subscriber/latest/tracing_subscriber/filter/struct.EnvFilter.html#directives

## Files and directories

### On every machine

| Path | Holds |
| --- | --- |
| State directory: `~/.local/state/musubi` (`%APPDATA%\musubi`) | `state.toml`, which lists the repositories the daemon serves, and the hub this machine saved as its default; `daemon.log`; `hub_key`, the machine's ssh key for reaching hubs; `ssh-agent`, a link to the latest ssh agent, for the daemon; locks. |
| `.jj/repo/musubi/` in each repository | The repository's membership (`hive.toml`), this machine's identity in it (`machine`), its last sync (`status.json`), and musubi's own record of the hive's operations. Removing it, or copying it into another repository, confuses musubi: use `musubi leave` and `musubi clone`. |

The daemon's control socket is `$XDG_RUNTIME_DIR/musubi/daemon.sock` on Linux,
`$TMPDIR/musubi/daemon.sock` on macOS, and the named pipe `\\.\pipe\musubi-<user>` on
Windows. Its directory must belong to you and be writable by no one else, or musubi won't use
it. `--socket`, `MUSUBI_SOCKET`, or `musubi.daemon.socket` choose another.

### On the hub's machine

The hub's directory, `musubi-hub` by default, holds:

| Path | Holds |
| --- | --- |
| `hub.toml` | The hub's settings: the name `--advertise` gave it. |
| `<hive id>/` | One directory per hive, with the hive's name in its `hive.toml`, and its operations and objects. |
| `removed/` | Hives that `musubi hub remove` removed, each emptied a day later and then kept, empty, as the record that it was removed; and stores the hub found corrupt and set aside. |
| `run/hub.sock` | The socket the hub listens on, which only you can reach. |

The hub only stitches together copies of repositories that exist anyway, so nothing in its
directory needs backing up: losing it loses no work. See
[Replace or move a hub](../guides/manage.md#replace-or-move-a-hub).
