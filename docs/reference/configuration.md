# Configuration

Most setups need no configuration: `musubi hub`, `create`, `join`, and `clone` write what
musubi needs. This page lists what you can set, and where musubi keeps its files.

## musubi's config file

musubi keeps its own settings in `config.toml` in its config directory:
`~/.config/musubi/config.toml` on Linux and macOS (or under `$XDG_CONFIG_HOME`), and
`%APPDATA%\musubi\config.toml` on Windows, beside jj's own config.

```toml
hub = "devbox"
repos = ["/home/you/src/app", "/home/you/src/dotfiles"]

[daemon]
log = "info,musubi_sync=debug"
```

- `hub` is the hub that commands use when not given `--hub`: the first one this machine used,
  or on the hub's own machine, that hub's directory. Change it to make another hub the
  default.
- `repos` lists the repositories the daemon serves. `create`, `join`, `clone`, and `leave`
  change it; you needn't.
- `[daemon] log` is what a daemon started in the background logs, as a filter in `RUST_LOG`'s
  syntax. See [Logging](#logging).
- `[daemon] socket` is the path of the daemon's control socket, in place of the usual one.
  See [Files and directories](#files-and-directories).

The daemon reads the file when it starts, so restart it (`musubi daemon restart`) after
editing `[daemon]`.

## jj config that musubi reads

musubi loads jj's config as `jj` does, user, repo and workspace, so the commits it makes when
it merges concurrent work carry your identity and are signed if you sign commits.

| Key | Effect |
| --- | --- |
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
| `MUSUBI_CONFIG_DIR` | One directory for musubi's config, state, and daemon socket, in place of the usual ones. Useful for running a second, separate musubi, as tests do. |
| `COMPLETE` | Set by your shell to have musubi complete what you type. See [Complete commands in your shell](commands.md#complete-commands-in-your-shell). |

On macOS and Linux, `musubi daemon install` passes the `MUSUBI_*` variables set when you run
it, and your `PATH`, to the service that starts the daemon. On Windows, the daemon started at
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
command, isn't given `--log`: set `log` under `[daemon]` in `config.toml` and run
`musubi daemon restart`. A daemon that another command starts itself, rather than through
launchd or systemd, also inherits that command's `RUST_LOG`, which takes the config's place.

[filter]: https://docs.rs/tracing-subscriber/latest/tracing_subscriber/filter/struct.EnvFilter.html#directives

## Files and directories

### On every machine

| Path | Holds |
| --- | --- |
| Config directory: `~/.config/musubi` (`%APPDATA%\musubi`) | `config.toml`. |
| State directory: `~/.local/state/musubi` (`%APPDATA%\musubi`, beside `config.toml`) | `daemon.log`; `hub_key`, the machine's ssh key for reaching hubs; `ssh-agent`, a link to the latest ssh agent, for the daemon; locks. |
| `.jj/repo/musubi/` in each repository | The repository's membership (`hive.toml`), this machine's identity in it (`machine`), its last sync (`status.json`), and musubi's own record of the hive's operations. Removing it, or copying it into another repository, confuses musubi: use `musubi leave` and `musubi clone`. |

The daemon's control socket is `$XDG_RUNTIME_DIR/musubi/daemon.sock` on Linux,
`$TMPDIR/musubi/daemon.sock` on macOS, and the named pipe `\\.\pipe\musubi-<user>` on
Windows. Its directory must belong to you and be writable by no one else, or musubi won't use
it. `--socket`, `MUSUBI_SOCKET`, or `socket` under `[daemon]` choose another.

### On the hub's machine

The hub's directory, `musubi-hub` by default, holds:

| Path | Holds |
| --- | --- |
| `hub.toml` | The hub's settings: the name `--advertise` gave it. |
| `<hive id>/` | One directory per hive, with the hive's name in its `hive.toml`, and its operations and objects. |
| `removed/` | Hives that `musubi hub rm` removed, and stores the hub found corrupt and set aside. |
| `run/hub.sock` | The socket the hub listens on, which only you can reach. |

The hub only stitches together copies of repositories that exist anyway, so nothing in its
directory needs backing up: losing it loses no work. See
[Replace or move a hub](../guides/manage.md#replace-or-move-a-hub).
