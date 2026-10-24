# Changelog

What changes in each release of musubi, and what to do on upgrading. Until 1.0, a release may
change the protocol, so run the same release on the hub and every machine (see
[Upgrading](README.md#upgrading)).

## Unreleased

- musubi completes its commands, flags, and hive and hub names in your shell, once you add a
  line to your shell's startup file, and `musubi completion <shell>` prints a completion
  script. See
  [Complete commands in your shell](docs/reference/commands.md#complete-commands-in-your-shell).
- `musubi hub rm` is now `musubi hub remove`, with `rm` still short for it, and takes a
  hive's whole name or its id, not a prefix. Each machine's copy of a removed hive now leaves
  it as it next syncs, keeping everything it has, rather than failing to sync until someone
  runs `musubi leave`.
- After a hub loses its state, `musubi join` in one copy of each hive makes it again, and the
  other machines fill it: no more `musubi leave` and `musubi create` on every machine.
  `musubi join --hub <hub>` in each copy moves a hive to another hub.
- `musubi top` watches what flows through the hubs as it happens: each hive's bytes a second
  in and out, the operations and commits that came in, and which machines are offline,
  behind, or failing to sync. Daemons now report to the hub after every sync for it. See
  [Watch every machine](docs/guides/manage.md#watch-every-machine).
- musubi has no config file of its own any more: its settings are jj's, under `musubi`, so
  `jj config list musubi` shows them. `[daemon] log` and `socket` in musubi's `config.toml`
  are now `musubi.daemon.log` and `musubi.daemon.socket` in jj's user config, where
  `musubi.hub` chooses another default hub than the one the first join saved. What musubi
  records for itself, the repositories the daemon serves and that saved hub, is now
  `state.toml` in its state directory. `MUSUBI_CONFIG_DIR` is now `MUSUBI_STATE_DIR`, which
  no longer separates a second musubi's settings: give it a `JJ_CONFIG` of its own too. On
  upgrading:

  1. Move the file. On Linux and macOS, unless you set `XDG_CONFIG_HOME` or
     `XDG_STATE_HOME`:

     ```sh
     mv ~/.config/musubi/config.toml ~/.local/state/musubi/state.toml
     ```

     On Windows, rename `%APPDATA%\musubi\config.toml` to `state.toml`. Where
     `MUSUBI_CONFIG_DIR` was set, rename `config.toml` in it to `state.toml`.
  2. Set again what you had under `[daemon]`, with `jj config set --user musubi.daemon.log`
     or `musubi.daemon.socket`.
  3. Restart the daemon: `musubi daemon install` if it starts at login, so that the service
     finds jj's config as your shell does, or else `musubi daemon restart`.

  See [Configuration](docs/reference/configuration.md#settings).
- The hub and machines talk differently, so upgrade the hub and every machine together.

## 0.1.0

The first release. musubi keeps a jj repository in sync across your machines by replicating
its operation log, through a hub on one machine that the others reach over ssh.

- `musubi hub` runs a hub, which serves any number of repositories, each its own hive.
- `musubi create` starts a hive from a repository, `musubi join` adds another machine's copy
  of it, and `musubi clone` makes a new copy.
- A daemon on each machine keeps its repositories in sync, and catches up after the machine
  was offline. `musubi daemon install` starts it at login, with launchd on macOS, systemd on
  Linux, or the registry on Windows.
- `musubi list` shows the hub's hives and how each copy's syncing goes, `musubi sync` syncs
  now, and `musubi leave` stops syncing a repository. `musubi hub rename` and `musubi hub rm`
  manage the hub's hives.
- musubi works with jj 0.46.0. It stops with an error rather than sync an operation that a
  newer `jj` wrote with fields jj 0.46.0 doesn't know.
- Builds for Linux (static, x86_64 and aarch64), macOS (x86_64 and aarch64), and Windows
  (x86_64 and aarch64).
- Published on crates.io as `jj-musubi`.
