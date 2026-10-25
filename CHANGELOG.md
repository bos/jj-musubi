# Changelog

What changes in each release of musubi, and what to do on upgrading. Until 1.0, a release may
change the protocol, so run the same release on the hub and every machine (see
[Upgrading](README.md#upgrading)).

## Unreleased

- When jj can't merge this machine's operations with the hive's (as when rebases on two
  machines form a loop), the sync error names the one operation to revert, the first of this
  machine's that jj can't merge with the hive's, rather than listing every operation the hive
  doesn't have yet.
- `jj op restore` (or `jj undo`) back to an operation in which a remote bookmark was
  conflicted, as concurrent fetches on two machines leave one, no longer moves that remote
  bookmark and the bookmark tracking it backwards on every machine. Each machine resolves the
  conflict to the commit the remote bookmark had before the restore, where the machine that
  restored and the others used to resolve it differently, and the hive merged the two to an
  older commit, which a plain `git push` from a colocated repository could then push.
- On each machine, the daemon cleans up what `jj util gc` would, short of deleting git
  objects, so that a busy hive's copies stop growing with files jj no longer reads: replaced
  extras segments, keep refs beyond the heads, and operations nothing reachable needs, once
  two weeks old. It runs once enough has built up, at most once a week, and not on battery.
- The hub's store of each hive, and each machine's copy of the shared history
  (`.jj/repo/musubi/canonical`), are now one log, with views kept as deltas: an operation
  and its view take under a kilobyte, where they took two files and the view's full size.
  Stores made before aren't read. On upgrading, a hub makes each hive again, as for a
  corrupt store, and its machines fill it; a machine's copy made before can't sync, so make
  it again with `musubi clone`.
- A hive forgets a copy that has gone unused for longer than its `musubi.forget-after`, as
  `musubi forget` would, and shows it again once it's used. `musubi join`, `create` and
  `clone` set it, and say what they set: `6h` when an agent runs them (`CODEX_THREAD_ID`,
  `CODEX_SESSION_ID` or `CLAUDE_CODE_SESSION_ID` is set), `never` otherwise, unless jj's
  config sets it already. Copies that joined before have none, and are never forgotten
  until one is set: `jj config set --repo musubi.forget-after 6h`. `musubi list` shows each
  copy, when it was last used, and when it will be forgotten.
- `musubi leave` now takes the repository out of its hive: it records what changed in the
  working copy and tells the hive, with the copy's last work, so that the other machines
  stop showing its working copy and the hub stops counting it. It keeps its working copy. It
  fails if the hub can't be reached, where it used to leave without a word, which scripts
  that run it may need to allow for; `musubi leave --force` leaves without telling the hive.
- `musubi forget <machine>` forgets a machine that went away without leaving. The other
  machines stop showing its working copy, and the hub stops counting it. If it's still
  there, it comes back as soon as it's used. See
  [Take a repository or machine out](docs/guides/manage.md#take-a-repository-or-machine-out).
- Two machines that share a name are shown as `laptop-1a2b/default@` and
  `laptop-3c4d/default@` from then on, even after one leaves, so that a name never moves to
  another machine. On upgrading, a machine that shares its name with any machine its hive
  has had, even one long gone, is shown that way from then on, as `mac-2222/default@` where
  it was `mac/default@`.
- On upgrading, a copy in which no `jj` command has recorded an operation since it joined
  stops showing on the other machines until one does: earlier releases didn't record joining
  as the copy's own. Upgrade every machine together: a machine on an earlier release that
  another forgets loses its own working copy.
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
