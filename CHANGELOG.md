# Changelog

What changes in each release of musubi, and what to do on upgrading. Until 1.0, a release may
change the protocol, so run the same release on the hub and every machine (see
[Upgrading](README.md#upgrading)).

## Unreleased

- On a terminal, `musubi create`, `join`, `clone` and `sync` show what the sync they wait on
  is doing: bytes sent or received, with a bar, commits being imported, operations applied,
  or waiting on the hub. They no longer print `Syncing...`. After upgrading, run `musubi
  daemon restart`: commands refuse a daemon from the release before.
- `create`, `join` and `clone` no longer print `Synced with the hub (hive at #N)`, nor `sync`
  `Synced (hive at #N)`, nor `musubi status` the hive's operation number: it meant nothing to
  anyone but musubi. A sync that worked prints nothing.
- When no hub serves a hub's directory, the error says so in a line, with `musubi hub` on a
  hint line of its own; `musubi list` and `musubi leave` no longer repeat it inside their own
  messages, and `leave`'s hint, `musubi leave --force`, is on a line of its own too.
- A machine shows another machine that shares its name as `laptop-1a2b`, as the hub's list
  does, where it used to show it as `laptop`.
- A `jj` command that was already running when a repository joined its hive, or one run with
  `--at-op` at an operation from before it joined, no longer sends the repository's history
  from before the join to the hive. Its work syncs once jj merges it with the history since.
- Two machines are never shown under one name, as `laptop-1a2b/default@` could show two
  machines named `laptop` whose ids start alike, and another machine's working copy never
  shows under the name of a workspace of this machine's own. Where `laptop-1a2b` is taken, a
  machine shows under its whole id, `laptop-1a2b3c4d`.
- On the hub's machine, `--hub localhost`, or the machine's name as `musubi hub` prints it,
  now reaches the hub `musubi hub` serves there without `--dir` through its directory rather
  than over ssh, and so does such a name in `musubi.hub` or saved as the default hub. A copy
  there that joined by such a name goes on using ssh; run `musubi join --hub localhost` in it
  to stop.
- Without `--dir`, `musubi hub` serves `~/musubi-hub`, where it served `musubi-hub` in the
  current directory, unless that is a hub's. To go on serving a hub kept elsewhere, run
  `musubi hub` in its directory, or pass `--dir`, or move it to `~/musubi-hub`.
- `musubi hub install` runs the hub at login, with launchd on macOS and systemd on Linux, as
  `musubi daemon install` does the daemon; `musubi hub uninstall` stops it. A hub you set up
  as a systemd unit of your own, as the guide used to say, can go: stop and disable it, then
  run `musubi hub install` in the hub's directory, or with `--dir`. See
  [Keep the hub running](docs/guides/setup.md#keep-the-hub-running).
- Added `skills/musubi` to help coding agents work in a hive.
  See [Coding agents](docs/guides/working-across-machines.md#coding-agents).
- musubi tells a copy from a repository made by copying its files, with `cp -a`, `rsync` or a
  backup, and doesn't sync the duplicate, where two repositories synced as one machine and
  overwrote each other's working copy. `musubi join --original` syncs a repository as the
  copy it was made from, once that is gone, as after restoring a backup onto a new machine.
  See [Move, copy or restore a repository](docs/guides/manage.md#move-copy-or-restore-a-repository).
- The daemon follows a copy moved with `mv`, once jj runs in it. It stops syncing a copy that
  is deleted or missing, or whose directory comes to hold another repository, writing
  nothing there, where it retried forever and wrote into whatever it found; a directory
  swapped for a copy of another hive could put each hive's work in the other. `musubi list`
  lists such copies, and `musubi leave <path>` stops syncing one. The daemon no longer keeps
  the directory it was started in, whose deletion stopped every repository on the machine
  syncing.
- A copy whose hive was removed remembers it: a plain `musubi join` says so, where it could
  join another hive whose history matched. `hive.toml` is kept, recording whether the copy
  joined, left, or its hive was removed.
- A copy that joins or starts a hive other than the one its history came from forgets the
  other copies that history brings, which the new hive used to list as members.
- musubi refuses to run in a repository another user owns, as under `sudo`, which left files
  the owner couldn't read.
- `musubi status` is a command of its own, no longer another name for `musubi list`. It shows
  what musubi does with the repository you're in: its hive, hub and machine name, its last
  sync, whether the hub has this machine's latest work, every machine's working copies, each
  copy in the hive, and the daemon's process, socket and log. It warns of what keeps the
  repository from syncing, saying what to do, and never starts the daemon or asks the hub, so
  scripts, agents and shell prompts can run it. `musubi list` no longer shows the current
  repository's details: run `musubi status` for them.
- Each machine picks up a renamed hive's new name as its daemon next syncs, rather than only
  once `musubi list` runs there. The hub answers a daemon's report of a sync with the hive's
  details, so a hub and machines must be upgraded together.
- `musubi sync`, `musubi leave` and `musubi join`, run in another workspace of a repository
  than the one it joined from, act on the repository the daemon serves: `sync` goes through
  the daemon rather than syncing alongside it, `leave` stops the daemon serving it, and `join`
  no longer has the daemon serve it twice.
- musubi prints through jj's own formatting: it colours what it prints as jj's `ui.color` and
  `colors` config say, and takes jj's `--color` flag (see
  [Colours](docs/reference/configuration.md#colours)); errors, warnings and hints read as
  jj's do, with hints and warnings on stderr. Logs are coloured only on a terminal, so
  `daemon.log`, and a hub's log written to a file, no longer hold colour codes.
- `musubi list` prints its hubs, hives and copies through a template in jj's template
  language, `musubi.templates.list` in jj's config, or one `-T` gives, as jj's list commands
  do; `-T 'json(self) ++ "\n"'` gives them as JSON. A hub with no hives no longer says so.
- `musubi status -T` prints its report through a template in jj's template language, and
  `musubi status -T 'json(self) ++ "\n"'` as JSON, for scripts and agents (see [`musubi status` as
  JSON](docs/reference/commands.md#musubi-status-as-json)).
- A command whose output stops being read, as in `musubi list | head`, no longer panics: it
  does all it would, printing nothing more there, and exits with status 3, as jj does then.
- `musubi sync` warns when it syncs in its own process because the daemon isn't running.
- When jj can't merge this machine's operations with the hive's (as when rebases on two
  machines form a loop), the sync error names the operation to revert, rather than listing
  every operation the hive doesn't have yet.
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
- Adding musubi's ssh key on the hub's machine no longer joins it to the last line of an
  `~/.ssh/authorized_keys` that doesn't end in a newline, which spoiled both keys and could
  lock you out of that machine.
- The daemon keeps one connection to each hub, shared by every repository it serves there,
  where it kept one, and an ssh, for each: a machine with two dozen repositories on a hub ran
  two dozen ssh processes, and the hub's machine as many `musubi hub connect`. It opens
  another for each transfer of 16 MiB or more, while it lasts; `musubi.daemon.connections =
  "one"` keeps it to one connection to each hub, as where each new ssh is costly (see
  [Configuration](docs/reference/configuration.md#this-machines)).
- When `jj op abandon` pauses syncing, the error says how to carry on, and `musubi status` says
  that retrying won't help, where it said that the daemon keeps trying.
- `musubi clone` checks out the hive's trunk, as `jj git clone` checks out a remote's
  default branch, where it left the new copy's working copy on the root commit, with no files.
- A daemon started at login on macOS, by `musubi daemon install`, no longer fails every sync
  with "Too many open files" once it serves some two dozen repositories: the daemon and the
  hub raise their limit on open files as far as the system allows, from launchd's 256.
- The daemon and the hub log only warnings from jj's library, whose notes on every lock it
  took and index it built made up most of `daemon.log`. `--log info` brings them back, as
  does `musubi.daemon.log = "info"` for the daemon.
- The hub and machines talk differently, so upgrade the hub and every machine together.
- On upgrading: `hive.toml` and `state.toml` have changed, and the daemon serves nothing
  until each copy joins again. On each machine, run `musubi daemon restart`, then in each
  copy delete `.jj/repo/musubi/hive.toml` and run `musubi join`.

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
