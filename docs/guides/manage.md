# Manage hives, machines, and hubs

This guide covers the changes you make now and then: checking on syncing, renaming and
removing hives, taking a machine out, upgrading musubi, and replacing a hub.

## Check on syncing

`musubi list` (or just `musubi`) shows every hub this machine knows, the hives on each, which
machines have copies, and how each copy on this machine is syncing:

```text
Hub devbox:
  app  2 machines: desktop, laptop
    here: /home/you/src/app  synced 4s ago
  dotfiles  1 machine: desktop
    here: /home/you/dotfiles  synced 12s ago
Daemon: running, serving 2 repositories; starts at login
```

`musubi status`, run in a hive's repository, shows that repository's hive, hub and machine
name, where each machine's working copy is, and whether the hub has this machine's latest
work.

### Watch every machine

`musubi list` knows only this machine's copies. `musubi top` asks the hubs, which hear from
every machine's daemon after each sync, and refreshes every five seconds:

```text
musubi top: 1 hub, every 5s
This machine's daemon is running, serving 2 repositories.
Hub devbox: up 3h12m, musubi 0.1.0, 2 hives.
Issues:
  app: desktop not heard from in 6m: offline, or its daemon isn't running

HIVE      HEAD  IN/s     OUT/s    OPS  COMMITS  MACHINES  ISSUES
app       #412  12 KiB/s 40 KiB/s 96   51       2/3       1
dotfiles  #88   0 B/s    0 B/s    3    1        1/1

app since the hub started:
  received 4.1 MiB and sent 12 MiB
  96 operations came in, with 51 commits, and 180 went out
  40 pushes moved the head, and 2 found it moved already
  MACHINE  HEARD   AT    MUSUBI  STATE
  desktop  6m ago  #401  0.1.0   not heard from in 6m: offline, or its daemon isn't running
  devbox   3s ago  #412  0.1.0   up to date
  laptop   2s ago  #412  0.1.0   up to date

  AGO     HEAD  FROM    OPS  COMMITS  WHAT
  2s ago  #412  laptop  1    1        snapshot working copy
```

Each hive's row shows the bytes a second going into and out of the hub, and the operations and
commits that came in since the hub started. Below, for the hive you pick with the arrow keys, it
shows each machine and the latest updates, with the machine each came from and what `jj op log`
calls it. The issues at the top are what needs you: a hub out of reach or failing requests, and
machines offline, stuck behind, or failing to sync.
[Troubleshooting](../troubleshooting.md#what-musubi-top-reports) says what to do about each.

`q` quits, `r` refreshes now, and `+` and `-` refresh less or more often. Without a terminal,
or with `--once`, it prints one snapshot, without the rates.

The hub keeps all this in memory. After the hub restarts, each machine shows up again once its
daemon next syncs, within half a minute. The hub forgets a machine it hasn't heard from in a
day.

## Rename or remove a hive

```sh
musubi hub rename app work-app
musubi hub remove work-app
```

Renaming changes the name that commands take and `musubi list` and `musubi status` show.
Copies keep syncing, and each machine picks up the new name as its daemon next syncs, within
half a minute, or the next time `musubi list` runs there.

`hub remove` takes the hive's whole name or its id, not a prefix as other commands do. Each
machine's copy leaves the hive as it next syncs, as with `musubi leave`, keeping everything it
has. The hub keeps the hive's data in `removed/` for a day, then only an empty directory, as a
record that the hive was removed, so that no copy brings it back. To share the repository
again, start a new hive with `musubi create`, and run `musubi join --hive <name>` in the other
copies: a plain `musubi join` in a copy whose hive was removed says so, rather than joining
another hive.

## Take a repository or machine out

In a repository, `musubi leave` takes it out of its hive and stops syncing it. It first
records what changed in the working copy and sends that last work to the hive. The other
machines then stop showing its working copy (`laptop/default@`), and the hub stops counting
the machine. The repository keeps everything it has, working copy included, and the other
machines keep everything it sent: a working-copy commit with changes stays as an ordinary
commit, and an empty one is dropped.

If the hub can't be reached, `musubi leave` fails and the repository stays in its hive, so
that a script tearing down a machine knows its last work didn't get out. `musubi leave
--force` leaves anyway, without telling the hive; the other machines go on showing the copy
until one of them forgets it. See
[Troubleshooting](../troubleshooting.md#leaving-a-hive-or-forgetting-a-machine) for the
messages.

### Forget a machine that went away

A machine that went away without leaving, such as a short-lived machine, or whose copy was
deleted, stays in the hive until it is forgotten. Forget it now, from any other machine, by
the name its working copy has there:

```sh
musubi forget laptop
```

The other machines stop showing `laptop/default@` as they sync, and the hub stops counting
it. If the copy still exists after all, it comes back as soon as a `jj` command in it records
an operation: one that changes something or snapshots a change to the working copy. But if
another machine runs `jj op abandon` while the copy is away, and every machine still in the
hive has taken it, the copy can't sync again: it stops with "this repository's history no
longer matches the hive's" ([what to
do](../troubleshooting.md#this-repositorys-history-no-longer-matches-the-hives-so-it-cant-sync-again)).

A copy can also be forgotten by itself once unused for long enough, as set by
`musubi.forget-after` in its repository's config. `musubi join`, `create` and `clone` set it,
and say what they set: `6h` when a coding agent such as Claude Code or Codex runs them, since
its machine may go away without leaving, and `never` otherwise. They leave it alone if jj's
config sets it already, as an agent's machine image might in the user config, or as a copy
that joins again keeps from when it last joined. Change it with `jj config`:

```sh
jj config set --repo musubi.forget-after '2 days'   # or 30m, '1h 30m', 1week, never
```

Any operation recorded in the copy counts as using it, as does changing this setting. Once a
copy goes unused for longer than its setting, the first daemon to notice forgets it, as
`musubi forget` would, within a few minutes; the copy comes back as soon as it's used again,
with the same exception. In a repository, `musubi status` shows each copy, when it was last
used, and when it will be forgotten.

### Rejoin, or stop using musubi

To sync a copy again after it has left, run `musubi join` in it. It carries on from the
history it shared, so a copy that joins a different hive brings its old hive's history along,
and the new hive's machines show the old hive's working copies too. If another machine ran
`jj op abandon` while the copy was away, and every machine still in the hive has taken it, the
copy can't sync again: it stops with "this repository's history no longer matches the hive's"
([what to
do](../troubleshooting.md#this-repositorys-history-no-longer-matches-the-hives-so-it-cant-sync-again)).

To stop using musubi on a machine altogether:

1. Take each of its repositories out with `musubi leave`. `musubi list` lists them.
2. Run `musubi daemon uninstall`, which stops the daemon and stops it starting at login.
3. If a hub runs on this machine, stop it (`musubi hub uninstall`, if `musubi hub install`
   runs it at login), delete its directory, and remove the other machines' lines, those
   ending in `musubi@<host>`, from `~/.ssh/authorized_keys` here.
   Move the hub first if other machines still use it: see [Replace or move a
   hub](#replace-or-move-a-hub).
4. Delete what musubi kept: `.jj/repo/musubi/` in each of those repositories, and its state
   directory, `~/.local/state/musubi` unless you set `XDG_STATE_HOME` or `MUSUBI_STATE_DIR`
   (`%APPDATA%\musubi` on Windows). [Files and
   directories](../reference/configuration.md#files-and-directories) lists everything musubi
   writes.
5. Unset its settings: `jj config list --user musubi` lists them, and
   `jj config unset --user <key>` unsets each. In each of those repositories, do the same
   with `--repo`, for `musubi.forget-after`.
6. On the hub's machine, if that is another, remove this machine's line from
   `~/.ssh/authorized_keys`: the one ending in `musubi@<host>`.

## Upgrade musubi

### Recreate hives when upgrading to 0.4.0

Release 0.4.0 changes operation ids to preserve identity when history is abandoned. Its hub
state and each copy's musubi state must be made afresh; the jj repositories and their work stay.

1. Before upgrading, sync every copy with the old release. In each copy run `musubi leave`,
   or `musubi leave --force` if its hub is gone, then stop its daemon with
   `musubi daemon stop`.
2. Keep a backup of every repository. Run `jj workspace list` in each copy, then
   `jj workspace forget <name>` for each workspace belonging to another machine. Keep this
   machine's own workspaces, including its linked workspaces. A local workspace's name can
   contain `/`; `jj workspace root --name <name>` shows its recorded local directory.
   Leaving can leave the other machines' workspaces here; remove them before the next step
   so that the new hive doesn't treat them as this machine's own. This removes their
   workspace names from this copy.
3. Move each repository's `musubi` directory out of its jj repository directory (normally
   `.jj/repo/musubi`) to a separate archive. Keep that archive; it includes the old hive
   membership and translation records. For linked workspaces, use the repository directory
   they share, once for that repository.
4. Stop the old hub and archive its state directory. Install 0.4.0 on the hub and every
   machine, then start the hub with an empty state directory, as in the setup guide.
5. In one preserved repository run `musubi create`, then in each other copy run
   `musubi join`. Joining starts its daemon. Use the usual join, which shares the present
   view; do not use `--full-history` to carry old realizations into the new hive.

The old operation history remains in the local jj repositories. Inspect work on every copy
before discarding any archive.

### Keep machines on the hub's release

Until 1.0, a release may change how machines and hubs talk, and a machine and a hub running
different releases refuse to sync, saying so. So run the same release on the hub's machine and
every other machine.

Each machine can follow its hub by itself. Give it a command that installs the release of
musubi it is told, as a script in your dotfiles:

```sh
jj config set --user musubi.upgrade-command ~/bin/upgrade-musubi
```

Whenever the daemon finds a hub running a newer release than its own, it runs the command
once for that release, with `MUSUBI_UPGRADE_TO` set to it, such as `0.3.0`, or for a build
[deployed from source](#deploy-a-build-from-source), its name. Once the `musubi`
the daemon started from says it is that release (`musubi --version`), the daemon starts again
from it. A machine that was asleep or away does this when it next reaches the hub.

To upgrade, then:

1. Read the release's section of [CHANGELOG.md](../../CHANGELOG.md) for anything else to do.
2. On the hub's machine, install the new `musubi` in place of the old one. Stop `musubi hub`
   and start it again, or if it runs at login, run `musubi hub install` again.
3. Every machine with `musubi.upgrade-command` upgrades itself. On any other machine, install
   the new `musubi` and run `musubi daemon restart`.

The command runs through `sh -c` (`cmd /C` on Windows), in the state directory, with no
terminal and the daemon's environment: where launchd or systemd starts the daemon, the `PATH`
that `musubi daemon install` saw. It may run for up to an hour, as `cargo install` can, and
its output goes to `upgrade.log` in the state directory. It must install exactly
`$MUSUBI_UPGRADE_TO`, where the daemon started `musubi` from: if the path changes, run
`musubi daemon install` again. A script that builds musubi with cargo:

```sh
#!/bin/sh
set -e
cargo install --locked --version "$MUSUBI_UPGRADE_TO" jj-musubi
```

If you build musubi on each machine from a jj repository of its source (made with `jj git
clone`), copy [contrib/upgrade-from-source](../../contrib/upgrade-from-source) into your
dotfiles and give it the repository:

```sh
jj config set --user musubi.upgrade-command '~/bin/upgrade-from-source ~/dev/jj-musubi'
```

For a release, it builds the release's tag, such as `v0.4.0`, and for a build deployed from
source, that build's commit, fetching first if the repository lacks it; otherwise it fails,
saying what it found. It builds a copy of the commit's files, so it never touches the
repository's working copy, or your edits in progress there. It needs `jj`, `git` and `cargo`
on the daemon's `PATH`. To try it, name a release; this installs it:

```sh
MUSUBI_UPGRADE_TO=0.4.0 ~/bin/upgrade-from-source ~/dev/jj-musubi
```

If the command fails, or installs another release, the daemon carries on as it was, and
`musubi status` says why. Once the command works, `musubi daemon restart` tries again.

Only a newer release starts the command, or a build deployed later, as below. A build from
source that wasn't deployed, as with `cargo install --path`, says only the release it follows,
so it starts nothing, and neither does putting a hub back on an older release: upgrade or go
back by hand then.

Upgrade `jj` with musubi, not before: each release of musubi works with one release of jj, and
refuses operations that a newer jj wrote.

### Deploy a build from source

To run a build of musubi's source on every machine between releases, deploy it from the hub's
machine with `upgrade-from-source --deploy`:

1. Push the revision where the machines' clones of the source fetch from, as by pushing
   `main`.
2. On the hub's machine, deploy it, `main` unless you name another revision:

   ```sh
   ~/bin/upgrade-from-source --deploy ~/dev/jj-musubi main
   ```

   This installs it with `cargo install`, into `~/.cargo/bin` or `CARGO_INSTALL_ROOT`, which
   must be where the hub runs `musubi` from, as a build named for the release it follows (the
   `version` in its `Cargo.toml`), the time in UTC, and its commit, such as
   `musubi 0.3.0+20261102153012.4a0db205e1f0`. `musubi --version` prints that name.
3. Stop `musubi hub` and start it again, or if it runs at login, run `musubi hub install`
   again.

Each machine whose upgrade command is `upgrade-from-source` then follows the hub to that build,
even if it changes how machines and hubs talk: it builds the build's commit, fetching it if its
clone lacks it. [`musubi top`](#watch-every-machine) shows which build each machine runs.
Another upgrade command, such as the cargo one above, can't install a deployed build, and
`musubi status` says so. A machine that tried before the commit was pushed tries again after
`musubi daemon restart`, or when you deploy again.

Of two builds that follow the same release, the one deployed later by the clock of the
machine you deploy on is newer, whatever its commit, so deploying an older revision again takes
every machine back to it. A deployed build is newer than the release it follows and older than
the next, so deploying a revision from before the release the machines run starts nothing.

## Move, copy or restore a repository

musubi follows a copy you move, with `mv`, on one disk or to another: once jj or musubi runs
in it at its new place, the daemon syncs it there.

A repository made by copying a copy's files, with `cp -a`, `rsync` or a backup, is a
duplicate. It carries the copy's identity in the hive, and two repositories syncing as one
would overwrite each other's working copy. So musubi doesn't sync a duplicate: `musubi status`
in it says it isn't synced, and `musubi join`, `sync` and `leave` there refuse. Use it as a
plain jj repository, or make another copy with `musubi clone`.

Some repositories are the copy, as far as you know, though musubi takes them for a
duplicate: a copy moved by copying it and deleting the original, or restored from a backup
onto a new machine. Once the original is gone, `musubi join --original` syncs it as the copy.
A backup restored in place, over the copy, is the copy already: it syncs as before, and
fetches the work it lacks.

A copy that is deleted, or on a disk that isn't mounted, stops syncing, and musubi writes
nothing there; it syncs again if it comes back. `musubi list` shows it as "not syncing",
saying why, and `musubi leave <path>` stops looking for it. The other machines show it until it's
forgotten. If the directory comes to hold another repository, musubi stops syncing it too,
and writes nothing there.

Run musubi as the user who owns the repository: it refuses another user's, as under `sudo`.
And don't let a file-syncing tool, such as Dropbox or Syncthing, sync a copy too: see
[Comparison](../comparison.md#file-syncing-dropbox-syncthing-icloud-rsync-nfs).

## Replace or move a hub

Every machine keeps everything it has synced, so losing a hub, whether its directory or its
whole machine, loses no work. Start a new hub at the address machines use for the old one, as
in [Set up a hub and machines](setup.md#start-the-hub). The new hub knows none of the hives,
so syncs fail, saying the hub has no record of the repository's hive. Make each hive again
from one machine's copy:

```sh
musubi join
```

That makes the hive again on the hub, with its old id and name. The other machines find it as
their daemons next try, within a minute, or at once with `musubi sync`, and fill it with what
they have. Working copies, commits, bookmarks and history all come through unchanged.

Machines don't do this by themselves, because a hub that doesn't know a hive may just be the
wrong hub, such as one started from another directory by mistake.

To move to a hub at another address, start it, and run `musubi join` with its address in each
machine's copy. The first makes the hive again there, and the others join it:

```sh
musubi join --hub newbox
```

Each machine's default hub, used when a command has no `--hub`, is still the old one, and
`musubi list` goes on showing it. To make the new hub the default, set `musubi.hub` (see
[Settings](../reference/configuration.md#this-machines)):

```sh
jj config set --user musubi.hub newbox
```
