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

Run in a hive's repository, it also shows that repository's hive, hub and machine name, where
each machine's working copy is, and the latest hub head this machine knows of.

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

app since the hub started: received 4.1 MiB and sent 12 MiB; 96 operations, writing 51
commits, came in, and 180 went out; 40 pushes moved the head, and 2 found it moved first.
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

Renaming changes the name that commands take and `musubi list` shows. Copies keep syncing,
and each machine picks up the new name the next time `musubi list` runs there.

`hub remove` takes the hive's whole name or its id, not a prefix as other commands do. Each
machine's copy leaves the hive as it next syncs, as with `musubi leave`, keeping everything it
has. The hub keeps the hive's data in `removed/` for a day, then only an empty directory, as a
record that the hive was removed, so that no copy brings it back. To share the repository
again, start a new hive with `musubi create`, and run `musubi join` in the other copies.

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
an operation: one that changes something or snapshots a change to the working copy.

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
`musubi forget` would, within a few minutes; the copy comes back as soon as it's used again.
In a repository, `musubi list` shows each copy, when it was last used, and when it will be
forgotten.

### Rejoin, or stop using musubi

To sync a copy again after it has left, run `musubi join` in it. It carries on from the
history it shared, so a copy that joins a different hive brings its old hive's history along,
and the new hive's machines show the old hive's working copies too.

To stop using musubi on a machine altogether:

1. Take each of its repositories out with `musubi leave`. `musubi list` lists them.
2. Run `musubi daemon uninstall`, which stops the daemon and stops it starting at login.
3. On the hub's machine, remove the machine's line from `~/.ssh/authorized_keys`: the one
   ending in `musubi@<host>`.

## Upgrade musubi

Until 1.0, a release may change how machines and hubs talk, and a machine and a hub running
different releases refuse to sync, saying so. So upgrade the hub's machine and every other
machine together:

1. Read the release's section of [CHANGELOG.md](../../CHANGELOG.md) for anything else to do.
2. Install the new `musubi` everywhere, in place of the old one. If its path changes on a
   machine, run `musubi daemon install` again there, since the daemon started at login runs
   the path `daemon install` found.
3. On the hub's machine, stop `musubi hub` and start it again.
4. On every machine, run `musubi daemon restart`.

Upgrade `jj` with musubi, not before: each release of musubi works with one release of jj, and
refuses operations that a newer jj wrote.

## Replace or move a hub

Every machine keeps everything it has synced, so losing a hub, whether its directory or its
whole machine, loses no work. Start a new hub at the address machines use for the old one, as
in [Set up a hub and machines](set-up.md#start-the-hub). The new hub knows none of the hives,
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
