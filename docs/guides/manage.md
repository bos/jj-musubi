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

Run in a hive's repository, it adds that repository's details: its hive, hub, and machine
name, where each machine's working copy is, and the latest head of the hub that this machine
knows of.

## Rename or remove a hive

```sh
musubi hub rename app work-app
musubi hub rm work-app
```

Renaming changes the name that commands take and `musubi list` shows under the hub. Copies
keep syncing, but each copy goes on calling the hive by its old name in the details
`musubi list` shows for it.

Removing a hive moves its store to `removed/` in the hub's directory. Its machines keep
everything they have, but their syncs fail, with `hub: this hub has no hive <id>`, until you
run `musubi leave` in each copy.

## Take a repository or machine out

In a repository, `musubi leave` stops syncing it. The repository keeps everything it has,
and the other machines keep everything it sent. Leaving doesn't tell the hub, though: the
other machines go on showing the machine's last working copy, as `laptop/default@`, and the
hub goes on counting the machine. Forgetting that workspace on another machine doesn't last,
since each machine's workspaces are its own: the next sync shows it again.

To take a machine out of a hive for good, remove its workspace from the machine itself
before it leaves:

```sh
jj workspace forget default
musubi sync
musubi leave
```

That leaves the repository on that machine without a working copy.

To sync a copy again after it has left, follow steps 2 to 4 of [Replace or move a
hub](#replace-or-move-a-hub). Joining without them fails if `jj` has run in the copy since it
left.

To stop using musubi on a machine altogether:

1. Take each of its repositories out, as above. `musubi list` lists them.
2. Run `musubi daemon uninstall`, which stops the daemon and stops it starting at login.
3. On the hub's machine, remove the machine's line from `~/.ssh/authorized_keys`: the one
   ending in `musubi@<host>`.

## Upgrade musubi

Until 1.0, a release may change how machines and hubs talk, and a machine and a hub running
different releases refuse to sync, saying so. So upgrade the hub's machine and every other
machine together:

1. Read the release's section of [CHANGELOG.md](../../CHANGELOG.md) for anything else to do.
2. Install the new `musubi` everywhere, in place of the old one. If its path changes, run
   `musubi daemon install` again on that machine, since the daemon started at login runs the
   path `daemon install` found.
3. On the hub's machine, stop `musubi hub` and start it again.
4. On every machine, run `musubi daemon restart`.

Upgrade `jj` with musubi, not before: each release of musubi works with one release of jj,
and refuses operations that a newer jj wrote.

## Replace or move a hub

Every machine keeps everything it has synced, so losing a hub, its directory deleted or its
machine gone, loses no work. But the machines can't fill a new, empty hub by themselves: each
copy belongs to a hive by an id that only the old hub knew, and syncs fail with
`hub: this hub has no hive <id>`. Make the hive again on the new hub, from the copies. The
same steps move a hive to another hub on purpose, or remake one that `musubi hub rm`
removed.

Start the new hub, as in [Set up a hub and machines](set-up.md#start-the-hub). Then, in each
machine's copy in turn:

1. Stop syncing it with the old hive:

   ```sh
   musubi leave
   ```

2. Forget the other machines' workspaces, which the new hive will bring back. List them with
   `jj workspace list`; they're the ones named after machines:

   ```sh
   jj workspace forget laptop/default desktop/default
   ```

3. Remove the copy's record of what the old hub last accepted, `accepted_base`, in the
   repository's `.jj/repo/musubi` directory:

   ```sh
   rm .jj/repo/musubi/accepted_base
   ```

   Without this, if `jj` has run in the copy since its last sync, the first sync with the new
   hive fails, saying that the operation history the hub accepted is no longer reachable.

4. On the first machine, start the hive, giving its old name, since a new hive is named after
   the repository's remote:

   ```sh
   musubi create app --hub newbox
   ```

   On the others, join it:

   ```sh
   musubi join --hub newbox
   ```

Working copies, commits, and bookmarks come through unchanged. The operation log keeps the old
hive's operations, and gains each machine's join to the new one.

If the hub moved, each machine's default hub, which commands use without `--hub`, is still
the old one, and `musubi list` goes on showing it. Change `hub` in `config.toml` (see
[Configuration](../reference/configuration.md#musubis-config-file)) to make the new hub the
default.
