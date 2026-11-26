# Manage hives, machines, and hubs

Check syncing, rename or remove hives, take machines out, and replace a hub.

A hub passes shared history between copies; each machine's daemon keeps them in sync.
See [How jj-musubi works](../how-it-works.md).

For release changes and automatic installers, see [Upgrading](upgrading.md).

## Check syncing

Inside a repository, run `musubi status`. Look for a running daemon serving this repo,
a recent successful sync, no error or sending hold, and `the hub has all its work`.

The report reads local state without contacting the hub or recording edits, and exits 0 even
with a problem. Run `musubi sync` to attempt a fresh sync; it reports failures but still sends
only work jj has recorded. Check for unwanted files before using `jj status` to snapshot edits.
A [snapshot hold](snapshots.md) pauses sending while receiving continues.

To check other machines, run `musubi top`, select a hive with the arrow keys and inspect
`STATE`. A quiet machine may be asleep. If it should be online, or is behind or failing, run
`musubi status` there and follow its [error](../troubleshooting.md) or inspect its
[daemon log](../reference/configuration.md#logging).

A successful send means the hub has the work; it does not establish that every receiver has
it. [Inspect the received work](working-across-machines.md#pick-up-on-another-machine)
before a handoff. Reports come from completed syncs, so a long first sync has no report until
it finishes. After a hub restart, machines reappear as they sync again.

After login, reboot or an upgrade, check that the hub runs and use `musubi list` on each
working machine expected online. Without a daemon, `musubi sync` syncs once and warns that
nothing will keep syncing. See [service setup](setup.md#keep-the-hub-running) and
[daemon troubleshooting](../troubleshooting.md#the-daemon).

`musubi top` sends no alerts; `status` and `top --once` exit successfully even with problems.
See the [dashboard reference](../reference/commands.md#read-musubi-top) for controls and report
expiry, and [JSON health checks](../reference/commands.md#musubi-status-as-json) for unattended
monitoring.

## Rename or remove a hive

```sh
musubi hub rename app work-app
musubi hub remove work-app
```

Renaming changes the name commands take and `musubi list` and `musubi status` show. Copies keep
syncing and learn the name at their next sync, within half a minute, or next `musubi list`.

`musubi hub remove` takes the hive's whole name or id. It waits for ongoing work, such as a
large fetch, while other hives remain available. Each copy leaves at its next sync, keeping
everything it has. The hub keeps the data in `removed/` for about a day by default.
`musubi hub remove --immediately` waits for the hub to delete the store. An empty directory
remains to prevent copies from recreating the removed hive. To share again after clearing
unwanted history, see [Purge shared history](../troubleshooting.md#purge-shared-history).

To share again, start a hive with `musubi create` and run `musubi join --hive <name>` in other
copies. A plain `musubi join` refuses while the copy records a removed hive; run
`musubi leave` first, after which `musubi join` matches it as any other repo. A copy that
creates or joins another hive sends it the removed hive's operation history, unless you pass
`--fresh` (see [Rejoin](#rejoin-or-stop-using-jj-musubi)).

## Pause syncing or leave

To pause background syncing on this machine:

```sh
musubi daemon stop
```

This stops syncing for all copies served by the daemon, keeping their memberships and work
already sent or received. It leaves the hub and other machines alone. Wait for completion,
then check `musubi status`; stopping does not undo an exchange or guarantee it had no effect.

`musubi daemon start` resumes syncing. Login startup remains installed;
`musubi daemon uninstall` stops the daemon and removes it. Explicit
`musubi sync` can still sync while the daemon is stopped, and `create`, `join` and `clone`
can start it again.

To remove one copy, [leave its hive](#take-a-repo-or-machine-out). Leaving attempts a
final sync, even with `musubi leave --force`, unless a workspace's name has a `/`; stop the
daemon while deciding what to send.

## Take a repo or machine out

In a repo, `musubi leave` snapshots current files and sends the last work before leaving
the hive and stopping sync. Other machines stop showing its working copy (`laptop/default@`),
and the hub stops counting it. The repo keeps its files and history; other copies keep
what it sent. A working-copy commit with changes becomes an ordinary commit; an empty one
is dropped.

If the final sync fails, `musubi leave` fails and the repo stays in its hive.
`musubi leave --force` attempts the same sync but leaves even if it fails; other machines may
show the copy until one forgets it. Fix the reported cause and retry, or pause background
traffic with `musubi daemon stop` while deciding what to send. A workspace whose name has a
`/` stops `musubi leave` before it changes anything; rename it as the hint says, or use
`musubi leave --force`, which then leaves without snapshotting files or sending the last work.

### Forget a machine that went away

A machine that disappeared without `musubi leave`, or whose copy was deleted, stays in the hive
until forgotten. From another machine, use the name its working copy has there:

```sh
musubi forget laptop
```

A copy remains present if its last workspace was removed with `jj workspace forget`.
`musubi status` still lists its name under Copies, and `musubi forget` accepts that name.

Other machines stop showing `laptop/default@` as they sync, and the hub stops counting it.
The copy keeps its local workspaces and returns when a `jj` command records an operation,
including a snapshot. Other machines' rewrites can make its working copy
[stale](working-across-machines.md#when-another-machine-rewrites-your-working-copy).

A copy deleted and cloned again on the same machine shows beside the new one, both under the
machine's name with part of their ids, as `laptop-1a2b` and `laptop-3c4d`. `musubi list` and
`musubi status` say which is the new copy; forget the other by its name, as in `musubi forget
laptop-3c4d`. The new copy then goes back to the machine's name.

Copies are never forgotten by default, whether joined by a person or agent. Give temporary
copies an inactivity lease with `musubi join`, `create` or `clone`:

```sh
musubi join --lease 6h
musubi clone app ~/src/app --lease 6h
```

`--lease` sets `musubi.forget-after` in this copy's repo config, replacing an existing value.
A conflicting workspace policy would override that repo value, so the command refuses it;
run `jj -R <workspace-path> config unset --workspace musubi.forget-after` for the workspace
named in the hint, then retry. Without `--lease`, joining keeps any configured value, or sets
`never` if none is configured. To change the policy later, including for copies previously
given the agent default of `6h`:

```sh
jj config set --repo musubi.forget-after never     # or 30m, '1h 30m', '2 days'
musubi sync
```

The daemon reads and shares the new policy at its next sync. `musubi sync` waits for it;
no restart is needed.

Recording an operation or changing this setting counts as use. After the inactivity limit,
the first daemon to notice forgets the copy within a few minutes, as `musubi forget` would.
It returns when used again. `musubi status` shows each copy's last use and when it will be
forgotten.

### Rejoin, or stop using jj-musubi

After leaving, run `musubi join` in the same repo to join again. It comes back as the same
machine, under the name it had, and sends the work you did while it was out; your files and jj
history stay in the checkout. To rename the machine, change its setting rather than leaving and
joining again: see [Naming machines](setup.md#naming-machines).

If you join a different hive, or start one with `musubi create`, the operation history you
already shared goes with you, with everything it holds, even work you have deleted since. The
command warns, with the number of operations. To leave that history out, pass `--fresh`, as
in `musubi create --fresh`: the repo sends its commits and bookmarks as they are now, as a
repo that was never part of a hive does, and keeps its own operation log. If the warning
comes too late, take the copy out with `musubi leave`, remove the new hive with `musubi hub
remove --immediately <hive>`, and run `musubi create --fresh <hive>`. Don't use `--fresh` to
join the hive you left again, which has that history already: where its commits changed
since, you would get divergent changes to resolve.

To stop using jj-musubi on a machine:

1. Take each of its repos out with `musubi leave`. `musubi list` lists them.
2. Run `musubi daemon uninstall`, which stops the daemon and stops it starting at login (at
   boot on illumos).
3. If a hub runs on this machine, stop it (`musubi hub uninstall`, if `musubi hub install`
   runs it), delete its directory, and remove the other machines' lines, those
   ending in `musubi@<host>`, from `~/.ssh/authorized_keys` here.
   Move the hub first if other machines still use it: see [Replace or move a
   hub](#replace-or-move-a-hub).
4. Delete what jj-musubi kept: `.jj/repo/musubi/` in each of those repos, and its state
   directory, `~/.local/state/musubi` unless you set `XDG_STATE_HOME` or `MUSUBI_STATE_DIR`
   (`%APPDATA%\musubi` on Windows). [Files and
   directories](../reference/configuration.md#files-and-directories) lists everything jj-musubi
   writes.
5. Unset its settings: `jj config list --user musubi` lists them, and
   `jj config unset --user <key>` unsets each. In each of those repos, do the same
   with `--repo`, for `musubi.forget-after`.
6. On the hub's machine, if that is another, remove this machine's line from
   `~/.ssh/authorized_keys`: the one ending in `musubi@<host>`.

## Move, copy or restore a repo

After moving a copy with `mv`, on one disk or between disks, run jj or `musubi` there so the
daemon finds its new location. On illumos the daemon doesn't yet find a moved copy: a known
limitation.

A copy made with `cp -a`, `rsync` or a backup duplicates the original's hive identity.
jj-musubi refuses to sync it because the two copies would overwrite each other's working
copy. `musubi status` reports this; `musubi join`, `sync` and `leave` refuse. Use it as a plain
jj repo, or make another copy with `musubi clone`.

This also applies after copying and deleting the original, or restoring onto a new machine.
Once the original is gone, `musubi join --original` syncs the replacement under its identity.
A backup restored over the original copy syncs as before and fetches work it lacks.

Deleted copies, unmounted disks and directories replaced by other repos stop syncing;
jj-musubi writes nothing there. `musubi list` reports "not syncing" and why. A returning copy
resumes syncing; `musubi leave <path>` stops looking for it. Other machines show it until
forgotten.

Run `musubi` as the repo's owner; it refuses another user's, as under `sudo`.
Do not also sync its files with Dropbox, Syncthing or similar tools: see
[Comparison](../comparison.md#file-syncing-dropbox-syncthing-icloud-rsync-nfs).

## Repo cleanup

The daemon cleans up what `jj util gc` would: operations unreachable from the current one
and files jj no longer reads, all at least two weeks old. Cleanup runs when enough has
accumulated, at most weekly, skips cleanup on battery power, and leaves Git objects untouched.

## Replace or move a hub

Rebuild a lost hub directory from work retained in surviving copies. Work held only on a lost
hub machine needs that machine's backup.

Start a new hub at the address machines used before, as in
[Set up a hub and machines](setup.md#start-the-hub). The new hub knows none of the hives, so
syncs say it has no record of the repo's hive.

If you replaced the whole hub machine, compare its SSH host key through your normal trusted
channel before updating your known-host entry. The new machine also needs the
clients' restricted jj-musubi keys in `~/.ssh/authorized_keys`. Restore those entries from a
trusted backup, or run `musubi join --hub <hub-host>` interactively in each client's copy to
authorize its key again. An unattended daemon cannot answer an SSH password or host-key
prompt. Test `ssh <hub-host> musubi --version` before expecting daemons to reconnect.

In one surviving copy of each hive, run:

```sh
musubi join
```

This recreates the hive with its old id and name. With ssh access working, other daemons find
it within a minute, or at once with `musubi sync`, and send retained work. Check each copy's
`musubi status`. Resolve any divergent changes left by rollback with jj, as for concurrent
rewrites.

Recreation requires your command: an unknown hive may mean the wrong hub directory was used.

Recreation keeps hives separate, even if another hive shares the repo's history, as
`musubi create <name>` does. To combine them, run `musubi leave` then `musubi join --hive <name>`
in each copy, and remove the recreated hive with `musubi hub remove`.

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
