# Manage hives, machines, and hubs

Check syncing, rename, remove, pause or reset hives, take machines out, and replace a hub.

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
everything it has. The hub keeps the data in `removed/` for a day, then an empty directory
that prevents copies from recreating the removed hive.

To share again, start a hive with `musubi create` and run `musubi join --hive <name>` in other
copies. A plain `musubi join` refuses while the copy records a removed hive; run
`musubi leave` first, after which `musubi join` matches it as any other repo.

## Pause a whole hive

To stop every machine syncing a hive, run this in any of its copies:

```sh
musubi pause
```

No copy can sync once `musubi pause` returns. Each machine's daemon finds out at its next
attempt to sync, within half a minute, or when the machine comes back online, and waits; from
then on, `musubi status` there says who paused the hive and when, as `musubi sync` does. jj
works as usual meanwhile, but work done on a machine exists only there until the pause ends.
`musubi join` and `musubi clone` refuse a paused hive.

`musubi pause` doesn't sync first, so it works in a copy whose syncing fails.

A pause ends one of two ways:

- `musubi pause --cancel`, in any copy, lets the hive carry on unchanged. Machines sync again
  within half a minute, or at once with `musubi sync`, sending what each did meanwhile. The
  work done meanwhile syncs as any work does: `jj op abandon` of operations the hive has still
  stops that copy syncing ([Abandoning
  operations](working-across-machines.md#abandoning-operations)).
- `musubi resume`, in a copy you've cleaned up, makes the hive again from that copy, without
  its old history, as the next section says.

## Clean up history on every machine

To remove something from every machine, such as a secret or a pile of files committed by
mistake, make the hive again from one copy that no longer has it. jj's own commands change only
the copy you run them in, and the hub and the other machines keep everything they've received.

1. In the copy you'll clean up, pause the hive, so that nothing syncs while you work:

   ```sh
   musubi pause
   ```

2. Remove what you don't want there with jj: `jj abandon <change>` to drop a commit, or `jj
   restore` and `jj squash` to take a file out of a commit you keep. Check with `jj log -r
   'all()'` that no commit it lists still has it. Abandoned commits and old operations need
   nothing more: the new hive gets only what this copy shows now.

3. Make the hive again from this copy:

   ```sh
   musubi resume
   ```

   It names the other machines and asks before going on. The hive keeps its name and
   settings, and starts again from this copy's current state, with none of its operation
   history. The hub deletes the old history at once. This copy goes on syncing, and keeps its
   own operation history, and with it the data you removed: see [Remove data from a machine's
   disk](#remove-data-from-a-machines-disk).

`musubi resume` refuses if the hive has work this copy hasn't received, such as work another
machine sent just before the pause, and names the machines it came from. To include it, run
`musubi pause --cancel` and `musubi sync` here, then `musubi pause` again, and repeat step 2,
since that work can bring back what you removed. (If you ran `jj op abandon` here, the sync
fails: this copy [lost history the hive has](../troubleshooting.md#rescue-work-in-a-new-copy).)
To leave the work out instead, run `musubi resume --force`; those machines keep it, and can
bring it across as below.

Any copy can resume a paused hive, even one that [lost history the
hive has](../troubleshooting.md#rescue-work-in-a-new-copy). The first to resume wins; a
later one is told the hive was reset, as below. If `musubi resume` stops partway, as when the
connection to the hub drops, run it again in the same copy to finish; if it then says this
repo duplicates a copy, run `musubi join --original` there instead.

### On the other machines

Every other copy stops syncing for good the next time it contacts the hub, or when its machine
comes back online. It keeps everything it has, including work it hadn't sent. `musubi status`
and `musubi sync` there say so:

```text
Error: hive app was reset (by laptop, 5m ago) to remove history this copy still has, so it no longer syncs
Hint: Make a new copy with `musubi clone app <dir>`, bring across any work it lacks, then delete this copy; "Clean up history on every machine" in the user guide says how.
```

Such a copy can't join a hive again, since joining would bring the old history back. Replace
it with a new copy, on each of those machines, as soon as it's back online:

1. Make the new copy, in a new directory:

   ```sh
   musubi clone app ~/src/app-new
   ```

2. Bring across any work the new copy lacks: what the old copy hadn't sent before the pause,
   what was done there while the hive was paused, and, after `musubi resume --force`, work the
   copy that resumed hadn't received. To find it, compare `jj log -r 'mutable()'` in the two:
   a commit with the same commit id in both is in the new copy already.

   Copy files across, which is the safe way if the work sits on top of what was removed. For
   each change to bring, list its files in the old copy with `jj diff -r <change> --name-only`,
   copy them into the new copy, and record them there with `jj commit -m '<description>'`.
   Don't copy `.jj` or `.git`. You can also transfer whole commits, as [Rescue work in a new
   copy](../troubleshooting.md#rescue-work-in-a-new-copy) says, but only where none of their
   ancestors has what was removed: fetching a commit brings its ancestors too.

3. Check the work in the new copy with `jj log`, and that `musubi sync` there succeeds. Then
   delete the old directory, and any other jj workspaces it has. It needs no `musubi leave`:
   it has stopped syncing already.

### What resetting can't do

Resetting reaches only the hub and jj-musubi's copies. It can't remove anything that was
pushed to a git remote, or that reached a fork, CI, a backup, an editor's history or a
file-syncing tool: treat a secret that went anywhere like that as leaked, and change it.

Don't delete `.jj/repo/musubi` from an old copy to make it join again: it would join the new
hive as a repo that never shared its history, bringing back every commit it shows. And if
the hub loses its state while a copy that hasn't heard of the reset is offline, that copy
hears nothing of the reset, and `musubi join` there would make the old hive again. So replace
or delete old copies as soon as their machines are back, and never run `musubi join` in one.

## Remove data from a machine's disk

`musubi resume` removes the old history from the hub, but not from any machine's disk: the
copy that resumed keeps its own operation history, and the other copies keep everything until
you delete them. jj-musubi never deletes git objects ([Repo cleanup](#repo-cleanup)).

The sure way is to make a new copy with `musubi clone`, check it with `jj log` and `musubi
sync`, then run `musubi leave` in the old copy, if it's the one that resumed, and delete the
old directory, with any other jj workspaces it has.

To clean up the copy that resumed in place instead, do this in it right after `musubi
resume`, while no other jj command runs there:

1. Abandon every operation from before the reset, which the new hive never had. In `jj op
   log`, find the operation `musubi: reset the hive`, and run, with its id:

   ```sh
   jj op abandon '..<id>-'
   ```

2. In a colocated repo, expire git's reflogs, which still name the old commits:

   ```sh
   git reflog expire --expire=now --all
   ```

3. Have jj delete what nothing refers to now:

   ```sh
   jj util gc --expire=now
   ```

To check, search what git has for a line of what you removed; this prints nothing once it's
gone:

```sh
git --git-dir "$(jj git root)" cat-file --batch-all-objects --batch | grep '<a line of it>'
```

## Stop syncing on this machine or leave

To stop background syncing on this machine only:

```sh
musubi daemon stop
```

This stops syncing for all copies served by the daemon, keeping their memberships and work
already sent or received. It leaves the hub and other machines alone. Wait for completion,
then check `musubi status`; stopping does not undo an exchange or guarantee it had no effect.

`musubi daemon start` starts syncing again. Login startup remains installed;
`musubi daemon uninstall` stops the daemon and removes it. Explicit
`musubi sync` can still sync while the daemon is stopped, and `create`, `join` and `clone`
can start it again.

To remove one copy, [leave its hive](#take-a-repo-or-machine-out). Leaving attempts a
final sync, even with `musubi leave --force`; stop the daemon while deciding what to send.

## Take a repo or machine out

In a repo, `musubi leave` snapshots current files and sends the last work before leaving
the hive and stopping sync. Other machines stop showing its working copy (`laptop/default@`),
and the hub stops counting it. The repo keeps its files and history; other copies keep
what it sent. A working-copy commit with changes becomes an ordinary commit; an empty one
is dropped.

If the final sync fails, `musubi leave` fails and the repo stays in its hive.
`musubi leave --force` attempts the same sync but leaves even if it fails; other machines may
show the copy until one forgets it. Fix the reported cause and retry, or pause background
traffic with `musubi daemon stop` while deciding what to send.

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
`musubi status` say which is the new copy; forget the other by its name.

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

After leaving, run `musubi join` to rejoin. Joining a different hive brings the old shared
history and working-copy names along.

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
