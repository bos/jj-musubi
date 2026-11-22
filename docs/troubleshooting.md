# Troubleshooting

Figure out why work isn't arriving on another machine, fix common setup problems, or rescue work
from a copy that can no longer sync.

## Start with this copy

In the affected repository, run:

```sh
musubi status
```

This reads local state without contacting the hub or snapshotting files. It exits 0 even
when reporting a problem, and its last sync report can be stale if the daemon has stopped.
The hub passes work between machines; each machine's daemon syncs its local copies with it.

Follow the symptom:

- **The daemon isn't running or serving this copy:** see [The daemon](#the-daemon).
- **The hub is unreachable:** see [Reaching the hub](#reaching-the-hub).
- **Sending is held:** see [Accidental files and cleanup](#accidental-files-and-cleanup).
- **This repository lost history the hive has:**
  [rescue work in a new copy](#rescue-work-in-a-new-copy).
- **Hive … is paused:** `musubi pause` stopped every machine syncing it; see [Pause a whole
  hive](guides/manage.md#pause-a-whole-hive).
- **Hive … was reset:** `musubi resume` in another copy made the hive again without its old
  history; replace this copy with a new one, as [On the other
  machines](guides/manage.md#on-the-other-machines) says.
- **Another sync error:** follow the command's hint, fix the cause, then run `musubi sync`.
  If it persists, [collect the logs](#report-a-problem).

“The hub has all its work” means work jj has recorded reached the hub. It doesn't include
unsnapshotted file edits, or establish that another machine received it.

If work reached the hub but hasn't arrived elsewhere, run `musubi status` on the receiving
machine. `musubi top` shows all machines' last reports; a sleeping machine will catch up when it
reconnects. See [Check syncing](guides/manage.md#check-syncing).

If recorded work arrived but the checkout is stale, run `jj workspace update-stale`. See
[When another machine rewrites your working
copy](guides/working-across-machines.md#when-another-machine-rewrites-your-working-copy).

## Reaching the hub

Run `musubi list` to check the connection. For a remote hub, check ssh and the executable
from this machine, replacing `devbox` with the hub's ssh name:

```sh
ssh devbox true
ssh devbox musubi --version
```

If ssh fails or waits for input, fix that first. The daemon never prompts and uses jj-musubi's
own key with your `~/.ssh/config`; a successful interactive login alone doesn't establish
that it can connect. If its key is refused, run `musubi join --hub devbox` interactively in
the affected copy to authorize it again.

If ssh can't find `musubi`, add its directory to `PATH` in `~/.zshenv` or `~/.bashrc`
before any early return for non-interactive shells. Alternatively, set the absolute
[SSH command path](reference/configuration.md#ssh).

On the hub's machine, check that `musubi hub` is running and inspect its
[log](reference/configuration.md#logging). If it serves with `--dir`, its entry in
`~/.ssh/authorized_keys` needs `command="musubi hub connect --dir <dir>"` too.
For a hub that stops at logout or reboot, see
[service setup](guides/setup.md#keep-the-hub-running).

For an incompatible protocol or a daemon running an older build, follow
[Upgrade jj-musubi](guides/upgrading.md). The hub and machines need the same release or source
build. For a missing hive on a replaced hub, follow
[Replace or move a hub](guides/manage.md#replace-or-move-a-hub).

Once the cause is fixed, run `musubi sync`. The daemon also retries automatically;
a large first sync can take time and shows progress in a terminal.

## The daemon

Run `musubi daemon start` to resume background syncing, or `musubi daemon install` to start it now
and at login (at boot on illumos). On Linux, the installed daemon stops at logout unless you run
`loginctl enable-linger`. `create`, `join` and `clone` start the daemon without installing login
startup.

If a running daemon doesn't serve this copy, run `musubi join` here again. For a duplicate
copy after a move, restore or state-directory change, follow
[Move, copy or restore a repo](guides/manage.md#move-copy-or-restore-a-repo).

If it won't start or answer, inspect the [daemon log](reference/configuration.md#logging).
Use the same socket setting in every shell; see
[Configuration](reference/configuration.md#environment-variables). For a socket that disappeared,
`musubi daemon restart` restarts it.

To stop background traffic while investigating, run `musubi daemon stop`. This stops syncing
all copies on this machine. `musubi leave` attempts a final sync, even with `--force`; see
[Stop syncing on this machine or leave](guides/manage.md#stop-syncing-on-this-machine-or-leave).

### illumos

For where SMF logs the daemon and hub, and the rights profile setting them up needs, see
[illumos](guides/setup.md#illumos); `svcs -xv svc:/site/musubi/daemon:<you>` (or `.../hub:<you>`)
says why one isn't running.

**The service is in maintenance:** SMF stopped restarting it because it kept exiting, or killed
it because it didn't stop within a minute of being asked; `svcs -xv` and the log it names say
why. Fix that, then run `musubi daemon start`, or for the hub, `musubi hub install` again with
the `--dir` you installed it with.

## Joining is refused

`musubi join` matches this repo to a hive: the copies of one project known to a hub.
Run `musubi list` to check the hub and hive names.

If several hives match, or history matches but remote URLs don't, choose the intended hive
with `musubi join --hive <name>`. This still requires shared history. Use `musubi create`
to start a separate hive, or `musubi clone <hive> <new-directory>` to get a copy of an existing
one. Clone needs a new or empty directory; it also avoids shallow-clone and object-hash
mismatches.

A remote name must have the same fetch and push destinations across a hive. `--hive` doesn't
bypass that check. Give a different destination an unused name, for example
`jj git remote rename origin fork`, then retry. Renaming does not release the old name's
binding. See [Fetch and push](guides/working-across-machines.md#fetch-and-push).

A filesystem copy duplicates the original's identity. Use `musubi clone` for another syncing
copy; use `musubi join --original` for a move or restore only once the original is gone.
See [Move, copy or restore a repo](guides/manage.md#move-copy-or-restore-a-repo).

If the first sync fails after joining or cloning, the repo is set up and the daemon keeps
trying. Fix the reported cause and run `musubi sync`; don't delete the repo to retry setup.

## Remote bookmarks remain conflicted after joining

`musubi join` and `musubi create` try fetching the conflicted bookmarks after their first
sync, with a 30-second limit per remote. If a remote is unavailable or isn't configured here,
the copy still joins and keeps the conflict. Restore access and run `musubi join` again, or
fetch the affected bookmark on a machine with access to that remote:

```sh
jj git fetch --remote exact:origin --branch exact:main
musubi sync
```

Use the remote and bookmark named by `jj bookmark list --all-remotes`. Exact branch selectors
override configured fetch filters that might otherwise omit the bookmark. Quote names as jj's
string-pattern syntax requires, or use `musubi join` to select them automatically. Add
`--ignore-working-copy` if the checkout is stale, to update recorded state without changing
checkout files. The resolution syncs to other copies. Local bookmark conflicts can
remain when the copies also have local changes; resolve those as described in
[When machines change the same thing][same-thing].

[same-thing]: guides/working-across-machines.md#when-machines-change-the-same-thing

Neither commit dates nor which copy joined last establishes which rewritten upstream target
is current. A fetch asks the remote for a fresh observation. Ordinary syncs never fetch Git
remotes automatically.

## Accidental files and cleanup

A snapshot hold pauses sending while receiving continues. Inspect the held history without
snapshotting files or contacting the hub:

```sh
musubi sync --outgoing
```

Follow [Snapshot limits and cleanup](guides/snapshots.md) to exclude accidental files, prune
their snapshots, or approve wanted history. Restarting the daemon doesn't clear a hold.

Before removing operations, cleanup snapshots current edits and deletions in the invoking
workspace. If cleanup is refused, it discards no operations, but that snapshot may remain. Follow
its hint to update a stale workspace or restore access to a missing one, then retry. If a
workspace is gone and no longer needed, remove its entry with `jj workspace forget <workspace>`.
If two workspace names share a path, restore their separate directories or forget the obsolete
workspace. Otherwise try a smaller selection, or approve the inspected history only if you want
all of it shared.

If the command says "cleanup finished, but workspace metadata could not be updated", history
was already pruned. Restore write access to the named workspaces' metadata, then run `jj status`
there and follow any recovery hint. Native jj recovery may restore discarded history. Inspect
`musubi sync --outgoing` again and prune the newly reported operations if needed; the original
operation ids may no longer exist. The history rewrite and metadata updates leave checked-out
files untouched; the preceding snapshot follows jj's normal colocated Git import/export behavior
and may update checkout files.

To recover wanted files without approving held history, make a new copy with `musubi clone
<hive> <new-directory>` and copy only the files you want into it. Don't copy `.jj` or `.git`.
Describe or commit the copied work with jj, then run `musubi sync` there. Keep the original
until you've checked the wanted work on another machine. For whole commits, use the rescue
below; fetching also brings ancestors, which may contain unwanted content.

## Rescue work in a new copy

If the error says this repo lost history the hive has, retrying or rejoining won't help:
`jj op abandon` removed operations that the hub and other machines still have ([Abandoning
operations](guides/working-across-machines.md#abandoning-operations)). `musubi status` shows
the same message. Keep the original repo: its work is still there.

To make this copy's history the hive's instead, run `musubi pause` and `musubi resume` here:
see [Clean up history on every
machine](guides/manage.md#clean-up-history-on-every-machine). That replaces every other copy
with this copy's state, which may be behind theirs: `musubi resume` then needs `--force`, and
work this copy hadn't received must be brought across by hand from each other machine.

Otherwise, make a new copy with `musubi clone <hive> <new-directory>`, which refuses a paused
hive until `musubi pause --cancel` or `musubi resume`. Bring across work since the last
successful sync, or all wanted work if the first sync never finished. You can copy files as
above, or transfer commits:

1. In the original copy, choose the commits you need. If rescuing held history, check their
   ancestors for unwanted content before fetching; transfer
   [only wanted files](#accidental-files-and-cleanup) if you cannot safely bring whole commits.
   Give each tip a temporary bookmark (`jj log` shows them), export it, and print the Git
   data directory:

   ```sh
   jj bookmark create rescue-1 -r <change>
   jj git export
   jj git root
   ```

2. In the new copy, fetch and track those bookmarks, then remove the temporary remote:

   ```sh
   jj git remote add rescue <the path jj git root printed>
   jj git fetch --remote rescue -b 'rescue-*'
   jj bookmark track 'rescue-*' --remote rescue
   jj git remote remove rescue
   ```

3. Inspect the rescued work with `jj log` and `jj diff`. If changes are divergent because
   the hive rewrote their ancestors, rebase your work onto the hive's versions before
   abandoning the old ones. Run `musubi sync` and check the work on another machine.

After checking the rescue, run `musubi leave --force` in the original copy. It keeps that
repo and still attempts a final sync before leaving.

## Report a problem

If a failure persists after following its hint, [open an
issue](https://github.com/bos/jj-musubi/issues). Include the command and full error,
`musubi --version` on the affected machine and hub, and the relevant
[daemon and hub logs](reference/configuration.md#logging).

For “the hub refused this machine's work”, include both logs: the hub's log identifies what
it couldn't accept. To continue working, use the [new-copy rescue](#rescue-work-in-a-new-copy).
If a copy says it lost history the hive has even though no one ran `jj op abandon` there,
report that too.
