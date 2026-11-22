# Work across machines

See other machines' work, update a stale working copy, undo, and configure each copy.

With jj-musubi, you use jj normally after joining a hive, the group of copies of one project.
Their daemons exchange history through the hub.

## Pick up on another machine

By default, jj creates a snapshot of your working directory for almost every command you run. My
shell prompt includes a call to `jj status`, so my shell creates a snapshot of my working copy
every time I run any command interactively.

So for me, there's no effort needed to snapshot and send one machine's work. jj-musubi syncs it
in the background and it shows up on other machines in moments. If you want to do this
explicitly, you can simply run `jj status` followed by `musubi sync` (which will probably have
run automatically on your behalf before you finish typing the explicit command).

The examples hand off from a laptop to a devbox; use the workspace names from `musubi status`.
If jj reports a stale working copy, [update it](#when-another-machine-rewrites-your-working-copy)
before continuing.

1. On your laptop, save your edits:

   ```sh
   jj status
   musubi sync    # for convenience, not necessary
   musubi status
   ```

   The `musubi sync` and `musubi status` commands are not usually necessary. Here, they're
   simply ways for you to verify that that jj-musubi is doing its job.

   When you look at the output of those commands, check for a recent successful sync and `the
   hub has all its work`.

2. In the devbox's repo, check that the laptop's recorded change has been received:

   ```sh
   musubi sync    # also for convenience, not necessary
   musubi status
   jj log
   jj diff -r laptop/default@
   ```

   As before, `musubi sync` and `musubi status` are just eyeball verification tools. I never run
   these commands in the normal course of events.

3. On your devbox, you can now check out the changes that were most recently snapshotted on your
   laptop:

   ```sh
   jj new laptop/default@   # a new change on top of the laptop's
   ```

   This checks out a child of the laptop's change without moving the laptop's checkout.

### Record saves automatically

Enable background snapshots on the machine doing the editing. Run this from a joined repo to
enable them for its local workspaces, including ones you add later.

```sh
jj config set --repo musubi.auto-snapshot true
```

Use `--workspace` to set it for one workspace or `--user` for all joined repos on the machine.
The daemon picks up config changes on its next periodic workspace scan. If you just replaced
the `musubi` executable, run `musubi daemon restart` to use the updated daemon.

The daemon checks for changes about five seconds after a filesystem notification. If jj has
`fsmonitor.backend = "watchman"` set, those checks use Watchman to find changed files. It also
scans the whole working copy every few minutes to catch missed notifications and changes to
global ignore rules. It records an operation only when the working-copy tree changes, and can
record edits while the hub is offline and send them when it reconnects.

Background snapshots read checked-out files and leave them in place. They wait if the workspace
is [stale](#when-another-machine-rewrites-your-working-copy), Git `HEAD` has moved, or a Git
operation is in progress. jj's ignore rules and jj-musubi's
[snapshot limits](snapshots.md) still apply. Keep secrets and scratch files ignored or outside
the repo before enabling this setting.

If edits aren't being recorded, check `musubi status` for a workspace warning. If Git moved
`HEAD`, run `jj status` in that workspace after your Git operation finishes so jj can import
the change. If jj has no location recorded for a workspace, run `jj status` in that workspace
to record its edits explicitly.

Musubi skips workspaces with jj's Watchman snapshot trigger enabled. To use musubi's background
snapshots there, set `fsmonitor.watchman.register-snapshot-trigger` to `false` at the same scope
and run `jj status` once in each affected workspace to unregister the trigger. Keep
`fsmonitor.backend = "watchman"` to use Watchman for background and interactive snapshots.
Use the same trigger setting in workspaces that share a Watchman project root, since Watchman
stores triggers on that root.

## Coding agents

Give each agent a workspace with `jj workspace add` so agents don't share files, as
`jj workspace add --name agent-2 ../agent-2`. If you pass `--name`, leave out `/`: a repo with
a workspace named like `agents/2` [doesn't sync](../how-it-works.md#other-machines-workspaces).
Their work appears on every machine as `devbox/default@` or `laptop/agent-2@`. Review it from
any machine:

```sh
jj log -r 'working_copies()'   # what every agent on every machine is working on
jj diff -r devbox/default@     # review one agent's change
```

[Enable background snapshots](#record-saves-automatically) to pick up edits even if an agent
never runs `jj`. [Pick up an agent's work](#pick-up-on-another-machine) as you would another
machine's.

Use `musubi status` to [check syncing](#see-what-other-machines-are-doing) before starting.
Copies stay in the hive until removed. For a temporary devbox, use `musubi join --lease 6h`
or `musubi clone <hive> <dir> --lease 6h` to forget it after six hours without a local operation.

The [`jj-musubi` skill](../../skills/jj-musubi/SKILL.md) helps agents choose a stable base,
avoid disrupting other machines, and handle stale copies and sync failures.

Link it into your agent's skills directory, replacing `~/src/jj-musubi` with your clone's path:

```sh
ln -s ~/src/jj-musubi/skills/jj-musubi ~/.claude/skills/jj-musubi   # Claude Code
ln -s ~/src/jj-musubi/skills/jj-musubi ~/.codex/skills/jj-musubi    # Codex
```

## See what other machines are doing

Workspace names in `jj log` show recorded work; unsnapshotted edits stay on their machine.
`jj op log` shows each machine's operations with the workspace that made them, such as
`laptop/default`.

`musubi status` reports this copy's last known sync and working copies without contacting the
hub or recording edits. It exits 0 even when reporting a problem. For all-machine reports,
logs and unattended checks, see [Monitor syncing](manage.md#check-syncing).

## When another machine rewrites your working copy

A rebase or squash on another machine can make your working copy stale. The next `jj` command
stops and says so:

```text
Error: The working copy is stale (not updated since operation dc4042ec91bd).
Hint: Run `jj workspace update-stale` to update it.
See https://docs.jj-vcs.dev/latest/working-copy/#stale-working-copy for more information.
```

`jj workspace update-stale` snapshots unrecorded edits before updating the files. Your
working-copy change may become divergent and need resolving.

To let `jj` commands update stale files automatically, set:

```sh
jj config set --user snapshot.auto-update-stale true
```

Then even `jj log` can change files under a build or editor. Set it on each machine where
you want that behavior.

## Undo across machines

`jj undo` refuses to undo another machine's operation, as it does another workspace's:

```text
Error: Refusing to undo operation bf73e005993e because it was performed in workspace laptop/default
Hint: Use `--allow-cross-workspace` to undo it anyway, or use `jj op revert` to revert a specific operation
```

Pass `--allow-cross-workspace` to undo it anyway. To revert one of this machine's operations
after others have arrived, use its id:

```sh
jj op log            # find the operation
jj op revert <id>
```

Undos, reverts and restores replicate like any other operation. `jj op restore` also puts
every machine's working copy back where it was, so other machines' working copies may become
stale.

## When machines change the same thing

Resolve a bookmark conflict or divergent change on any machine; the resolution syncs to the
others:

- A bookmark moved to different commits on two machines is conflicted everywhere, shown as
  `main??`. Move it once, anywhere, with `jj bookmark set main -r <rev>`.
- A change rewritten on two machines becomes divergent everywhere. Keep one version with
  `jj abandon <commit-id>`, or combine them with `jj converge`.
- A commit abandoned on one machine while another builds on it is rebased onto its parent,
  once.

In a colocated repo, sync updates the Git branches for resolved bookmarks moved by a merge.
A conflicted bookmark leaves each machine's branch where it is until you resolve it.

## Fetch and push

`jj git fetch` on one machine updates every copy's remote bookmarks and `.git` remote-tracking
refs. A `jj git push` shows as pushed everywhere.

Remote definitions stay local. Copies without remotes, or with unused matching remotes, still
receive Git results and share work. `musubi clone` adds none; it checks inherited global config,
including conditional includes for the new path, before creating the destination. To fetch or
push from another copy, configure a remote there:

```sh
jj git remote add origin https://github.com/you/app.git
```

A hive binds each remote name to its fetch and push destinations for its lifetime. `musubi join`
checks them even with `--hive` or when rejoining. A copy may omit a remote; a different repo
or push destination needs an unused remote name or another hive. Equivalent URL forms agree.

Renaming or removing a remote renames or removes shared bookmarks such as `main@origin`, but
leaves other machines' remote definitions alone. Coordinate before anyone fetches or pushes.
Join checks destinations at that time; it cannot inspect offline config or prevent later edits.

After changing a remote URL, run `musubi join` again to register it; the destination must
still match. See [configuration](../reference/configuration.md) and
[remote-name refusals](../troubleshooting.md#joining-is-refused)
if joining is refused.

## Configure each machine

jj config stays local, including `trunk()`, `immutable_heads()`, `git.private-commits`, aliases
and signing settings. Clone uses the destination's `trunk()`; its one-time defaults are chosen
[during setup](setup.md#optional-clone-defaults). See the [configuration
reference](../reference/configuration.md#settings) for config scope and reload behavior.

Set protections on every machine that needs them. `immutable_heads()` cannot prevent rewrites
elsewhere. `git.private-commits` limits that copy's Git pushes, not what jj-musubi shares.

## Abandoning operations

Don't run `jj op abandon` on operations the hive already has. The other machines keep them,
and this copy can't sync without them, so it stops syncing for good, with "this repository
lost history the hive has (was `jj op abandon` run?)". To carry on, make a new copy and bring
your work across, as the [new-copy rescue
steps](../troubleshooting.md#rescue-work-in-a-new-copy) say.

The daemon sends each operation to the hub soon after jj records it, so the hive has nearly
every operation. Two kinds of abandon are fine:

- Abandoning operations from before this copy joined its hive.
- Abandoning operations this copy hasn't sent yet, such as snapshots held back by the
  [snapshot limits](snapshots.md). Use `musubi sync --prune` for those instead: it refuses
  any operation this copy has tried to send, and keeps your current work. Add `--dry-run` to
  check without changing anything.

Abandoning an operation doesn't remove its data from disk, on this machine or any other. To
remove something from every machine, such as a secret committed by mistake, see [Clean up
history on every machine](manage.md#clean-up-history-on-every-machine).
