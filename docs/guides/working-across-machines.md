# Work across machines

See other machines' work, update a stale working copy, undo, and configure each copy.

Keep using `jj` after joining a hive, the group of copies of one project. Their daemons exchange
history through the hub; each machine keeps its own checkout files.

## Pick up on another machine

First record and send the source machine's work, then receive and inspect it on the destination.
The examples hand off from a laptop to a devbox; use the workspace names from `musubi status`.
If jj reports a stale working copy, [update it](#when-another-machine-rewrites-your-working-copy)
before continuing.

1. On the laptop, save your edits and exclude generated or accidental files before recording:

   ```sh
   jj status
   musubi sync
   musubi status
   ```

   Check for a recent successful sync and `the hub has all its work`. This covers recorded
   work, not later edits. If sending is held, follow [snapshot recovery](snapshots.md) before
   switching machines. Keep secrets ignored; small accidental files can still sync.

2. In the devbox's copy, receive and inspect the laptop's recorded change:

   ```sh
   musubi sync
   musubi status
   jj log
   jj diff -r laptop/default@
   ```

   Check the sync report for errors and compare the change with the work you expected.
   A sender reporting that its work was sent doesn't establish that this receiver has it.

3. Build on it here:

   ```sh
   jj new laptop/default@   # a new change on top of the laptop's
   ```

   This checks out a child of the laptop's change without moving the laptop's checkout.

To return to the laptop, repeat the record/send and receive/inspect steps in the other direction,
then continue there with:

```sh
jj new devbox/default@
```

### Record saves automatically

Edits sync after jj records them. To record each save, install
[watchman](https://facebook.github.io/watchman/) and enable its jj trigger:

```sh
jj config set --user fsmonitor.backend watchman
jj config set --user fsmonitor.watchman.register-snapshot-trigger true
```

## Coding agents

Give each agent a workspace with `jj workspace add` so agents don't share files. Their work
appears on every machine as `devbox/default@` or `laptop/agent-2@`. Review it from any machine:

```sh
jj log -r 'working_copies()'   # what every agent on every machine is working on
jj diff -r devbox/default@     # review one agent's change
```

[Pick up an agent's work](#pick-up-on-another-machine) as you would another machine's.

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

In a colocated repository, a conflicted bookmark isn't exported to git, so each machine's
`.git` keeps its own branch until you resolve it.

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
[remote-name refusals](../troubleshooting.md#remote-names--have-different-fetch-or-push-destinations-than-hive--recorded)
if joining is refused.

## Configure each machine

jj config stays local, including `trunk()`, `immutable_heads()`, `git.private-commits`, aliases
and signing settings. Clone uses the destination's `trunk()`; its one-time defaults are chosen
[during setup](setup.md#choose-clone-defaults). See the [configuration
reference](../reference/configuration.md#settings) for config scope and reload behavior.

Set protections on every machine that needs them. `immutable_heads()` cannot prevent rewrites
elsewhere. `git.private-commits` limits that copy's Git pushes, not what jj-musubi shares.

## Abandoning operations

`jj op abandon` removes operations from every machine's log, including offline members when
they return. Remaining operations keep their repo state, but descendants get new ids:
ids saved from `jj op log` no longer work. jj-musubi logs this as
`musubi: pass on jj op abandon`.

An offline member can return and take the abandon. If all remaining members took an abandon
while a copy was forgotten or out of the hive, that copy cannot sync again. The same can
happen to a copy away before its first `musubi join` or `musubi clone` sync finished: after a
day without contact, or an hour after a hub restart. It reports "this repository's history
no longer matches the hive's"; follow the [new-copy recovery
steps](../troubleshooting.md#this-repositorys-history-no-longer-matches-the-hives-so-it-cant-sync-again).

A command already running when the abandon arrives, such as `jj git fetch`, still syncs its
work. If another command merges it before jj-musubi sees it, bookmarks changed by the first
command can conflict. Set them again with `jj bookmark set`, as after `jj op abandon` on one
machine.
