# Work across machines

See other machines' work, update a stale working copy, undo, and configure each copy.

Once a repository is in a hive, keep using `jj` as you always do. Its daemon keeps it in sync
with the other machines.

## Pick up on another machine

Stop work on the laptop, and pick it up on the devbox. In the same repository there, the change
the laptop was working on is already in `jj log`, as `laptop/default@`. Carry on from it:

```sh
jj new laptop/default@   # a new change on top of the laptop's
```

When you open the laptop again, its daemon reconnects and brings in what you did on the
devbox; there's nothing to run.

What reaches the devbox is the laptop's work as of its last `jj` command, since that's when
jj records edits. To have jj record them each time you save a file, without running a command,
turn on its [watchman](https://facebook.github.io/watchman/) trigger, with watchman installed:

```sh
jj config set --user fsmonitor.backend watchman
jj config set --user fsmonitor.watchman.register-snapshot-trigger true
```

Everything jj records reaches every machine, so keep secrets in ignored files.

## Coding agents

Agents working on several machines in one repository see each other's work as you do. Give
each agent on a machine its own jj workspace, with `jj workspace add`, so that agents don't
share files; every machine then shows the change each agent is working on, as
`devbox/default@` or `laptop/agent-2@`. From any machine:

```sh
jj log -r 'working_copies()'   # what every agent on every machine is working on
jj diff -r devbox/default@     # review one agent's change
jj new devbox/default@         # build on it here, or hand it to another agent
```

`musubi status` answers at once, so an agent can check that its repository syncs, and see the
other machines' working copies, before it starts. Persistent copies stay in the hive until
you take them out. For a short-lived devbox, use `musubi join --lease 6h` or
`musubi clone <hive> <dir> --lease 6h`: the hive forgets that copy after six hours without a
local operation, so it doesn't linger in every machine's `jj log`.

Another machine's rewrites can repeatedly make a coding agent's working copy stale. The
[`jj-musubi` skill](../../skills/jj-musubi/SKILL.md) helps agents choose a stable base, avoid
disrupting other machines, and handle stale copies and sync failures.

To install it, link it into your agent's skills directory. Replace `~/src/jj-musubi` with the
path to your clone:

```sh
ln -s ~/src/jj-musubi/skills/jj-musubi ~/.claude/skills/jj-musubi   # Claude Code
ln -s ~/src/jj-musubi/skills/jj-musubi ~/.codex/skills/jj-musubi    # Codex
```

## See what other machines are doing

`jj log` shows each other machine's working copy as a workspace named after the machine, such
as `laptop/default@`. Use it like any revision:

```sh
jj diff -r laptop/default@   # what the laptop is working on
jj new laptop/default@       # build on it here
```

This is what the laptop last snapshotted, when a `jj` command last ran there. Edits it hasn't
snapshotted yet stay on the laptop.

`jj op log` shows every machine's operations, each with the workspace that made it, such as
`laptop/default`.

`musubi status`, run in the repository, shows each machine's working copy at a glance, when
this copy last synced, and whether the hub has its latest work:

```text
Hive: app on devbox
This machine: devbox, synced 3s ago; the hub has all its work
Working copies:
default@: kxqpwzlm 3f2a1c9e fix the parser
laptop/default@: vruxwmqv 8d0b4e11 (no description set)
Copies:
devbox (this machine): used 1m ago, never forgotten
laptop: used 2h ago, never forgotten
Daemon: running (pid 4182), serving this repository; starts at login
Daemon socket: /run/user/1000/musubi/daemon.sock
Daemon log: /home/you/.local/state/musubi/daemon.log
```

## When another machine rewrites your working copy

If another machine changes the commit your working copy is on, say by rebasing it or squashing
it into its parent, jj here treats the working copy as stale, as it would after the same
change in another workspace. The next `jj` command stops and says so:

```text
Error: The working copy is stale (not updated since operation dc4042ec91bd).
Hint: Run `jj workspace update-stale` to update it.
See https://docs.jj-vcs.dev/latest/working-copy/#stale-working-copy for more information.
```

Run `jj workspace update-stale` to update the files. Edits that `jj` hadn't snapshotted yet
are snapshotted first, so they survive; at worst, your working-copy change becomes divergent,
and you resolve it as usual.

To have every `jj` command update a stale working copy by itself, set:

```sh
jj config set --user snapshot.auto-update-stale true
```

The cost is that any `jj` command, even `jj log`, can then change files under a running build
or an open editor. Set it separately on each machine where you want that behavior.

## Undo across machines

To jj, another machine is another workspace, so `jj undo` refuses to undo an operation that
another machine made:

```text
Error: Refusing to undo operation bf73e005993e because it was performed in workspace laptop/default
Hint: Use `--allow-cross-workspace` to undo it anyway, or use `jj op revert` to revert a specific operation
```

That keeps `jj undo` here from undoing what you just did on another machine. To undo the other
machine's operation anyway, pass `--allow-cross-workspace`. To undo one of this machine's own
operations after others have arrived, revert it by id:

```sh
jj op log            # find the operation
jj op revert <id>
```

Undos, reverts and restores replicate like any other operation. `jj op restore` also puts
every machine's working copy back where it was, so other machines' working copies may become
stale.

## When machines change the same thing

Changes made on different machines at once combine as jj combines two `jj` commands run at
once on one machine ([How musubi works](../how-it-works.md#when-machines-change-the-same-thing)).
To resolve what that leaves:

- A bookmark moved to different commits on two machines is conflicted everywhere, shown as
  `main??`. Move it once, anywhere, with `jj bookmark set main -r <rev>`.
- A change rewritten on two machines becomes divergent everywhere. Keep one version with
  `jj abandon <commit-id>`, or combine them with `jj converge`.
- A commit abandoned on one machine while another builds on it is rebased onto its parent,
  once.

In a colocated repository, a conflicted bookmark isn't exported to git, so each machine's
`.git` keeps its own branch until you resolve it.

## Fetch and push

Remote bookmarks replicate, so `jj git fetch` on one machine updates every machine's remote
bookmarks and their `.git` remote-tracking refs; there's no need to fetch on each. A
`jj git push` on one machine shows as pushed on all of them.

Git remote definitions stay local. You can use one machine for all upstream fetches and
pushes. Other copies can have no remotes, or keep matching remotes as unused declarations;
they still receive Git results through musubi and can commit, rewrite, and share work.
`musubi clone` adds no Git remotes. It checks any remotes inherited from global Git config,
including conditional includes for the new copy's path, before creating the destination.
To use another copy for Git access, configure it explicitly:

```sh
jj git remote add origin https://github.com/you/app.git
```

A remote name is bound to its fetch and push destinations for the lifetime of a hive.
`musubi join` checks every configured remote against those bindings before joining, including
when you choose `--hive` or rejoin. A copy may omit a remote. Equivalent URL forms agree,
but a different repository or push destination needs an unused remote name or another hive.

Remote bookmarks such as `main@origin` are shared by name. A rename or removal also renames
or removes the shared remote bookmarks, while leaving the other machines' configured remotes
alone. Coordinate those changes before another machine fetches or pushes. The preflight
checks reported destinations at join time; it cannot inspect an offline machine's current
files or prevent you changing local config afterwards.

Each machine can use its own equivalent URL and credentials. Git aliases are expanded before
checking destinations; an SSH host alias that normalizes to a different host is a mismatch. musubi
records credential-free URL hints when a copy explicitly joins, to match later copies to
the hive. Bracketed IPv6 forms such as `git@[2001:db8::1]:team/project.git` and
`ssh://git@[2001:db8::1]/team/project.git` match for joining. After changing a remote URL,
run `musubi join` again to register an equivalent URL. `--hive` chooses a hive; it never
bypasses the destination check.
Credentials are stripped from these hints and from URLs in jj's recorded command arguments.

## Configure each machine

jj user, repo, and workspace config stay local. This includes `trunk()`, `immutable_heads()`,
`git.private-commits`, aliases, and signing settings. `musubi clone` uses the destination
machine's config to evaluate `trunk()` and adds no Git remotes.

When a hive is created or recreated after hub loss, it records the creating copy's configured
`user.name` and `user.email` as defaults for future clones. Clone fills missing values in its new
repo config, leaving existing destination settings alone, even when they differ. When they are
already configured, it creates no identity overrides. This happens once; later changes on any
machine do not update the defaults or other copies.

To choose other keys, set `musubi.clone-config` before `musubi create`, for example:

```sh
jj config set --repo musubi.clone-config '["user.name", "user.email", "aliases.l"]'
```

The list replaces the default selection; `[]` records no defaults. Choose portable settings:
signing keys, tool paths, and filesystem watchers belong to each machine. Aliases and
repository protections may depend on other aliases or remote names; include what they need,
or configure them locally. `musubi.forget-after` remains each copy's own policy and cannot
be selected. Rejoining an existing hive never changes its recorded clone defaults. If a hub is
lost or replaced, the first copy to recreate the hive supplies fresh defaults.

Set any protection you need on every machine where it matters. A local `immutable_heads()`
rule cannot prevent another machine rewriting shared history. `git.private-commits` controls
that machine's Git pushes; it does not keep commits out of musubi. All committed and
snapshotted work replicates to the hive.

After changing jj settings, `musubi sync` waits for a sync with the new settings. A sync
already in progress finishes using its earlier settings. Joining or cloning can set this
copy's local `musubi.forget-after` default; sync does not copy config values from other
machines.

## Abandoning operations

`jj op abandon` works across machines. The operations you abandon go from every machine's
operation log, as from this one's, and never come back, even from a machine that was offline
at the time, so think of it as abandoning them on every machine. As with jj on one machine,
the repository stays as it was at each operation that's left, and the operations after the
abandoned ones get new ids: ids you noted from `jj op log` on any machine no longer work.
musubi adds an operation to the log saying so, `musubi: pass on jj op abandon`.

Trimming every operation already shared with the hive, beneath new work that has not synced
there yet, keeps the other machines in the hive too. Their next sync takes the abandon as
usual, even if they were offline while you trimmed the history.

Trimming all earlier history keeps each copy's own Git refs and HEAD as they were, including
when a sync is finishing as you trim. Other copies remain in the hive or forgotten as they
were, including when the trim removes a forget that the hub just accepted.

The hub remembers an abandon until every machine still in the hive has taken it, so a machine
that's offline delays this until it syncs. Then the hub forgets it, so trimming old history
with `jj op abandon ..<operation>` doesn't leave the hub remembering every abandoned operation,
though it keeps them on its disk. A copy that was away when the abandon happened, forgotten with
`musubi forget` or by its `musubi.forget-after`, or out with `musubi leave`, can't sync again when
it comes back: it stops with "this repository's history no longer matches the hive's" ([what to
do](../troubleshooting.md#this-repositorys-history-no-longer-matches-the-hives-so-it-cant-sync-again)).

A `jj` command that was already running on another machine when the abandon reached it,
such as a long `jj git fetch`, still syncs its work. If a second command there merges that
work before musubi has seen it, bookmarks the first one changed can come out conflicted, as
they can after `jj op abandon` on one machine: set them again with `jj bookmark set`.

## Things to avoid

- **A newer `jj`** than the one musubi supports, 0.47.1. Operations with unknown fields stop
  the sync. [Upgrade jj and musubi
  together](manage.md#upgrade-musubi).
- **Copying a repository's directory** to make another machine's copy. Use `musubi clone`, or
  clone from the remote and `musubi join`.
