# Work across machines

Once a repository is in a hive, keep using `jj` as you always do. This guide covers what
changes when other machines share it: picking up on another machine, coding agents, seeing
other machines' work, stale working copies, undo, concurrent changes, and the settings machines
share.

## Pick up on another machine

Close the laptop, and sit down at the desktop. In the same repository there, the laptop's
working copy is already in `jj log`, as `laptop/default@`. Carry on from it:

```sh
jj new laptop/default@   # a new change on top of the laptop's
```

When you open the laptop again, its daemon reconnects and brings in what you did on the
desktop; there's nothing to run.

What reaches the desktop is the laptop's work as of its last `jj` command, since that's when
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
share files; every machine then shows each agent's working copy, as `devbox/default@` or
`laptop/agent-2@`. From any machine:

```sh
jj log -r 'working_copies()'   # what every agent on every machine is working on
jj diff -r devbox/default@     # review one agent's change
jj new devbox/default@         # build on it here, or hand it to another agent
```

`musubi status` answers at once, so an agent can check that its repository syncs, and see the
other machines' working copies, before it starts. A copy that an agent joins or clones is
forgotten by itself after 6 hours unused (`musubi.forget-after`), so a short-lived devbox
doesn't linger in every machine's `jj log`.

Another machine's rewrites can repeatedly make a coding agent's working copy stale. The
[`musubi` skill](../../skills/musubi/SKILL.md) helps agents choose a stable base, avoid
disrupting other machines, and handle stale copies and sync failures.

To install it, link it into your agent's skills directory. Replace `~/src/jj-musubi` with the
path to your clone:

```sh
ln -s ~/src/jj-musubi/skills/musubi ~/.claude/skills/musubi   # Claude Code
ln -s ~/src/jj-musubi/skills/musubi ~/.codex/skills/musubi    # Codex
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
Hive: app on devbox, at #412
This machine: desktop, synced 3s ago; the hub has all its work
Working copies:
default@: kxqpwzlm 3f2a1c9e fix the parser
laptop/default@: vruxwmqv 8d0b4e11 (no description set)
Copies:
desktop (this machine): used 1m ago, never forgotten
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
or an open editor. To set it on every machine at once, [share it](#share-settings).

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

## Fetch and push from any machine

Remote bookmarks replicate, so `jj git fetch` on one machine updates every machine's remote
bookmarks and their `.git` remote-tracking refs; there's no need to fetch on each. A
`jj git push` on one machine shows as pushed on all of them.

## Share settings

Some settings live outside jj's operation log, in each machine's git and repo config, yet
machines need to agree on them. musubi shares these, and leaves the rest of each machine's
config alone.

### Git remotes

Adding, renaming or removing a git remote on one machine, or pointing it at a different
repository, does the same on every machine. Each machine keeps its own spelling of a URL: one
can reach `origin` over https while another uses ssh, and neither changes the other's.

If a machine needs its own identity for a remote, such as an ssh key of its own, keep the
ordinary URL and rewrite it in that machine's user git config, since other machines wouldn't
know an ssh host alias in the URL itself:

```sh
git config --global url."git@github-work:".insteadOf "git@github.com:"
```

An https URL can carry a user and password, often a token meant for that machine alone.
musubi strips them before sharing the URL, and from the command line that jj records with
the operation that added the remote. To share them anyway, set
`musubi.share-credentials = true` in that machine's jj config.

### Repo config

The hive always shares the repo config keys that decide what is safe to rewrite or push, such
as `revset-aliases."trunk()"` and `revset-aliases."immutable_heads()"` ([the full
list](../reference/configuration.md#each-repositorys)). To share other keys, list them in
`musubi.shared-config`, on any machine:

```sh
jj config set --repo musubi.shared-config '["snapshot.auto-update-stale", "aliases.l"]'
jj config set --repo snapshot.auto-update-stale true
```

A shared key is set in every machine's repo config, so it takes precedence over each
machine's user config. Other repo config stays each machine's own.

### When machines disagree

Each setting carries the time it was written, by the clock of the machine that wrote it. If
two machines change the same setting before either has synced, the later write wins
everywhere, and the daemon on the machine whose value was replaced logs the old and new
values. A machine whose clock is wrong can win when it shouldn't.

A machine joining a hive takes the hive's value for each setting the hive has, and adds the
others it has, such as a remote the hive lacks.

## Things to avoid

- **`jj op abandon`** of operations other machines already have. musubi can't replicate it
  yet, so it pauses syncing that repository with an error rather than bring the abandoned
  operations back. See [Syncing paused after
  `jj op abandon`](../troubleshooting.md#syncing-paused-after-jj-op-abandon). Abandoning only
  operations from before the machine joined is fine.
- **A newer `jj`** than the one musubi supports, 0.46.0. musubi refuses operations with fields
  it doesn't know rather than drop them. [Upgrade jj and musubi
  together](manage.md#upgrade-musubi).
- **Copying a repository's directory** to make another machine's copy. Use `musubi clone`, or
  clone from the remote and `musubi join`.
