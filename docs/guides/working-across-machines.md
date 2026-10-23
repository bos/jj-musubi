# Work across machines

Once a repository is in a hive, keep using `jj` as you always do. This guide covers what
changes when other machines share the repository: what you see from them, how their changes
reach your working copy, undoing, concurrent changes, and the settings machines share.

## See what other machines are doing

`jj log` shows each other machine's working copy as a workspace named after the machine,
such as `laptop/default@`. Use it like any revision:

```sh
jj diff -r laptop/default@   # what the laptop is working on
jj new laptop/default@       # build on it here
```

These show what the laptop last snapshotted, which is whenever a `jj` command last ran there.
Edits it hasn't snapshotted yet stay on the laptop.

`jj op log` shows every machine's operations, each with the workspace that made it, such as
`laptop/default`, so you can tell what happened where.

`musubi list`, run in the repository, shows the same at a glance, with when it last synced:

```text
This repository:
  Hive:      app (8e1f6b0c-4d2a-4f57-9a43-0d5c6e7f8a9b)
  Hub:       devbox
  Machine:   desktop
             default@desktop is at 3f2a1c9e07b4
             default@laptop is at 8d0b4e11c2a7
  Last sync: synced 3s ago
  Hub head:  #412 5c0e9d7a3b21
```

## When another machine rewrites your working copy

When another machine changes the files of the commit your working copy is on, by rebasing it
onto new work or squashing into its parent, say, jj on this machine treats the working copy as
stale, as it would after the same change in another workspace. The next `jj` command stops
and says so:

```text
Error: The working copy is stale (not updated since operation dc4042ec91bd).
Hint: Run `jj workspace update-stale` to update it.
See https://docs.jj-vcs.dev/latest/working-copy/#stale-working-copy for more information.
```

Run `jj workspace update-stale` to update the files. If you had edits that `jj` hadn't
snapshotted yet, it snapshots them first, so they survive; at worst, your working-copy change
becomes divergent, and you resolve it as usual.

To have every `jj` command update a stale working copy by itself, set:

```sh
jj config set --user snapshot.auto-update-stale true
```

The trade-off is that then any `jj` command, even `jj log`, can change files under a running
build or an open editor. To set it for every machine at once, see [Share
settings](#share-settings).

## Undo across machines

`jj undo` undoes the latest operation, but refuses when another workspace made it, and to jj,
another machine is another workspace:

```text
Error: Refusing to undo operation bf73e005993e because it was performed in workspace laptop/default
Hint: Use `--allow-cross-workspace` to undo it anyway, or use `jj op revert` to revert a specific operation
```

That keeps `jj undo` on one machine from undoing what you just did on another. If you mean
to undo the other machine's operation, pass `--allow-cross-workspace`. To undo one of this
machine's own operations once others have arrived after it, revert it by id:

```sh
jj op log            # find the operation
jj op revert <id>
```

Undos, reverts and restores replicate like any other operation. `jj op restore` puts every
machine's working copy back where it was too, so the other machines' working copies may
become stale.

## When machines change the same thing

Changes made on different machines at once combine exactly as jj combines changes from two
`jj` commands run at once on one machine, and every machine ends up with the same result:

- A bookmark moved to different commits on two machines is conflicted everywhere, shown as
  `main??`. Move it once, anywhere, with `jj bookmark set main -r <rev>`.
- A change rewritten on two machines becomes divergent everywhere. Keep one version with
  `jj abandon <commit-id>`, or combine them with `jj converge`.
- A commit abandoned on one machine while another builds on it is rebased onto its parent,
  once.

In a colocated repository, a conflicted bookmark isn't exported to git, so each machine's
`.git` keeps its own branch until you resolve it.

[docs/internals/races.md](../internals/races.md) lists every case musubi tests, with its
outcome.

## Fetch and push from any machine

Remote bookmarks replicate, so a `jj git fetch` on one machine updates every machine's remote
bookmarks, and their `.git` remote-tracking refs. A `jj git push` on one machine shows as
pushed on all of them. There's no need to fetch on each.

## Share settings

Some settings live outside jj's operation log, in each machine's git and repo config, yet
machines need to agree on them. musubi shares these, and leaves the rest of each machine's
config alone.

### Git remotes

Adding, renaming, or removing a git remote, or changing its URL, on one machine does the same
on every machine. A machine's own spelling of a remote stays its own: one machine can reach
`origin` over https while another uses ssh, and neither changes the other's. Only pointing a
remote at a different repository replicates.

If a machine needs its own identity for a remote, such as an ssh key of its own, keep the
ordinary URL and rewrite it in that machine's user git config:

```sh
git config --global url."git@github-work:".insteadOf "git@github.com:"
```

A URL spelled with an ssh host alias names a host other machines don't know, so they couldn't
use it.

An https URL can carry a user and password, often a token meant for that machine alone.
musubi strips them before sharing the URL, and from the command line jj records with the
operation that added the remote. To share them anyway, set `musubi.share-credentials = true`
in that machine's jj config.

### Repo config

These keys of jj's repo config are shared, since they decide what is safe to rewrite or push:

- `revset-aliases."immutable_heads()"`
- `revset-aliases."trunk()"`
- `git.private-commits`
- `musubi.shared-config`

To share other keys, list them in `musubi.shared-config`, on any machine:

```sh
jj config set --repo musubi.shared-config '["snapshot.auto-update-stale", "aliases.l"]'
jj config set --repo snapshot.auto-update-stale true
```

A shared key is set in every machine's repo config, so it takes precedence over each
machine's user config. Other repo config stays each machine's own.

### When machines disagree

Each setting carries the time it was written, by the clock of the machine that wrote it.
If two machines change the same setting before either has synced, the later write wins on
every machine, and the daemon on the machine whose value was replaced logs the old and new
values. A machine whose clock is wrong can win when it shouldn't.

When a machine joins a hive, it takes the hive's value of each setting the hive has, and adds
its own others, such as a remote the hive doesn't have.

## Things to avoid

- **`jj op abandon`** of operations other machines already have. musubi can't yet replicate
  it, so it pauses syncing that repository, with an error, rather than bring the abandoned
  operations back. See [Syncing paused after
  `jj op abandon`](../troubleshooting.md#syncing-paused-after-jj-op-abandon). Abandoning
  only the operations from before the machine joined is fine.
- **A newer `jj`** than the one musubi supports, 0.46.0. musubi refuses an operation with
  fields it doesn't know, rather than drop them. Upgrade `jj` and musubi together.
- **Copying a repository's directory** to make another machine's copy. Use `musubi clone`,
  or clone from the remote and `musubi join`.
