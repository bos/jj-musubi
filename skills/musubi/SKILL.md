---
name: musubi
description: >
  Work in jj repositories on machines where musubi is installed. Use with the jj skill to
  check hive membership, choose a stable base, avoid disrupting other machines, and handle
  stale working copies or sync failures.
---

# musubi

musubi syncs jj's operation log through a hub. Copies in one **hive** behave like workspaces:
other machines appear as `laptop/default@`, and their operations appear in `jj op log`.

## Check hive membership once

After confirming that the repository uses jj, run `musubi status`. It reads local state
without contacting the hub or starting the daemon. Record the hive name for this session, or
`musubi: none` if the repository is outside a hive or musubi isn't installed. Check again only
after joining or leaving. Outside a hive, stop here unless the user asks to join one.

## Choose a base

Another machine can rewrite `@` or a mutable ancestor, making your working copy stale.
Updating it brings those edits into your files. If already stale, follow
[Update a stale working copy](#update-a-stale-working-copy) first. Then inspect the history:

```sh
jj log -r '(::@ & mutable()) | heads(::@ & immutable()) | working_copies()'
```

Use the nearest immutable ancestor, or `trunk()` for the latest trunk commit. Build on a
mutable change only if the task requires it, and inspect incoming rewrites after each stale
update. If the only immutable ancestor is `root()`, ask the user which base to use.

If `@` contains someone else's edits, preserve them and create a separate workspace on that
base; see the jj skill. Otherwise, start a new change on the chosen base; for example:

```sh
jj new 'latest(heads(::@ & immutable()))'
```

If your own edits are already in `@`, move that change instead, after checking for other
working copies as [described below](#avoid-disrupting-other-working-copies). For example:

```sh
jj rebase -r @ -d 'latest(heads(::@ & immutable()))'
```

The user can protect `main` from rewrites by making it immutable across the hive:

```sh
jj config set --repo 'revset-aliases."immutable_heads()"' \
  'builtin_immutable_heads() | present(main)'
```

## Avoid disrupting other working copies

Before a squash, rebase, split, abandon, or `jj fix`, check for other working copies on the
commits you would rewrite or their descendants. Replace `ROOTS` with those commits:

```sh
jj log -r '(ROOTS):: & working_copies() ~ @'
```

Changing their files makes the listed working copies stale. Put the fix in a new child
change, or ask before rewriting them. Description-only changes are safe.

- `jj rebase -b @` can move other people's mutable ancestors. Select your changes by change id.
- Revsets such as `empty()` and `mine()` can match other machines' commits. Use change ids.
- `jj op restore` moves every machine's working copy. `jj op abandon` permanently stops this
  copy syncing if it removes operations the hive already has. Run either only when asked.
- Forgetting a `<machine>/...` workspace removes it locally; it returns on a later sync.

Every working-copy snapshot replicates, even if you immediately abandon the change. Keep
secrets and bulky scratch files outside the repository, or ignore them before running jj.

## Update a stale working copy

When jj reports `The working copy is stale`, run:

```sh
jj workspace update-stale
jj log -r '::@ & mutable()'
```

Inspect the result:

- If another machine's rewrite changed files your task doesn't need, move your change to an
  immutable base: `jj rebase -r @ -d 'latest(heads(::@- & immutable()))'`.
- If `@` is divergent, your unsnapshotted edits may be in another version of the change.
  Inspect the versions with `jj log -r 'change_id(<change>)'`. If another commit contains your
  edits on the same parent, run `jj restore --from <other-commit-id>`, then
  `jj abandon <other-commit-id>`.

## Join or leave

Join or leave only when asked. `musubi list` shows hubs, hives, and this machine's copies.

- `musubi join` adds this copy to an existing hive; `musubi create` starts a hive;
  `musubi clone <hive> <dir>` makes a new copy. Each accepts `--hub <host>`, starts the daemon,
  and performs the first sync. For agents, `musubi.forget-after` defaults to six hours unused
  unless jj's config already sets it. Tell the user which setting applies.
- `musubi daemon install` starts the daemon at login. Don't run it or change
  `musubi.forget-after` unless asked; explain the effect when proposing either.
- `musubi leave` removes this copy from its hive and needs to reach the hub. Offer `--force`
  only if the hub is gone: other machines keep showing this copy until it is forgotten.

Update the session's recorded hive status after joining or leaving.

For missing work, failed musubi commands, or musubi errors from jj, follow
[Debugging musubi](references/debugging.md).
