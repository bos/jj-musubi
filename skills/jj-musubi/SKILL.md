---
name: jj-musubi
description: >
  Work in jj repositories on machines where musubi is installed. Use before starting work in
  such a repository, before choosing a base or rewriting commits there, when jj says the
  working copy is stale, and when a musubi command or sync fails.
---

# jj-musubi

musubi syncs jj's operation log through a hub. Copies in one **hive** behave like workspaces:
other machines appear as `laptop/default@`, and their operations appear in `jj op log`.

## Check hive membership once

After confirming that the repository uses jj, run `musubi status`. It reads local state
without contacting the hub or starting the daemon. Record for this session the hive name it
shows, or that there is none: the repository isn't part of a hive, or musubi isn't installed.
Check again only after joining or leaving. Outside a hive, stop here unless the user asks to
join one.

## Choose a base

Another machine can rewrite `@` or a mutable ancestor, making your working copy stale.
Updating it changes the files in your checkout to match that machine's rewrite. If already
stale, follow [Update a stale working copy](#update-a-stale-working-copy) first. Then list
your mutable ancestors, the nearest immutable one, and every machine's working copy:

```sh
jj log -r '(::@ & mutable()) | heads(::@ & immutable()) | working_copies()'
```

Use the nearest immutable ancestor, or `trunk()` for the latest trunk commit. Build on a
mutable change only if the task requires it, and inspect incoming rewrites after each stale
update. If the only immutable ancestor is `root()`, ask the user which base to use.

Run `jj diff -s` before you edit anything: the files it lists that you haven't edited
yourself aren't yours. If there are any, work in place, and ask the user before editing one
of those files. Don't put `@` on another commit (`jj new`, `jj edit`), and don't restore,
abandon, or describe it while it holds those edits. After editing, commit only your paths,
which makes your change `@-` and leaves the other edits pending in `@`; fold later edits into
it with `squash`:

```sh
jj commit -m MESSAGE PATHS
jj squash -u --into @- PATHS
```

Until you move it, your change stays the parent of `@`, so its files remain in the checkout
for building and testing. When the task is done, move it onto the chosen base by its change id
with `jj rebase -r CHANGE -d BASE`. jj rebases `@` onto your change's old parent, so the other
edits stay in the checkout but yours leave it. Before squashing or rebasing, check for other
working copies as [described below](#avoid-disrupting-other-working-copies). Run `jj diff -s`
again before each commit; if files you didn't touch have changed, someone is editing live, so
ask the user before going on.

If `@` holds no one else's edits, start a new change on the chosen base; for example:

```sh
jj new 'latest(heads(::@ & immutable()))'
```

If your own edits are already in `@`, move that change instead, after checking for other
working copies as [described below](#avoid-disrupting-other-working-copies). For example:

```sh
jj rebase -r @ -d 'latest(heads(::@ & immutable()))'
```

The user can protect `main` from rewrites by making it immutable across the hive. Suggest it;
don't set it unasked:

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
- `jj op restore` moves every machine's working copy, and `jj op abandon` removes operations
  from every machine's operation log. Run either only when asked.
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

- If another machine's rewrite changed files your task doesn't need, move your change onto
  an immutable base as [Choose a base](#choose-a-base) says.
- If `@` is divergent, your unsnapshotted edits may be in another version of the change.
  List the versions with `jj log -r 'change_id(<id>)'`, using `@`'s change id. If another
  version has the same parent and `jj diff --from @ --to <other-commit-id>` shows only your
  edits, run `jj restore --from <other-commit-id>`, then `jj abandon <other-commit-id>`.
  Otherwise, ask the user.

## Join or leave

Join or leave only when asked. `musubi list` shows hubs, hives, and this machine's copies.

- `musubi join` adds this copy to an existing hive; `musubi create` starts a hive;
  `musubi clone <hive> [<dir>]` makes a new copy. Each accepts `--hub <host>`, starts the
  daemon, and performs the first sync. Copies default to `musubi.forget-after = "never"`,
  including when an agent joins them. Keep that default on a user's persistent machine. When
  setting up an explicitly temporary copy, pass `--lease 6h`: the hive forgets the copy after
  six hours without a local operation. Without `--lease`, existing configured policies are
  kept.
- `musubi daemon install` starts the daemon at login. Don't run it or change
  `musubi.forget-after` unless asked; explain the effect when proposing either.
- `musubi leave` removes this copy from its hive and needs to reach the hub. Offer `--force`
  only if the hub is gone: other machines keep showing this copy until it is forgotten.

Update the session's recorded hive status after joining or leaving.

For missing work, failed musubi commands, or musubi errors from jj, follow
[Debugging musubi](references/debugging.md).
