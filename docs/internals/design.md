# jj-musubi design

jj-musubi keeps one jj repository in sync across several machines. A daemon on each machine
watches the repository's operation log, publishes new operations, and the objects they refer to,
to a hub, and applies the operations that other machines published. A commit, rebase or abandon on
one machine reaches the others through the hub, and a machine that was offline catches up when
it reconnects.

This document gives musubi's design rules and the reasons for them. [protocol.md](protocol.md)
specifies the messages between nodes and the hub and the properties they guarantee, and
[races.md](races.md) the outcome of each race. musubi pins jj-lib 0.47.1.

## Vocabulary

- **Hive**: one logical repository replicated by musubi. It has a hive id, a UUID that musubi
  generates; a human-readable name (`jj-musubi`); and one hub. jj repositories have no identity of
  their own: every repository shares the same all-zero root operation and root commit, and
  `.jj/repo/config-id` is a machine-local pointer that jj regenerates when it detects a copy. So
  which hive a repository belongs to is decided by its history, when it joins
  ([Joining](#joining)).
- **Machine**: a computer taking part. Each user on it runs one daemon, which serves all of that
  user's copies.
- **Copy**: a jj repository on a machine that belongs to a hive. Its **machine key** is its
  lasting identity in the hive: the machine's name plus a random suffix (`laptop#1a2b3c4d`),
  stored in `.jj/repo/musubi/machine` on first use, so that two machines that share a hostname are
  never confused. Within one hive, this document often says "machine" for a machine's copy.
- **Node**: a copy and the daemon serving it, as the sync protocol sees them.
- **Hub**: a long-running musubi process that stores a complete copy of each of its hives, orders
  their updates, and serves catch-up. It never originates changes. Any machine can run it, and one
  hub serves any number of hives.
- **Canonical operation**: the form of a jj operation that is replicated, without the state that
  belongs to one machine ([Per-machine state](#per-machine-state-in-a-replicated-view)). Its id is
  computed by jj's own op store code, so it is an ordinary jj operation id. Each machine keeps the
  canonical operations it has in a canonical op store, `.jj/repo/musubi/canonical`.
- **Local operation**: an operation in a node's own jj op store, `.jj/repo/op_store`.
- **Canonicalizing** a local operation computes its canonical form. **Realizing** a canonical
  operation that arrived from elsewhere writes a local operation to stand for it, its
  **realization**. Together they are **translation** ([Translation](#translation)).
- **Canonical head**: the single operation the hub currently considers the latest state of the
  hive.
- **Join operation**: the canonical operation that `musubi create` or `musubi join` writes to
  stand for a repository's existing history. The local operation it stands for is the **join
  point** ([Joining](#joining)).
- **Work**, **forget**, **present**: an operation is work by a copy when the copy chose to make
  it, and a forget when it takes copies out of the hive; a copy is present while it has work that
  no forget saw ([Copies that go away](#copies-that-go-away)).
- **Colocated**: a git-backed jj repository with a workspace whose root is also a working tree
  of its git repository, so that git commands there use it too: usually the `.git` beside
  `.jj`, or a store inside `.jj` that `jj workspace add --colocate` made a worktree of. A
  repository whose git repository is external, even one named `.git`, isn't colocated unless
  one of its workspaces is also that repository's working tree, as jj decides. musubi decides
  when it opens the repository, so a daemon notices a workspace colocated later only once it
  opens it again.

## What is replicated

| Data | Replicated | Notes |
| --- | --- | --- |
| Operations and views | yes | In canonical form. |
| Commit predecessors (`Operation::commit_predecessors`) | yes | Part of the operation; drives `jj evolog`. |
| Commits, trees, files, symlinks | yes | git objects for the git backend; store files for the simple backend. |
| git backend extras (change ids not recoverable from the commit) | yes, when needed | See [git backend](#git-backend). |
| Workspaces (`View::wc_commit_ids`) | yes | Each machine's are its own; the others' show as `laptop/default`. See [Workspaces](#workspaces). |
| Working copies and working-copy state | no | Each machine snapshots its own. |
| Commit index (`.jj/repo/index`) | no | Derived; jj rebuilds it. |
| `View::git_refs`, `View::git_heads`, the `git` pseudo-remote | no | Per-machine record of this machine's `.git`. |
| Git remote definitions (names and URLs) | no | Each machine configures its own Git access. |
| Repo config | no | Each machine owns its settings, including rewrite and push protections. |
| User config | no | |

Every operation is replicated, including working-copy snapshots. If you snapshot a file containing
a secret, every machine in the hive receives it.

## Working copies

musubi never touches working copies. It writes only what jj itself keeps: the operation log; the
commit store, and in git-backed repositories the git object database and refs. Sync never
rewrites Git remote definitions or jj config ([Local configuration](#local-configuration)).

A remote operation can still rewrite this machine's working-copy commit, for example by rebasing
its parent. jj then treats the working copy as stale, exactly as after a `jj rebase` run in
another workspace: by default the next `jj` command stops and suggests `jj workspace
update-stale`, which updates the files. With `snapshot.auto-update-stale = true` jj updates the
files itself, but then any `jj` command, even `jj log`, can change files under a running build or
an editor, so musubi doesn't turn it on. Each machine can set it for itself.
jj snapshots edits not yet snapshotted before it updates the files, so instead of losing
them you get, at worst, a divergent working-copy change.

## Why replicate the operation log

The alternative is fetch-style sync: replicate heads and bookmarks only, as `jj git fetch` does.
That loses the operation history, so `jj op log` and `jj undo` stay per-machine, and commits that
no bookmark points to, such as another machine's working copy, don't travel. Since jj 0.42 a fetch
infers rewrites from change ids and rebases local descendants of a rewritten commit, but musubi
would still have to reconcile other concurrent changes itself.

Replicating operations reuses jj's own concurrency model. jj already lets several processes write
to one repository without locking each other out: each writes an operation, and when a later load
finds several operation heads, jj merges their views three-way, writing a merge operation and
rebasing descendants of rewritten commits. To jj, a remote machine is just another concurrent
writer. So `jj op log` shows the other machines' operations, undo works across machines, and
divergence shows the way jj always shows it.

## Per-machine state in a replicated view

A jj view mixes state that describes the repository with state that describes one machine.
Replicating views verbatim corrupts the second kind, which is:

- **This machine's record of its `.git`**: `git_refs`, the `git` pseudo-remote (`foo@git`,
  `tag@git`), and each workspace's git HEAD (`git_heads`). These record what jj last saw in this
  machine's `.git`. Each `jj` command in a colocated repository compares them with the real refs
  and imports any difference as a change made with git. [The hazard](#the-hazard) shows what goes
  wrong if they replicate.
- **Workspaces** (`wc_commit_ids`), which say where this machine's working copies are, and the
  workspace name that each operation's metadata records ([Workspaces](#workspaces)).

[Translation](#translation) removes this state from what a machine sends and adds its own to what
it receives.

### The hazard

Machine A moves bookmark `main` from X to Y and exports it, so A's view records `main@git = Y` and
`git_refs[refs/heads/main] = Y`. Suppose B adopts that view verbatim while B's `.git` still has
`refs/heads/main = X`. B's next `jj` command sees that git "moved" `main` from Y back to X. It
merges that into the local bookmark three-way (local Y, base Y, git X) and gets X: jj silently
reverts A's change on B. The reverting operation then replicates back to A.

Updating B's `.git` refs before showing B the operation fixes the common case, but leaves the
recorded values wrong whenever B's export can't succeed, such as for a conflicted bookmark or a
ref moved with git in the meantime. Any operation that fixes the record replicates back to A and
breaks A's record in turn.

### Workspaces

jj keeps every workspace in one map in the view. Replicated as is, it would make every machine's
workspaces workspaces of every other machine's repository: any machine could forget or rename
another's, and every machine's `default` would collide. So each machine's workspaces are its own,
and every machine shows the others'.

The canonical view records every machine's workspaces under keys qualified by machine key
(`laptop#1a2b3c4d/default`). A machine realizes its own under their plain names, and the others'
as workspaces named after their machine: `jj log` shows the laptop's working copy as
`laptop/default@`, and `jj new laptop/default@` builds on it. Where that name is taken, as by two
machines that share a name, it is shown as `laptop-1a2b/default`. These are never git refs, so
nothing git does can drop them, and jj's git import never abandons work because of them.

jj moves another machine's workspace as it moves any workspace: when it rewrites the commit, the
workspace follows (to the second half of a split, say); when it abandons it, the workspace gets a
new empty commit on the parents; and `jj undo`, `jj redo` and `jj op restore` restore every
workspace's position. The machine that owns the workspace adopts those moves, as a second
workspace on one machine does: its working copy becomes stale. Nothing else a machine does to
another machine's workspaces counts: adding, forgetting or renaming them stays local, and the next
sync shows them again. Only a forget of the whole copy, which musubi writes, removes them ([Copies
that go away](#copies-that-go-away)). Where concurrent operations disagree about a workspace,
musubi merges it three-way as jj does, so a machine's removal of its own workspace wins over
another machine moving it meanwhile. If a machine that has forgotten another's workspace then
abandons that workspace's commit, or rewrites its parent, the owner gives itself a fresh `@` where
jj would have put it. [races.md, "Workspaces"](races.md#workspaces) has the details.

Which workspace made an operation is per-machine too. jj records it in the operation's metadata,
and `jj undo` and `jj redo` refuse to undo another workspace's operation, telling workspaces apart
only by name. If every machine's operations kept the plain name, each machine's `default` would be
the same workspace to `jj undo`, which would then undo whatever operation last arrived from
another machine. So canonical operations record the machine-qualified key, and a machine realizes
another machine's operations under that machine's workspace name: `jj op log` shows
`laptop/default@`, and `jj undo` refuses to undo the laptop's operation unless given
`--allow-cross-workspace`.

### Translation

Translation keeps per-machine fields per-machine:

- **Canonicalizing** a local operation copies it, but with this machine's record of `.git` removed
  from its view, its workspaces and its own workspace name machine-qualified, and its parents
  replaced with their canonical ids. It is written to the canonical op store, which assigns the
  id.
- **Realizing** a canonical operation C on a node writes a local operation with C's metadata, its
  workspace name made local as above, and a `musubi.canonical = <id>` attribute. Its parents are
  the realizations of C's parents, and its view is C's view plus per-machine fields. jj's
  `Transaction` can't reproduce another machine's metadata, so musubi writes these operations
  through jj-lib's `OpStore`, as `jj op integrate` does, and mostly leaves the index for jj to
  build when it needs it. jj's op store syncs each file it writes to disk, which is slow, so a
  node catching up writes its realizations, and makes their views, in parallel; nothing names them
  until they are all written.
  - An operation that won't be an op head inherits its parent realization's per-machine fields, or
    for a merge, their three-way merge, as jj's merge of the operations would make it. That makes
    realizing deterministic, given the op heads, whose own workspace names other machines'
    are shown clear of ([Which workspaces are this machine's
    own](#which-workspaces-are-this-machines-own)), so re-realizing after a crash rewrites
    identical files, or, where a `jj` command changed those meanwhile, leaves the first
    unreachable.
  - For the operation that becomes an op head, in a colocated repository, musubi runs jj's
    `export_refs` with C's bookmarks, tags, and remote bookmarks against this machine's `.git`.
    This writes `refs/heads`, `refs/tags`, and `refs/remotes`, compare-and-swapping against the
    recorded values as a local `jj` would, and musubi records the resulting per-machine fields. It
    holds jj's `git_import_export.lock` from the export until it has published the op head, so a
    concurrent `jj` command never sees the operation before `.git` matches it.
  - Before publishing it, musubi merges it with this machine's own concurrent operations as jj
    will, in jj's order and the reverse, since the result can depend on the order. jj 0.47 can't
    merge some concurrent operations ([races.md, "Known jj
    limitations"](races.md#known-jj-limitations)), and publishing them would leave every `jj`
    command here failing. So if the merge fails, musubi publishes nothing, and the sync fails,
    naming this machine's operations that the hive doesn't have yet, so that the user can revert
    one. Otherwise, in a colocated repository, musubi exports that merge too and publishes it in
    place of the realization.
- Canonicalizing a realization returns the canonical operation its attribute names. Realizing
  never creates new canonical operations, so updates can't loop between machines.

Translation applies to every backend. Canonical operations are always written by musubi's pinned
jj-lib, while local operations may be older files in legacy formats, so even with nothing to strip
the two need not share ids. An operation has one id on the hub and its own local id on each
machine; `musubi debug op-id` translates between them. [protocol.md, "Translation
layer"](protocol.md#translation-layer) states what translation must guarantee.

## Copies that go away

A copy that goes away without `musubi leave`, as a short-lived machine's does, would otherwise
stay in its hive for good: every machine would go on showing its last working copy, and the hub
counting it. So a hive forgets copies: `musubi forget` forgets another machine's, and `musubi
leave` this machine's own. Forgetting is soft: a copy that is still there comes back as soon as it
is used, unless the hub has since pruned records of `jj op abandon` it never took ([What an
abandon costs the hub](#what-an-abandon-costs-the-hub)).

### Presence

Each canonical operation is work by a copy, a forget of copies, or neither:

- **Work** by a copy is an operation the copy chose to make: one of its own `jj` commands, which
  the canonical workspace name says it made, or an operation musubi makes for it, marked
  `musubi.work = <machine key>`: its join, joining again after leaving, or recording its
  `musubi.forget-after` ([Copies that go unused](#copies-that-go-unused)).
- A **forget** is marked `musubi.forget = <machine keys>`. `musubi forget` and `musubi leave`
  write one, which removes the copies' workspaces from the view as `jj workspace forget` would,
  abandoning each working-copy commit that is empty.
- **Neither**: merges, and the other operations musubi writes, for new working copies,
  or showing workspaces again.

A copy is **present** at an operation when some of its work in the operation's history is in the
history of no forget of it there. So a forget removes only the work it saw, and only work brings a
copy back. `formal/Musubi/Presence.lean` ([formal/README.md](../../formal/README.md)) proves that
every machine agrees on presence; that it can't loop, nothing but work bringing a copy back; that
`musubi leave` sticks however its forget is merged, given that the forget follows all of the
copy's work, as [Leaving](#leaving) ensures; and that work done meanwhile survives a forget that
didn't see it.

An operation's canonical view has a machine's workspaces exactly when the machine is present there
(`canonical_view`). This machine's own go in only if it is present, so nothing musubi writes here
brings it back. Another machine's are merged three-way, as in [Workspaces](#workspaces), but over
only the parents where it is present: a parent where it isn't lacks its workspaces because a
forget saw its work, not because the machine removed them. The hub counts the machines with
workspaces in its head's view, which are therefore the present ones.

Presence is computed from an operation's parents and its work or forget marker. A merge keeps
each parent's latest work unless another parent has seen and forgotten it. Work is named by its
original identity so contraction cannot change the answer ([Presence through an
abandon](#presence-through-an-abandon)). Generation numbers bound the ancestry queries, and a
cache avoids walking the whole history on each sync.
[conformance.md, "Presence"](conformance.md#presence) describes the check against the model.

### Which workspaces are this machine's own

In a local view, this machine's workspaces have plain names (`default`), and another machine's are
named `<machine>/<workspace>` (`laptop/default`). But jj allows `/` in a workspace name, so a
workspace of this machine's own can have that form too, and the name alone doesn't say whose it
is. Canonicalizing has to tell the two apart, from history alone, so that it stays deterministic.

Another machine is shown under its name, or, where two machines share a name, this one included,
or the name would clash with a workspace of this machine's own, under its name and the start of
its key's random suffix (`laptop-1a2b`; `local_names`). Where that clashes too, with another
machine's name or a workspace of this machine's own, it is shown under its name and its whole
suffix, then that with ever more dashes: each machine in turn takes the first of these that is
free, and `formal/Musubi/Names.lean` proves that no two workspaces are shown alike. The names are
chosen among every machine the history has known, present or forgotten (`Presence::known`), so a
machine keeps its name as others come and go, and a forgotten machine's name is never another's.
The hub names every machine with workspaces in the hive for `musubi list`, among themselves, so a
machine shows here as the hub lists it but where a forgotten machine, which only the hub leaves
out, or a workspace of this machine's own makes its name longer here. `musubi status` names this
machine among the copies present, as the hub names those with workspaces (`name_in_hive`);
`musubi list` finds a copy here among the hub's names by its key (`listed_as`); and `musubi
forget` takes this machine's key and that name for this machine's, and any other name it could
be shown under, where no other machine could be. This machine's own names as of a canonical
operation are its workspaces in that view, or, where the hive has forgotten it, those as of its
latest work, which `Presence` keeps through forgets (`own_names`).

`jj undo` and `jj op restore` bring back older views, with names the hive no longer gives: a
forgotten machine's, say, or, as here, one shown plainly before another machine of its name
joined:

1. This machine, `desk`, shares a hive with a machine named `laptop`, shown here as
   `laptop/default`.
2. A second machine named `laptop` joins. The two are now shown as `laptop-1a2b/default` and
   `laptop-3c4d/default`.
3. On `desk`, `jj op restore` to an operation from before the second laptop joined brings back
   a view with a workspace `laptop/default`.

Nothing in that name says it isn't `desk`'s own, but it is the first laptop's, under its old
name, and taking it for `desk`'s would nest one machine's workspaces in another's. So a name
whose prefix is one that a known machine other than this one can be shown under (here `laptop`,
`laptop-1a2b` or `laptop-3c4d`; `names_other_machine`) is this machine's own only if:

- this machine's own names as of a canonical parent have it already; or
- the operation made it: it is in none of the views of the operation's local parents. An
  operation that goes back to an older one (an undo, redo, restore or revert) makes no names: a
  name is its own if it was among this machine's own names as of that older operation or its
  parents.

Otherwise `canonical_view` doesn't publish it. `show_other_workspaces` also drops it from the
local view, unless jj's workspace store says this machine has a working copy for it.

Which of another machine's workspaces a name is comes from the operation's local parents: each
canonical parent's workspaces are named as the local parent standing for it named them. A
`jj` command that adds a name none of the views it started from had, as after `jj workspace
forget laptop/default` here, makes a workspace of `desk`'s own, though the hive shows one of the
laptop's by that name. An operation that goes back to an older one starts from the view it
brings back, less what was `desk`'s own there, so that `jj undo` of forgetting `desk`'s own
`laptop/x` brings back `desk`'s workspace. musubi's own operations make no names: they show other
machines' workspaces again under the names the hive gives them.

A realization of another machine's operation is merged with `desk`'s op heads, published or not,
so it names other machines' workspaces clear of `desk`'s own names in them too
(`reserved_names`), and records those names (`RESERVED_WORKSPACES`), by which `canonical_view`
names them so again at the merge. Otherwise the laptop's workspace `x`, which the laptop adds
while `desk` adds its `laptop/x`, or that of a machine named `laptop` joining meanwhile, would
be `laptop/x` here too, and jj's merge would keep one of the two working copies under the name.
Showing the laptop as `laptop-1a2b` drops the names it had here, which jj's merge takes for
removals, and a removal wins over `desk`'s own workspace of such a name, as after `jj workspace
forget laptop/default` and `jj workspace add --name laptop/default`. So a realization keeps such a
name as the base of the merge has it (`reserved_for`), which leaves the merge `desk`'s own. A
realization not yet published that was named clear of fewer of `desk`'s names than its op heads
have now, as one made before a crash or a `jj` command, is realized again before it is merged.

A workspace of `desk`'s own that it named `laptop/x` therefore stays its own, and the laptop is
shown as `laptop-1a2b`, to keep clear of it:

- whether it was made before a machine named `laptop` joined, while it joins, or after;
- while the laptop adds a workspace `x` of its own;
- after `desk` forgot the laptop's `laptop/x` here;
- while the hive has forgotten `desk`;
- through `jj undo`.

[races.md](races.md#copies-that-go-away) says where a `jj` command racing a sync can still put
the two under one name, and where showing the laptop's workspace under a longer name can undo
the laptop's move of it meanwhile.

### A forgotten copy's working copies

A machine the hive has forgotten keeps its own working copies. When it realizes an operation whose
canonical view leaves it out, it keeps its workspaces as the realization of the parent with its
latest work had them (`Presence::worked`), following the operation's rewrites
(`with_own_workspaces`). So at a merge of a forget that saw its latest work with an operation that
saw only earlier work, it keeps the workspaces the forget's realization had. It keeps them so too
at work by it that another machine wrote, a [fix-up](#the-fix-up)'s, where it is present: a
machine that had forgotten it wrote that view without its workspaces, and only its own operations
remove them. Where another machine rewrote its working-copy commit, as one can while no other
machine sees it as a working copy, it follows the rewrite (`replace_abandoned_working_copies`).
Where the forget abandoned an empty working-copy commit, it stays on the hidden commit, since a
new one would be an empty commit of no one's on every other machine. jj's next snapshot, or any
command that rewrites `@`, makes a new visible commit of it, and that work publishes the machine's
workspaces again. No other machine sees the commit as a working copy, so jj doesn't rebase it when
another machine rewrites or abandons its parents, and the snapshot would bring them back. So the
machine rebases it itself, as jj would have rebased a working-copy commit it saw, writing it
hidden and recording no rewrite, in an operation that isn't its work, so that it stays forgotten
(`replace_abandoned_working_copies`).

### Leaving

`musubi leave` snapshots the working copy (`jj util snapshot`), forgets this copy with an
operation that removes its workspaces here, and syncs, so that the forget reaches the hub after
all of the copy's work, and with it. A `jj` command run in the copy meanwhile is work the forget
didn't see, which goes up too and keeps the copy present, so `leave` checks presence at the hub's
head, and forgets and syncs again, up to three times. Then it puts the workspaces back here, in an
operation it never sends, and stops syncing. If it can't snapshot or sync, it puts the
workspaces back and stays; a forget it wrote goes up with the daemon's next sync, and the copy's
next work brings it back. `--force` leaves anyway, without telling the hive: the other machines go
on showing the copy until one of them forgets it, with `musubi forget` or by its
`musubi.forget-after`. A copy that `musubi leave` takes out, even one already forgotten, gives
each workspace whose commit is hidden a new `@` (`give_back_working_copies`), since no later work
of its will be in the hive to do it.

## Copies that go unused

Each copy records how long it may go unused before the hive forgets it, its `musubi.forget-after`
(`6h`, say, or `never`), in an operation that is its work and changes nothing else: `musubi.work =
<machine key>` and `musubi.forget-after = 6h`. Its daemon writes one when the value jj's config
gives differs from the one the copy last recorded (`record_forget_after`), reading the repo config
afresh each time. A copy that has recorded nothing is never forgotten, so
one set to `never` writes nothing. `musubi join`, `create` and `clone` put the value in the repo
config unless jj's config sets it already: `never` regardless of who runs the command. An
explicit `--lease <duration>` replaces the copy's repo policy with that inactivity timeout.

`Presence` keeps each copy's latest operations recording its forget-after, and what they record,
through forgets, merged as `worked` is; where two lines of history recorded different values, the
longer holds. A daemon, once idle after fetching the hive's head (`NodeAdapter::when_idle`),
forgets each present copy other than its own whose latest work ended longer ago than its
`musubi.forget-after`, by the work's timestamp and the daemon's clock (`expire_idle`). This is an
ordinary forget, as `musubi forget` writes, so everything the presence rule proves holds of it.
The hub takes no part.

- Clock skew only moves when a copy is forgotten. But a copy whose clock runs behind a daemon's by
  more than its setting is forgotten after each of its operations, and shown again by the next:
  machines' clocks are assumed close, as jj's timestamps assume.
- `musubi.forget-after` is local to each copy: an agent's `6h` mustn't reach a person's copy.
- Each machine adds a delay of its own, up to five minutes, from a hash of its machine key and the
  copy's, so that one machine's forget usually reaches the others before their own time comes.
  Duplicate forgets are harmless anyway.

## Local configuration

Git remote definitions and jj user, repo, and workspace config belong to each machine. Sync
never applies another machine's configuration, including after a failed or interrupted sync.
There is no settings merge, timestamp ordering, pending settings journal, or configuration
recovery step. Explicit join/create/clone commands may set the local `musubi.forget-after`
default, as described above; that is independent of synchronization.

Remote bookmarks still replicate with jj's view, by remote name. Machines using `origin`
should configure it to name the same upstream; URLs and credentials may differ. A remote
rename or removal changes the replicated remote bookmarks but not other machines' Git
config. Users coordinate those changes before fetching or pushing elsewhere. A machine can
receive remote bookmarks without having that remote configured; receiving them never creates
its definition.

Each machine's `immutable_heads()` and `git.private-commits` apply to commands on that machine.
They do not constrain other machines, nor exclude committed work from replication. A new
clone evaluates `trunk()` using its destination machine's jj config and adds no Git remote
definitions; inherited global Git config still applies.

A creating join includes the effective, explicitly configured values selected by
`musubi.clone-config` (name and email by default), serialized as TOML values. The hub stores this
immutable snapshot in `hive.toml` and returns it in `HiveInfo`; joins to an existing hive ignore
their supplied defaults. Recreating a lost hive takes fresh defaults from the first rejoining
copy, since the hub snapshot is disposable. Clone validates the selected keys and values before
creating any paths, uses missing values for jj initialization, then rechecks the destination's
resolved config and writes only still-missing values once. Destination user, repo, workspace,
conditional, and environment settings take precedence. No sync reads or writes this bootstrap
data. `musubi.forget-after` is excluded because clone chooses it for its own caller.

### Join and clone preflight

A remote name is bound to one normalized effective fetch destination and a set of normalized
effective push destinations for the lifetime of a hive. Missing remotes make no claim. Git's
`insteadOf` and `pushInsteadOf` expansions determine the effective destinations; the URL
normalizer makes equivalent HTTPS, SSH, and bracketed IPv6 spellings agree. Candidate overlap
is not equality: an identical alias expanding to different repositories must be refused.

A join sends its bindings separately from its discovery URL hints. An existing copy's
explicit rejoin first checks and restores known constraints from its scoped canonical join
observations, so remaking a lost hub cannot silently rebind a known name. That history scan
runs only on explicit rejoins, never ordinary syncs. After hive selection,
including explicit `--hive` and an existing copy's rejoin, the hub checks every supplied name
against its fixed bindings and accepted join evidence. It reserves any new names in
`hive.toml` before approving the join, so expiry of a delayed first push cannot release them.
A refusal records no pending join and reserves no names. A different destination needs an
unused remote name or another hive; renaming does not release the previous name's binding.

The client records exactly the approved snapshot, without rereading Git. Its operation
attributes contain `musubi.join-hive`, indexed `musubi.join-url.*` discovery hints,
`musubi.join-fetch.<name>` identities, and `musubi.join-push.<index>.<name>` identities. The
index retains all distinct binding observations and discovery hints scoped to its own hive, so
carried history from another hive neither imposes its contracts nor matches its copies. It can
rebuild evidence from immutable operations; no timestamp ordering, latest-observation
selection, or settings replay is needed.

`Resolve` refuses if accepted evidence disagrees with the fixed bindings. Clone then reads
inherited Git config with the prospective Git directory as the context for conditional
includes, before creating any parent directory or initializing the repository. The preview
uses jj's Git parser and its initial branch selection. A Git comparison test pins URL rewrite
rules, including multiple push destinations. `PrepareClone` takes the exact hive id returned by `Resolve`, never another name lookup,
and checks and reserves the inherited bindings under the same hub lock as joins, so two concurrent approvals cannot claim a new
name differently. The client records exactly that snapshot. Conflicting evidence from a
buggy peer is retained and reported. A consistently configured source can start another hive;
configuration in existing copies stays untouched.

Discovery hints contain fetch URLs as written and expanded, sorted and deduplicated. Ordinary
syncs do not observe config changes or make settings operations. A copy can explicitly rejoin
to register equivalent URLs; an op abandon can remove an observation from a rebuilt index.
The hub's fixed bindings remain authoritative. These checks validate reported identities at
preflight time; they cannot inspect offline copies or prevent later local edits.

HTTP(S) credentials are removed from hints and URLs in jj's operation arguments unconditionally.
Canonicalization uses immutable recorded metadata and never reads current configuration when
translating an old operation. Sync never applies configuration or restores it in a fix-up.

## Ordering: one hub, one canonical head

When two machines make concurrent operations, someone has to merge them. Suppose each machine
merged independently. A's operation rewrites commit X; B's concurrent operation adds a child Y of
X. A's merge rebases Y onto the rewritten X, giving Y'. B's merge does the same, giving Y''. Y'
and Y'' have different committer timestamps, so they are different commits, and the hive ends up
with a spurious divergent change.

The hub keeps a single canonical head. Ordinary pushes are fast-forward updates; an operation
abandon contracts the history as described in [Abandoning operations](#abandoning-operations).
A node pushes by uploading what the hub lacks and asking it to compare-and-swap the canonical
head from H to H',
which the hub does only if H' descends from H and everything H' refers to is stored. A node pulls
by fetching the operations between its last-known canonical head and the current one, realizing
them in topological order, and publishing the realization of the new head. If the node has local
operations the canonical head lacks, its push fails; it pulls, jj merges its local heads, which
include the new realization, and it pushes the merge. So each merge is made exactly once, by the
node that owns the concurrent local work, the same outcome as two jj processes on one machine:
every merge has a parent that only its creator had, so two machines never make the same one.
[protocol.md](protocol.md) specifies these steps, and the [formal model](../../formal/README.md)
proves this and the protocol's other safety properties.

Notifications are hints: the hub announces each new canonical head, but nodes also compare heads
with it whenever they connect, and periodically, so correctness never depends on receiving one.

### Offline work

A disconnected node keeps working locally; jj doesn't need the hub. When it reconnects, it pulls,
merges, and pushes, the same path as any concurrent update.

### Replacing the hub

A hub is just a store. Every node holds every operation it has seen, so a new, empty hive fills up
as soon as nodes connect: the first node fast-forwards it to its head, and the others fast-forward
or merge as usual. A hub makes no synchronous fsyncs: one that loses its state is deleted and
made again, and the machines' repositories fill the new one.

A new hub doesn't have the hive id the nodes know, so it answers their requests "no hive", and
their syncs fail, saying so. `musubi join` in one copy then makes the hive again (a join with
`JoinChoice::Remake`), empty, under its id and the name the copy knew, as `musubi create <name>`
would make it, though the copy matches another hive the hub has: hives made from copies of one
repository under names of their own were made apart on purpose. If that name is another hive's, or
the copy knows none, or none valid, it makes the hive under a name from its remote or directory,
as an unnamed `musubi create` would, and refuses as that would if the copy belongs in a hive the
hub has, such as one made again by hand meanwhile under that name. One made again by hand under
another name stays apart, as the hub can't tell it from one made apart on purpose. It refuses too
if the hub removed that hive. The other nodes find their hive at their next sync and fill it, as
nodes follow any hub that goes back. A person makes the hive again, not the first node to sync,
because a hub that doesn't know a hive may be the wrong hub, such as one started from another
directory by mistake, which would otherwise fill up with every hive. `musubi join --hub` makes the
hive again on another hub in the same way, which moves a copy there.

A hub does that itself for a hive whose store it finds corrupt as it opens it, its heads file
torn, say. The store goes under `removed/`, and the hive is made again, empty, under its id, name,
and index. Machines that knew its later heads follow it back to its root, as they follow any hub
that goes back ([protocol.md, "Network and failures"](protocol.md#network-and-failures)), and push
what they have. A machine whose last head the first to push lacked then fetches the whole hive
again, as from a new hub, since the hub can't tell what it has. The old store is deleted once it
has been set aside a day and the new one has accepted a head, or once the hive has been taken out
of the hub.

A power cut can also leave a file the hub wrote just before it cut short or garbled: the end of
the hive's log of operations and views, or a git object. The hub finds the first as it opens the
store, reading the log up to the last whole record: if what it lost includes an operation the hub
had accepted, the store is corrupt, and the hive is made again as above. It doesn't look for the
second, since that would read every object. Such a file is rare, needing a cut within a minute or
so of the write. A hive stuck on one, its syncs failing on the same object, is made again by hand:
stop the hub, delete the hive's `heads`, and start it again. The hub then finds the store corrupt
and makes the hive again under its id, for its machines to fill.

Duplicate merges can occur in two cases: two hubs serving the same hive at once (split brain),
when nodes that synced through different hubs can each merge the same work once they meet at one;
and a hub going back to a head it accepted earlier, having lost later ones to a power cut
([protocol.md, "Network and failures"](protocol.md#network-and-failures)).

## Objects

A canonical operation is complete on a node or hub when its ancestors and every object its view
refers to are present: commits referenced by heads, bookmarks, tags, remote bookmarks, and
working-copy entries, plus `commit_predecessors`, with all ancestors, trees, and files. The hub
refuses a head whose closure is incomplete, and a node realizes only complete operations, so
uploads and downloads can be interrupted at any point without anyone seeing a dangling reference.

Object replies are checked for completeness even when empty: after a hub remake, the hub may
no longer know the requested operations. A node still missing required commits restarts from a
fresh fetch rather than retrying object requests against the old head. An accepted fetch base is
usable only while its required commits remain locally available; otherwise the node fetches
from the root. This matters after `jj util gc`, which can collect objects from an abandoned
base's original view even when its surviving local image is present.

### git backend

Objects move as git packfiles, made and read by the `git` binary: `git pack-objects --revs` with
the receiver's known commits as exclusions, and `git index-pack --fix-thin` to receive. jj already
needs `git` for fetch and push, and this gets delta compression, and bitmaps for clones, for free.
A node runs the git jj is configured to use (`git.executable-path`); a hub, which has no jj
config, runs `git` from its `PATH`. Questions that need only an answer (which commits exist, which
commits a transfer covers and which of them have no parents, which refs the hub has) musubi asks
gix in-process, as jj does, since starting git would cost more than the answer, on Windows most of
all. Each question opens the repository afresh, so that gix sees what git has just written and
holds no pack open that git's gc might delete, which Windows forbids.

- A pack is written once on each side: `git pack-objects` writes it straight into the bundle that
  carries it, which goes into the blob store as a hard link rather than a copy where the
  filesystem allows, and the receiver pipes it from the bundle into git.
- As `git fetch` does, a received pack of fewer than 100 objects is unpacked into loose objects,
  and a larger one kept as a pack.
- A node writes received objects into the repository's object store (usually `.git` for
  colocated repositories), reopening the repository first, since jj-lib's git backend can't read packs added
  after it opened it. It then calls jj-lib's `GitBackend::import_head_commits`, which creates the
  backend extras and the `refs/jj/keep/*` refs. The keep refs protect commits that no bookmark
  reaches from `git gc`; without them, git would eventually delete every anonymous head.
- jj commits carry `change-id` and conflict headers by default, so for nearly every commit the raw
  object is enough: the receiver derives the same extras from it. The exceptions are commits
  written by older jj or with the header disabled, whose change id lives only in the backend
  extras, and conflicts written before 2024, whose conflict trees do too. For each commit it
  sends, the sender compares its extras entry with what the receiver would derive from the object,
  and where they differ, ships the entry alongside the pack, which the receiver writes before
  importing. Per-commit predecessors in the extras are not shipped: since jj 0.30, evolution
  history comes from the operation's `commit_predecessors`.
- The hub stores objects in a bare git repository, in the files ref format, the only one gix
  reads. Its only refs are under `refs/musubi/head/`, naming the visible heads of its accepted
  head's view. Nodes never see them, since the hub sends bundles, not refs; they are there so that
  git can keep a bitmap index, which makes counting what a clone needs much faster. The hub writes
  its first bitmap index, with a full `git gc` in the background, once it holds 10,000 objects,
  and the full repacks of `git gc --auto` refresh it. Only clones use it: with a bitmap, git skips
  the walk that finds what the receiver has to make deltas against, so if other fetches used it,
  an edit pushed a moment ago would go to every other node whole.
- musubi runs git with `attr.tree` naming the empty tree, which spares git 2.43 to 2.45 slow
  attribute lookups on a hub.

musubi never deletes an object, reachable or not. After receiving, the hub and nodes run `git gc
--auto` in the background (on Windows too, where git can't detach itself) when musubi, measuring
as git does, finds there is work to do: more than `gc.autoPackLimit` packs not kept, or more than
`gc.auto` loose objects. Pruning is disabled; on the hub, what its head's refs don't reach goes to
a cruft pack. On battery, musubi defers that gc until an import on mains power. It asks `pmset` on
macOS, and on Linux defers when no mains or USB supply is online and the machine's own battery is
discharging. Elsewhere it can't tell, and doesn't defer.

On a machine, the daemon also cleans up what `jj util gc` would, short of pruning git objects
(`crates/musubi-jj/src/gc.rs`), removing each of these once it is two weeks old, as jj's gc does:
segments of jj's extras table that newer ones replaced; keep refs, of which jj writes one for
every commit it writes or imports, thousands a week in a busy repository, leaving only those for
the heads of jj's index, which has every commit a reachable operation refers to, in its view or
its recorded predecessors; and operations no op head reaches. It deletes no object: what the
removed keep refs held stays, since pruning is disabled, and nothing the protocol needs depends on
what it removes. A `git gc` that does prune, as the user's git or `jj util gc` may run, can then
remove objects fetched for operations not yet realized, which nothing refers to yet; the node
fetches them again before realizing the operations. The cleanup runs after a sync that worked, on
a thread of its own, one repository at a time, and only with over 1,000 extras files or 10,000
keep refs to clean up, a week after it last ran (even if that run failed partway), with one op
head, not on battery, and not while another process runs it. The hub never runs it: there, what
git can't reach from the head is history the hive still needs.

A process killed partway through updating refs, musubi, git or jj alike, leaves behind the lock
file git takes on a ref, `<ref>.lock` or `packed-refs.lock`, and every later update of that ref
fails until it goes: git never removes one. musubi does, when one of its own ref updates fails:
an import's keep refs, the cleanup's and the hub's `update-ref`, and the export to a colocated
`.git`. A lock records nothing of who took it, and git closes it before renaming it, but a ref
lock is held for one update, seconds at most, so musubi removes those over ten minutes old,
logging each, then tries the import or `update-ref` again. A ref that failed to export is
exported again by the next export, musubi's or a `jj` command's, so musubi looks only at the
locks on the refs that failed, and `packed-refs.lock`, since a failure that isn't a lock's
recurs at every export. A keep ref matters most: an import that failed on one has its objects
already, so the next import wouldn't fetch the commit, nor make its keep ref. musubi never
removes git's other locks, such as `index.lock`, which `git commit -a` holds while its editor
is open (`crates/musubi-jj/src/ref_locks.rs`).

### Simple backend

jj's simple backend exists mainly for jj's own tests, but supporting it keeps the operation layer
independent of git. Objects are content-addressed files. Transfer walks from missing commits and
sends the store files the receiver lacks, in batches.

### Size limits and chunking

The hub takes messages up to 1 MiB, and says so when a connection opens. Control messages are
small. Something bulky (packs, large views, batches of operations) travels inline in the request
or reply it belongs to when it fits in a quarter of that, and otherwise as a content-addressed
blob, sent in chunks in a resumable session ([protocol.md, "Chunked
blobs"](protocol.md#chunked-blobs)). The hub deletes a blob it prepared once it has served the
last chunk and 18 minutes have passed without a request for any chunk of it, long enough for a
node to ask again for a chunk of the last window whose reply came too late, and a blob no chunk
has moved to or from for an hour, as of an unfinished session, expires. A blob prepared again, for
another reply with the same content, counts as one prepared just now. A node deletes what it
uploads or downloads once it is done with it, however the call ends, except a partial download,
which it keeps for a later call to resume until it has gone a day untouched.

A sync takes few round trips: one if it brings something new, two if it pushes
([protocol.md, "Policy"](protocol.md#policy)).

jj stores a whole view for every operation, and a repository with thousands of remote bookmarks
can have megabyte-sized views, while consecutive views usually differ in a few bookmarks. In
transit, musubi compresses a bundle's operations and views together with zstd, and sends each view
as a delta against its operation's first parent's view: the view compressed with the parent's as a
prefix that zstd may refer back to, a few hundred bytes for a view of any size. A view a parent
has is not sent at all. The receiver always has the parents' views: a bundle holds the ancestors
of a head that aren't ancestors of a base the receiver has, parents first, so each parent is
either earlier in the bundle or one the receiver has already. Ids remain those of the uncompressed
views, and the receiver checks them after rebuilding each one.

musubi's own stores keep views as deltas too: the hub's, and each machine's canonical op store.
jj's op store on the machine keeps them whole, as jj needs. A store is one log, appended to
(`crates/musubi-jj/src/canonical/log.rs`): operations as encoded, and each view, in a normal form
whose bytes depend only on its content, as a delta against the view before it in the log, which
the record therefore needn't name. Every 128th view is compressed whole, so that rebuilding one
never applies more than 127 deltas, and the view rebuilt or appended last is kept, since the next
one asked for usually follows it. A busy repository's operation and view then take under a
kilobyte together, where jj's two files take two disk blocks and the view's full size. Each record
carries a checksum, and a scan stops at the first that fails, so damage to the log loses only what
was written after it. Writers append a batch at a time under a lock file, so that the daemon and a
command can share a store, and the next writer cuts off what a scan stopped at before appending.

A stored delta is usually against the view of its operation's first parent, so a bundle carries it
as it is, and a receiver whose last view is the delta's base stores it as it came: neither
compresses it again. jj-lib decodes views only from files, so a view is decoded, or encoded, by
writing it to a scratch op store and reading it back. Checking each view a bundle brings against
its id, by decoding and hashing it, is most of what an import costs, so an import checks a batch
of views at once on several threads, each with a scratch store of its own, then appends the batch.
musubi decodes operations itself; a read of a whole operation checks that the result hashes to its
id, while a walk over the history, as when the hub opens a hive, reads only parents, from the
encoding.

## Joining

`musubi create` starts a hive from an existing repository, and `musubi join` makes another copy of
it part of that hive. By default each replicates the repository's current state, not its operation
history: it writes one canonical join operation whose parent is the root operation and whose view
is the current view, and records that the current local head, the join point, canonicalizes to it.
Earlier operations stay local. A repository in use for years can have tens of thousands of
operations, and every one of their views pins commits that would otherwise never need
transferring, such as old working-copy snapshots. `--full-history` replicates everything instead.

A `jj` command that loaded the repository before the join and wrote its operation after it, as an
editor's can, or one run with `--at-op` at an operation from before the join, makes an operation
on that local history. It has no canonical form: the hive takes its work once jj merges it with
the history since the join, as the next `jj` command does, and the merge's canonical form leaves
out the parents from before the join, whose work its view has merged (`canonicalize`). Until then
the node syncs the rest of its history.

A repository that previously shared canonical history carries that history when it joins
again, even into another hive. Replacing it with a join on the root would make its accepted
base unreachable, falsely indicating an op abandon, and lose the ownership of other machines'
workspaces. Joining records fresh work if needed to make this copy present again.

Carrying history does not bring every old member into a different hive. The join forgets copies
absent from the target hive, except the joining copy itself; copies already present or joining
there stay present. Joining the same hive, including one remade on another hub, forgets none.
[copies.md](copies.md#rules) specifies the membership and duplicate checks.

Merging needs no special machinery. Every jj repository's operation log starts at the same root
operation, so a joining node's history and the hive's meet there. The joining node pulls the
canonical head, and jj merges the two three-way against the empty root view. Bookmarks set
identically on both sides merge cleanly; bookmarks that differ become conflicted bookmarks that
you resolve as usual. The node then pushes. Commits that both sides already have, such as history
cloned from the same origin, are never transferred twice, because transfers leave out what the
receiver has. A node fetching objects names, as haves, the commits of its op heads and of the
operations it has that the new ones descend from, and the hub leaves out everything they reach. A
node also fetches operations starting from the newest hub head it has, which includes its own
accepted push, so it never downloads what it uploaded.

### Which hive

A hub holds many hives, and a joining repository doesn't say which it belongs to: the hub works it
out, so that adding a machine is one command. Neither command guesses about creating a hive,
though: `join` that matches nothing is refused, and so is `create` that matches a hive, unless it
names the new one. Otherwise a copy whose remote URL doesn't look like the others', behind an ssh
host alias, say, would get a hive of its own and sync with nothing, with no sign anything was
wrong. In one request the node sends its backend, its remotes' URLs, its root commits, and the
commits its remote bookmarks point to. Its root commits are those whose only parent is jj's root
commit, which in git are those with no parents, leaving out an empty, undescribed working-copy
commit. The hub decides under its lock, so a copy joining while another creates the hive finds it.

musubi refuses a shallow or partial clone before asking the hub, and won't sync one: the hub
accepts an operation only with everything it requires, which such a clone can't send.

A backend includes the hash a git repository names its objects with, SHA-1 or SHA-256: the same
history has different commit ids under each, and git can't convert a repository, so a hive has
one and every copy must too. A hive takes its first copy's, the hub makes its store with it
(`git init --object-format`, whatever git's default), and the hub refuses a join whose backend
differs from the hive's, even one its remotes match. `musubi clone` makes the copy with the
hive's, whatever jj's `git.object-hash` says.

1. A repository with no commits of its own is refused: there is nothing to match, and nothing to
   share.
2. `--hive <name>` joins that hive, but only if the repository is related to it.
3. `musubi create <name>` creates a hive. `musubi create`, unnamed, creates one named as below,
   unless the rules that follow would join a hive, when it is refused.
4. Otherwise, a hive is *related* if it has stored one of the repository's root commits (ever:
   hidden ones count), or has a commit one of its remote bookmarks points to. Among related hives,
   the one that shares a remote URL with the repository, any remote and not only `origin`, is
   joined; if several do, joining is refused, naming them, to choose from with `--hive`. If none
   does, joining is refused, naming the related hives, so a fork, sharing history but with remotes
   of its own, isn't taken for the original; `musubi create` gives it a hive of its own. A
   repository without remotes joins its one related hive, and one with remotes joins a single
   related hive that has none. No related hive at all is refused too.

URLs match as written or as the joining machine's `insteadOf` rules expand them, after
normalization: https, ssh, scp-style, `file://`, and local paths reduce to a lowercase host,
without any user or default port, and a path without trailing `/` or `.git`, and the host and path
are what is compared. Azure DevOps' https and ssh forms are made one. Each hive keeps the URL
hints recorded by explicit joins. After changing a remote to an equivalent URL, an existing copy
can run `musubi join` again to register it.

For this the hub keeps an index for each hive: the URL hints explicit joins to it recorded,
every root commit it has stored, and the machines with workspaces at its head. The index is
updated whenever a head is accepted, and is a cache: the hub rebuilds it from the hive's
operations and objects when it is missing. A join also counts what the joining repository says
it brings, its URLs and root commits, as its hive's for a couple of minutes, so that another
copy joining before the first one's push finds the same hive. That stops once the joining
machine's first push is accepted, which puts what it really brought in the index, or when the
time is up, so a join that never pushes leaves nothing behind.

A new hive is named after the remote named `origin`, else the first remote by name, else the
repository's directory. The name follows the forge: `owner/repo` on GitHub, Codeberg, Forgejo,
Gitea, and Bitbucket; the full group path on GitLab; `user/repo` for sourcehut's `~user/repo`;
`org/project/repo` on Azure DevOps; a Gerrit project without its `a/`; and otherwise the last two
components of the path. A hive gets the shortest form of its name no other hive has: `jj-musubi`,
then `bos/jj-musubi`, then `github.com/bos/jj-musubi`. A name has no whitespace or control
characters, so one taken from a URL or a directory has its `%`-escapes decoded, each run of
whitespace made a `-`, and other control characters dropped: `My%20Project` and `My Project`
both name a hive `My-Project`. Names never change by themselves; `musubi hub rename` changes
one. Commands that take a hive accept any unique prefix of its name, except
`musubi hub remove`, which takes a whole name or an id, since a prefix is too easily mistaken.

`musubi clone <name>` creates a new colocated repository and joins it to the named hive.

## Abandoning operations

`jj op abandon` removes operations from the operation log. jj keeps every view, so the repository
is as it was at each operation that stays, but it rewrites every operation after the removed
ones, with a new id, since an operation's id hashes its parents. musubi replicates it: the
operations go from every machine and the hub, and their old ids, and those of the operations
after them, never come back.

### Contraction

An operation's nonparent content need not be unique: jj can make equal views, metadata and
commit predecessors at different places in history. Reparenting one can otherwise recreate
another's exact bytes and id, including an id the hive dropped. Each fresh canonical operation
therefore records its initial canonical parents in `musubi.original-parents`, replacing any
caller-supplied value. Contraction preserves that attribute verbatim. The original operation's
hash is recomputed by removing the attribute and restoring those parents; the original parents
are identity material and need not remain stored or reachable after an abandon.

Contraction requires at most one version of each original in its input history, even in the
ancestry it need not rewrite. The hub enforces this when accepting a history and rejects an
alternate version of a dropped original. The original-parent attribute preserves identity; it
is not proof that a peer followed the protocol.

A local survivor carries its canonical identity through rewriting. Unmarked jj rewrites whose
identity musubi has established are retained as source aliases too: an in-flight command may
still write on them. These facts must survive loss of the disposable translation cache, so a
restart cannot mistake a renamed operation for new work.
The alias records identity alone. Rebuilding the translation cache walks its parents before
recording it there, so that realization does not write another copy of an existing ancestor.
An alias whose identity has not been superseded is reparented and marked with that identity
before its descendants are normalized.
That marker carries the private workspace ownership inherited through its native parents too:
future ownership walks stop at the marked operation.
The identities retained for an interrupted head move obey the same rule. Recovery walks the
settled target heads before moving workspaces; it does not cache their saved identities as
completed ancestry walks. Cache rows distinguish this guarantee from older disposable entries,
which are ignored and rebuilt.
An older marked realization below a delayed command also keeps its original identity when its
native parents still map exactly to that stored operation's parents. An unmarked ancestor on
renamed parents is first checked against an already stored original on its raw parent identities.
The command above it uses the current images of those identities. Reparenting skips bodies
superseded since they were queued: the counted rewrite already supplied their replacements.

The hive's history drops a set of canonical operations. Each surviving operation's parent list
has every dropped parent replaced, where it stands, by that parent's own parents, themselves so
replaced, and then each duplicate after the first removed. A survivor whose parents change gets a
new id, and so does every operation after it; the others keep theirs. Dropping one set and then
another gives the same ids as dropping both at once, in either order
(`formal/Musubi/Contract.lean`). So two machines' abandons taken in either order, or an abandon
published again to a hub that lost it, reach the same history.

This isn't jj's own rewrite. jj's `op_walk::reparent_range` puts every operation outside the
abandoned range that has a parent anywhere in `::abandon_heads` on the range's root, which moves
concurrent branches as well, and two such abandons give different ids in different orders.
Where the two differ, as for a branch of the operation log that forks inside the range and
merges after it, musubi rewrites the abandoning machine's local operations again to match
contraction.

A workspace's recorded operation is its snapshot basis: its view must still name the exact
working-copy commit whose tree the files were based on. musubi chooses a surviving operation
with the same workspace and commit, preferring the contracted image. If none exists, it keeps
the old record so jj can snapshot local edits against the correct tree. A later native stale
recovery can bring back old operation history, as described under known jj limitations in
[races.md](races.md).

A full trim can also leave unpublished native operations on the operation root, with none
of the canonical parents that identified foreign workspace aliases. Before moving those
heads, musubi records `musubi.workspace-context`: the observed local-name bindings and known
machine keys from the last accepted namespace, scoped to this machine. It preserves the
actual root parents, without reconstructing erased native ancestry. The rewritten operations
carry this evidence, and the counted source records also bind the old unstamped native ids
so delayed commands and translation-cache loss use the same interpretation.

The first surviving operation above the root uses these bindings to distinguish local
workspaces from foreign aliases, but presence still comes from its real parents and work.
Each subsequent fix-up WORK
restores that copy's workspace bindings from the native view as it restores its last use;
a following forget removes them again. Descendants inherit the context only on the capturing
machine. Its exact foreign bindings apply only to aliases already in their native parents,
so a new local workspace can reuse a forgotten foreign alias. Other machines consume the
canonical views and render the canonical keys in their own namespaces.

A receiving machine also captures and canonicalizes the exact native heads that exist when
it prepares a trim, before contracting them. This covers commands that finished after the
policy last inspected its heads. These operations still have their actual source parents,
so ordinary canonicalization and contraction preserve their namespace and presence. The
held renaming also records their undropped native source identities, keeping delayed commands
on those original ids consistent after translation-cache loss.

Accepted base and push can both have contracted to root while later materialized operations
still name stored canonical sources. Those immutable source tips remain anchors for noticing
native trims after cache loss. Unchanged markers map back exactly; a marker whose parents jj
changed enters the same counterpart and contraction path. Even if another branch still reaches
the original tip, the changed marker is inspected: the surviving branch then prevents a drop,
and the out-of-place physical operation is repaired on its original canonical parents.

### Presence through an abandon

Contraction keeps every surviving operation's view, but presence ([Presence](#presence)) is
worked out from the history below an operation, which contraction changes. Dropping a copy's
work below an operation would leave the copy absent there, though the view has its workspaces;
dropping a forget would bring the copy back there, though the view lacks them. A machine would
then realize the operation, or another machine's operation on it, as presence there has it,
and make a view jj never makes: one with a machine's HEAD but none of its workspaces, or one
without the workspace a forgotten copy keeps for itself.

So presence at every operation that survives is what it was. Presence names work by its
original identity, which contraction keeps, not by its id. Contraction stamps an operation it
rewrites with its presence, in `musubi.presence`, where the presence worked out from its new
parents would be another, and only there; at a stamped operation presence is the stamp, and at
any other it is worked out as before. Work that no operation stands for any more, as the
abandon dropped it, counts as seen below every operation that doesn't keep it: a merge keeps it
only where every parent does, so a copy that left stays gone when a line of history from before
the abandon is merged. Whether an operation is stamped, and with what, depends only on its new
parents and what is gone, so dropping one set and then another stamps, and so names, every
operation as dropping both at once does. `formal/Musubi/PresenceContract.lean` models the rule,
and proves that and that presence at every surviving operation is as it was
([formal/README.md](../../formal/README.md), "Presence through a contraction"); the
conformance tests check the Rust against it. The stamp is no part of an operation's original
identity, and a fresh operation never has one. A copy is named in it by its machine key, which
has no whitespace (an operation naming a copy by anything else is no copy's work), and a work
by its original identity, so every presence can be written as a stamp; a machine or hub
refuses an operation received with a stamp that doesn't read, as presence there and after it
couldn't be worked out. Of two works an abandon dropped, neither counts as before the other.

### Publishing an abandon

jj's own reparenting can also recreate an earlier local id. When the surviving local history
cannot distinguish which published original was dropped, musubi refuses before recording drops
or moving heads. The error names `jj op integrate <operation>` to restore the missing history;
`jj op restore` restores only a view.

Inference uses the operation's full nonparent content, recorded against its immutable canonical
original before publication. Equal timestamps alone cannot establish identity. This evidence is
kept separately from the translation cache and survives jj gc; missing or ambiguous evidence
causes a refusal rather than a guessed drop.

A machine notices an abandon when canonical operations it had published are no longer
reachable from its op heads. It watches the operation it fetches from, and its own last push from
the moment it learns that the hub took it, from a reply that names it or among what it fetches: it
moves the base to the push only at its next step, which a sync cut short or a lost reply delays. A
sync polls the hub before it reads the op heads, so that it knows by then. It matches surviving
operations against both accepted histories together: a push may contain a survivor above a
base dropped in full. Matching against the older base first and stopping there mistakes that
survivor for new work, losing its original identity and presence. Where the surviving head
is unpublished work and all accepted history was trimmed, its pre-trim state comes from a
maximal accepted descendant of the surviving mapped ancestor. The older saved base must not
shadow a newer accepted push, whose presence and expected refs are the state to preserve. It looks
before
anything else reads the op heads, to merge or canonicalize them, since an op head read before may
be one of jj's rewrites that musubi then replaces. What was dropped is each canonical operation it
had that no reachable local operation now stands for. A realization stands for the canonical
operation its `musubi.canonical` names, even with its parents changed; any other local operation
for the one that is the same but for its parents. The machine names the dropped set as the hub
does: an operation that an abandon not yet published rewrote, as one it kept above what it
dropped, by the name it had before, which the hub still uses. It records the dropped set as
pending, writes the fix-up (below) on its head, and pushes it with the dropped set: a *supersede*.
The hub takes it with the push, in the push's compare-and-swap, and computes the rewritten history
itself, so the push carries only the machine's new operations. A supersede that loses the race, to
another push or another supersede, is rewritten by what won, and pushed again.

A machine publishes the drop of a push even if the hub has since gone back and lost it: another
machine may have taken the push first, and would push it again. That costs a record and a
[fix-up](#the-fix-up), and only after the hub loses heads.

### Taking the hub's

If the prepared base is the root, because a trim removed the old base or the hub lost records
this copy held, publication carries the current physical heads' per-machine Git fields into
the incoming local tips, merged as jj merges those heads. The root has none of this copy's
Git state. This happens after realization, under the colocated lock: a realization may be
cached from before the records arrived, or a jj command may have changed Git state since it
was made. Shared views and parents stay as the contraction names them. If other heads remain,
their shared payloads are merged before the first export. Exporting the incoming tip first could
move Git backward, then merge its record forward without writing Git again. A failed merge
publishes nothing. The next jj command therefore does not import unchanged Git refs or HEAD
as moves. Ordinary realization still inherits its parents' per-machine fields.

The hub keeps the dropped sets it took, in order, each a *record* naming operations by the ids
they had before it. A machine that lacks some of the hub's records applies them in order. It
rewrites the history it has from the hub, and its own operations the hub lacks, by contraction.
It reparents each local operation, which keeps the operation's view and per-machine fields, so
nothing is exported to `.git` and no ref moves; and it renames its own pending drops. It applies
a record only once none of its heads is dropped by it. When a record drops a head, the machine
prepares the record and fetches the hub's current history. Advancing to its surviving images
takes the record as part of the head move. This also handles a hub rollback to a head the
machine has dropped locally. So applying a record never leaves a machine two heads to
merge, and never repeats a merge another machine made. The hub never takes a head it has
dropped, and a machine never advances to one.

A machine takes the records that a reply about the head it knows announces, however old the
reply: after a restart, or from a hive made again, that can be fewer records than it took, or
others. What the records it took drop and the hub's don't then stands among its pending drops,
to publish once it has taken the hub's, unless they drop it too. The same holds for records it
received and kept in custody before writing history they explain, even if it never took them.
These are the ways pending drops grow without a new abandon. A machine publishes them again
only to a hub that lacks them, having gone back or been made again: a hub that pruned them
refuses its push, its records not being the hub's, and the machine takes them back with the
hub's ([What an abandon costs the hub](#what-an-abandon-costs-the-hub)). So the records a hub
appends are bounded by new drops and what a hub that went back lost.

Taking records has three ordering requirements:

- Before preparing any local rewrite, save the received records in custody. Custody is not an
  acknowledgement that they have been applied. If the hub loses them, the machine remains
  responsible for publishing their drops again.
- Recheck the op heads before applying the prepared rewrite. A concurrent jj command may have
  added work on the old history; that work must be renamed too before it can be published.
- Save the applied records, renamings, pending drops and head-move intent together before
  moving heads. Recovery must finish a partially published move and update workspace records,
  even after another crash or translation-cache loss, while retaining newer jj work.

These requirements keep every locally removed operation accounted for by an applied record or a
pending drop. They also let record adoption finish as part of advancing the repository; callers
must then discard plans based on the old record state. [conformance.md](conformance.md) describes
the adapter and native recovery checks.

Each machine keeps, for every id a record superseded, the id or ids it became, and translation
renames through it. An operation that a `jj` command wrote on a superseded operation, having
loaded the repository before the record arrived, is canonicalized with its parents renamed;
musubi then reparents it locally too, before anything merges it. musubi also moves each other
workspace's recorded operation to its rewrite, which `jj op abandon` itself doesn't do, and
the one `jj op abandon` ran in too, if another operation came after that workspace's last
command. It finds the rewrite through the renamings; for an operation not yet published, which
no renaming names, it looks for jj's rewrite of it, which differs only in its parents. A `jj`
command that merges such an operation with the rewritten head before musubi reparents it merges
against an older common ancestor, as jj does after a local `jj op abandon` ([races.md, "Known jj
limitations"](races.md#known-jj-limitations)).

Each machine's dropped set, and the hub's, only grows, the hub's while it doesn't go back. So an
id once superseded on a machine never again names an operation it has, whether the operation
comes back through a rejoin, an offline machine or a command that started before the abandon. A
hub that goes back loses the records it took after the head it goes back to, and an offline
machine that never saw them can then push old ids to it. The machines that have the records
publish them again, renamed to the hub's history, and the hive converges with every machine's
drops on every machine. [formal/README.md](../../formal/README.md), "Abandoned operations",
lists the theorems.

jj can bring back what `jj op abandon` dropped before musubi notices the abandon: a command in a
working copy the abandon left at an operation it rewrote integrates that operation, with
`snapshot.auto-update-stale` ([races.md, "Known jj limitations"](races.md#known-jj-limitations)).
A later abandon below can then move what came back onto other parents, so that operations
standing for the hive's are elsewhere than the hive has them, though none is dropped. musubi
then puts its history back as the hive has it, as after a restart partway through a rewrite,
and publishes nothing: what jj brought back stays, as it does on one machine.

### The fix-up

musubi works some state out from the history rather than from views: which copies are present,
each copy's latest work and forget-after, the machines the hive has known (and so the names other
machines' workspaces show under), and the expected value of a conflicted
remote bookmark. Presence, and with it the machines known, is as it was ([Presence through an
abandon](#presence-through-an-abandon)), but a copy's latest work may be work the abandon
dropped, whose time can no longer be read, and the rest would change. So the machine
that publishes a dropped set first writes, on its head, a fix-up that puts it back as it was at
its head before the abandon:

- work by every copy whose latest work or forget-after the abandon dropped, including a copy
  lost entirely when the whole accepted base becomes the root, one operation each,
  recording that work's time and forget-after, then a forget of it again if it is forgotten at
  the op head the fix-up is written on, which may have operations the rewritten history lacks,
  as a forget not yet published. A copy absent from that head's known copies keeps its presence
  from before the abandon; surviving concrete work or forget-after takes precedence over the
  saved values. The machine decides that as the fix-up starts, and saves it
  before writing anything, keeping it through a fix-up that replaces this one: written again
  after a crash, the fix-up would find its own work at the op head, and the copy present;
- in the first operation, the conflicted remote bookmarks' expected
  values as they were. These are worked out when the machine notices the abandon, and until
  the fix-up is written, every export of the machine's refs takes them as known at the op head
  they were worked out at.

Each operation is work by one copy or a forget, as presence requires, and `Presence.lean` proves
what each does to which copies are present (`fixup_present`, `pass_present`): each copy ends as
it was.
The state is then as it was at the head and from there on, and a copy whose latest work was
dropped has work again that merges keep. An operation from before the abandon keeps presence as
it was, but the rest of the rewritten history's own state, so `jj op restore` to one can
resolve a conflicted remote bookmark to the other side.

The machine remembers that it wrote this restoring work, so a failed push or restart reuses
it. The hub can nevertheless acquire the same head without its dropped set: another machine
may have received the operation before holding its records, then published it after a hub
rollback. If the machine still has pending drops and its single head equals the hub's, it
writes a fresh child to publish them. This child keeps its parent's view and records only the
fix-up marker: it replays no saved work, forget or expected values, and is not work
by a copy. A lost request reuses that child too. Before writing it the machine checks that its
current head still equals the head the core observed; a concurrent change makes the core
poll and reconsider instead.

`jj util gc` removes only data that is no longer reachable locally, so it needs no special
handling. Neither the hub nor the nodes ever delete an object, and the daemon's own cleanup on a
machine ([git backend](#git-backend)) deletes only operations that no op head reaches.

### What an abandon costs the hub

The hub keeps in memory the records it took, every id they dropped, and, for every id they
superseded, the id or ids it became. It needs them to send a machine the records it lacks, to
rename such a machine's fetch base, and to refuse a push whose new head is an old id. It writes a
rewrite of each operation a record renames and keeps the old one, and a record's line in the
`heads` log names every operation it drops. On opening a hive's store, the hub takes every record
in the log again, working out each contraction as it first did.

A record renames every operation after one it drops. In a hive that is nearly every operation
since the oldest one dropped, because merges tie every machine's work back together. So
rewriting recent operations costs little after the full identity check described above, but
trimming the history (`jj op abandon ..X`) leaves
the hub no smaller. The dropped operations' ids still take the memory that the operations did.
The kept operations' old ids are added, and every kept operation is stored twice.

So that a trim makes the hub smaller, the hub prunes the records every machine has taken, as
`Supersede.lean` models. Every push and fetch carries the records its machine took, as a count and
a digest, and names the machine, and the hub remembers, in memory, what each machine said last; a
hub that restarts waits to hear from each again. It waits for every copy the hive hasn't
forgotten: those present at its head, as the history it holds says ([Presence](#presence)), and
any machine joining, one the history doesn't know or one that asked the hub to join the hive, that
has said what it took in the last day, as a machine joining does before the hub accepts its first
push. Its first fetch realizes the hive's history, and its first push may then not land for hours,
if the machine sleeps meanwhile; a join that fails holds pruning back for a day. A copy that left
and runs `musubi join` again is known to the history but not present until its push lands, as a
copy the hive forgot is, whose daemon may go on saying what it took; only the joining copy sends
the hub the Join request, which the hub records in memory for the hive's thread, and which counts
until the copy is present at the head. So a forgotten copy whose `musubi join` failed after the
hub took it, before its push, is waited for while it goes on saying what it took, until a day
after it falls silent: a harmless exception, since it is waited for only while it lags. A hub that
opens a hive's store, as after a restart, no longer knows which machines were joining, so it
prunes nothing for an hour, as if each had said what it took just before: a machine that is online
says so again within minutes, pruning only saves memory, and nothing need be written to remember
them. A hive's thread that opens its store again after a panic keeps what it knew of the machines,
which the panic leaves as it was, so that a peer whose requests panic the hub can't keep it from
pruning. Once every machine it waits for has said it took every record the hub has, those records,
their ids and the old ids they renamed matter only to a machine coming back from before them. The
hub then forgets them, keeping only their count and digest, which a push's records must match, and
writes the `heads` log again, starting with that count and digest and naming every head as the
history now names it, so that opening takes no pruned record again. It prunes after any request
that leaves it able to, all of its records at once: the model allows any first records every
machine has taken, and pruning all of them leaves nothing to replay.

It keeps the old operations themselves, and the rewrites, in its canonical store: deleting them
would mean compacting the store's log, whose views are deltas against the one before ([Size limits
and chunking](#size-limits-and-chunking)). So a trim frees the records' memory, their words in the
`heads` log and the work of replaying them on opening, but not the old operations' disk.

A hub that has pruned an id can't refuse a push to it by the id. The check of each push's
records keeps it out instead: a push whose records are the hub's comes from a machine that took
every record the hub pruned, and a machine never pushes an operation that a record it took
drops, which it asserts before every push. A buggy machine that did could make the hub take
back an operation it pruned, which nothing the hub checks would catch: the protocol trusts every
machine that can reach the hub, as with any history it pushes. `Supersede.lean` proves that,
whatever the hub prunes, it never takes a head it dropped while it doesn't go back
(`dropped_never_head`), as long as no machine names such an operation; and that every machine
still converges when the hub prunes only records every machine has taken
(`eventually_convergesS`, `Exec.sexec_allPruned`).

What this means for a machine:

- One that is offline, and that the hive hasn't forgotten, holds pruning back until it syncs.
- Once the hive forgets a copy, the hub no longer waits for it, so forgetting is no longer soft
  ([Copies that go away](#copies-that-go-away)) for a copy behind what the hub has pruned. It
  never took the records the hub pruned, which the hub can no longer send, and it may hold
  operations they drop, under ids the hub no longer knows (`behind_not_carried`). Its next
  fetch says so, and it stops, with the message for a history that no longer matches the hive's:
  a new copy takes its work. So does a copy that left, if the hub pruned while it was out,
  before it ran `musubi join` again; from then on the hub waits for it as for a copy new to the
  hive (`a_copy_joining_again_is_waited_for`, `a_copy_joining_again_away_for_over_a_day_stops`).
- So does a copy joining whose first sync realized the hive's history but stopped before its
  first push landed, and that the hub then didn't hear from for a day, or that was away when
  the hub restarted and for an hour after: the hub no longer waits for it. A copy new to the
  hive has had nothing reach the hive until its push lands, and the history doesn't know it. It
  could join again on the root from its view as it is, but merging that view with the hive's
  against the root's, rather than against the head it realized, would bring back the commits
  the hive abandoned since, and those it rewrote as divergent changes; so it stops instead
  (`a_joining_machine_away_for_over_a_day_stops`,
  `a_joining_machine_away_for_over_an_hour_after_a_hub_restart_stops`).
- One that took the records the hub pruned, but holds fewer now, takes the hub's from them all
  the same. A machine takes the records an old reply announces ([Taking the
  hub's](#taking-the-hubs)), which may be fewer than it said it took, and the hub may prune
  them meanwhile. The hub prunes only records every machine said it took, and each said so of
  records it held then, so a machine keeps, in its `records.json`, the records it took and no
  longer holds: among those and the ones it holds, it finds the ones the hub pruned by their
  count and digest, and takes the hub's after them, dropping what it had left to publish of
  them. A reply that it can't complete from the records it holds, as one to a request sent
  before it took fewer, it ignores: the reply to its next request starts from the pruned ones.
  `Exec.sexec_announced_held` proves that every machine the hub waits for has held what it
  pruned. But a machine that joined after a prune, holding the pruned records only by their
  count and digest, no longer finds them once it has taken other records whole in their place
  (below): if the hub's pruned records start with those again and it holds fewer, it stops, as
  lacking records the hub pruned. The model, whose machines are fixed, has no such machine.
- One that joins after a prune starts from the hub's records where it pruned them, holding
  their count and digest but none of the pruned ids, as the `Fetched` reply carries them.
  Only a machine with nothing of the hive's may: one that joined on the root, and has taken no
  records, pushed nothing and realized nothing since, as its `records.json` says. It holds
  nothing they drop. The model, whose machines are fixed, doesn't cover joining.
- A hub that goes back to before a prune, as when a power cut loses the `heads` log it wrote,
  names the records again, and every machine carries on. One made again, or gone back further, has
  lost records that a machine that joined after a prune knows only by count and digest, and can't
  publish again; the machines that took them whole publish them again, but perhaps as fewer
  records, whose digest that machine can't match. Holding nothing they drop, it takes the hub's
  records whole in their place, provided the hub has pruned none: whichever of them drops what it
  has, it drops by name. If the hub has pruned some meanwhile, it stops.

## Transport

The transport provides bounded request/response messages and subscriptions for head
notifications. Each hive has its own worker, which opens its store on demand and answers one
request at a time. This serializes a push's checks and head update without making unrelated
hives wait. Only joining creates a hive or makes a missing one again; an ordinary sync cannot
silently create a hive on the wrong hub. Operations and objects are checked against their
content hashes on receipt.

The hub's in-memory network and stream connections carry the same subjects and messages. Tests
can interrupt or reorder delivery on the in-memory network. Streams connect through a local
socket or the standard input and output of `musubi hub connect` over ssh. An incomplete frame
is never delivered.

A disconnected stream fails its in-flight requests and reconnects with its subscriptions
restored. Calls have bounded waits, and a peer that cannot keep up with queued frames is
disconnected rather than allowed to accumulate unbounded work. Reconnection triggers a sync,
since notifications may have been missed. Invalid greetings and repeated connection failures
back off; only a valid hub greeting counts as a successful connection. A bounded shell banner
may precede that greeting, whose unambiguous prefix prevents mistaking shell output for the
protocol.

Each stream connection admits at most 1024 subscriptions and 1024 requests in flight, with
distinct ids within each kind. Excess or duplicate live ids close the connection before the
new work starts. The client checks the same limits before sending; subscriptions to a subject
already on the connection share its slot. There is no unsubscribe frame, so a client keeps a
subject's slot until disconnect. Completed relay tasks release their slots. These limits bound
the relay's tasks, not work a timed-out request has already queued inside the hub.

### Running a hub

A hub is for one person's machines or a team whose members trust each other: anyone who can
reach it can read and write every hive. Its local socket is accessible only to its owner and
lives with the hub, so a temporary-file cleaner or the end of a login does not remove it.
Directory locks prevent two processes from serving the same store; the default-hub lock also
prevents accidentally starting a second default hub. Explicit directories allow separate hubs.

Each hive has its own stored history, objects and membership metadata. Removing a hive leaves a
tombstone after its data is deleted, so its machines leave rather than recreate it. A corrupt
store is set aside without that tombstone: its hive can be filled again by the machines
([Replacing the hub](#replacing-the-hub)). The
[file reference](../reference/configuration.md#files-and-directories) lists the layout.

The hub keeps activity counters and the latest daemon reports in memory for `musubi top`.
Reports identify the head a machine knows, its sync result and its release; reporting does not
hold up a sync. None of this is durable, and a restart begins a fresh observation period.

### Reaching a hub over ssh

An ssh destination uses the user's ssh configuration, including aliases and proxy commands.
Joining installs a machine-specific key restricted to `musubi hub connect`, using the user's
ordinary ssh access while interactive authentication is possible. The daemon then connects
without prompting or requiring an ssh agent for that key. The restricted command reaches the
hub's local socket; the hub itself needs no exposed network listener.

Copies on one machine share the daemon's connection to each hub. The connection belongs to the
daemon's runtime and lasts while any copy needs it, so one repository stopping does not break
the others. Large transfers can use a separate connection to avoid delaying small requests,
falling back to the shared one if it cannot be opened. The
[connection setting](../reference/configuration.md) controls this policy.

Every reconnect starts a fresh ssh process. Keepalives and sleep detection discard dead
connections, while backoff prevents repeated ssh failures from launching processes or tunnel
login prompts continuously. It is the connection that tells a dead link: ssh ends one that
hears nothing from the hub's machine for a minute, which fails every request in flight on it at
once. A request's deadline, two minutes, is how long a hub that is there may take to answer,
and how long the link may take to carry a chunk; a hub that takes longer answers the request
when the node asks again. Over a slow link, the hub machine's sshd says how much more it may
take, about every 100 KB of an upload, so a minute without a word from it means the link
carried under about 20 kbit/s for that minute, well under the 70 kbit/s a chunk needs to arrive
within its deadline. ssh's errors remain available in the copy's sync status.

## Local integration

Each user runs one daemon, with an independent worker for each repository in its state file.
`musubi create`, `join` and `clone` record membership and ask the daemon to serve the copy,
starting it if necessary, then wait for its first sync. The local control connection exposes
status and sync progress while that work runs.

Only the owner may reach the control socket. musubi refuses unsafe socket directories or a
named pipe another user has claimed, and a lock prevents a second daemon from taking over the
endpoint. Commands check the daemon's version before using it. Installation delegates startup
to the platform's login service where supported; commands use that service too, rather than
starting a competing daemon. The service retains the installing environment needed to find
programs, jj configuration and musubi state. The
[command reference](../reference/commands.md#run-the-daemon) describes daemon installation.

A daemon outlives the command and login session that started it. Repository-specific git
environment variables therefore reach neither the daemon nor the git processes musubi runs,
and those processes run no git hooks. Signing and proxy hops may still need an ssh agent: a
stable link in musubi's state directory follows the latest responsive agent supplied by a
command, so the daemon can use a later session's agent after its original session ends.

Commands update the state file under a lock and publish the complete replacement together,
protecting concurrent joins and process-crash recovery. There is no power-loss durability
guarantee ([AGENTS.md, "Resilience"](../../AGENTS.md#resilience)). The daemon watches op heads
and jj's record of repository moves, with polling as a fallback; [copies.md](copies.md) gives
the checks that keep moved or replaced repositories from syncing under the wrong identity.

Repository loads and merges use jj-lib's repo loader and op-heads lock, so concurrent jj
commands participate in the same reconciliation. In colocated repositories, realization also
holds jj's import/export lock while rereading the local heads, merging, exporting and
publishing. Publishing only the exported merge prevents a later jj import from mistaking
musubi's ref update for a git change. When taking abandonment records, this merge uses the
heads as the rewritten history names them. Commands in secondary workspaces do not all take
the colocated import/export lock; [races.md](races.md#remotes) records that limitation.

Merges load the same system, user, repo and workspace configuration as jj, including identity
and signing settings. musubi's own settings live under `musubi.` in jj's config. Machine-wide
settings come from user config alone so every repository finds the same daemon. Local indexes,
repository identity and working-copy state stay local
([What is replicated](#what-is-replicated)).

Publication follows dependency order: objects, views, operations with their ancestors, and only
then the op head. Together with the record-taking order in [Taking the hub's](#taking-the-hubs),
this keeps published history readable across interruption and restart.
[Conformance](conformance.md) states which native boundaries are checked against the models.

## Compatibility

jj's operation format changes every few months, almost always by adding fields, and jj keeps
reading older files. Ids are hashes of jj-lib's in-memory structs, not of file bytes, and jj-lib
never verifies them on read. Two consequences:

- An older jj-lib decoding an operation written by a newer `jj` silently drops the fields it
  doesn't know, and canonicalizing it would lose them. So before canonicalizing a local operation
  or view, musubi walks its protobuf encoding and refuses any field number that jj-lib 0.47
  doesn't define. A newer `jj` CLI writing to the repository is therefore a clear error, not
  silent data loss.
- Canonical operations are always written by musubi's pinned jj-lib, so a receiver can verify each
  canonical operation and view by decoding and re-hashing it. A mismatch means a peer is running
  an incompatible version, or is lying.

Every message between a node and the hub starts with its protocol and jj-lib versions and the
sender's release of musubi, encoded the same way in every release. Each side reads them first and
refuses a message whose protocol or jj-lib versions aren't its own, so that a message from another
release is refused as such rather than misread. A daemon that hears from a hub of a newer release,
in the hub's answer to its report after each sync, which comes even when the hub refuses it, runs
`musubi.upgrade-command` for that release (`crates/musubi/src/upgrade.rs`). A build deployed from
source gives, after its release, when it was deployed and its commit, as semver build metadata
(`crates/musubi-sync/build.rs`), which the daemon orders releases by too, so that a build
deployed later is newer, without a version of its own.

On Unix, the upgrade command inherits `upgrade.lock` as standard input, so it can outlive a
stopped daemon without a new daemon starting an upgrade beside it. A worker that encounters a busy
lock leaves that release eligible for a later sync to try; a failed command consumes its
attempt until the daemon restarts. Installers must preserve that input and remain in the
foreground. Unix upgrade commands have their own process group, which the one-hour timeout
kills before reaping the shell; Windows timeouts stop the command process. The timeout runs
only in the launching daemon: if that daemon stops, a surviving command has no monitor.
Detached installers are outside that cleanup. `upgrade::process_tests` checks these Unix OS
boundaries rather than modeling them in Lean; Windows lock inheritance is not tested here.

## Testing

The hub logic and the node sync logic are sans-IO state machines (`crates/musubi-core`): they do
no I/O themselves, but consume events and produce effects. That keeps them deterministic under
test, and lets them correspond step by step to the Lean model of the protocol, which proves its
safety properties, and convergence for a model of the nodes' policy over reliable delivery
([formal/README.md](../../formal/README.md),
[conformance.md](conformance.md)). [testing-philosophy.md](testing-philosophy.md) says what a test
must protect, and [testing.md](testing.md) describes each layer of tests.
