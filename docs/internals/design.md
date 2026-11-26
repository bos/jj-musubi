# jj-musubi design

jj-musubi keeps one jj repository in sync across several machines. A daemon on each machine
watches the repository's operation log, publishes new operations, and the objects they refer to,
to a hub, and applies the operations that other machines published. A commit, rebase or abandon on
one machine reaches the others through the hub, and a machine that was offline catches up when
it reconnects.

This document gives musubi's design rules and the reasons for them. [protocol.md](protocol.md)
specifies the messages between nodes and the hub and the properties they guarantee, and
[races.md](races.md) the outcome of each race.

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

Sync writes jj's operation log and commit store and, in Git-backed repos, the object database
and refs. Opt-in background snapshots also read working-copy files and record snapshot state
with jj-lib. Background snapshots leave checked-out files in place. Sync leaves Git remote
definitions and jj config alone ([Local configuration](#local-configuration)).

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
    for a merge, their three-way merge, as jj's merge of the operations would make it. A
    change in workspace names goes through jj's merge: removing a workspace can also remove
    its Git HEAD record, even if those records agree in all parents. That makes
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
is used.

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
original identity (`musubi.original-parents`), not by an operation's id, which an earlier
release changed by contracting history; an operation it rewrote may carry the presence it had
(`musubi.presence`), which is read in place of the one its new parents give. History that was
never contracted reads the same either way. Generation numbers bound the ancestry queries, and a
cache avoids walking the whole history on each sync.
[conformance.md, "Presence"](conformance.md#presence) describes the check against the model.

### Which workspaces are this machine's own

In a local view, this machine's workspaces have plain names (`default`), and another machine's are
named `<machine>/<workspace>` (`laptop/default`). jj allows `/` in a workspace name too, but
musubi doesn't take a name of that form for one of this machine's own: whatever made it, a local
name with a `/` is never published under this machine's key (`canonical_view`,
`is_publishable`). So no other machine's workspace, under any name this machine shows it by now
or showed it by before, can become this machine's own, whatever `jj undo`, `jj op restore`,
`jj op revert` or `jj op abandon` bring back (#167). Canonicalizing needs no history to decide it,
and stays deterministic.

Nor does musubi keep such a name here, unpublished, unless jj's workspace store records a
directory for it, as it does for every workspace of this machine's and for none of another's
(`own_of_view`), and then the copy doesn't sync (below). Any other name with a `/` is a name
another machine's workspace is shown by, as this machine shows it or showed it in a view `jj undo`
or `jj op restore` brings back, under a name the hive no longer gives it, even from a hive the
copy left before joining afresh. musubi takes it for no workspace of this machine's: realizations
show other machines' workspaces as the canonical view has them, and the sync that shows them again
drops the rest (`show_other_workspaces`). The store is read as it is now, not as it was when an
operation ran, so a workspace with a `/` that a jj made before it recorded directories counts as
another machine's, and is dropped. Compatibility until 2027-02-25: an earlier release kept such a
workspace, so until a copy first finds none, it refuses to sync while its op heads have one that
no other machine's workspace is shown by, as of its nearest translated operations, saying to
rename it or forget it (`unrecorded_workspaces`), and then records that it checked, in
`.jj/repo/musubi/unrecorded_workspaces_checked`. A repository that has never been part of a hive
refuses to join with one, since joining on the root forgets it, and so records the check at its
first join.

### Machine names

A machine's key keeps the name it joined under (`laptop#1a2b3c4d`), but its name in the hive can
change. Its daemon records the name `musubi.machine-name` gives it, read from the machine's jj
config, not a repository's, whenever that differs from the copy's name in the hive: an operation
that is the copy's work and records `musubi.name` (`record_name`, as `record_forget_after`
records `musubi.forget-after`). A copy's name at an operation is the greatest of its latest such
records there, or, with none, the name its key embeds (`Presence::name`; `NameIs` in
`formal/Musubi/Identity.lean`). Forgets leave the records, so a copy that comes back keeps its
name. With the setting unset, nothing is recorded: a copy keeps its name, and never follows the
hostname after its join. `--machine` on `create`, `join` and `clone` sets the setting where
nothing does, and is refused where it names the machine otherwise, or, in a repository with a
key, where it isn't that key's name or the setting's.

At a canonical operation, the machines named are the copies present there (and any with
workspaces in its view, as one that joined before joining was work), by their names there:
nothing remembers a machine forgotten, or a name a machine had before. Of the machines that share
a name, the one that has been present under it longest keeps it plain: the smallest by since,
the generation of its latest mark, a record of its name or a return (work made where it was
absent just before: a join, or its first work after a forget that saw all its work), and then by
key (`Presence::since`; `SinceIs`). Generation, not ancestry, so that the order is total:
concurrent claims are settled by their generations, then by key, the same way on every machine.
So a machine that stays keeps its label when another renames into its name or comes back with
it (`keeps_label`). Those machines are named first, then the rest, each taking the first of its
candidates that no machine before it took and that starts no name of this machine's own and `/`:
its name and the start of its key's random suffix (`laptop-1a2b`; `local_names`), its name and
the whole suffix, then that with ever more dashes. `formal/Musubi/Identity.lean` proves that no
two workspaces are shown alike (`localName_injective`), and that every machine names an operation
alike, from its history alone (`naming_local`). The hub names the same machines by the same rule
for `musubi list`, from its head (`HiveIndex::machines`), so a machine shows here as the hub lists
it but where a workspace of this machine's makes its name longer here; a copy whose join the hub
has taken but that hasn't pushed is listed by the name its key embeds, after the others.
`musubi status` names this machine among the copies present (`name_in_hive`); `musubi list` shows
a copy here by the name the hub lists it under where that isn't its own (`listed_as`); and
`musubi forget` takes this machine's key and that name for this machine's, and any other name it
could be shown under by its name now, where no other machine could be. This machine's own names as
of a canonical operation are its workspaces in that view, or, where the hive has forgotten it,
those as of its latest work, which `Presence` keeps through forgets (`own_names`).

Labels change over time, so a name is read as of the operation it was made at. Canonicalizing a
`jj` command reads the names in its local view by its canonical parents' naming
(`inherited_from_parents`), and a command that goes back to an older operation (`jj undo`, `jj op
restore`, `jj op revert`) by the naming of the canonical operation the view it brings back came
from (`started_from`): after a rename, or a forget and a rename into the forgotten machine's
name, the old name stands for the workspace it stood for then, or for none. A name left in the
local view at another commit than the hive gives the workspace it names now is shown at the
hive's commit at the next sync (`show_other_workspaces`), so that it isn't taken later as a move of
that workspace. `jj op log` keeps the names operations were realized under.

A copy doesn't sync while it has a workspace of its own whose name has a `/`: one in its op
heads' views that jj's workspace store records a directory for, whether the directory is there or
not (`slashed_workspaces`). jj records one from `jj workspace add` on, and moves it with `jj
workspace rename`; musubi makes no working copies for other machines' workspaces, so none is
recorded for them. `jj workspace forget` leaves the record, but jj ignores it once the name has
left the view, and so does musubi. A sync stops as it starts, before it shows other machines'
workspaces again, and at each step, before it reads the op heads or publishes a realization
(`refuse_slashed_workspaces`). `musubi sync`, `musubi status`, `musubi create`, `musubi join`
and `musubi leave` (unless forced) say so first, with the command to run.
The daemon waits for the next local operation, as for a publication hold, so the rename's
operation wakes it. So whenever musubi canonicalizes, realizes or shows other machines'
workspaces, every `/` name in this machine's op heads is a name another machine's workspace
is shown by, now or in a view brought back.

A record `jj workspace forget` left counts once this machine shows another machine's workspace by
its name, or the copy adds a workspace of its own by it, and the copy stops syncing. musubi
doesn't tell the two apart, and says so in one hint (`slashed_hint`): rename the workspace in its
directory, or, if the user ran `jj workspace forget` on it earlier, move out any ignored files to
keep and run `jj workspace remove`, which keeps the tracked files in a commit, deletes the
directory and drops the record; `jj workspace rename` there would make the other machine's
workspace this machine's. Where the directory is missing, the hint adds `jj workspace forget` for
a workspace no longer needed, and mounting the disk to rename it there; for a leftover whose
directory is gone, `jj workspace remove` can't open it, and the troubleshooting guide gives the
commands that make one to remove. musubi tried to tell by the commit the hive gives the other
machine's workspace, and by the operation and change a directory's working-copy state records;
each took some live workspace, after a rebase or a squash or abandon of its commit, for a
leftover, and so pointed at a removal that deletes the directory of a workspace in use, so the
user, who knows, chooses. musubi doesn't drop the record itself: outside jj's locks it could drop
that of a workspace being added under the name.

Otherwise a workspace this machine adds as `laptop/x`, beside the laptop's `x`, which the laptop
adds meanwhile, would be one workspace to jj's merge with it, and its directory would snapshot
into the laptop's working copy. musubi once kept such names apart by whether this machine had a
working copy for them, asking jj's workspace store as it is now rather than as it was when an
operation ran, which a directory away during a sync got wrong.

Which of another machine's workspaces a name is comes from the operation's parents: each canonical
parent's workspaces are named as a realization of it names them, from its canonical view alone
(`inherited_from_parents`), and not from jj's workspace store, which changes after an operation
runs. A name in a `jj` command's view stands for the laptop's workspace only where a view the
command started from had it at the commit the canonical parents give that workspace, as a
realization shows it and as an earlier command that moved it left it (`move_others_here`). So a
workspace this machine adds under the name, as after `jj workspace forget laptop/default` here,
never moves the laptop's, though `jj workspace add` moves the new workspace to its commit in a
second operation that starts from a view with the name, and though commands run in it are
canonicalized only after it is renamed: adding changes nothing of another machine's. An operation
that goes back to an older one (`jj undo`, `jj op restore`, `jj op revert`) starts from the view
it brings back, and a name there stands for the laptop's workspace only at the commit that view's
canonical form gives it; a revert starts from its parents' views too, and each view that has the
name must agree. So a workspace of this machine's by the name, brought back over the laptop's or
beside it, moves nothing of the laptop's. musubi's own operations add no names: they show other
machines' workspaces again under the names the hive gives them.

[races.md](races.md#workspaces) says where a `jj` command racing a sync can still put the two
under one name.

### A forgotten copy's working copies

A machine the hive has forgotten keeps its own working copies. When it realizes an operation whose
canonical view leaves it out, it keeps its workspaces as the realization of the parent with its
latest work had them (`latest_work_parent`, by `Presence::worked`), following the operation's
rewrites (`with_own_workspaces`). So at a merge of a forget that saw its latest work with an
operation that saw only earlier work, it keeps the workspaces the forget's realization had. A
parent whose history has every other parent's latest work by the machine, none of it its own
latest, has the later work, even if an earlier release's contraction has erased that work since,
so that no operation stands for it. Otherwise the parent whose surviving work includes every
other's has it, and erased work counts as below surviving work, as in presence. It keeps them so
too at work by it that another machine wrote, as an earlier release's fix-up was, where it is
present: a machine that had forgotten it wrote that view without its workspaces, and only its own
operations remove them. Where another machine rewrote its working-copy commit, as one can while no
other machine sees it as a working copy, it follows the rewrite
(`replace_abandoned_working_copies`). Where the forget abandoned an empty working-copy commit, it
stays on the hidden commit, since a new one would be an empty commit of no one's on every other
machine. jj's next snapshot, or any command that rewrites `@`, makes a new visible commit of it,
and that work publishes the machine's workspaces again. No other machine sees the commit as a
working copy, so jj doesn't rebase it when another machine rewrites or abandons its parents, and
the snapshot would bring them back. So the machine rebases it itself, as jj would have rebased a
working-copy commit it saw, writing it hidden and recording no rewrite, in an operation that isn't
its work, so that it stays forgotten (`replace_abandoned_working_copies`).

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

After restoring the working copies, leave writes a local operation that marks where its old
key stopped owning new work. It clears the machine key and membership record. A subsequent
join uses a fresh key. The detach operation and the retired keys preserve the translation of
native operations from before the detach, including after rebuilding the translation cache.

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
translating an old operation. Sync never applies configuration.

## Ordering: one hub, one canonical head

When two machines make concurrent operations, someone has to merge them. Suppose each machine
merged independently. A's operation rewrites commit X; B's concurrent operation adds a child Y of
X. A's merge rebases Y onto the rewritten X, giving Y'. B's merge does the same, giving Y''. Y'
and Y'' have different committer timestamps, so they are different commits, and the hive ends up
with a spurious divergent change.

The hub keeps a single canonical head. Pushes are fast-forward updates: the hub never rewrites
history, and a copy that has lost history the hub has stops instead ([Lost
history](#lost-history)). A node pushes by uploading what the hub lacks and asking it to
compare-and-swap the canonical head from H to H', which the hub does only if H' descends from H
and everything H' refers to is stored. A node pulls by fetching the operations between its
last-known canonical head and the current one, realizing them in topological order, and publishing
the realization of the new head. If the node has local operations the canonical head lacks, its
push fails; it pulls, jj merges its local heads, which include the new realization, and it pushes
the merge. So each merge is made exactly once, by the node that owns the concurrent local work,
the same outcome as two jj processes on one machine: every merge has a parent that only its
creator had, so two machines never make the same one. [protocol.md](protocol.md) specifies these
steps, and the [formal model](../../formal/README.md) proves this and the protocol's other safety
properties.

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
from the root. This matters after `jj util gc`, which can collect objects an old base's view
refers to.

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
base unreachable, falsely indicating lost history ([Lost history](#lost-history)). Joining
after a leave records fresh work under a new key on top of that history. `create` and `join`
say so when the hive isn't one the history records a join to, with the number of canonical
operations the copy holds: a bound on what it sends, cheap to count.

`--fresh` drops that history instead, so that the join is on the root, as a repository's
that never joined: the canonical store, join records, translations, and the accepted and
pushed markers and publication offers that name canonical operations, all of which go
together, so the accepted base goes with them. It keeps the local operation log and the
retired keys, which still name the earlier operations' machines and keep a new key from
repeating an old one. A repository whose hive was removed, or that kept a key from a stopped
first sync, first leaves as `musubi leave` would. The discard is marked before anything is
removed and unmarked after, and any join that finds the mark finishes it, since a join over
part of the history would carry a history with holes (`Copies.Detach`,
[conformance.md](conformance.md#detach-and-join-write-boundaries)). Joining a hive afresh
merges as any new copy does, against the root: where the hive rewrote commits this copy still
has, both show, divergent, which is why a plain `join` back into a hive the copy left carries
its history instead. The local history before such a join holds realizations of canonical
operations the copy no longer has, or has again from the hive it left: `canonicalize` takes an
unmapped one below a join point as from before the join, as any other operation there, so that
a late operation on that history waits for jj's merge rather than failing every sync. Other machines' workspaces the copy still shows,
`beta/x`, are removed before the join point, since nothing else would remove them.

Carrying history does not bring every old member into a different hive. The join forgets copies
absent from the target hive, except the joining copy itself; copies already present or joining
there stay present. Joining again while still a member of the same hive, including one
remade on another hub, forgets none.
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

The explicit `join` and `create` commands inspect remote-bookmark conflicts after their first
sync. Native merging already selects a descendant from either snapshot. For the remaining
ambiguity, each command attempts one native `jj --ignore-working-copy git fetch` per conflicted
remote. Exact remote and branch selectors fetch only affected bookmarks, overriding configured
filters. The command selects a verified colocated workspace, if any exists, to take jj's Git
import/export lock; this can be a secondary workspace of a non-colocated primary workspace. Each
attempt is bounded to 30 seconds. Timeout or interruption terminates jj and its Git/SSH
descendants using a Unix process group or Windows job, and reaps the child. An interrupt stops the
command, leaving the copy joined. Otherwise the command syncs and reports unresolved remotes.
Fetch changes recorded state without snapshotting or updating checkout files; normal native fetch
semantics preserve and merge local bookmark differences. Failed calls can retain completed
effects, so the second sync runs after failed attempts too. There is no retry loop, timestamp
ranking, or machine priority. Ordinary sync does not contact Git remotes. This command policy adds
native operations; it does not change canonical views or their merge rules.

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

## Snapshot publication budgets

The node gates a publication before `pushing` and before preparing or uploading attachments.
Incoming replies and objects are applied first; a held sender remains a receiver. A filesystem
publication lock serializes this path with inspection, exact approval and cleanup across
processes. The local control protocol changes with this feature so a new CLI cannot hand an
approval or cleanup to an older unguarded daemon.

The budget measures content required only by outgoing recovery history, relative to the
accepted basis and intentional change versions. Walk every required commit and its parents,
then every raw tree side, including directory sides of conflicts and symlink targets. Count
distinct extra paths and distinct extra content bytes. A new path pointing to already required
content costs a path but no bytes. File and symlink object kinds are distinct; submodule links
cost paths but no external repository content bytes. Equal versions retained by several
operations contribute once to the total; per-operation contributions overlap.

Intent comes from actual jj transaction records. Automatic snapshots and automatic divergent
operation reconciliation create no intent. Explicit creation/rewrite outputs and selected
history references do; a freshly created working-copy continuation with no predecessors is
excluded, since `jj commit PATH` leaves its unselected remainder there. An unrelated explicit
command does not bless unchanged automatically rebased descendants. Initial joining consults
pre-join native operation facts, restricted to commit versions in the exported closure; it
neither exports that whole recovery log nor blesses arbitrary current working-copy content.
Selections come from intrinsic creation/rewrite records, parents chosen for fresh working-copy
tips, and pinned command descriptions containing full commit ids or selected reference names.
They never come from differences against parent views: native operation abandonment can replace
those parents, and garbage collection can erase the original views before the first inspection.
Unknown command records grant only their intrinsic write-output exemptions and block cleanup;
exact publication approval remains available. Bootstrap joins use the same classification.
The pinned jj argument encoding identifies explicit `jj git import/init/clone` invocations,
including global options; unknown or ambiguous encodings are conservative. jj's quoting cannot
distinguish some apostrophes and trailing backslashes, so those values grant no exemption.
Automatic imports grant no
write exemptions: they can rebase existing descendants or newly index a Git-only snapshot left
by an interrupted export. Explicit Git imports freeze output roots before stripping private
Git refs only when every possible selected Git target is already in those outputs' commit
closure. Importing an existing unexplained target remains incomplete: unchanged Git refs can
point to automatically moved
working-copy bookmarks, so exempting the whole ref set would approve unrelated snapshots.

The approval token hashes this copy's identity, accepted basis, applicable limits and exact
outgoing operation ids, charged file-version set and byte count. Approval is exact; any change is
rechecked. The sender records a compact frontier of every attempted publication *before*
uploading, retaining incomparable histories. Only exact ancestry subsumes an older frontier
entry: equal original ids after an earlier release's contraction, or cleanup's, cannot establish
that an older uploaded ancestor was never shared. On activation in an existing copy,
pre-activation heads and saved offers are conservatively frozen. Malformed or missing source
bodies fail closed. Exclusive creation prevents a late initializer from replacing a sender's
record, and a checksum detects mixed old/new records after an interrupted in-place write. This is
provenance, not a durable network acknowledgement.

Cleanup selects whole operations known never to have been offered. It never enlarges a user's
selection. Before contracting native parents, freeze each survivor's source intent in
`musubi.publication-intent`. This hash-visible annotation is a separate body transformation from
`Contract.cpar`; infer no new intent from the new parent relation. Declared roots must also be
predecessor-record keys. Changed operations receive new physical identities, and preparation
refuses coalescing identities.

A selected operation that records the copy's name (`musubi.name`, "Machine names") stays, so
that the copy keeps its name, and the mark that decides which of the copies sharing it keeps it
plain stays where it was: a record in the checkpoint would mark the copy anew, at the head, and
in a clash it could lose its plain name. It changes nothing else, so it takes its new parents'
view, merged as jj merges operations where it has several, and retains nothing they don't.
Its since, a generation, can still fall, as removing operations below it shortens the longest
path there, so a claim to the name that lost to a concurrent one by no more than that can win
instead, alike on every machine (races.md). No cleanup can avoid that while since is a
generation: keeping each removed operation's place in the history would keep the operations
the user chose to drop. A pruned operation that brought the copy back after a forget isn't
kept: the next work that is, or the checkpoint, brings it back instead, later.

A fresh checkpoint retains the exact current view and every intentional commit version, with
intentional predecessor links connected across removed automatic versions. It records genuine
new local work, the local lease and expected Git-ref values. It does not invent activity for other
copies. Before installing its op head under the op-head lock, canonicalize and read the prepared
native bodies. Require exact current view, expected values, full foreign causal presence, each
survivor's view and frozen intent, retained intentional commit references, and the exact content
set and bytes promised by the preview. Compare source heads again; an error leaves them untouched.

Workspace records move only when their exact working-copy commit survives. A command finishing
later on old ancestry may reintroduce recovery history, which is checked by the same gate.
Pruning removes references, not physical object files; normal jj garbage collection reclaims
unreachable objects. It is not retroactive secret removal.

`Publication.lean` and its native/oracle conformance fixtures cover the accounting and cleanup
contract. The existing sync safety checks remain applicable to permitted sends. Progress is
conditional on publication holds eventually being resolved, disabled, or approved; the existing
convergence theorem does not prove that a user will resolve a deliberate hold.

## Lost history

`jj op abandon` removes operations from the operation log. jj keeps every view, so the repository
is as it was at each operation that stays, but it rewrites every operation after the removed ones
with a new id, since an operation's id hashes its parents. musubi doesn't pass that on.
Replicating it would remove nothing a user wanted gone, because musubi never deletes an object
([git backend](#git-backend)): a committed secret stays in the hub's store and on every machine's
disk until someone runs a pruning gc there. And syncing what an abandon left would put the removed
operations back on every machine, under ids of their own. So a copy that loses history the hive
has stops syncing, and the hive carries on without it. The hub never learns of the abandon, and
the other machines keep the operations.

A sync notices it where it reads the op heads, before it rewrites or publishes anything. The
heads, canonicalized, must reach two operations: the hub's head this copy accepted last (its fetch
base), and the head it pushed last that the hub took. A base the canonical store doesn't have, as
after a hub was made again, or the root, says nothing, so neither is watched. A realization whose
parents no longer reach every parent of the canonical operation it stands for is lost history too.
Either raises one error, "this repository lost history the hive has (was `jj op abandon` run?)"
(`NodeError::UnreachableHistory`, `NodeError::RewrittenRealization`). The copy publishes and
changes nothing. The check reads the heads, not a record of what was done, so every later look
finds the same loss, and retrying or rejoining doesn't help. `musubi status` shows the message. If
the user brings the operations back, as `jj op integrate` can, the heads reach them again and the
copy syncs on. Otherwise they make a new copy and bring their work across ([troubleshooting.md,
"Rescue work in a new copy"](../troubleshooting.md#rescue-work-in-a-new-copy)).

These are not lost history:

- **History from before the join.** The join operation's parent is the root, so nothing below it
  is watched, and `jj op abandon` there rewrites only the operations above it. The join point
  is recognized by what identifies it apart from its parents, its view, metadata and rewrites
  (`fingerprint`), which an abandon doesn't change, so it still stands for the join operation.
  `op_abandon_of_pre_join_history_is_harmless` pins this.
- **Operations not yet sent.** Nothing the hub accepted depends on them, so abandoning them,
  or everything before the first sync, changes nothing the hive has
  (`op_abandon_of_unpublished_operations_stays_here`,
  `abandoning_everything_before_the_first_sync_syncs_on`). jj rewrites the realizations that
  sat beside such an operation onto its parents. A realization on other parents is accepted
  while its parents still reach every parent of its canonical operation, and `reparent_late`
  puts it back on them. `musubi sync --prune` removes unsent operations on purpose
  ([Snapshot publication budgets](#snapshot-publication-budgets)).
- **A rewrite of an operation this machine wrote, by itself.** musubi marks its rewrite of such
  an operation with its canonical form, as it marks a realization, but without the original
  parents every canonical operation records. Abandoning work below one translates it afresh, as
  an unmarked operation would be, and the fetch base and the accepted push say whether the hub
  had what went (`abandoning_own_work_below_a_rewritten_merge_keeps_syncing`).
- **`jj undo`, `jj redo` and `jj op restore`.** They add operations and lose none.

`op_abandon_of_published_history_stops_that_copy` pins the stop: the copy publishes nothing,
carries on failing, and leaves its history as it was, while another machine syncs on. A base out
of reach where jj rewrote nothing, which no abandon explains, stops the copy the same way
(`an_unexplained_lost_base_pauses_without_dropping`). [races.md, "Operation
history"](races.md#operation-history) has the other races.

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
status and sync progress while that work runs. Until the first sync answers, the command can
stop it: by asking, when interrupted, or by going away, as when it is killed, which closes
its connection. The daemon stops the sync only while the copy has applied none of the hive's
history: a gate the sync passes before each realization or advance of the op heads either
refuses, once the sync is stopped, or ends the time it can be stopped. Until then the sync has
written none of the hive's history where jj shows it, only objects jj doesn't reach and
operations of this machine's own, such as a merge of its op heads, so ending it wherever it
waits leaves the repository with none of the hive's history. Only a repository that had no
record of a hive can stop it: stopping drops the record. The copy then leaves its hive without
telling it, which would take the sync that was stopped, keeping the key the hub took for a join
again, or for `musubi leave` to retire; a copy whose sync has begun applying finishes it.

Only the owner may reach the control socket. musubi refuses unsafe socket directories or a
named pipe another user has claimed, and a lock prevents a second daemon from taking over the
endpoint. Installation delegates startup to the platform's login service where supported;
commands use that service too, rather than starting a competing daemon. The service retains
the installing environment needed to find programs, jj configuration and musubi state. The
[command reference](../reference/commands.md#run-the-daemon) describes daemon installation.

Commands reach the daemon over the [hub's stream transport](#transport), on its local socket:
the daemon greets, a command sends a JSON request, and the daemon answers with a JSON
response, for each of nine operations (`Request` and `Response` in
`crates/musubi/src/control.rs`). Every message names first the build that sent it, and a
build reads no further into another's. A daemon writes its build as a fourth line of
`daemon.pid`, so a command refuses one of another build, and says to restart it, without
connecting; a daemon from before the protocol changed wrote none. The socket's greeting is the
second check: a greeting that isn't the transport's is taken for another build's. A daemon that
doesn't greet within a short wait is only slow to answer, as a busy one is, and is not taken for
another build; one that closes the connection before greeting, as one stopping does, is taken
for none. Only a request to stop is obeyed across builds, so that `musubi daemon restart`
works. A daemon from before the protocol, which spoke tarpc, can't be asked, so `stop` and
commands that need the daemon fail at once, with its pid and a hint to end it by hand and run
`musubi daemon start`, or, where its pid isn't among this process's, as in a container sharing
the state directory, to end it where it runs. `stop` never signals a process: a pid file left
by a daemon killed hard may name anything by now. A daemon of this build that isn't listening,
as for one starting, or that doesn't answer, is asked again until the deadline, and then fails
with the same hint. Each call names how long it waits. A
call that returns once a copy has synced waits an hour, the most the transport waits for any
request. The daemon drops a request when its deadline passes, as tarpc's server did, and not
when its command goes away: the request runs to the end.

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
musubi's ref update for a git change. Commands in secondary workspaces do not all take
the colocated import/export lock; [races.md](races.md#remotes) records that limitation.

Merges load the same system, user, repo and workspace configuration as jj, including identity
and signing settings. musubi's own settings live under `musubi.` in jj's config. Machine-wide
settings come from user config alone so every repository finds the same daemon. Local indexes,
repository identity and working-copy state stay local
([What is replicated](#what-is-replicated)).

Publication follows dependency order: objects, views, operations with their ancestors, and only
then the op head. This keeps published history readable across interruption and restart.
[Conformance](conformance.md) states which native boundaries are checked against the models.

### Moving op heads

musubi replaces op heads it read earlier: with the realization of work it fetched, with the
exported copy of a merge, and with the checkpoint that cleanup after `musubi sync --prune`
writes. Every jj command but two publishes its operation under jj's op-heads lock, in place of
the op heads it loaded. `jj op abandon` and `jj op integrate` take no lock: an abandon puts its
rewrite in place of each op head it read, however long ago it read them. A replacement of op
heads that changed meanwhile would leave musubi's operation beside the newer one, or take out an
operation a jj command wrote on a head musubi never read.

So musubi replaces op heads only under jj's op-heads lock, and only while they are exactly those
it read. Otherwise it moves nothing and works the move out again from the op heads as they are.
It puts the new heads in before it takes the old ones out, so that a crash between leaves extra
heads, which jj merges, rather than none. musubi doesn't try to undo a local `jj op abandon`
that lands while it moves the op heads, or after: what the abandon dropped comes back when jj
merges the two, as it does on one machine where `jj op abandon` races another command
([races.md, "Known jj limitations"](races.md#known-jj-limitations)). A machine that loses
history the hive has stops syncing, and says so.

`OpHeadsRace.lean` models this among jj's commands and the lockless writers, and proves what
holds: no command's operation lands between musubi's read and its move once the check passes, and
no command runs while musubi holds the lock ([conformance.md, "Moving op
heads"](conformance.md#moving-op-heads)).

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
