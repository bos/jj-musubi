# jj-musubi design

jj-musubi keeps one jj repository in sync across several machines. A daemon on each machine
watches the repository's operation log, publishes new operations, and the objects they refer to,
to a hub, and applies the operations that other machines published. A commit, rebase or abandon on
one machine shows up in `jj op log` on the others within a second or so, and a machine that was
offline catches up when it reconnects.

This document gives musubi's design rules and the reasons for them. [protocol.md](protocol.md)
specifies the messages between nodes and the hub and the properties they guarantee, and
[races.md](races.md) the outcome of each race. musubi pins jj-lib 0.46.0.

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
- **Colocated**: a git-backed jj repository whose git repository is the `.git` beside `.jj`, which
  git commands use too. A repository that isn't colocated keeps its git store inside `.jj`.

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
| Git remote definitions (names and URLs) | yes | See [Hive settings](#hive-settings). |
| Repo config | chosen keys | Those that decide what is safe to rewrite or push, and any named in `musubi.shared-config`. See [Hive settings](#hive-settings). |
| User config | no | |

Every operation is replicated, including working-copy snapshots. If you snapshot a file containing
a secret, every machine in the hive receives it.

## Working copies

musubi never touches working copies. It writes only what jj itself keeps: the operation log; the
commit store, and in git-backed repositories the git object database and refs; and the git remotes
and repo config that the hive shares ([Hive settings](#hive-settings)).

A remote operation can still rewrite this machine's working-copy commit, for example by rebasing
its parent. jj then treats the working copy as stale, exactly as after a `jj rebase` run in
another workspace: by default the next `jj` command stops and suggests `jj workspace
update-stale`, which updates the files. With `snapshot.auto-update-stale = true` jj updates the
files itself, but then any `jj` command, even `jj log`, can change files under a running build or
an editor, so musubi doesn't turn it on. Each machine can set it for itself; to set it for the
whole hive, set it in the repo config and name it in `musubi.shared-config` ([Hive
settings](#hive-settings)), and the hive's value then overrides each machine's user config. Either
way, jj snapshots edits not yet snapshotted before it updates the files, so instead of losing
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
    realizing deterministic, so re-realizing after a crash rewrites identical files.
  - For the operation that becomes an op head, in a colocated repository, musubi runs jj's
    `export_refs` with C's bookmarks, tags, and remote bookmarks against this machine's `.git`.
    This writes `refs/heads`, `refs/tags`, and `refs/remotes`, compare-and-swapping against the
    recorded values as a local `jj` would, and musubi records the resulting per-machine fields. It
    holds jj's `git_import_export.lock` from the export until it has published the op head, so a
    concurrent `jj` command never sees the operation before `.git` matches it.
  - Before publishing it, musubi merges it with this machine's own concurrent operations as jj
    will, in jj's order and the reverse, since the result can depend on the order. jj 0.46 can't
    merge some concurrent operations ([races.md, "Known jj
    limitations"](races.md#known-jj-limitations)), and publishing them would leave every `jj`
    command here failing. So if the merge fails, musubi publishes nothing, and the sync fails,
    naming this machine's operations that the hive doesn't have yet, so that the user can revert
    one.
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
- **Neither**: merges, and the other operations musubi writes, for settings, new working copies,
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

Each machine keeps, for each copy present at a canonical operation, the copy's latest work there
that no forget saw, and computes an operation's from its parents' (`Presence::merge` and `apply`,
whose rules the model proves in `umax_merge`, `umax_work` and `umax_forget`): a copy's work
becomes its latest; a forget leaves the copies it forgets nothing; a merge keeps each latest work
its parents keep, unless a parent whose history has that work doesn't keep it. Only merges need an
ancestry test, which generation numbers bound (the root's is 0, and any other operation's one more
than its largest parent's). An open repository remembers presence at the 256 canonical operations
it computed last, so an operation reads the history below it only down to one it remembers. The
first one asked about reads all of it, as computing generation numbers does anyway: when a daemon
starts, and in each `musubi list`, `forget` and `leave`. Realizing a run of operations computes
presence at the run's first before its threads start, so that each thread reads only the run below
its own. [conformance.md, "Presence"](conformance.md#presence) describes the test that checks the
Rust against the model.

### Which workspaces are this machine's own

In a local view, this machine's workspaces have plain names (`default`), and another machine's are
named `<machine>/<workspace>` (`laptop/default`). But jj allows `/` in a workspace name, so a
workspace of this machine's own can have that form too, and the name alone doesn't say whose it
is. Canonicalizing has to tell the two apart, from history alone, so that it stays deterministic.

Another machine is shown under its name, or, where two machines share a name or the name would
clash with a workspace of this machine's own, under its name and the start of its key's random
suffix (`laptop-1a2b`; `local_names`). The names are chosen among every machine the history has
known, present or forgotten (`Presence::known`), so a machine keeps its name as others come and
go, and a forgotten machine's name is never another's. This machine's own names as of a canonical
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
local view, unless jj's workspace store says this machine has a working copy for it. A workspace
of `desk`'s own that it named `laptop/x` therefore stays its own, whether it was made before a
machine named `laptop` joined or after, while the hive has forgotten `desk`, and through
`jj undo`; and that machine is shown as `laptop-1a2b`, to keep clear of it.

### A forgotten copy's working copies

A machine the hive has forgotten keeps its own working copies. When it realizes an operation whose
canonical view leaves it out, it keeps its workspaces as the realization of the parent with its
latest work had them (`Presence::worked`), following the operation's rewrites
(`with_own_workspaces`). So at a merge of a forget that saw its latest work with an operation that
saw only earlier work, it keeps the workspaces the forget's realization had. Where another machine
rewrote its working-copy commit, as one can while no other machine sees it as a working copy, it
follows the rewrite (`replace_abandoned_working_copies`). Where the forget abandoned an empty
working-copy commit, it stays on the hidden commit, since a new one would be an empty commit of no
one's on every other machine. jj's next snapshot, or any command that rewrites `@`, makes a new
visible commit of it, and that work publishes the machine's workspaces again.

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
afresh each time, as it does for settings. A copy that has recorded nothing is never forgotten, so
one set to `never` writes nothing. `musubi join`, `create` and `clone` put the value in the repo
config unless jj's config sets it already: `6h` if a coding agent runs the command (it checks for
the environment variables that agents set), and `never` otherwise.

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
- `musubi.forget-after` is never shared across a hive, whatever `musubi.shared-config` says
  (`config_keys`): an agent's `6h` mustn't reach a person's copy.
- Each machine adds a delay of its own, up to five minutes, from a hash of its machine key and the
  copy's, so that one machine's forget usually reaches the others before their own time comes.
  Duplicate forgets are harmless anyway.

The generated end-to-end tests set forget-after values and run `expire_idle` on a clock they move
on two hours, with no delay.

## Hive settings

Some settings must agree across the hive but live outside jj's operations. Remote bookmarks
replicate with the view, so a fetch or push on one machine reaches every other. But which remotes
exist, and where they point, is in each machine's git config. Without more, `jj git remote rename`
on one machine would rename the remote bookmarks everywhere while every other machine's git config
kept the old name.

Some repo config must agree too. If `immutable_heads()` or `git.private-commits` differed, one
machine would rewrite or push what another protects. But much repo config is personal, and some is
a machine's own business, so musubi shares only chosen keys: `revset-aliases."immutable_heads()"`,
`revset-aliases."trunk()"`, `git.private-commits`, `musubi.shared-config`, and any keys that
`musubi.shared-config` names (`["aliases.l"]`, say). jj keeps repo config outside the repository,
so musubi finds the file as `jj` does.

The hive settings are these: each remote's name, URL, and push URL, and the shared config keys.

### Recording and merging

At the end of every sync, and at its start once the machine knows the hive's settings, a machine
reconciles its settings with the hive's. A setting that differs from what the machine last applied
is a change of its own. It records its changes in an attribute, `musubi.settings`, of an operation
that changes nothing else, which replicates like any other. It applies the hive's changes, remotes
with `git remote` (which also renames or deletes the remote-tracking refs) and config keys in its
repo config file, and its daemon logs each value it replaces: the old value, the new one, and
which machine wrote it when.

Where machines disagree, the later write wins. Each setting carries the time it was written, by
the writing machine's clock (the modification time of the file holding it), and the writing
machine's key, which breaks ties: the one that sorts last wins. The hive's settings as of an
operation are those of its nearest ancestor that records settings, and at a merge, for each
setting, those of the parent whose write is later. A remote is one setting, so one machine
changing its URL while another changes its push URL are two writes, and the later stands. Clock
skew can make the wrong write win. That is accepted: the rule isn't sound, but it is simple and
does what people expect ("I changed it at 9, you changed it at 8, mine stands").

What counts as a change ignores spelling. Config values are compared as normalized TOML, so that
machines that write the same value differently agree on it. Remotes are compared by the
repositories they name: two are equal when their URLs have the same key (the normalized form used
for joining, under [Which hive](#which-hive)), and so do their push targets (the push URL, or else
the URL). So one machine can reach a remote over https and another over ssh: neither spelling is a
change, respelling records nothing, and applying a change writes only the URLs whose repository
differs, removing a push URL that no longer names where pushes go. A machine that doesn't have a
remote yet gets the spelling of the machine that last wrote it.

### Remote URLs

A remote's URLs go as written and, where the writing machine's `url.<base>.insteadOf` rules change
them, as its git expands them, since other machines needn't have the same rules. A machine
receiving a URL writes it as written where its own git expands it the same way, so that an alias
they share stays one, and otherwise as expanded. An alias is keyed as a host, `gh:team/p` as
`gh/team/p`, so two machines' aliases of the same name compare as one repository whatever they
expand to (though joining a hive takes shared history too). Once machines share an expanded URL,
it stays until the remote points at another repository: a machine that drops a redirect to a
mirror doesn't take the mirror's URL back from the others, though each can respell its own copy.

Unless `musubi.share-credentials` is set in jj's config, URLs go without the user and password an
http(s) URL may carry, a token meant for one machine, and so does the command line jj records with
each operation.

A machine that needs another identity for a remote, an ssh key of its own, say, should keep the
ordinary URL and rewrite it with git's `url.<base>.insteadOf` in its user config. A URL spelled
with an ssh host alias names a host no other machine knows, so it doesn't count as the same
repository, and a machine without the alias can't use it.

### A joining machine's settings

A machine that joins adds its remotes to the hive's, but takes the hive's where both have a remote
of the same name for different repositories; the first machine's settings become the hive's.
Joining adds a machine rather than changing the hive's mind, so a joining machine's remote or
shared config key comes back even if the hive had removed it: remove it again afterwards.

## Ordering: one hub, one canonical head

When two machines make concurrent operations, someone has to merge them. Suppose each machine
merged independently. A's operation rewrites commit X; B's concurrent operation adds a child Y of
X. A's merge rebases Y onto the rewritten X, giving Y'. B's merge does the same, giving Y''. Y'
and Y'' have different committer timestamps, so they are different commits, and the hive ends up
with a spurious divergent change. That is unacceptable for a tool whose point is to make several
machines feel like one.

So the hub keeps a single canonical head and accepts only fast-forward updates. A node pushes by
uploading what the hub lacks and asking it to compare-and-swap the canonical head from H to H',
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
or merge as usual. So a hub needn't be durable, and it syncs nothing to disk: one that loses its
state, to a power cut say, is deleted and made again, and the machines' repositories fill the new
one.

A new hub doesn't have the hive id the nodes know, so it answers their requests "no hive", and
their syncs fail, saying so. `musubi join` in one copy then makes the hive again (a join with
`JoinChoice::Remake`), empty, under its id and the name the copy knew, or if that's taken, a name
from its remote or directory. It refuses if the hub removed that hive, or if the copy belongs in a
hive the hub has, as an unnamed `musubi create` would be refused. The other nodes find their hive
at their next sync and fill it, as nodes follow any hub that goes back. A person makes the hive
again, not the first node to sync, because a hub that doesn't know a hive may be the wrong hub,
such as one started from another directory by mistake, which would otherwise fill up with every
hive. `musubi join --hub` makes the hive again on another hub in the same way, which moves a copy
there.

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
- A node writes received objects into the repository's object store (`.git` for colocated
  repositories), reopening the repository first, since jj-lib's git backend can't read packs added
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
last chunk and a minute has passed without a request for any chunk of it, and unfinished sessions
expire after an hour. A blob prepared again, for another reply with the same content, counts as
one prepared just now. A node deletes what it uploads or downloads once it is done with it,
however the call ends, except a partial download, which it keeps for a later call to resume until
it has gone a day untouched.

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

A repository that was part of a hive before, and left it, writes no join operation when it joins
again, if its head descends from the history it shared (an operation canonicalized already, a
realization, or a join point): that history is canonical already, and the head is canonicalized on
top of it as any operation is. A join operation on the root would hide that history from the head.
The head the old hub last accepted, which the node keeps, would no longer be reachable from it,
which musubi takes for an op abandon ([Abandoning operations](#abandoning-operations)), whichever
hive the repository joins; and other machines' workspaces, no longer recognized as theirs, would
come back as this machine's own. So joining a different hive brings the old hive's shared history
with it, its machines' workspaces included, which show on every machine of the new hive, as a
machine's workspaces do once it stops syncing.

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
are what is compared. Azure DevOps' https and ssh forms are made one. Each hive keeps every URL it
has ever had, so renaming a remote or moving a repository doesn't orphan it.

For this the hub keeps an index for each hive: every remote URL its settings have recorded, every
root commit it has stored, and the machines with workspaces at its head. The index is updated
whenever a head is accepted, and is a cache: the hub rebuilds it from the hive's operations and
objects when it is missing. A join also counts what the joining repository says it brings, its
URLs and root commits, as its hive's for a couple of minutes, so that another copy joining before
the first one's push finds the same hive. That stops once the joining machine's first push is
accepted, which puts what it really brought in the index, or when the time is up, so a join that
never pushes leaves nothing behind.

A new hive is named after the remote named `origin`, else the first remote by name, else the
repository's directory. The name follows the forge: `owner/repo` on GitHub, Codeberg, Forgejo,
Gitea, and Bitbucket; the full group path on GitLab; `user/repo` for sourcehut's `~user/repo`;
`org/project/repo` on Azure DevOps; a Gerrit project without its `a/`; and otherwise the last two
components of the path. A hive gets the shortest form of its name no other hive has: `jj-musubi`,
then `bos/jj-musubi`, then `github.com/bos/jj-musubi`. Names never change by themselves; `musubi
hub rename` changes one. Commands that take a hive accept any unique prefix of its name, except
`musubi hub remove`, which takes a whole name or an id, since a prefix is too easily mistaken.

`musubi clone <name>` creates a new colocated repository and joins it to the named hive.

## Abandoning operations

`jj op abandon` rewrites the descendants of the abandoned operations into new operations with new
ids. If musubi ignored that, the next pull would bring the old operations straight back. So a node
notices when canonical operations it had published stop being reachable from its op heads, which
happens only in `op abandon`, and pauses replication for that repository, saying why, rather than
undoing it.

Replicating an op abandon, as a record that the new history supersedes the old for every machine
to apply, is not built yet.

`jj util gc` removes only data that is no longer reachable locally, so it needs no special
handling. Neither the hub nor the nodes ever delete an object, and the daemon's own cleanup on a
machine ([git backend](#git-backend)) deletes only operations that no op head reaches.

## Transport

The transport is a small trait. Every message goes to a subject, a dotted name that requests and
subscriptions address. Request/response carries messages up to the negotiated size limit, and
subscriptions carry hub notifications. Requests about a hive go to `musubi.<id>.rpc`, where `<id>`
is the hive's id, and notifications to `musubi.<id>.head`. Requests about the hub as a whole
(join, list, resolve a name, rename, remove, a daemon's report on a sync, and `musubi top`'s
request for activity) go to `musubi.hub.rpc`. The hub takes all of them on one subscription,
`musubi.*.rpc`. Each hive's requests go to a thread of its own, which opens the hive's store on
its first request and answers one request at a time: that is what makes each push atomic, while
different hives don't wait for each other. A request for a hive the hub doesn't have is answered
"no hive", or "removed" for a hive `musubi hub remove` removed: only a join creates a hive, or
makes one again. Every operation and object is verified against its content hash on receipt, so a
misbehaving peer can't inject data under a false id.

- **In-memory**: an in-process network, on which the hub's service and the connections it serves
  meet. Tests run nodes and hubs over one too, which can drop, delay, duplicate, and reorder
  messages, and disconnect peers.
- **Streams** carry the same subjects over a byte stream: the hub's local socket, and over ssh,
  the standard input and output of `musubi hub connect`. Each frame is its length, a kind, and its
  fields: `SUB`, `PUB` and `REQ` from the client; `MSG` for its subscriptions, and `REPLY` or
  `FAIL` for its requests, from the hub, which relays each connection through its own in-memory
  network, every request as it comes. A frame the connection ends partway through is never
  delivered. The client subscribes on the hub once a subject, however many subscriptions it makes
  to it: there is no unsubscribing there, so one that nobody reads any more stays until the
  connection ends, for the next subscription to the subject to take up. It opens a new connection
  whenever one ends, subscribing again to what it still reads; requests in flight on the old one
  fail at once, and those made in between wait for the new one, up to their timeout. Either side ends a connection that falls 1024 frames behind, as it
  would one whose other side vanished. If a hub greets the client wrongly (another version, too
  much noise first, or an implausible payload limit), the first connection fails at once, and
  after that the client tries again only after a minute.
- Over ssh, the hub's machine may print something before the hub greets: some shells' startup
  files print for every shell, a banner in ASCII art, say. The client passes over up to 64 KiB of
  it; past that, it fails, quoting the first thing printed. The greeting starts with a NUL, which
  is never part of text, so that a banner can't be mistaken for it. The client greets the hub only
  after the hub has greeted it, so that nothing that runs there first can read the greeting.

### Running a hub

A hub is meant for one person's machines, or a team whose members trust each other: anyone who can
reach it can read and write every hive on it. `musubi hub` serves a directory holding one
subdirectory per hive, named by the hive's id, each with the hive's store (`canonical/`,
`backend`, `git/` and `extras/` or `simple/`, `heads`, `blobs/`, `tmp/`), its `hive.toml` (name
and backend), and its index. Removed hives move to `removed/`, as do corrupt stores ([Replacing
the hub](#replacing-the-hub)). A removed hive's store is emptied a day later, and its directory,
`<id>-<time>`, stays for good, empty, as its tombstone: the hub answers the hive's machines
"removed", and they leave it, keeping what they have. A lost hive, which has no tombstone, can be
made again. Corrupt stores' directories end in `.corrupt`, and their hives are still there.

Without `--dir` the hub serves `./musubi-hub`, or the current directory if it is a hub's, and
takes a lock in the user's state directory, so that a second hub started the same way says where
the first one is instead of starting. `--dir` runs more hubs on purpose, and a lock in each hub's
directory stops two hubs serving the same one.

The hub listens on a local socket that only its owner can reach, `run/hub.sock` in its directory,
in a subdirectory only its owner can open (on Windows, a named pipe named after the directory),
where neither a temp cleaner nor the end of the login that started the hub removes it. `musubi hub
connect`, and commands on its machine, find it there. It prints the commands other machines run,
with this machine's host name, or the name `--advertise` gave it, which it keeps in `hub.toml`
too, since a machine doesn't always know a name others can reach it by. It also saves its
directory as the machine's default hub, unless the machine has one, so that commands on the hub's
machine need no `--hub`.

For `musubi top`, the hub keeps account in memory, per hive, of the bytes each hive's requests and
replies carry, the heads it accepts and what they bring (operations, and the commits their
`commit_predecessors` say they wrote), pushes it turns away, requests it fails, and the latest
report of each machine's daemon (`musubi_hub::activity`). A daemon reports after every sync that
ran, without waiting for an answer: the hub's head as the sync left it knowing it, its error if it
failed, and its release. The hub tells that a machine is behind from when it accepted the first
head the machine's report lacks. None of this is persisted: a hub that restarts knows nothing of
what came before, and needn't.

### Reaching a hub over ssh

Often ssh is the only way one machine can reach another, as when a laptop reaches a devbox through
a zero-trust tunnel, and since the protocol trusts whoever can reach the hub, the hub can't simply
be exposed. A `--hub` that isn't an absolute path is an ssh destination, passed to the user's own
`ssh` (or `$MUSUBI_SSH`), so `~/.ssh/config` applies: aliases, `ProxyCommand`, and the rest.

- Each machine has a key of its own, `hub_key` in its state directory. Joining a hub over ssh
  first tries it, and if ssh refuses it (or there's no key yet, when it creates one), adds it to
  `~/.ssh/authorized_keys` on the hub's machine, through the user's ordinary ssh, which can prompt
  then, since the user is at the terminal: `restrict,command="musubi hub connect"`, so a stolen
  key reaches the hub and nothing else. The daemon needs no ssh agent to reach the hub, and never
  prompts (`BatchMode=yes`), which a process started at login couldn't answer.
- `musubi hub connect` relays its stdin and stdout to the socket of the user's hub (the one
  `musubi hub` last served without `--dir`).
- On the other machine, each connection is an ssh of its own, and the stream transport speaks
  through its stdin and stdout. Nothing outlives a connection: an `ssh -L` forward that lasts goes
  dead when the machine sleeps, while here, connecting again is a new ssh. ssh's
  `ServerAliveInterval` gives up on a dead link within half a minute, and musubi ends every
  connection at once when it sees that the machine has slept (its monotonic clock stops during
  sleep and the wall clock doesn't), so the transport connects again within seconds of waking.
- Once the transport reconnects, over ssh or not, the daemon syncs at once, since it missed the
  hub's announcements while it was away, even if it was waiting to retry a sync that failed (only
  once per run of failures, in case the sync is what loses the connection). A request in flight
  when the connection dropped fails at once, so a sync it was part of starts again.
- ssh doesn't compress (`Compression=no`): musubi already compresses what it sends.
- A failing ssh backs off, up to a minute, and the transport's attempts to connect meanwhile fail
  at once: otherwise they would run ssh, and perhaps a tunnel's login page in a browser, every few
  seconds. Only the hub's greeting coming through counts as ssh working, not whatever the shell
  printed first. What ssh said, or that `musubi` isn't on the `PATH` there (exit status 127),
  becomes part of the error `musubi list` shows.

## Local integration

- Each user runs one daemon, which serves every repository listed in its state file (`state.toml`
  in musubi's state directory, the source of truth), one thread each. Commands reach it over a
  control socket: tarpc (a Rust RPC library), with JSON messages, over a Unix domain socket
  (`$XDG_RUNTIME_DIR/musubi/daemon.sock` on Linux, `$TMPDIR/musubi/daemon.sock` on macOS) or a
  Windows named pipe (`\\.\pipe\musubi-<user>`). It answers `version`, `add` (start serving a
  repository now, and reply after its first sync), `remove`, `sync`, `status`, and `stop`. `musubi
  create`, `join`, and `clone` write the repository's membership and the state file, then ask the
  daemon to add it, starting the daemon in the background first if none is running.
- Only the user can reach the daemon. A Unix socket's directory must be theirs and writable by no
  one else, as tmux and ssh-agent check, or the daemon won't listen there and commands won't
  connect. A named pipe admits only its owner, and the daemon creates it as the first instance, so
  it can't start if another user took the name. A lock file in the state directory, named after
  the socket, keeps a second daemon from starting; the daemon holding it removes a socket a
  crashed daemon left behind. Commands check the daemon's version first, and suggest `musubi
  daemon restart` when it differs.
- `musubi daemon install` hands the daemon to the platform's service manager, to start at login: a
  launchd agent on macOS and a systemd user unit on Linux, which restart it after a crash but not
  after `musubi daemon stop`, and an entry in the user's `Run` registry key on Windows, which runs
  `musubi daemon start`. Where launchd or systemd runs it, commands that need the daemon ask the
  service manager to start it rather than starting one themselves, so there is never a second. The
  service gets the installing shell's `PATH` (the daemon runs `git`), and the variables that say
  where jj's config (which holds the daemon's own settings too) and musubi's state are:
  `JJ_CONFIG`, `XDG_CONFIG_HOME`, `XDG_STATE_HOME`, and `MUSUBI_*` settings. A marker in the state
  directory records the installation, so commands with another `MUSUBI_STATE_DIR` (tests) leave it
  alone.
- A daemon that a command starts outlives it, so it takes nothing from the command's environment
  that only says where the command ran. git's variables naming a repository (`git rev-parse
  --local-env-vars`), which a git hook has, reach neither the daemon nor any git musubi runs, and
  that git runs no hooks, as jj runs none when it writes `.git`. The daemon's `SSH_AUTH_SOCK`, for
  signing with a key an agent holds or for a `ProxyJump` host, names `ssh-agent` in the state
  directory: a link that every command points at its own agent when that answers. So the daemon
  uses the agent of the latest session to run musubi, and outlives the session it started in, such
  as an ssh login with a forwarded agent. The systemd unit names the link too, since a user's
  service manager rarely has an agent; launchd has one of its own.
- Commands change `state.toml` holding a lock beside it, and write it whole, so that concurrent
  joins keep each other's changes and a crash never leaves half a file.
- The daemon watches `.jj/repo/op_heads/heads` with filesystem notifications, and also polls
  slowly. It reads operations through jj-lib's op store and never parses jj files itself.
- Loads and merges go through jj-lib's repo loader, which takes jj's op heads lock, so musubi
  merges concurrent heads exactly once per machine even while `jj` commands run.
- In colocated repositories, realization holds `.jj/repo/git_import_export.lock`, the lock the jj
  CLI holds around its own import and export, so the two never interleave.
- Merges that musubi makes rebase commits, which needs the user's jj config (identity, and signing
  if enabled). musubi loads the same system, user, repo, and workspace config that `jj` does. The
  merge operation looks like one `jj` would write ("reconcile divergent operations"), with this
  machine's hostname.
- musubi's own settings are jj's too, under `musubi.`, so `jj config` shows and changes them, and
  musubi has no config file. Those that are a machine's rather than a repository's (`musubi.hub`,
  `musubi.daemon.*`) come from the user config alone: the daemon serves every repository from one
  socket, and commands must find that socket wherever they run.
- Operations reach the op store in dependency order: objects, then views, then operations,
  ancestors first, then the op head. A jj process can therefore never see a reference to something
  missing.
- musubi never replicates `index/`, `config-id`, `workspace_store/`, or `store/git_target`.

## Compatibility

jj's operation format changes every few months, almost always by adding fields, and jj keeps
reading older files. Ids are hashes of jj-lib's in-memory structs, not of file bytes, and jj-lib
never verifies them on read. Two consequences:

- An older jj-lib decoding an operation written by a newer `jj` silently drops the fields it
  doesn't know, and canonicalizing it would lose them. So before canonicalizing a local operation
  or view, musubi walks its protobuf encoding and refuses any field number that jj-lib 0.46
  doesn't define. A newer `jj` CLI writing to the repository is therefore a clear error, not
  silent data loss.
- Canonical operations are always written by musubi's pinned jj-lib, so a receiver can verify each
  canonical operation and view by decoding and re-hashing it. A mismatch means a peer is running
  an incompatible version, or is lying.

Every message between a node and the hub starts with its protocol and jj-lib versions, encoded the
same way in every release. Each side reads them first and refuses a message whose versions aren't
its own, so that a message from another release is refused as such rather than misread.

## Testing

The hub logic and the node sync logic are sans-IO state machines (`crates/musubi-core`): they do
no I/O themselves, but consume events and produce effects. That keeps them deterministic under
test, and lets them correspond step by step to the Lean model of the protocol, which proves its
safety properties, and convergence for a model of the nodes' policy over reliable delivery
([formal/README.md](../../formal/README.md),
[conformance.md](conformance.md)). [testing-philosophy.md](testing-philosophy.md) says what a test
must protect, and [testing.md](testing.md) describes each layer of tests.
