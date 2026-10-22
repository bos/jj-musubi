# jj-musubi design

jj-musubi keeps one jj repository in sync across several machines. A daemon on each machine
watches the repository's operation log. It publishes new operations, and the objects they
refer to, to a hub. It also applies operations that other machines published. When you commit,
rebase, or abandon on one machine, the same operation shows up in `jj op log` on the others
within a second or so. A machine that was offline catches up when it reconnects.

musubi never touches working copies. It writes only to the operation log, the commit store,
and, in git-backed repositories, the git object database and refs. A remote operation can
rewrite this machine's working-copy commit, exactly as an operation in another workspace can, for
example by rebasing its parent. jj then treats the working copy as stale, exactly as after a `jj
rebase` run from another workspace. By default the next `jj` command stops and suggests `jj
workspace update-stale`. With `snapshot.auto-update-stale = true`, jj updates the files itself,
so `musubi create`, `join` and `clone` set it in the repo config unless the user or repo config
already has it on. If the working copy had edits not yet snapshotted, jj snapshots them first,
and you get a divergent working-copy change instead of losing them.

This document targets jj-lib 0.46.0.

## Vocabulary

- **Hive**: one logical repository replicated by musubi. It has a hive id, a UUID that musubi
  generates, a human-readable name (`jj-musubi`), and one hub. jj repositories have no identity
  of their own: every repository shares the same all-zero root operation and root commit,
  and `.jj/repo/config-id` is a machine-local pointer that jj regenerates when it detects a
  copy. Which hive a repository belongs to is therefore decided by its history, when it
  joins (see [Joining](#joining)).
- **Node**: one local jj repository on one machine taking part in a hive, together with the
  musubi daemon serving it.
- **Hub**: a long-running musubi process that stores a complete copy of each of its hives,
  orders their updates, and serves catch-up. It never originates changes. Any machine can
  run it, and one hub serves any number of hives.
- **Canonical operation**: the form of a jj operation that is replicated (see
  [Per-machine state](#per-machine-state-in-a-replicated-view)). Its id is computed by jj's own
  op store code, so it is an ordinary jj operation id.
- **Local operation**: an operation in a node's own `.jj/repo/op_store`.
- **Realization**: the local operation a node writes to represent a canonical operation that
  arrived from elsewhere.
- **Canonical head**: the single operation the hub currently considers the latest state of the
  hive.

## What is replicated

| Data | Replicated | Notes |
| --- | --- | --- |
| Operations and views | yes | In canonical form. |
| Commit predecessors (`Operation::commit_predecessors`) | yes | Part of the operation; drives `jj evolog`. |
| Commits, trees, files, symlinks | yes | git objects for the git backend; store files for the simple backend. |
| git backend extras (change ids not recoverable from the commit) | yes, when needed | See [git objects](#git-backend). |
| Working copies and working-copy state | no | Each machine snapshots its own. |
| Commit index (`.jj/repo/index`) | no | Derived; jj rebuilds it. |
| `View::git_refs`, the `git` pseudo-remote | no | Per-machine record of this machine's `.git`. |
| Git remote definitions (names and URLs) | yes | See [hive settings](#hive-settings). |
| Repo config | chosen keys | Those that decide what is safe to rewrite or push, and any named in `musubi.shared-config`. See [hive settings](#hive-settings). |
| User config | no | |

Every operation is replicated, including working-copy snapshots. If you snapshot a file
containing a secret, every machine in the hive receives it.

## Why replicate the operation log

The alternative is fetch-style sync: replicate heads and bookmarks only, as `jj git fetch`
does. That loses the operation history, so rebases and abandons arrive as unexplained new
commits, and musubi would have to reconcile concurrent changes itself.

Replicating operations reuses jj's own concurrency model. jj already lets several processes
write to one repository without locking each other out: each writes an operation, and when a
later load finds several operation heads, jj merges their views three-way. That merge creates
a merge operation and rebases descendants of rewritten commits. A remote machine is, to jj,
just another concurrent writer. So `jj op log` shows the other machines' operations, undo
works across machines, and divergence is shown the way jj always shows it.

## Per-machine state in a replicated view

A jj view mixes state that describes the repository with state that describes one machine.
Replicating views verbatim corrupts the second kind.

- **Workspaces** (`wc_commit_ids`) and each workspace's **git HEAD** (`git_heads`) say where
  this machine's working copies are checked out. jj keeps every workspace in one shared
  map, and replicating it as is would make every machine's workspaces workspaces of every
  other machine's repository: any machine could forget or rename another's, and every
  machine's `default` would collide. So each machine's workspaces are its own, but every
  machine shows the others'. Each machine has a durable identity, its name plus a random
  suffix (`laptop#1a2b3c4d`), so two machines that share a hostname are never confused.
  The canonical view records every machine's workspaces under machine-qualified keys
  (`laptop#1a2b3c4d/default`). A machine realizes its own under their plain names and the
  others' as workspaces named after the machine, `laptop/default`, so `jj log` shows the
  laptop's working copy as `laptop/default@`, and `jj new laptop/default@` builds on it.
  (Two machines that share a name are shown as `laptop-1a2b/default`.) These are never git
  refs, so nothing git does can drop them, and jj's git import never abandons work because
  of them.

  jj moves another machine's workspace as it moves any workspace: when it rewrites the
  commit, its workspace follows (to the second half of a split, say), and when it abandons
  it, the workspace gets a new empty commit on the parents. Restoring an older view,
  through `jj undo`, `jj redo` or `jj op restore`, restores every workspace's position.
  Canonicalization takes those moves, and the machine that owns the workspace adopts them,
  as a second workspace does on one machine: its working copy becomes stale, and its next
  command updates the files (with `snapshot.auto-update-stale`). Nothing else a machine
  does to another machine's workspaces counts: adding, forgetting or renaming them stays
  local (forgetting one doesn't even abandon its empty working-copy commit, as
  `jj workspace forget` otherwise would, unless this machine then rewrites or abandons
  that commit's parents: jj, no longer seeing the commit, leaves it behind, and keeping it
  would bring the old parents back), and at the end of every sync musubi shows any
  that went missing again. Where concurrent operations disagree about a
  workspace, musubi merges it three-way exactly as jj does, so a machine's removal of its
  own workspace wins over another machine moving it meanwhile. If another machine
  abandons this machine's working-copy commit without moving its workspace (because it had
  forgotten the workspace), this machine gives itself a fresh `@` where jj would have put
  it: on the nearest visible ancestor, or on the rewrite of an ancestor that was rewritten
  rather than abandoned (the change's one visible commit). Much as when jj merges
  concurrent operations, a commit moved with `jj rebase -r` counts as rewritten, so the
  fresh `@` follows it, where a local `jj rebase -r` would have left the working copy
  behind.

  Which workspace made an operation is per-machine too. jj records it in the operation's
  metadata, and `jj undo` and `jj redo` refuse to undo another workspace's operation, telling
  workspaces apart only by name. If every machine's operations kept the plain name, each
  machine's `default` would be the same workspace to `jj undo`, which would then undo
  whatever operation last arrived from another machine. So canonical operations record the
  machine-qualified key, and a machine realizes another machine's operations under that
  machine's workspace name: `jj op log` shows `laptop/default@`, and `jj undo` refuses to
  undo the laptop's operation unless given `--allow-cross-workspace`.
- **`git_refs`** and the **`git` pseudo-remote** (`foo@git`, `tag@git`) record what jj last
  saw in this machine's `.git`. Each `jj` command in a colocated repository compares them with
  the real refs and imports any difference as a change made with git.

### The hazard

Machine A moves bookmark `main` from X to Y and exports it, so A's view records
`main@git = Y` and `git_refs[refs/heads/main] = Y`. Suppose B adopts that view verbatim while
B's `.git` still has `refs/heads/main = X`. B's next `jj` command sees that git "moved" `main`
from Y back to X. It merges that into the local bookmark three-way (local Y, base Y, git X)
and gets X. jj silently reverts A's change on B. The reverting operation then replicates back
to A.

Updating B's `.git` refs before showing B the operation fixes the common case. It still leaves
the recorded values wrong whenever B's export cannot succeed, such as a conflicted bookmark or
a ref moved with git in the meantime. Any operation that fixes the record replicates back to A
and breaks A's record in turn.

### Translation

The per-machine fields therefore stay per-machine.

- **Canonicalizing** a local operation copies it, but with `git_refs` and the `git`
  pseudo-remote removed from the view, and its workspace machine-qualified. Its parents are replaced with their canonical ids. It
  is written to a canonical op store kept beside the repository, which assigns the id.
- **Realizing** a canonical operation C on a node writes a local operation with C's metadata,
  its workspace named as above, plus a `musubi.canonical = <id>` attribute. Its parents are the local realizations of C's
  parents, and its view is C's view plus per-machine fields. jj's `Transaction` cannot
  reproduce another machine's metadata, so musubi writes these operations through jj-lib's
  `OpStore`, as `jj op integrate` does, and lets jj build the index lazily. The op store
  syncs each file it writes to disk, which takes milliseconds on a cloud disk, so a node
  catching up writes its realizations in parallel. Nothing reads them, and no op head or
  translation names them, until they are all written.
  - An operation that will not be an op head inherits its parent realization's per-machine
    fields, merging them three-way with jj's `merge_ref_targets` for a merge. That makes it
    deterministic, so re-realizing after a crash rewrites identical files.
  - The operation that becomes an op head is realized while musubi holds jj's
    `git_import_export.lock`. musubi runs jj's `export_refs` with C's bookmarks, tags, and
    remote bookmarks against this machine's `.git`. This writes `refs/heads`, `refs/tags`, and
    `refs/remotes`, with compare-and-swap against the recorded values, exactly as a local `jj`
    process would. musubi records the resulting per-machine fields and then publishes the op
    head. Because of the lock, a concurrent `jj` command never sees the operation before
    `.git` matches it.
  - Before publishing it next to this machine's own concurrent operations, musubi merges
    them as jj will, in jj's order and the reverse, since the result can depend on it. jj
    0.46 can't merge some concurrent operations (docs/races.md, "Known jj limitations"),
    and published, they would leave every `jj` command here failing or panicking. So if
    the merge fails, musubi publishes nothing: the sync fails, naming this machine's
    operations the hive doesn't have yet, one of which to revert, and jj keeps working.
- Canonicalizing a realization returns the canonical operation its attribute names.
  Realizing never creates new canonical operations, so updates cannot loop between machines.

Translation applies to every backend. Canonical operations are always written by musubi's
pinned jj-lib, while local operations may be older files in legacy formats, so even with
nothing to strip the two need not share ids. An operation has one id on the hub and its own
local id on each machine. `musubi debug op-id` translates between them.

## Hive settings

Some settings must agree across the hive but live outside jj's operations. Remote
bookmarks replicate with the view, so a fetch or push on one machine reaches every other.
But which remotes exist, and where they point, is in each machine's git config. Without
more, `jj git remote rename` on one machine would rename the remote bookmarks everywhere
while every other machine's git config kept the old name.

Some repo config must agree too. If `immutable_heads()` or `git.private-commits`
differed, one machine would rewrite or push what another protects. But much repo config
is personal, and some is a machine's own business, so musubi shares only chosen keys:
`revset-aliases."immutable_heads()"`, `revset-aliases."trunk()"`, `git.private-commits`,
and any that the shared key `musubi.shared-config` names (`["aliases.l"]`, say). jj keeps
repo config outside the repository, so musubi finds the file as `jj` does.

So musubi treats the remote definitions (each remote's name, URL, and push URL) and the
shared config keys as hive settings. When a machine's settings change, musubi records the
new settings in an attribute (`musubi.settings`) of an operation it writes, which changes
nothing else. That operation replicates like any other. Each remote and shared config key
carries the time it was written, by the writing machine's clock (the modification time of
the file holding it), and the machine that wrote it, and where machines disagree, the later
write wins: the hive's settings as of an operation are the nearest recording ancestor's, and
at a merge operation, for each setting, the parent whose write is later. Equal times go to
the machine key that sorts last. Clock skew can make the wrong write win; that is accepted,
for a rule anyone can predict ([settings-merge.md](settings-merge.md)). Settings recorded
before writes were timed take their operation's time.

At the start and end of every sync, a machine reconciles its settings: a setting that
differs from what it last applied is a change of its own, written at the file's modification
time, and the later write wins against the hive's. It records its own changes, and applies
the hive's, logging each value it replaces: remotes with `git remote`, which also renames or
deletes the remote-tracking refs, and config keys in its repo config file. Config values are
compared as TOML, normalized, so that machines that write the same value differently agree
on it. Remotes, likewise, are compared by the repositories they name: two are equal when
their URLs have the same key (as for joining, under "Which hive"), and so do their push
targets (the push URL, or else the URL). The merge, the checks for what changed, and the
detection of renames all use that equality, so they work on where remotes point, not on how
they are spelled, and the key is a pure function of the URL, so every machine agrees on it.
A machine's own spelling of a shared remote, over https on one machine and ssh on another,
is never a change, and respelling it records nothing. Applying a change writes only the URLs
whose repository differs, and removes a push URL that no longer names where pushes go, so a
machine keeps its spelling of whatever it still shares. For machines that don't have a
remote yet, the settings hold the spelling of the machine that last wrote it; every spelling
names the same repository. A remote is one setting: one machine changing its URL while
another changes its push URL are two writes, and the later stands. A machine that joins adds
its remotes to the hive's, but takes the hive's where both have a remote of the same name
for different repositories; the first machine's settings become the hive's. A machine that
needs another identity for a remote, an ssh key of its own, say, should keep the ordinary
URL and rewrite it with git's `url.<base>.insteadOf` in its user config: a URL spelled with
an ssh host alias names a host no other machine knows, so it doesn't count as the same
repository, and a machine without the alias can't use it.

## Ordering: one hub, one canonical head

When two machines make concurrent operations, someone has to merge them. Suppose each machine
merged independently. A's operation rewrites commit X; B's concurrent operation adds a child
Y of X. A's merge rebases Y onto the rewritten X, giving Y'. B's merge does the same, giving
Y''. Y' and Y'' have different committer timestamps, so they are different commits, and the
hive ends up with a spurious divergent change. That is unacceptable for a tool whose point is
to make several machines feel like one.

The hub therefore keeps a single canonical head and accepts only fast-forward updates.

- **Push**: in one request, a node uploads any missing canonical operations and objects, and
  asks the hub to compare-and-swap the canonical head from H to H'. The hub stores the
  upload, then agrees only if H' descends from H and everything H' refers to is stored.
- **Pull**: a node fetches the operations and objects between its last-known canonical head
  and the current one, realizes them in topological order, and publishes the realization of
  the new head. Any of its local heads that are ancestors drop out.
- **Merge**: if a node's local operations are not ancestors of the canonical head, its push
  fails. It pulls, and jj merges its local heads, which include the new realization. It then
  pushes the merge. The merge is performed exactly once, by the node that owns the concurrent
  local work, which is the same outcome as two jj processes on one machine.

Every merge operation has at least one parent that only its creator had. Two machines
therefore never perform the same merge. The [formal model](#formal-model) proves this,
together with the other safety properties.

Notifications are hints. The hub publishes each new canonical head on a subject. Nodes also
compare heads with the hub whenever they connect, and periodically. Correctness never depends
on receiving a notification.

### Offline work

A disconnected node keeps working locally; jj does not need the hub. When it reconnects, it
pulls, merges, and pushes. That is the same path as any concurrent update.

### Moving the hub

A hub is just a store. Every node holds every operation it has seen, so a new, empty hub fills
up as soon as nodes connect: the first node fast-forwards it to its head, and the others
fast-forward or merge as usual. A hub location is an ssh destination, or on the hub's
machine its directory, and a subject prefix. The old hub can publish a signed-by-config
`hub-moved` advertisement carrying the new location and a higher epoch. Nodes then
reconnect there and ignore lower-epoch hubs from then on.

Two hubs running at once for the same hive (split brain) is the one case where duplicate
merges can occur, if nodes on both sides reconnect to one hub at the same moment. Epochs make
that case detectable.

## Objects

A canonical operation is complete on a node or hub when its ancestors and every object its
view refers to are present: commits referenced by heads, bookmarks, tags, remote bookmarks,
and working-copy entries, plus `commit_predecessors`, with all ancestors, trees, and files.
The hub refuses a head whose closure is incomplete, and a node realizes only complete
operations. Uploads and downloads can therefore be interrupted at any point without anyone
observing a dangling reference.

### git backend

Objects move as git packfiles. musubi uses the `git` binary: `git pack-objects --revs` with
the receiver's known commits as exclusions, and `git index-pack --fix-thin` to receive. jj
already needs `git` for fetch and push, and this gets delta compression and bitmaps for free,
the latter for clones.

- The hub stores objects in a bare git repository. Its only refs are under
  `refs/musubi/head/`, naming the visible heads of its accepted head's view, so that git can
  keep a bitmap index of what they reach: with one, counting what a clone needs takes a
  fraction of the time. Nodes never see them, since what the hub sends is bundles, not refs.
  The hub writes its first bitmap index, with a full `git gc` in the background, once it
  holds 10,000 objects, and `git gc --auto`'s full repacks refresh it. Only a clone, which
  has nothing, uses it: with a bitmap, git skips the walk that finds what the receiver has
  to make deltas against, so an edit pushed a moment ago, with no delta stored, would go to
  every other node whole.
- musubi runs git with `attr.tree` naming the empty tree. git 2.43 to 2.45 otherwise read a
  bare repository's attributes from HEAD's tree, path by path, and where HEAD names a branch
  that doesn't exist, as on a hub, each lookup tried every way of spelling HEAD as a ref:
  `pack-objects` for a clone of jj spent three times as long on that as on packing.
- A pack is written once on each side: `git pack-objects` writes it straight into the bundle
  that carries it, which goes into the blob store as a hard link rather than a copy where
  the filesystem allows, and the receiver pipes it from the bundle into git.
- A node writes received objects into the repository's object store (`.git` for colocated
  repositories). It then calls jj-lib's `GitBackend::import_head_commits`, which creates the
  `refs/jj/keep/*` refs and backend extras. The keep refs are what protect commits that no
  bookmark reaches from `git gc`. Without them, git would eventually delete every anonymous
  head.
- As `git fetch` does, a received pack of fewer than 100 objects is unpacked into loose
  objects, and a larger one kept as a pack. After receiving, the hub and nodes run
  `git gc --auto`, which consolidates packs and loose objects once there are enough of them
  (by git's thresholds, or the repository's), in the background as git does
  (`gc.autoDetach`, including on Windows, where git can't detach itself), but with pruning
  disabled: musubi never deletes an object, reachable or not. On the hub, what its head's
  refs don't reach goes to a cruft pack.
- jj-lib's git backend sizes gix's table of pack indexes when it opens the repository, so a
  long-running node could fail to read objects in packs added since. A node therefore reopens
  the repository before it imports objects.
- jj commits carry `change-id` and conflict headers by default, so for nearly every commit the
  raw object is enough: the receiver derives the same extras from it. The exceptions are
  commits written by older jj or with the header disabled, whose change id lives only in the
  backend extras, and conflicts written before 2024, whose conflict trees do too. For each
  commit it sends, the sender compares its extras entry with what the receiver would derive
  from the object. When they differ, it ships the entry alongside the pack, and the receiver
  writes it before importing. Per-commit predecessors in the extras are not shipped: since
  jj 0.30, evolution history comes from the operation's `commit_predecessors`.

### Simple backend

jj's simple backend exists mainly for jj's own tests, but supporting it keeps the operation
layer independent of git. Objects are content-addressed files. Transfer walks from missing
commits and sends the store files the receiver lacks, in batches.

### Size limits and chunking

The hub takes messages up to 1 MiB, and says so when a connection opens. Control messages
are small. Something bulky (packs, large views, batches of operations) travels
inline in the request or reply it belongs to when it fits in a quarter of that, and
otherwise moves as a content-addressed blob in a resumable upload or download session. Each
chunk carries its offset and fits under the negotiated limit, up to eight chunks are in
flight at once, and the blob's hash is checked when the session finishes. An interrupted
session resumes from the receiver's reported offset. The hub deletes a blob it prepared a
minute after serving its last chunk, and unfinished sessions expire after an hour.

A sync takes few round trips. A node's first request, which it also sends whenever it
polls, asks for the hub's head together with every operation accepted since the newest
head the node has, and the objects they require. Its push carries its upload along with the
compare-and-swap. A sync that brings something new therefore takes one round trip, and one
that pushes two.

Views are stored whole for every operation, and a repository with thousands of remote
bookmarks can have megabyte-sized views, while consecutive views usually differ in a few
bookmarks. In transit, musubi compresses a bundle's operations and views together with zstd,
and sends each view as a delta against its operation's first parent's view: the view
compressed with the parent's as a prefix that zstd may refer back to, a few hundred bytes for
a view of any size. A view a parent has is not sent at all. The receiver always has the
parents' views. Every bundle of operations is a range `anc*(head) \ anc*(base)` for a `base`
the receiver has, in topological order, so each parent is either earlier in the bundle or in
`anc*(base)`. Ids remain those of the uncompressed views, and the receiver checks them after
reconstructing each one. Stores keep views whole and uncompressed, as jj does.

## Joining

`musubi create` starts a hive from an existing repository, and `musubi join` makes another
copy of it part of that hive. By default each replicates the repository's current state,
not its operation history. It writes one canonical join
operation whose parent is the root operation and whose view is the current view, and records
that the current local head canonicalizes to it. Earlier operations stay local. A repository
that has been in use for years can have tens of thousands of operations, and every one of
their views pins commits that would otherwise never need transferring, such as old
working-copy snapshots. `--full-history` replicates everything instead.

Merging needs no special machinery. Every jj repository's operation log starts at the same
root operation, so a joining node's history and the hive's history meet there. The joining
node pulls the canonical head, and jj merges the two three-way against the empty root view.
Bookmarks set identically on both sides merge cleanly; bookmarks that differ become conflicted
bookmarks that you resolve as usual. The node then pushes. Commits that both sides already
have, such as history cloned from the same origin, are never transferred twice, because
transfers exclude objects the receiver already has. A node fetching objects names, as haves,
the commits of its op heads and of the operations it has that the new ones descend from,
and the hub leaves out everything they reach. A node also fetches operations starting from
the newest hub head it has, which includes its own accepted push, so it never downloads
what it uploaded.

### Which hive

A hub holds many hives, and a joining repository doesn't say which it belongs to: the hub
works it out, so that adding a machine is one command. Neither command guesses about
creating a hive, though: `join` that matches nothing is refused, and so is `create` that
matches a hive, unless it names the new one. A copy whose remote URL doesn't look like the
others', behind an ssh host alias, say, would otherwise get a hive of its own and sync with
nothing, with no sign anything was wrong. In one request the node sends its backend, its
remotes' URLs, its root commits (the commits whose parent is the root commit, git's
parentless commits, leaving out an empty, undescribed working-copy commit), and the
commits its remote bookmarks point to. The hub decides under its lock, so a copy joining
while another creates the hive finds it:

1. A repository with no commits of its own is refused: there is nothing to match, and
   nothing to share.
2. `--hive <name>` joins that hive, but only if the repository is related to it.
3. `musubi create <name>` creates a hive. `musubi create`, unnamed, creates one named as
   below, unless the rules that follow would join a hive, when it is refused.
4. Otherwise, a hive is *related* if it has stored one of the repository's root commits
   (ever: hidden ones count), or has a commit one of its remote bookmarks points to (which
   covers a shallow clone, whose roots are cut off). Among related hives, one that shares a
   remote URL with the repository, any remote and not only `origin`, is the one: exactly
   one is joined, and several are refused with their names, to choose from with `--hive`.
   With none, joining is refused, naming the related hives, so a fork, sharing history but
   with remotes of its own, isn't taken for the original; `musubi create` gives it a hive
   of its own. A repository without remotes joins its one related hive, and one with
   remotes joins a single related hive that has none. No related hive at all is refused
   too.

URLs match after normalization: https, ssh, scp-style, `file://`, and local paths reduce
to a lowercase host, without any user or default port, and a path without trailing `/` or
`.git`, and the host and path are what is compared. Azure DevOps' https and ssh forms are
made one. Each hive keeps every URL it has ever had, so renaming a remote or moving a
repository doesn't orphan it.

For this the hub keeps an index for each hive: every remote URL its settings have recorded,
every root commit it has stored, and the machines with workspaces at its head. The index is
updated whenever a head is accepted, and is a cache: the hub rebuilds it from the hive's
operations and objects when it is missing. A join also counts what the joining repository
says it brings, its URLs and root commits, as its hive's for a couple of minutes, so that
another copy joining before the first one's push finds the same hive. That stops counting
once the joining machine's first push is accepted, which puts what it really brought in
the index, or when the time is up, so a join that never pushes leaves nothing behind.

A new hive is named after the remote named `origin`, else the first remote by name, else
the repository's directory. The name follows the forge: `owner/repo` on GitHub, Codeberg,
Forgejo, Gitea, and Bitbucket; the full group path on GitLab; `user/repo` for sourcehut's
`~user/repo`; `org/project/repo` on Azure DevOps; a Gerrit project without its `a/`; and
otherwise the last two components of the path. A hive gets the shortest form of its name no
other hive has: `jj-musubi`, then `bos/jj-musubi`, then `github.com/bos/jj-musubi`. Names
never change by themselves; `musubi hub rename` changes one. Commands that take a hive
accept any unique prefix of its name.

`musubi clone <name>` creates a new colocated repository and joins it to the named hive.

## Abandoning operations and garbage collection

`jj op abandon` rewrites the descendants of the abandoned operations into new operations with
new ids. If musubi ignored that, the next pull would bring the old operations straight back.

musubi treats an op abandon as an update in its own right. A node notices when canonical
operations it had published stop being reachable from its op heads. jj never does that except
in `op abandon`. The node pairs each rewritten operation with its original by matching
metadata and view, and pushes a supersede record: the new head replaces the old one, with
equal views at the tips. The hub accepts it like a fast-forward. Other nodes apply the same
rewrite locally, reparenting any unpushed work of their own onto the new chain as
`jj op abandon` does. The hub later discards superseded operations and objects nothing
references.

Until supersede records are implemented, a node that detects an op abandon pauses
replication for that repository and says why, rather than undoing it.

`jj util gc` only removes data that is no longer reachable locally, so it needs no special
handling. The hub runs its own garbage collection.

## Transport

The transport is a small trait. Request/response carries messages up to the negotiated size
limit. Subscriptions carry hub notifications. Hub requests go to `musubi.<hive>.rpc`, and
notifications to `musubi.<hive>.head`. Requests about the hub as a whole (join, list,
resolve a name, rename, remove) go to `musubi.hub.rpc`. The hub takes all of them on one
subscription, `musubi.*.rpc`; each hive's requests go to a thread of its own, which opens
the hive's store on its first request and answers one request at a time, which is what
makes each push atomic, while different hives don't wait for each other. A request for a
hive the hub doesn't have is an error: only a join creates hives. Every operation and
object is verified against its content hash on receipt, so a misbehaving peer cannot inject
data under a false id.

- **In-memory**: an in-process network, which the hub's service and the connections it
  serves meet on. Tests run nodes and hubs over one too, which can drop, delay, duplicate,
  and reorder messages, and disconnect peers.
- **Streams** carry the same subjects over a byte stream: the hub's local socket, and over
  ssh, the standard input and output of `musubi hub connect`. Each frame is its length,
  a kind, and its fields: `SUB`, `PUB` and `REQ` from the client, and `MSG` for its
  subscriptions, and `REPLY` or `FAIL` for its requests, from the hub, which relays each
  connection through its own in-memory network, every request as it comes. A frame the
  connection ends partway through is never delivered. The client opens a new connection
  whenever one ends, subscribing again to what it had; requests in flight on the old one
  fail at once, and those made in between wait for the new one, up to their timeout.
  Either side ends a connection that falls 1024 frames behind, as one whose other side
  vanished without a word does. Once connected, a client tries a hub that then answers
  with another version's greeting, more noise than it passes over, or an implausible
  payload limit again only after a minute; connecting the first time, that fails at once,
  and the daemon backs off as after any failure.
- Over ssh, the hub's machine may print something before the hub greets: some shells'
  startup files print for every shell, a banner in ASCII art, say. The client passes over
  up to 64 KiB of it, as Mercurial's ssh client passes over noise before its handshake;
  past that, it fails, quoting the first thing printed. The greeting starts with a NUL,
  which is never part of text, so that a banner passes for it only by printing it on
  purpose. The client greets the hub only after the hub has greeted it, so that nothing
  that runs there first can read the greeting. Messages broadcast to terminals, as by
  `wall` or `shutdown`, never reach the stream: the session has no terminal, so it isn't
  among the logins they write to.

### Running a hub

A hub is meant for one person's machines, or a team that trusts each other: anyone who can
reach it can read and write every hive on it. `musubi hub` serves a directory holding one
subdirectory per hive, named by the hive's id, each with the hive's store (`canonical/`,
`backend`, `git/` and `extras/` or `simple/`, `heads`, `blobs/`, `tmp/`), its `hive.toml`
(name and backend), and its index. Removed hives move to `removed/`. Without `--dir` the
hub serves `./musubi-hub`, or the current directory if it is a hub's, and takes a lock in
the user's state directory, so that a second hub started the same way says where the first
one is instead of starting; `--dir` runs more hubs on purpose.

The hub listens on a local socket that only its owner can reach, `run/hub.sock` in its
directory, in a subdirectory only its owner can open (on Windows, a named pipe named after
the directory), where no temp cleaner, or the end of the login that started the hub,
removes it. `musubi hub connect`, and commands on its machine, find it there. It prints
the commands other machines run, with this machine's host name, or the name `--advertise`
gave it, which it keeps in `hub.toml` too: a machine doesn't always know a name others can
reach it by. It also saves its directory as the machine's default hub, unless the machine
has one, so that commands on the hub's machine need no `--hub`.

### Reaching a hub over ssh

Often ssh is the only way one machine can reach another, as when a laptop reaches a devbox
through a zero-trust tunnel, and the protocol trusts whoever can reach the hub, so it can't
simply be exposed. A `--hub` that isn't an absolute path is an ssh destination,
passed to the user's own `ssh` (or `$MUSUBI_SSH`), so `~/.ssh/config` applies: aliases,
`ProxyCommand`, and the rest.

- Each machine has a key of its own, `hub_key` in its state directory. Joining a hub over
  ssh first tries it, and if ssh refuses it (or there's no key yet, when it creates one),
  adds it to `~/.ssh/authorized_keys` on the hub's machine, through the user's ordinary ssh,
  which can prompt then, since the user is at the terminal: `restrict,command="musubi hub
  connect"`, so a stolen key reaches the hub and nothing else. The daemon needs no ssh agent
  to reach the hub, and never prompts (`BatchMode=yes`), which a process started at login
  couldn't answer.
- `musubi hub connect` relays its stdin and stdout to the socket of the user's hub (the one
  `musubi hub` last served without `--dir`).
- On the other machine, each connection is an ssh of its own, and the stream transport
  speaks through its stdin and stdout. Nothing outlives a connection: an `ssh -L` forward
  that lasts goes dead when the machine sleeps, while here, connecting again is a new ssh.
  ssh's `ServerAliveInterval` gives up on a dead link within half a minute, but `Instant`
  stops while the machine sleeps and the wall clock doesn't, so a jump between them ends
  every connection at once, and the transport connects again within seconds of waking.
- Once the transport reconnects, over ssh or not, the daemon syncs at once, even if it was
  waiting to retry a sync that failed (once in a run of failures, since a sync could lose
  the connection itself): the hub's announcements while it was away are lost.
  A request in flight when the connection dropped fails at once, so a sync it was part of
  starts again.
- ssh doesn't compress (`Compression=no`): musubi already compresses what it sends.
- A failing ssh backs off, up to a minute, and the transport's attempts to connect
  meanwhile fail at once: otherwise they would run ssh, and perhaps a tunnel's login page in
  a browser, every few seconds. Only the hub's greeting coming through counts as ssh
  working, not whatever the shell printed first. What ssh said, or that `musubi` isn't on
  the `PATH` there (exit status 127), becomes part of the error `musubi list` shows.

The hub logic and the node sync logic are sans-IO state machines. They consume events and
produce effects, which keeps them deterministic under test, and they correspond directly to
the formal model.

## Local integration

- Each user runs one daemon, which serves every repository listed in its config file
  (`config.toml` in musubi's config directory, the source of truth), one thread each.
  Commands reach it over a control socket: tarpc, with JSON messages, over a Unix domain
  socket (`$XDG_RUNTIME_DIR/musubi/daemon.sock` on Linux, `$TMPDIR/musubi/daemon.sock` on
  macOS) or a Windows named pipe (`\\.\pipe\musubi-<user>`). It answers `version`, `add`
  (start serving a repository now, and reply after its first sync), `remove`, `sync`,
  `status`, and `stop`. `musubi create`, `join`, and `clone` write the repository's
  membership and the config file, then ask the daemon to add it, starting the daemon in the
  background first if none is running. Only the user can reach the daemon: a Unix socket's directory
  must be theirs and writable by no one else, as tmux and ssh-agent check, or the daemon
  won't listen there and commands won't connect; a named pipe admits only its owner, and
  the daemon creates it as the first instance, so it can't start if another user took the
  name. A lock file in the state directory, named after the socket, keeps a second daemon
  from starting; the daemon holding it removes a socket a crashed daemon left behind.
  Commands check the daemon's version first, and suggest `musubi daemon restart` when it
  differs.
- `musubi daemon install` hands the daemon to the platform's service manager, to start at
  login: a launchd agent on macOS and a systemd user unit on Linux, which restart it after
  a crash but not after `musubi daemon stop`, and an entry in the user's `Run` registry key
  on Windows, which runs `musubi daemon start`. Where launchd or systemd runs it, commands
  that need the daemon ask the service manager to start it rather than starting one
  themselves, so there is never a second. The service gets the installing shell's `PATH`
  (the daemon runs `git`) and `MUSUBI_*` settings, and a marker in the state directory
  records it, so commands with another `MUSUBI_CONFIG_DIR` (tests) leave it alone.
- A daemon that a command starts outlives it, so it takes nothing from the command's
  environment that only says where the command ran. git's variables naming a repository
  (`git rev-parse --local-env-vars`), which a git hook has, reach neither the daemon nor
  any git musubi runs, and that git runs no hooks, as jj runs none when it writes `.git`.
  The daemon's `SSH_AUTH_SOCK`, for signing with a key an agent holds or for a `ProxyJump`
  host, names `ssh-agent` in the state directory: a link that every command points at its
  own agent when that answers, so the daemon uses the agent of the latest session to run
  musubi, and outlives the session it started in, such as an ssh login with a forwarded
  agent. The systemd unit names the link too, since a user's service manager rarely has an
  agent; launchd has one of its own.
- Commands change `config.toml` holding a lock beside it, and write it whole, so
  that concurrent joins keep each other's changes and a crash never leaves half a file.
- The daemon watches `.jj/repo/op_heads/heads` with filesystem notifications and also polls
  slowly. It reads operations through jj-lib's op store and never parses jj files itself.
- Loads and merges go through jj-lib's repo loader, which takes jj's op heads lock. musubi
  therefore merges concurrent heads exactly once per machine even while `jj` commands run.
- In colocated repositories, realization holds `.jj/repo/git_import_export.lock`, the lock the
  jj CLI holds around its own import and export, so the two never interleave.
- Merges that musubi performs rebase commits, which needs the user's jj config (identity, and
  signing if enabled). musubi loads the same user and repo config that `jj` does. The merge
  operation looks like one `jj` would write ("reconcile divergent operations"), with this
  machine's hostname.
- Operations reach the op store in dependency order: objects, then views, then operations
  ancestors first, then the op head. A jj process can therefore never observe a reference to
  something missing.
- musubi never replicates `index/`, `config-id`, `workspace_store/`, or `store/git_target`.

## Compatibility

jj's operation format changes every few months, almost always by adding fields, and jj keeps
reading older files. Ids are hashes of jj-lib's in-memory structs, not of file bytes, and
jj-lib never verifies them on read. Two consequences:

- An older jj-lib decoding an operation written by a newer `jj` silently drops the fields it
  does not know, and canonicalizing it would lose them. Before canonicalizing a local
  operation or view, musubi walks its protobuf encoding and refuses any field number that
  jj-lib 0.46 does not define. A newer `jj` CLI writing to the repository is therefore a
  clear error, not silent data loss.
- Canonical operations are always written by musubi's pinned jj-lib, so a receiver can verify
  each canonical operation and view by decoding and re-hashing it. A mismatch means a peer is
  running an incompatible version, or is lying.

Nodes and hub exchange protocol and jj-lib versions when they connect and refuse to talk
across incompatible ones. musubi is pinned to jj-lib 0.46.0.

## Testing

- **Formal model**: a Lean 4 model of the hub and node protocol, covering lossy and reordering
  networks, crashes, interrupted uploads, and concurrent local operations. It proves the
  safety properties: the hub only ever references complete data; the canonical head only moves
  forward, so accepted operations are never lost; nodes only realize complete operations;
  operations not yet accepted are visible only on the node that made them; and no two nodes
  perform the same merge. It also proves progress: when local activity stops and the network
  delivers, every node converges to the canonical head.
- **Protocol property tests**: Hegel (the Rust port of Hypothesis) stateful tests drive the
  sans-IO hub and nodes over the in-memory transport with fault injection, checking the same
  invariants as the model after every step and convergence after a quiescence step.
- **Generated end-to-end tests**, in the style of jj-stack's property harness: a Hegel state
  machine runs real `jj` commands (commit, describe, rebase, abandon, new, bookmark moves,
  `op abandon`, git-side ref changes) against several real repositories, some colocated. Each
  repository is served by a real musubi node, with faults kept as separate rules
  (disconnects, crashes mid-upload, hub restarts). Invariants are checked against the
  repositories themselves. The default test run covers fixed scenarios. The generated search
  is a separate, sharded, opt-in run, with one example database per shard, and reports which
  rules it never reached.
- **Transport tests** hold the in-memory and stream transports to the same contract, and run
  nodes and a hub over streams. The CLI tests run hubs and daemons as processes of their
  own, over local sockets and a stand-in for ssh.

## Milestones

1. Formal model; sans-IO protocol core, in-memory transport, and protocol property tests.
2. jj integration: canonical op store, format guard, translation of per-machine fields,
   op-heads watching, realization under the colocated lock.
3. Objects: git packs, keep refs, and extras; simple-backend store files.
4. Hub storage, a transport between machines, daemon and CLI (`hub`, `join`, `clone`,
   `sync`, `list`, `leave`, `debug op-id`); hubs serving many hives, matching joining
   repositories to them, and a daemon controlled over a local socket.
5. Generated end-to-end tests, and tests across processes.
6. Supersede records for `jj op abandon`, hub garbage collection.
7. Starting the daemon at login, as a launchd agent, systemd user unit, or Windows `Run`
   entry.
