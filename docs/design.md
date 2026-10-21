# jj-musubi design

jj-musubi keeps one jj repository in sync across several machines. A daemon on each machine
watches the repository's operation log. It publishes new operations, and the objects they
refer to, to a hub. It also applies operations that other machines published. When you commit,
rebase, or abandon on one machine, the same operation shows up in `jj op log` on the others
within a second or so. A machine that was offline catches up when it reconnects.

musubi never touches working copies. It writes only to the operation log, the commit store,
and, in git-backed repositories, the git object database and refs. A remote operation can
rewrite this machine's working-copy commit, for example by rebasing its parent. jj then
treats the working copy as stale, exactly as after a `jj rebase` run from another workspace.
By default the next `jj` command stops and suggests `jj workspace update-stale`. With
`snapshot.auto-update-stale = true`, which musubi recommends for hive repositories, jj
updates the files itself. If the working copy had edits not yet snapshotted, jj snapshots them
first, and you get a divergent working-copy change instead of losing them.

This document targets jj-lib 0.46.0.

## Vocabulary

- **Hive**: one logical repository replicated by musubi. It has a hive id, a UUID that musubi
  generates, and one hub. jj repositories have no identity of their own: every repository
  shares the same all-zero root operation and root commit, and `.jj/repo/config-id` is a
  machine-local pointer that jj regenerates when it detects a copy.
- **Node**: one local jj repository on one machine taking part in a hive, together with the
  musubi daemon serving it.
- **Hub**: a long-running musubi process that stores a complete copy of the hive, orders
  updates, and serves catch-up. It never originates changes. Any machine can run it.
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
  rather than abandoned (the change's one visible commit).

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
  `OpStore`, as `jj op integrate` does, and lets jj build the index lazily.
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
shared config keys as hive settings. When a machine's settings change, musubi records the new settings in an
attribute (`musubi.settings`) of an operation it writes, which changes nothing else. That
operation replicates like any other, so settings changes are ordered by the hub, and where
concurrent operations meet, the settings merge three-way, remote by remote, as jj merges
workspaces. The hive's settings as of an operation are the nearest recording ancestor's,
merged at merge operations.

At the start and end of every sync, a machine reconciles its settings three-way: what it
has now, what the hive has as of its head, and what both had when they last agreed. It
records its own changes, and applies the hive's: remotes with `git remote`, which also
renames or deletes the remote-tracking refs, and config keys in its repo config file.
Config values are compared as TOML, normalized, so that machines that write the same value
differently agree on it. A machine that joins adds its remotes to
the hive's, but takes the hive's where both have a remote of the same name; the first
machine's settings become the hive's. A machine that needs another URL for the same remote
can rewrite it with git's own `url.<base>.insteadOf` in its user config.

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
fast-forward or merge as usual. A hub location is a NATS URL and a subject prefix. The old hub
can publish a signed-by-config `hub-moved` advertisement carrying the new location and a
higher epoch. Nodes then reconnect there and ignore lower-epoch hubs from then on.

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
already needs `git` for fetch and push, and this gets delta compression and bitmaps for free.

- The hub stores objects in a bare git repository.
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
  (by git's thresholds, or the repository's), but with pruning disabled: musubi never deletes
  an object, reachable or not. The hub's repository has no refs, so to git all of its
  objects are unreachable, and they go to a cruft pack.
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

NATS rejects messages larger than the server's `max_payload`, which defaults to 1 MiB. Control
messages are small. Something bulky (packs, large views, batches of operations) travels
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

`musubi join` makes an existing repository part of a hive. By default it replicates the
repository's current state, not its operation history. It writes one canonical join
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

`musubi hub` creates a hive, with a new id, the first time it runs on a directory. Every
machine, the first included, then runs `musubi join <hive>`. `musubi clone <hive>` creates a
new colocated repository from a hive and joins it.

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
limit. Subscriptions carry hub notifications.

- **NATS** is the first real transport. Hub requests go to `musubi.<hive>.rpc`, and
  notifications to `musubi.<hive>.head`. Core NATS is enough: the hub is the durable store,
  so JetStream is not needed. TLS and NATS credentials authenticate machines. Every operation
  and object is verified against its content hash on receipt, so a misbehaving peer cannot
  inject data under a false id.
- **In-memory** transport for tests. It can drop, delay, duplicate, and reorder messages, and
  disconnect peers.

The hub logic and the node sync logic are sans-IO state machines. They consume events and
produce effects, which keeps them deterministic under test, and they correspond directly to
the formal model.

## Local integration

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
- **NATS integration tests** run the same scenarios across processes against a real
  `nats-server`.

## Milestones

1. Formal model; sans-IO protocol core, in-memory transport, and protocol property tests.
2. jj integration: canonical op store, format guard, translation of per-machine fields,
   op-heads watching, realization under the colocated lock.
3. Objects: git packs, keep refs, and extras; simple-backend store files.
4. Hub storage, NATS transport, daemon and CLI (`hub`, `join`, `clone`, `sync`, `status`,
   `debug op-id`).
5. Generated end-to-end tests and multi-process NATS tests.
6. Supersede records for `jj op abandon`, hub garbage collection.
