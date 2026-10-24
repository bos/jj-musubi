# Sync protocol

The exact protocol between nodes and the hub, and the properties it guarantees. The Lean model
in [formal/](../../formal/README.md) and the state machines in `crates/musubi-core`, which do
no I/O themselves, both follow it: a change here changes both. [design.md](design.md) explains
why the protocol has this shape, and defines its terms ("Vocabulary"): a *hive* is one
replicated repository, a *node* is one machine's copy of it with musubi's daemon, and the
*hub* stores the hive and orders its updates.

The protocol works on *canonical operations*: the form of a jj operation that is replicated,
the same on every node. Each node also has its own *local operations*, in its jj op store, and
writes a *realization*, a local operation, for each canonical operation it receives.
Translating between the two is a separate layer, specified at the end
([Translation layer](#translation-layer)).

## Data

- `OpId`: a canonical operation id. `root` is the root operation, present everywhere.
- Each canonical operation `x` has an immutable list `parents(x)` (empty only for `root`) and
  an immutable finite set `objs(x)` of object ids it requires: the commits its view and
  `commit_predecessors` refer to, with everything reachable from them.
- `anc*(x)`: `x` and all its ancestors.
- `closure(x)`: `anc*(x)` together with `objs(y)` for every `y` in `anc*(x)`.
- `creator(x)`: the node that wrote the local operation whose canonical form is `x`. It is not
  stored anywhere; it exists only for stating properties.

Operations and objects are content-addressed. Storing one is idempotent, and two stores that
contain the same id contain the same bytes.

## Hub

Persistent state:

- `ops`, `objects`: the canonical operations and objects stored so far. These can include
  uploads that were never accepted.
- `head: OpId`, initially `root`.
- `seq: Nat`, the number of accepted head changes, initially 0. `(seq, head)` pairs therefore
  identify heads in acceptance order.

Requests and replies (each request carries a node-chosen request id that the reply echoes):

| Request | Reply |
| --- | --- |
| `Fetch(base, haves H)` | `Fetched(seq, head, ops, objects)`: the hub's `(seq, head)`, the stored operations in `anc*(head) \ anc*(base)`, and the stored objects they require, less `closure(base)` and `H` |
| `GetObjects(for operations S, base, haves H)` | `Objects`: the stored objects `S` requires, less `closure(base)` and `H` |
| `Push(operations, objects, expected, new)` | `Accepted(seq, head)`, `Rejected(seq, head)`, or `Incomplete(seq, head)` |

`Fetch` asks for a range ending at the hub's own head, because a node cannot name operations
it has never seen, and the reply says which head that was. `base` is an operation the hub
accepted that the node has, so the hub leaves out `closure(base)`. The haves name other
objects the node has, which the hub leaves out too. In a git-backed hive haves are commits,
and they cover everything those commits reach. The hub ignores haves it does not have.

The hub answers `Push(operations, objects, expected, new)` in one atomic critical section. It
stores the operations and objects, then answers `Cas(expected, new)`, a compare-and-swap of
its head:

1. If `new = head`, it replies `Accepted(seq, head)` and changes nothing else, whatever
   `expected` is. This makes a retried `Push` idempotent.
2. Otherwise it accepts if and only if `head = expected`, `closure(new) ⊆ ops ∪ objects`, and
   `expected ∈ anc*(new)`. The ancestry check walks `parents` over stored operations, so it
   is only meaningful once the closure check has passed. Since the closure of every
   operation in `anc*(head)` is stored ([HubClosed](#properties)), the closure check need
   only look at what `new` adds to them.
3. On acceptance it sets `head := new` and `seq := seq + 1`, persists both, and only then
   replies `Accepted(seq, new)` and publishes `Head(seq, new)` to the hive's nodes.
4. Otherwise, if `head = expected` but `closure(new) ⊄ ops ∪ objects`, it replies
   `Incomplete(seq, head)`. The node pushed from the head but lacks what `new` requires, so
   pushing again would send the same: it stops with an error rather than retry forever.
   Otherwise it replies `Rejected(seq, head)`: the head isn't `expected`, as when another
   push came first, or `new` doesn't descend from it.

Every `Head`, `Accepted`, `Rejected`, `Incomplete`, and `Fetched` carries a `(seq, head)`
pair the hub actually had.

Each request takes one round trip. Operations and objects travel inline in their message
when they fit in a quarter of the transport's message limit, and otherwise as chunked blobs
([Chunked blobs](#chunked-blobs)). At this level of the protocol each message is atomic.

The formal model also has finer-grained requests, which musubi doesn't send: `GetHead`,
`PutOps` and `PutObjects` (each answered by `Stored`), `GetOps(S)` for operations
`S ⊆ anc*(known.head)` (answered by `Ops`), and `Cas`. A `Push` is `PutOps`, `PutObjects` and
`Cas` handled together. Safety is proved for nodes that send any of them.

## Node

Persistent state:

- `local`: the canonical ids of operations present in the local op store, as originals or
  realizations.
- `heads`: the canonical ids of the local op heads.
- `staged`: canonical operations and objects downloaded from the hub but not yet realized.
- `known: (seq, OpId)`: the newest hub head the node has heard of, initially `(0, root)`.

The node can lose volatile state, such as in-flight requests and partial downloads, at any
time.

### Environment actions

These happen outside musubi, through `jj`:

- `UserOp(p)` for some `p ∈ local`: a `jj` command based at `p` writes a new operation `o`,
  with `parents(o) = [p]` and fresh objects that are stored locally. Then
  `local := local ∪ {o}` and `heads := max(heads \ {p} ∪ {o})`, where `max(S)` keeps the
  elements of `S` that are not ancestors of another element. `p` need not be a head, because
  a long-running command may have loaded an older operation.
- `Merge`, when `|heads| ≥ 2`: some process, musubi or `jj`, loads the repo, and jj writes a
  merge `m` with `parents(m) = heads` and possibly fresh objects (rebased commits). Then
  `local := local ∪ {m}` and `heads := {m}`.

### Sync actions

- `Learn(s, h)`: on receiving `Head`, `Accepted`, `Rejected`, `Incomplete`, or `Fetched`
  carrying `(s, h)`, if `s > known.seq` then `known := (s, h)`. Stale and duplicated
  notifications are therefore harmless.

  Over musubi's transports, a reply to the node's own request can't be stale: they match it to the
  one request the node has outstanding, and drop it if it comes after that request timed out, and
  the hub answers only after everything the node learned before sending it. So a reply with
  `s < known.seq`, or with `s = known.seq` and `h ≠ known.head`, means the hub has gone back
  ([Network and failures](#network-and-failures)). The node then restarts, forgetting `known`,
  and learns `(s, h)`. Over a network that duplicates replies, as the model's does, this rule
  can fire on a stale reply too, which costs a restart, and a restart is always safe.
- `Fetch`: send `Fetch(base, H)`, where `base` is any local operation the node knows the hub
  accepted, and `H` names objects of its heads. So that the node is never sent what it has,
  `base` is the newest `known.head` that was local and in `anc*(heads)`, which includes the
  node's own push once the hub accepts it.

  On the reply, learn its head, and add its operations and objects to `staged`, but only
  operations in `anc*(known.head)`: the reply's head must be `known.head`, and its operations
  must all be reachable from it through parents in the reply. Anything else is ignored. The
  hub replies only with accepted operations, so this check guards only against a hub that
  lies. **Staging only operations in `anc*` of a head the hub accepted is the one guard
  Locality, and so MergeOwnership, depends on** ([Properties](#properties)).

  `GetObjects` asks for the objects of staged operations that lack them, with the objects of
  the node's heads and of the local operations those descend from as haves.
- `Realize(x)`, for `x ∈ staged` with `parents(x) ⊆ local` and `objs(x)` available locally:
  write the realization and set `local := local ∪ {x}`. `heads` does not change.
- `Advance`, when `known.head ∈ local` and `known.head ∉ anc*(heads)`: set
  `heads := max(heads ∪ {known.head})`.
- `Push`, when `heads = {h}`, `h ≠ known.head`, and `known.head ∈ anc*(h)`: send
  `Push(closure(h) \ closure(known.head), known.head, h)`, that is, what the hub lacks of `h`,
  and `Cas(known.head, h)`.

### Policy

Only three node-side rules matter for safety: stage and realize only operations in `anc*` of
a head the hub accepted, push only local operations, and merge all current heads. The guards
on `Push`, the order below, and `Learn`'s sequence filter matter only for liveness and
efficiency. The formal model proves safety even for a node that ignores them, and proves
that any interleaving of policy steps converges.

The node's daemon repeatedly takes the first applicable step:

1. If `|heads| ≥ 2`, merge (musubi loads the repo, so jj performs the merge).
2. If `known.head ∉ local`, fetch and realize until it is local, then advance. One walk down
   from `known.head` plans the realization: the staged operations in an order that puts
   parents first, with their objects checked together, so that catching up on `n`
   operations takes time linear in `n`.
3. If `known.head ∉ anc*(heads)`, advance. Afterwards `|heads| ≥ 2` or `heads = {known.head}`.
4. If `heads = {h}` with `h ≠ known.head`, which by now implies `known.head ∈ anc*(h)`: push,
   uploading what the hub lacks with it.
5. Otherwise idle until a notification, a local op-heads change, or the poll timer.

On connecting, and on every poll, the node sends `Fetch`. A sync that finds something new
therefore takes one round trip, and one that pushes takes two.

## Network and failures

- Messages can be lost, duplicated, delayed, and reordered. They are never corrupted:
  content hashes are checked on receipt, and a corrupt message counts as lost.
- A node can crash, keeping its persistent state and losing everything else. Only `local`
  and `heads` must survive (they are the jj repository); safety holds even if `known` and
  `staged` are lost.
- The hub can crash. It must keep `head`, `seq`, and `closure(head)`, persisting a head
  change before replying. It may lose, or garbage-collect, any operations and objects
  outside `closure(head)`, and upload sessions.

musubi's hub persists nothing synchronously, though, so a power cut can lose the last heads it
accepted. The hub then goes back to a head it accepted earlier, with that head's sequence number;
or, when what it lost leaves a hive's store corrupt, to the root, making the hive again, empty.
The model takes what the hub keeps to be intact: a store that a power cut tore without the hub
noticing is made again by hand ([design.md, "Replacing the hub"](design.md#replacing-the-hub)).

After the hub goes back, the safety properties below that rest on its history only growing
(HubMonotone, KnownIsHubHistory, Locality, MergeOwnership) can fail, and two nodes can merge
the same heads. The others still hold. So does liveness: nodes that knew the lost heads
follow the hub back, by the rule in `Learn`, and once it stops going back they converge on
it, with every operation any node created in `anc*(hub.head)`.

## Properties

Safety. These hold in every reachable state:

- **HubClosed**: `closure(head) ⊆ ops ∪ objects`.
- **HubMonotone**: each accepted head descends from the previous one. Hence an operation that
  is ever in `anc*(head)` stays there.
- **NodeClosed**: `local` is closed under parents and its operations' objects are present;
  `heads ⊆ local`; `heads` is an antichain.
- **KnownIsHubHistory**: `known.head` is a head the hub accepted at sequence number
  `known.seq`.
- **Locality**: every `x ∈ local(n)` satisfies `creator(x) = n` or `x ∈ anc*(hub.head)`. An
  operation the hub has not accepted is visible only on the node that made it.
- **MergeOwnership**: every merge created on node `n` has a parent `p` with `creator(p) = n`
  that the hub had not accepted when the merge was made. Hence two different nodes never
  create merges with the same parents, so no merge, and none of the commits it rebases, is
  ever performed twice.

Liveness. If environment actions stop and every node keeps following the policy over a
network that eventually delivers, every node reaches `heads = {hub.head}`, and every operation
any node created is in `anc*(hub.head)`.

No feedback loop. Realizing an operation never creates a canonical operation. So once
environment actions stop and the system converges, no further messages are sent apart from
polls.

## Chunked blobs

A blob is a byte string with id `hash(bytes)`. A session transfers one blob in chunks of at
most `limit` bytes, each tagged `(blob id, offset, length)`. Sessions are keyed by blob id,
so that one is never reused for a different blob: otherwise stale duplicated chunks from an
earlier session could make every retry fail its hash check.

- The receiver keeps the set of byte ranges it has. Chunks can be lost, duplicated, or
  arrive out of order; duplicates and overlaps are ignored.
- `Status(session)` returns the ranges the receiver is missing. The sender retransmits those.
- `Finish(session, id, total_length)` succeeds only when every byte in `[0, total_length)` has
  arrived and `hash(assembled) = id`. Otherwise it reports the missing ranges, or a hash
  mismatch, which restarts the session.
- Sessions are volatile. After a crash the sender starts again, and a content-addressed
  receiver that already stored the blob answers immediately.

Properties: a finished blob is byte-identical to the one sent, even when corrupt or stale
chunks arrive; and if the network eventually delivers and the receiver eventually stops
crashing, every session finishes.

musubi's transfers stay within this model, doing less than it allows:

- A sender keeps up to eight chunks in flight, uploading and downloading, rather than wait
  for each chunk's acknowledgement, so that a transfer costs a round trip per eight chunks.
  The model lets a sender send any chunk at any time, so this needs nothing more.
- The receiver keeps only bytes that extend what it has contiguously, as if the others had
  been lost. It reports the length of that prefix, not the missing ranges, and checks the
  hash as soon as the prefix reaches the blob length a chunk claims, with no `Finish`.
- A crash keeps the partial blob. A sweep of old blobs removes it, or the stored blob.

`formal/Musubi/Chunks.lean` proves, for an injective hash, that each step of this receiver is a
run of the model's steps, and that a sender resending from the prefix it reports finishes. A test
checks the receiver against that model ([conformance.md, "Chunked
blobs"](conformance.md#chunked-blobs)).

## Verification

`formal/` proves in Lean, for any number of nodes, every safety property above, and liveness
under reliable delivery ([formal/README.md](../../formal/README.md) says why that stands for the
real network). `formal/Musubi/Regress.lean` proves what still holds of a hub that goes back: its
head stays closed, its history a chain from the root, each node's repository closed, and the
nodes converge once it stops going back, whatever order they take their steps in. The proofs pin
down several requirements in this document: the `Cas` order, the `Fetch` guard, what must be
durable, and keying chunk sessions by blob id.
[formal/README.md](../../formal/README.md) lists the theorems, and
[conformance.md](conformance.md) describes how the Rust implementation is checked against
the model.

## Translation layer

`canon(L)` maps a local operation to its canonical form:

- If `L` carries the attribute `musubi.canonical = C`, then `canon(L) = C`.
- If `L` is the join point recorded by `musubi create` or `musubi join`, then `canon(L)` is
  the join operation recorded with it.
- Otherwise `canon(L)` is `L` with its view's per-machine fields (`git_refs`, `git_heads` and the
  `git` remote) removed; its workspaces, and its operation's workspace name, under
  machine-qualified names, keeping only the workspaces of machines present there; and its parents
  replaced by their `canon`. It is stored in the canonical op store ([design.md,
  "Translation"](design.md#translation); [design.md, "Copies that go
  away"](design.md#copies-that-go-away)).

`realize(C)` writes a local operation `L` with `canon(L) = C`. It requires every parent of
`C` to be realized already.

Requirements:

- `canon(realize(C)) = C`.
- `canon` is injective on the operations reachable from one node's op heads: distinct
  reachable local operations have distinct canonical forms. Each node's local graph
  therefore embeds the canonical graph, which is what lets the properties above be stated
  over canonical ids. A crash can leave a second, unreachable realization of the same
  canonical operation behind. It is harmless garbage, and `jj util gc` removes it.
- Realizations of non-head operations are deterministic: each carries its parent realization's
  per-machine fields, or for a merge the parents' fields merged three-way as jj merges them
  ([design.md, "Translation"](design.md#translation)). Only the realization that becomes an op
  head runs `export_refs` against `.git`. Re-realizing after a crash therefore rewrites identical
  files.
- Neither `canon` nor `realize` writes to the hub or creates an operation that `canon` would
  map to a new canonical id.
