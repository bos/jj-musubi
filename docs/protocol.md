# Sync protocol

This is the precise protocol between nodes and the hub. The Lean model in `formal/` and the
sans-IO state machines in `crates/musubi-core` both follow it; a change here changes both.
[design.md](design.md) explains why the protocol has this shape.

Everything below works on canonical operations. Translation between canonical and local
operations is a separate layer, specified at the end.

## Data

- `OpId`: a canonical operation id. `root` is the root operation, present everywhere.
- Each canonical operation `x` has an immutable list `parents(x)` (empty only for `root`) and
  an immutable finite set `objs(x)` of object ids it requires: the commits its view and
  `commit_predecessors` refer to, with everything reachable from them.
- `anc*(x)`: `x` and all its ancestors.
- `closure(x)`: `anc*(x)` together with `objs(y)` for every `y` in `anc*(x)`.
- `creator(x)`: the node that wrote the local operation `x` canonicalizes. It is not stored
  anywhere; it exists only for stating properties.

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
| `GetHead` | `Head(seq, head)` |
| `PutOps(operations)` | `Stored` |
| `PutObjects(objects)` | `Stored` |
| `GetOpsSince(head, base)` | `Ops`: the stored operations in `anc*(head) \ anc*(base)` |
| `GetObjects(for operations S)` | `Objects`: the stored objects of `S` |
| `Cas(expected, new)` | `Accepted(seq, head)` or `Rejected(seq, head)` |

`GetOpsSince` names a range because a node cannot name operations it has never seen. A node
sends it only with `head = known.head`.

The hub answers `Cas(expected, new)` in one atomic critical section:

1. If `new = head`, it replies `Accepted(seq, head)` and changes nothing, whatever
   `expected` is. This makes a retried `Cas` idempotent.
2. Otherwise it accepts if and only if `head = expected`, `closure(new) ⊆ ops ∪ objects`, and
   `expected ∈ anc*(new)`. The ancestry check walks `parents` over stored operations, so it
   is only meaningful once the closure check has passed.
3. On acceptance it sets `head := new` and `seq := seq + 1`, persists both, and only then
   replies `Accepted(seq, new)` and publishes `Head(seq, new)` to subscribers. Otherwise it
   replies `Rejected(seq, head)`.

Every `Head`, `Accepted`, and `Rejected` carries a `(seq, head)` pair the hub actually had.

Bulky `PutOps`, `PutObjects`, `Ops`, and `Objects` payloads travel as chunked blobs (see
[Chunked blobs](#chunked-blobs)). At this level of the protocol each is atomic.

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
  `local := local ∪ {o}` and `heads := max(heads \ {p} ∪ {o})`. Here `max(S)` keeps the
  elements of `S` that are not ancestors of another element. `p` need not be a head, because
  a long-running command may have loaded an older operation.
- `Merge`, when `|heads| ≥ 2`: some process, musubi or `jj`, loads the repo, and jj writes a
  merge `m` with `parents(m) = heads` and possibly fresh objects (rebased commits). Then
  `local := local ∪ {m}` and `heads := {m}`.

### Sync actions

- `Learn(s, h)`: on receiving `Head`, `Accepted`, or `Rejected` carrying `(s, h)`, if
  `s > known.seq` then `known := (s, h)`. Stale and duplicated notifications are therefore
  harmless.
- `Fetch`: send `GetOpsSince(known.head, base)`, where `base` is any operation the node knows
  the hub accepted (for instance the last `known.head` it fully realized), and
  `GetObjects` for the operations it receives. Add the replies to `staged`, but only
  operations in `anc*(known.head)`: a reply's operations must all be reachable from the
  requested head through parents in the reply or in `local`. Anything else, including any
  reply to a request the node did not make, is ignored. **This is the one guard Locality,
  and so MergeOwnership, depends on.**
- `Realize(x)`, for `x ∈ staged` with `parents(x) ⊆ local` and `objs(x)` available locally:
  write the realization and set `local := local ∪ {x}`. `heads` does not change.
- `Advance`, when `known.head ∈ local` and `known.head ∉ anc*(heads)`: set
  `heads := max(heads ∪ {known.head})`.
- `Upload`, when `heads = {h}` and `known.head ∈ anc*(h)`: send `PutOps` and `PutObjects` for
  `closure(h) \ closure(known.head)`.
- `Push`, when `heads = {h}`, `h ≠ known.head`, and `known.head ∈ anc*(h)`: send
  `Cas(known.head, h)`.

### Policy

Only three node-side rules matter for safety: stage and realize only operations in
`anc*(known.head)`, push only local operations, and merge all current heads. The guards on
`Upload` and `Push`, the order below, and `Learn`'s sequence filter matter only for liveness
and efficiency; the formal model proves safety even for a node that ignores them, and proves
that any interleaving of policy steps converges.

The node's daemon repeatedly takes the first applicable step:

1. If `|heads| ≥ 2`, merge (musubi loads the repo, so jj performs the merge).
2. If `known.head ∉ local`, fetch and realize until it is local, then advance.
3. If `known.head ∉ anc*(heads)`, advance. Afterwards `|heads| ≥ 2` or `heads = {known.head}`.
4. If `heads = {h}` with `h ≠ known.head`, which by now implies `known.head ∈ anc*(h)`:
   upload, then push.
5. Otherwise idle until a notification, a local op-heads change, or the poll timer.

On connecting, and on every poll, the node sends `GetHead`.

## Network and failures

- Messages can be lost, duplicated, delayed, and reordered. They are never corrupted:
  content hashes are checked on receipt, and a corrupt message counts as lost.
- A node can crash, keeping its persistent state and losing everything else. Only `local`
  and `heads` must survive (they are the jj repository); safety holds even if `known` and
  `staged` are lost.
- The hub can crash. It must keep `head`, `seq`, and `closure(head)`, persisting a head
  change before replying. It may lose, or garbage-collect, any operations and objects
  outside `closure(head)`, and upload sessions.

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
most `limit` bytes, each tagged `(blob id, offset, length)`. Keying sessions by blob id, so
that one is never reused for a different blob, matters: otherwise stale duplicated chunks
from an earlier session could make every retry fail its hash check.

- The receiver keeps the set of byte ranges it has. Chunks can arrive lost, duplicated, or out
  of order; duplicates and overlaps are ignored.
- `Status(session)` returns the ranges the receiver is missing. The sender retransmits those.
- `Finish(session, id, total_length)` succeeds only when every byte in `[0, total_length)` has
  arrived and `hash(assembled) = id`. Otherwise it reports the missing ranges, or a hash
  mismatch, which restarts the session.
- Sessions are volatile. After a crash the sender starts again, and a content-addressed
  receiver that already stored the blob answers immediately.

Properties: a finished blob is byte-identical to the one sent, even when corrupt or stale
chunks arrive; and if the network eventually delivers and the receiver eventually stops
crashing, every session finishes.

## Verification

`formal/` proves every property above in Lean, for any number of nodes. The proofs found no
counterexamples. They did make several requirements in this document more precise (the `Cas`
order, the `Fetch` guard, what must be durable, keying sessions by blob id).
[conformance.md](conformance.md) describes how the Rust implementation is checked against
the model.

## Translation layer

`canon(L)` maps a local operation to its canonical form:

- If `L` carries the attribute `musubi.canonical = C`, then `canon(L) = C`.
- If `L` is the join point recorded by `musubi join`, then `canon(L)` is the join operation
  recorded with it.
- Otherwise `canon(L)` is `L` with its view's `git_refs` and `git` remote removed, its parents
  replaced by their `canon`, and stored in the canonical op store.

`realize(C)` writes a local operation `L` with `canon(L) = C`. It requires every parent of
`C` to be realized already.

Requirements:

- `canon(realize(C)) = C`.
- `canon` is injective on the operations reachable from one node's op heads: distinct
  reachable local operations have distinct canonical forms. Each node's local graph
  therefore embeds the canonical graph, which is what lets the properties above be stated
  over canonical ids. A crash can leave a second, unreachable realization of the same
  canonical operation behind. It is harmless garbage, and `jj util gc` removes it.
- Realizations of non-head operations are deterministic: they carry the parent realization's
  per-machine fields unchanged. Only the realization that becomes an op head runs `export_refs`
  against `.git`. Re-realizing after a crash therefore rewrites identical files.
- Neither `canon` nor `realize` writes to the hub or creates an operation that `canon` would
  map to a new canonical id.
