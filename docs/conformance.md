# Conformance between the Lean model and the Rust core

The Lean model in `formal/` proves the protocol's properties. The Rust core in
`crates/musubi-core` implements the protocol. This document defines the link between them: a
trace format, an oracle built from the Lean model, and a refinement check run under Hegel.

## The claim

Every behavior of the Rust core, at the level of abstraction of the model, is a behavior of
the Lean model. The Lean safety theorems hold for every reachable model state, so they hold
for every state the Rust core reaches.

The chain has three links:

1. **Relational model to executable model.** `formal/Musubi/Exec.lean` defines `execStep`
   on finite states. `exec_sound` proves that whenever `execStep` accepts an action, the
   corresponding relational `Step` exists between the abstracted states. The executable model
   therefore never accepts anything the proofs don't cover.
2. **Executable model to oracle.** `formal/Oracle.lean` is a thin JSON wrapper around
   `execStep`, built by `lake build oracle`. It contains no protocol logic of its own.
3. **Oracle to Rust.** The Hegel conformance tests in `crates/musubi-core/tests/conformance.rs`
   run the Rust hub and nodes, translate every step they take into model actions, and check
   each one with the oracle. They fail on any action the oracle rejects, or any difference
   between the Rust state and the oracle's state. Hegel shrinks failures to a minimal trace.

## The abstraction

The conformance tests run the real Rust core (`HubCore`, `NodeCore`, and their message
handling) against test implementations of its storage traits. These keep exactly the
model's state:

| Model | Rust test implementation |
| --- | --- |
| Universe: `next`, `par`, `objs` | the test's operation table; operation and object ids are small integers, root `0` |
| Hub `ops`, `objs`, `head`, `seq` | `FakeHubStorage` |
| Node `lops`, `lobj`, `heads`, `known`, `sops`, `sobj` | `FakeRepo` (`lops`…`sobj`) and `NodeCore` (`known`) |
| `net`, the set of every message sent | the test's network: a set, so any message can be delivered any number of times, or never |

The jj-specific parts of a real node (canonicalization, realization, bundles) are not
covered by this link. The jj integration tests and the generated end-to-end tests cover them.

## Wire format

The oracle reads one JSON object per line on stdin and writes one per line on stdout. Every
request gets exactly one reply.

### Requests

```json
{"op": "reset", "nodes": 3}
{"op": "step", "action": <action>}
```

### Actions

Fields mirror the constructors of `EnvStep` and `SyncStep` in `formal/Musubi/Model.lean`.
`node` is a node index below `nodes`. Op and object ids are naturals. Sets are arrays,
compared as sets.

| `"kind"` | Fields | Model step |
| --- | --- | --- |
| `userOp` | `node`, `parent`, `objs` | `EnvStep.userOp`: the new op gets id `next` |
| `merge` | `node`, `parents`, `objs` | `EnvStep.merge`: `parents` must enumerate `heads` |
| `getHead` | `node` | `SyncStep.getHead` |
| `learn` | `node`, `headKind`, `seq`, `head` | `SyncStep.learn`: the `head` message must be in `net`, and `seq > known.seq` |
| `fetchOps` | `node`, `ops` | `SyncStep.fetchOps` |
| `fetchObjs` | `node`, `objs` | `SyncStep.fetchObjs` |
| `recvOps` | `node`, `ops` | `SyncStep.recvOps` |
| `recvObjs` | `node`, `objs` | `SyncStep.recvObjs` |
| `realize` | `node`, `opId` | `SyncStep.realize` |
| `advance` | `node` | `SyncStep.advance` |
| `uploadOps` | `node`, `ops` | `SyncStep.uploadOps` |
| `uploadObjs` | `node`, `objs` | `SyncStep.uploadObjs` |
| `push` | `node`, `expected`, `new` | `SyncStep.push` |
| `crashNode` | `node` | `SyncStep.crashNode` |
| `loseKnown` | `node` | `SyncStep.loseKnown`: `known := (0, root)` |
| `loseVolatile` | `node` | `SyncStep.loseVolatile` |
| `hubGetHead` | `node` | `SyncStep.hubGetHead` |
| `hubPutOps` | `node`, `ops` | `SyncStep.hubPutOps` |
| `hubPutObjs` | `node`, `objs` | `SyncStep.hubPutObjs` |
| `hubGetOps` | `node`, `ops` | `SyncStep.hubGetOps` |
| `hubGetObjs` | `node`, `objs` | `SyncStep.hubGetObjs` |
| `casIdem` | `node`, `expected`, `new` | `SyncStep.casIdem` |
| `casAccept` | `node`, `expected`, `new` | `SyncStep.casAccept` |
| `casReject` | `node`, `expected`, `new` | `SyncStep.casReject` |
| `crashHub` | none | `SyncStep.crashHub` |

`headKind` is one of `head`, `accepted`, `rejected`, `notify`. The Rust hub decides how to
answer a `Cas`, and the test sends whichever of `casIdem`, `casAccept`, or `casReject` it
chose. The oracle checks that choice's guard, so a hub that accepts a `Cas` the model would
reject is caught.

### Replies

```json
{"ok": true, "state": <state>}
{"ok": false, "error": "casAccept: closure of 7 not stored at hub (missing op 6)"}
```

A rejected action leaves the oracle's state unchanged. The error names the guard that failed,
as `"<action>: <guard>"`, for example
`casAccept: closure of 1 not stored at hub (missing op 1)`.

Two consequences of the model that the Rust test implementations must match:

- `realize` adds an operation to `lops` and its objects to `lobj` but does not remove them
  from `sops` and `sobj`. Staging is only ever cleared by `loseVolatile`.
- `casAccept` adds an `accepted` reply for the sender and a `notify` message for every node
  below `nodes`, including the sender.

### State

```json
{
  "next": 5,
  "ops": [{"id": 1, "parents": [0], "objs": [10]}, ...],
  "hub": {"ops": [0, 1], "objs": [10], "head": 1, "seq": 1},
  "nodes": [
    {"lops": [0, 1], "lobj": [10], "heads": [1], "known": [1, 1], "sops": [], "sobj": []}
  ],
  "net": [
    {"msg": "getHead", "node": 0},
    {"msg": "putOps", "node": 0, "ops": [1]},
    {"msg": "putObjs", "node": 0, "objs": [10]},
    {"msg": "getOps", "node": 0, "ops": [1]},
    {"msg": "getObjs", "node": 0, "objs": [10]},
    {"msg": "cas", "node": 0, "expected": 0, "new": 1},
    {"msg": "head", "node": 0, "headKind": "accepted", "seq": 1, "head": 1},
    {"msg": "ops", "node": 0, "ops": [1]},
    {"msg": "objs", "node": 0, "objs": [10]},
    {"msg": "stored", "node": 0}
  ]
}
```

Every array is sorted ascending. `net` is sorted by `(msg, node, ...)`. `ops` lists every
created operation except the root.

## Running it

```sh
just oracle                          # lake build oracle
cargo nextest run -p musubi-core     # protocol_invariants and conformance
```

The oracle binary is `formal/.lake/build/bin/oracle`; `MUSUBI_ORACLE` overrides the path.
`formal/test/run_smoke.sh` replays a fixed two-node run through it.

## Evidence that the check has teeth

Deliberately broken versions of the core, each caught:

| Change | Caught by |
| --- | --- |
| Hub accepts `Cas` without checking the closure is stored | invariants (HubClosed) and conformance |
| Hub accepts `Cas` without checking ancestry | invariants and conformance |
| Hub accepts `Cas` when `head ≠ expected` | invariants and conformance |
| Node realizes an operation before its parents | invariants and conformance |
| Node realizes an operation before its objects arrive | invariants and conformance |
| Node learns a head whose `seq` equals the one it knows | conformance only: harmless, but not a model step |

`just mutants` (cargo-mutants over `hub.rs` and `node.rs`) found 7 surviving mutants out of
58; adding a lying hub, a hub that forgets unaccepted uploads, and a directed test for
re-uploading after a forgotten upload killed three. The four left are behaviorally
equivalent:

| Surviving mutant | Why it is harmless |
| --- | --- |
| `seen.insert(..) \|\| is_local(..)` to `&&` in the two ancestry walks | Revisits nodes; same result, more work. |
| Push after one `Stored` acknowledgement instead of two | A premature push fails the hub's atomic closure check and is retried. |
| Reset the upload on every non-rejection head message instead of on rejections | Polling delivers such a message, so a rejected push still re-uploads. |

## How Rust events map to model actions

| Rust core event | Model actions |
| --- | --- |
| A machine runs a `jj` command (test rule) | `userOp` |
| `NodeCore` asks the repo to merge heads | `merge` |
| `NodeCore` sends `GetHead` | `getHead` |
| `NodeCore` sends `GetOpsSince { head: k, base: b }` | `fetchOps` with `anc*(k) \ anc*(b)` |
| `NodeCore` sends `GetObjects { for_ops: S }` | `fetchObjs` with `objs(S)` |
| `NodeCore` sends `PutOps { ops: S }` | `uploadOps` with `S` |
| `NodeCore` sends `PutObjects { for_ops: S }` | `uploadObjs` with `objs(S)` |
| `NodeCore` sends `Cas { expected, new }` | `push` |
| `NodeCore` accepts a head-carrying reply | `learn`; a stale one it ignores maps to nothing |
| `NodeCore` stages an `Ops` / `Objects` reply | `recvOps` / `recvObjs` |
| `NodeCore` realizes or advances | `realize` / `advance` |
| `HubCore` handles a request | the matching `hub*` or `cas*` action |
| A node restarts | `loseKnown` (its staged files survive; `known` does not) |
| The hub restarts | `crashHub` |

`GetOpsSince` asks for a range rather than a list because a node cannot name operations it
has never seen. The test computes the set the range denotes, and the oracle checks that it
satisfies `fetchOps`'s guard: every member is in `anc*(known.head)`.
