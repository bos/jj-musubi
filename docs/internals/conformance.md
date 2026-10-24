# Conformance between the Lean model and the Rust core

The Lean model in `formal/` proves the protocol's properties. The Rust core in
`crates/musubi-core` implements the protocol. This document defines the link between them: a
trace format, an oracle built from the Lean model, and a refinement check run under Hegel.

## The claim

Every behavior of the Rust core, at the level of abstraction of the model, is a behavior of
the Lean model. The Lean safety theorems hold for every reachable model state, so they hold
for every state the Rust core reaches. A run in which the hub goes back, or the hive is made
again, is a behavior of the extended model of `formal/Musubi/Regress.lean`, and the weaker
invariant proved there holds in it.

The chain has three links:

1. **Relational model to executable model.** `formal/Musubi/Exec.lean` defines `execStep`
   on finite states. `exec_sound` proves that whenever `execStep` accepts an action other
   than `hubRegress`, the corresponding relational `Step` exists between the abstracted
   states, and `exec_rsound` that whenever it accepts any action, an `RStep` of the extended
   model does. The executable model therefore never accepts anything the proofs don't cover.
2. **Executable model to oracle.** `formal/Oracle.lean` is a thin JSON wrapper around
   `execStep`, built by `lake build oracle`. It contains no protocol logic of its own.
3. **Oracle to Rust.** The Hegel test `conformance`, in `crates/musubi-core/tests/protocol.rs`,
   runs the Rust hub and nodes, translates every step they take into model actions, and checks
   each one with the oracle. It fails on any action the oracle rejects, or any difference
   between the Rust state and the oracle's state. Hegel shrinks failures to a minimal trace.

That carries safety, not liveness. The test also runs the nodes to convergence, which
catches a node that never gets there, but not one whose steps the termination proof does
not cover, or whose pushes don't upload what the proof assumes. So it also checks the Rust
policy against the liveness proofs ([Liveness](#liveness)).

## The abstraction

The conformance test runs the real Rust core (the hub's `hub::handle` and `NodeCore`) against
test implementations of its storage traits, in `tests/support/model.rs`. These keep exactly the
model's state:

| Model | Rust test implementation |
| --- | --- |
| Universe: `next`, `par`, `objs` | the test's operation table; operation and object ids are small integers, root `0` |
| Hub `ops`, `objs`, `head`, `seq` | `FakeHub` |
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
{"op": "measure"}
{"op": "upload", "node": 0, "new": 4}
```

`measure` and `upload` read the session's state and leave it as it was
([Liveness](#liveness)).

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
| `pushAll` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.pushAll`: the merged `Push` |
| `fetchAll` | `node`, `base`, `haves` | `SyncStep.fetchAll`: the merged `Fetch` |
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
| `hubPushIdem` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushIdem` |
| `hubPushAccept` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushAccept` |
| `hubPushReject` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushReject` |
| `hubPushIncomplete` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushIncomplete` |
| `hubFetch` | `node`, `base`, `haves` | `SyncStep.hubFetch`: replies with a `head`, an `ops` and an `objs` message |
| `crashHub` | none | `SyncStep.crashHub` |
| `hubForget` | `ops`, `objs` | `SyncStep.hubForget`: the hub keeps only `ops` and `objs`, which must be among what it stores and hold `closure(head)` |
| `hubRegress` | `seq` | `RStep`'s `State.regress` (`Regress.lean`), the hub going back: `seq ≤ hub.seq`; `head := hist seq`, `seq := seq`, and nothing else changes |

`headKind` is one of `head`, `accepted`, `rejected`, `incomplete`, `notify`. The Rust hub
decides how to answer a `Push`, and the test sends whichever of `hubPushIdem`,
`hubPushAccept`, `hubPushReject`, or `hubPushIncomplete` it chose. The oracle checks that
choice's guard, so a hub that accepts a `Push` the model would reject is caught, and so is
one that rejects a `Push` the model says is incomplete. The Rust core sends only the merged
requests; the finer-grained actions remain in the model and the oracle.

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
    {"msg": "stored", "node": 0},
    {"msg": "push", "node": 0, "ops": [1], "objs": [10], "expected": 0, "new": 1},
    {"msg": "fetch", "node": 1, "base": 0, "haves": []}
  ]
}
```

Every array is sorted ascending. `net` is sorted by `(msg, node, ...)`. `ops` lists every
created operation except the root.

## Running it

```sh
cargo nextest run -p musubi-core     # protocol_invariants and conformance
```

The conformance test runs `lake build oracle` first, so that the oracle matches the model;
it does nothing when the oracle is up to date. The oracle binary is
`formal/.lake/build/bin/oracle`. Setting `MUSUBI_ORACLE` to another binary skips the build,
as CI does with the one it has just built. `formal/test/run_smoke.sh` replays a fixed
two-node run through it.

The test makes 150 cases on CI, where it runs as a job of its own, and 50 elsewhere, where
it would otherwise take most of `just test`'s time. `MUSUBI_CONFORMANCE_CASES` sets the
number; `just mutants` sets 150.

## Evidence that the check has teeth

Deliberately broken versions of the core, each caught:

| Change | Caught by |
| --- | --- |
| Hub accepts a `Push` without checking the closure is stored | invariants (HubClosed) and conformance |
| Hub accepts a `Push` without checking ancestry | invariants and conformance |
| Hub accepts a `Push` when `head ≠ expected` | invariants and conformance |
| Node realizes an operation before its parents | invariants and conformance |
| Node realizes an operation before its objects arrive | invariants and conformance |
| Node learns a head whose `seq` equals the one it knows | conformance only: harmless, but not a model step |
| Node's `Push` uploads every operation since the root, not since `known.head` | conformance only: not `upOps` |
| Node with two heads pushes one of them before merging | conformance only: the push raises the other nodes' staleness, and the measure rises; the run still converges |

`just mutants` runs cargo-mutants over `hub.rs` and `node.rs`; the property and conformance
tests should kill every mutant it makes.

## How Rust events map to model actions

| Rust core event | Model actions |
| --- | --- |
| A machine runs a `jj` command (test rule) | `userOp` |
| `NodeCore` asks the repo to merge heads | `merge` |
| `NodeCore` sends `Fetch { base, haves }`, on every poll | `fetchAll` |
| `NodeCore` sends `GetObjects { for_ops: S, haves: H, .. }` | `fetchObjs` with `objs(S) \ H` |
| `NodeCore` sends `Push { ops: S, objects: O, expected, new, .. }` | `pushAll` |
| `NodeCore` accepts a head-carrying reply | `learn`; a stale one it ignores maps to nothing |
| `NodeCore` takes in a `Fetched` reply | `learn` if its head is newer, then `recvOps` and `recvObjs` if it stages the operations; the states are compared after the last |
| `NodeCore` stages an `Objects` reply | `recvObjs` |
| `NodeCore` realizes or advances | `realize` / `advance` |
| The hub handles `Fetch` | `hubFetch` |
| The hub handles `GetObjects { for_ops: S, haves: H, .. }` | `hubGetObjs` with `objs(S) \ H` |
| The hub handles `Push` | `hubPushIdem`, `hubPushAccept`, `hubPushReject`, or `hubPushIncomplete` |
| A node restarts | `loseKnown` (its staged files survive; `known` does not) |
| A node restarts while taking in a `Fetched` reply, after staging its operations and before staging its objects (test rule) | `learn` if its head is newer, `recvOps`, then `loseKnown` |
| The hub restarts | `crashHub` |
| The hub goes back (test rule) | `hubRegress` |
| The hub forgets every operation and object outside `closure(head)` (test rule) | `hubForget` with what it keeps |
| The hive is made again, empty, as `HubDir::remake` makes one whose store is corrupt (test rule) | `hubRegress` to 0, then `hubForget` keeping only the root: `State.remake` (`exec_remake`), a run of the extended model (`remake_reachable`) |
| A reply to the node's own request that says the hub went back (`NodeCore::handle_reply`) | `loseKnown`, then `learn` if the reply's `seq` is above 0 (at 0, the restarted node already knows `(0, root)`) |

The test's objects have no structure, so the test's hub ignores `closure(base)` and leaves
out exactly what the haves name, as the model's `hubFetch` does; a node's haves there are
every object it holds.

## Liveness

`formal/Musubi/Liveness.lean` proves that once users stop, nodes following the policy
(`PStep`) converge: a lexicographic measure falls on every policy step, and some step is
enabled until every node is at the hub's head. `Regress.lean` proves the same of a hub that
has gone back, with the policy `PStepR` and the measure `rmeasure`. `Merged.lean` shows that
the merged `Push` and `Fetch` reach states that agree with policy steps on everything the
measure reads, provided a `Push` uploads `upOps` and `upObjs`: `anc*(new) \ anc*(known.head)`
and the objects of `closure(new) \ closure(known.head)`. `Merged.lean` covers only a hub that
has never gone back; after it has, that the merged requests serve the policy rests on this
test alone.

`formal/Musubi/Exec.lean` computes these on the oracle's state: `measureE`, `rmeasureE`,
`convergedE`, `upOpsL` and `upObjsL`, proved equal to `measure`, `rmeasure`, `Converged`,
`upOps` and `upObjs` of the abstracted state (`measureE_eq`, `rmeasureE_eq`,
`convergedE_iff`, `mem_upOpsL`, `mem_upObjsL`, in `ExecSound.lean`). The oracle answers with
them:

```json
{"op": "measure"}
{"ok": true, "measure": [1, 0, 0, 0, 0], "rmeasure": [1, 0, 0, 0, 0, 0], "converged": false}
{"op": "upload", "node": 0, "new": 1}
{"ok": true, "ops": [1], "objs": [10]}
```

`measure` is `(dirty nodes, Σ staleness, Σ missing ops, Σ pending advances, Σ pending
merges)`; `rmeasure` is `(nodes not good, inconsistent nodes, Σ staleness of consistent nodes,
Σ missing ops, Σ pending advances, Σ pending merges)` (formal/README.md). Both compare
lexicographically.

The conformance test checks:

- Every `Push` the policy sends (not a rogue one) carries exactly `upOps` and `upObjs`.
- `World::quiesce`, which stops users and runs every node's policy over a reliable network,
  asks for the measures after each exchange: a node's `Fetch` and the reply, or one policy
  step and the replies to what it sent. An exchange that changes the node's operations,
  heads or `known` must make the measure fall, and any other must leave it where it was or
  lower. `rmeasure` must do so in every case; `measure` only while the hub has never gone
  back, since its proof needs every state to be `Reachable`. Each node's turn starts with a
  `Fetch`, whose reply puts its `known` in the hub's current history before it realizes
  anything, as `PStepR` requires. A crash the test armed before
  quiescing, which happens when the node next stages a `Fetched` reply, is not a policy step,
  so the check starts afresh after it.
- Once the Rust side has converged, so has the oracle's state. The states already agree
  after every action, so this cross-checks `convergedE`.

Two fixed runs check what the search may reach only rarely. `regress_scenario_conformance`
drives the core through `RegressScenario.trace`, requires the actions it records to be that
trace, so that nodes A and B both merge heads `{1, 2}` (`duplicateMerge`), and then
quiesces. The trace restarts A and B before they fetch, so the test crashes them, rather
than have them restart on the hub's reply. `remade_hive_conformance` makes a hive again
under nodes that know heads it has lost, and requires each to take the hub's reply as
saying it went back (`NodeCore::handle_reply`) and fill it again. Their names end in
`conformance`, as CI selects the tests that need the oracle.

The measure falling shows that the policy's steps are ones the termination proof covers, not
that each is a `PStep`. Hub-only work, such as storing a rejected push's upload, changes
nothing the measures read.

`formal/Musubi/Presence.lean` proves which copies a hive shows when copies go away
([design.md](design.md#copies-that-go-away)). musubi computes it with `Presence::merge` and
`Presence::apply` (`crates/musubi-jj/src/presence.rs`), from each operation's parents'
presence alone. The chain has three links:

1. **The incremental rule.** What `Presence` keeps for each copy present, its latest work
   that no forget saw (`UMax`), follows from the parents' alone as the Rust computes it
   (`umax_merge`, `umax_work`, `umax_forget`), and says whether the copy is present
   (`present_iff_umax`).
2. **Relational to executable.** `formal/Musubi/PresenceExec.lean` defines the rule on a
   finite history: `presentB` and `latestB`, proved to compute `Present` and `UMax`
   (`presentB_iff`, `mem_latestB`). The oracle answers with them.
3. **Oracle to Rust.** The Hegel test `presence::conformance`, in
   `crates/musubi-jj/tests/it/presence.rs`, makes histories of up to 12 operations and 3
   copies, each operation work by one copy or a forget of some, never both, as musubi makes
   them. It computes every operation's presence with `Presence::merge` and `apply`, and
   requires it to equal the oracle's, copy by copy, latest work included.

The test checks the rule, not where it is applied: that `canonical_view` publishes exactly
the present copies' workspaces, and realizing keeps a forgotten copy's own, is for the race
catalogue (`crates/musubi-sync/tests/races/forget.rs`) to check.

### Request and reply

```json
{"op": "presence", "ops": [{"parents": [], "work": 7, "forgets": []}, {"parents": [0], "work": null, "forgets": [7]}]}
{"ok": true, "presence": [[{"copy": 7, "latest": [0]}], []]}
```

Operation `i` is the `i`th of `ops`, and its parents must come before it. `work` is the copy
the operation is work by, or `null`, and `forgets` the copies it forgets. The reply has, for
each operation, the copies present there, ascending, each with its latest work that no
forget saw. A presence request leaves the oracle's session as it was.

```sh
cargo nextest run -p musubi-jj -E 'test(/^presence::/)'
```

`MUSUBI_CONFORMANCE_CASES` sets the number of histories, 300 by default: each takes the
oracle about a millisecond. Dropping the check that a parent whose history has a copy's work
keeps it, which lets a forget's merge bring the copy back, fails within a few histories.

## Per-machine refs

`formal/Musubi/Refs.lean` proves that, for one git ref of a colocated repository, an import
changes a bookmark only if git moved the ref (`noSpuriousRevert`, `remoteNoSpuriousRevert`),
whatever musubi realizes, assuming jj's ref merge obeys three laws (`RefAlg`). Its state is a
few ref targets, so the test keeps a copy of the model in Rust rather than running an oracle.
The chain has two links:

1. **The laws.** `ref_laws::merge_ref_targets_obeys_ref_alg`, in
   `crates/musubi-jj/tests/it/ref_laws.rs`, checks `merge a b b = a`, `merge b b c = c` and
   `merge a b a = a` for jj-lib's `merge_ref_targets` on 300 triples of targets from a small
   real repository: absent, one commit (the root among them), or a conflict of three or five
   terms, any of them absent. jj resolves these before looking at commits
   (`trivial_merge`), so a failure means a jj upgrade changed that.
2. **The steps.** `refs::bookmarks_conform_to_refs_model`, in
   `crates/musubi-sync/tests/races/refs.rs`, is a Hegel state machine over two colocated
   repositories synced through an in-process hub, as in the race catalogue. It follows a
   local bookmark `x`, which git moves; a local bookmark `y`, which git doesn't; and
   `y@origin`, which `y` tracks and git and fetches move. Beside the real machine it keeps
   the model's `Machine` for each of the three, with jj's `merge_ref_targets` as the merge,
   and steps them as each real action does:

   | Real action | Model steps |
   | --- | --- |
   | `git update-ref` moves or deletes `refs/heads/x` or `refs/remotes/origin/y` | `gitMove` |
   | A `jj` command moves `x` or `y` (`jj bookmark set`, `jj bookmark delete`), or changes nothing (`jj status`) | `jjImport` of every ref; `jjExport` of every ref if that changed the view; then, if the command moves a bookmark, `set` and `jjExport` of every ref |
   | `y` moves in `origin`, and `jj git fetch` fetches it | as a `jj` command, whose change is `RStep.fetch` |
   | The other machine moves `x` or fetches `y`, and both sync, with `refs/heads/x.lock` held here or not | `LStep.advance` of `x` and `y` and `RStep.advance` of `y@origin`, then `jjExport` of every ref, except where the lock makes `x`'s update fail; nothing if there was nothing to realize |

   jj imports `x@git`, `y@git` and `y@origin` in that order, and the two refs of `y` share
   the bookmark, so an import of one is a `set` of the other. jj exports only a transaction
   with changes, which is why a `jj` command that imports nothing exports nothing, and a
   failed export waits for a command that changes something. After every action the test
   requires, for each ref, the bookmark, the remote bookmark, its `git_refs` entry and the
   git ref to be the model's, `LInv` (`RInv` for `y@origin`) to hold, and the repository to
   have one op head. It also checks that the other machine's command left its bookmarks as
   the model says, so that its own refs reverted nothing either.

What the test found, and how it is kept within the model:

- **An update to the value git already has succeeds.** jj's export counts an update of a
  ref a success if `.git` already has the new value (`move_git_ref`, `create_git_ref`,
  `delete_git_ref`), and records it, though `.git` didn't have `git_refs`'s value. That
  happens when git moves `refs/heads/x` to a commit and musubi then realizes another
  machine's move of `x` there. The model's `exportLocal` and `exportRemote` were stricter,
  and now say so; every theorem still holds.
- **Tracking.** The model merges into a bookmark as from a tracked remote bookmark. jj keeps
  a tracked remote bookmark with no target only while its bookmark exists, so once git or a
  fetch deletes `refs/remotes/origin/y` and the import deletes `y` with it, jj forgets that
  `y` tracked it. When `y@origin` comes back, jj imports it untracked and leaves `y` absent,
  where the model sets `y`. The test has both machines track `y` automatically
  (`remotes.origin.auto-track-bookmarks`), as the model assumes; without that, a deletion
  and a fetch fail it.
- **Not covered.** One op head throughout, so neither jj's merge of concurrent op heads'
  records nor musubi's (`inherited_per_machine`), which `merge_in_sync` describes but no
  step makes; no remote ref locked, since `RStep.advance` admits only exports that can
  succeed (a failed one ends as `remote_reset_without_export` says);
  no conflicted remote bookmark, so not `export_conflicted_remote_bookmarks`; and no tags.

```sh
cargo nextest run -p musubi-jj -E 'test(/^ref_laws::/)'
cargo nextest run -p musubi-sync -E 'test(/^refs::/)'
```

The state machine makes 12 cases of up to 10 actions, about 4 seconds on 32 cores, which
makes it the longest test after the protocol's conformance test, so it starts next;
`MUSUBI_CONFORMANCE_CASES` sets the number. Each case runs real `jj`, `git` and syncs, so
shrinking a failure takes minutes, and nextest lets the test run for six. Before the model's
export said what jj does, the first run of 10 cases failed: git moved `x` to a commit, then
musubi realized a move of `x` to it.
