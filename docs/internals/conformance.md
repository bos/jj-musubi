# Conformance between the Lean models and the code

The Lean models in [formal/](../../formal/README.md) prove properties of musubi's designs. This
document says how each is tied to the code that implements it. Each tie is a chain: the model's
own definitions, where they compute, or an executable form of the model, proved to agree with it,
or a copy of the model in Rust; and a Hegel property-based test ([testing.md](testing.md)) that
runs the real code and requires it to agree with the model: step by step for the protocol and the
blob receiver, and operation by operation, law by law or merge by merge for the others. The Lean
side runs as the *oracle*, a program the tests send JSON requests to.

| Model | Code | Test | Section |
| --- | --- | --- | --- |
| The sync protocol ([protocol.md](protocol.md)) | `crates/musubi-core` | `conformance`, through the oracle | [The claim](#the-claim) to [Wire format](#wire-format) |
| `Presence.lean`: which copies a hive shows | `Presence` | `presence::conformance`, through the oracle | [Presence](#presence) |
| `Refs.lean`: per-machine refs | jj's import and export, and musubi's realization | `ref_laws` (the laws the model assumes), and `refs` and `view::tests`, against a Rust copy | [Per-machine refs](#per-machine-refs) |
| `Chunks.lean`: chunked blobs | `BlobStore::receive` | `receive_follows_the_prefix_model`, through the oracle | [Chunked blobs](#chunked-blobs) |
| `Names.lean`: the names other machines' workspaces show under | `workspaces::display_names` | `workspaces::tests::names_conform`, through the oracle | [Workspace names](#workspace-names) |

## The claim

Every behavior of the Rust protocol core, at the level of abstraction of the model, is a
behavior of the Lean model. The Lean safety theorems hold for every reachable model state, so
they hold for every state the Rust core reaches. A run in which the hub goes back, or the hive
is made again, is a behavior of the extended model of `formal/Musubi/Regress.lean`, and the
weaker invariant proved there holds in it.

The chain has three links:

1. **Relational model to executable model.** The proofs are about a relational model: `Step`
   says which transitions are allowed, over states that need not be finite.
   `formal/Musubi/Exec.lean` defines `execStep` on finite states. `exec_sound` proves that
   whenever `execStep` accepts an action other than `hubRegress`, the corresponding
   relational `Step` exists between the abstracted states, and `exec_rsound` that whenever it
   accepts any action, an `RStep` of the extended model does. The executable model therefore
   never accepts anything the proofs don't cover.
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
test implementations of its storage traits, in `crates/musubi-core/tests/support/model.rs`.
These keep exactly the model's state:

| Model | Rust test implementation |
| --- | --- |
| Universe (every operation created): `next`, `par`, `objs` | the test's operation table; operation and object ids are small integers, root `0` |
| Hub `ops`, `objs`, `head`, `seq` | `FakeHub` |
| Node `lops`, `lobj`, `heads`, `known`, `sops`, `sobj` | `FakeRepo` (`lops`…`sobj`) and `NodeCore` (`known`) |
| `net`, the set of every message sent | the test's network: a set, so any message can be delivered any number of times, or never |

`lops` and `lobj` are a node's local operations and objects, and `sops` and `sobj` what it
has staged. The jj-specific parts of a real node (canonicalization, realization, bundles) are
not covered by this link; the jj example tests and the generated end-to-end tests cover them
([testing.md](testing.md)).

## How Rust events map to model actions

A "test rule" is something the test's state machine does to the system, not something the
core does.

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

The Rust hub decides how to answer a `Push`, and the test sends whichever of `hubPushIdem`,
`hubPushAccept`, `hubPushReject`, or `hubPushIncomplete` it chose. The oracle checks that
choice's guard, so a hub that accepts a `Push` the model would reject is caught, and so is
one that rejects a `Push` the model says is incomplete. The Rust core sends only the merged
requests (`Push`, `Fetch`); the finer-grained actions remain in the model and the oracle.

The test's objects have no structure, so the test's hub ignores `closure(base)` and leaves
out exactly what the haves name, as the model's `hubFetch` does; a node's haves there are
every object it holds.

## Liveness

`formal/Musubi/Liveness.lean` proves that once users stop, nodes following the policy
(`PStep`) converge: a lexicographic measure falls on every policy step, and some step is
enabled until every node is at the hub's head. `Regress.lean` proves the same of a hub that
has gone back, with the policy `PStepR` and the measure `rmeasure`. The policy there takes
single steps; the Rust core sends merged requests instead. `Merged.lean` shows that the
merged `Push` and `Fetch` reach states that agree with policy steps on everything the measure
reads, provided a `Push` uploads `upOps` and `upObjs`: `anc*(new) \ anc*(known.head)` and the
objects of `closure(new) \ closure(known.head)`, both for a hub that has never gone back,
against `PStep`, and for one that may have, against `PStepR` and `rmeasure`
(`pushAcceptR_merged`, `fetchR_merged` and the rest; `fetchR_current` for a `Fetch` by a
node that knows the hub's head and `seq` already, for which the policy has no step).

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
Σ missing ops, Σ pending advances, Σ pending merges)`. Both compare lexicographically;
[formal/README.md](../../formal/README.md) defines their terms.

The conformance test checks:

- Every `Push` the policy sends (not one the test's `rogue_push` rule makes) carries exactly
  `upOps` and `upObjs`.
- `World::quiesce`, which stops users and runs every node's policy over a reliable network,
  asks for the measures after each exchange: a node's `Fetch` and the reply, or one policy
  step and the replies to what it sent. An exchange that changes the node's operations,
  heads or `known` must make the measure fall, and any other must leave it where it was or
  lower. `rmeasure` must do so in every case; `measure` only while the hub has never gone
  back, since its proof needs every state to be `Reachable`. Each node's turn starts with a
  `Fetch`, whose reply puts its `known` in the hub's current history before it realizes
  anything, as `PStepR` requires. A crash the test armed before quiescing, which happens
  when the node next stages a `Fetched` reply, is not a policy step, so the check starts
  afresh after it.
- Once the Rust side has converged, so has the oracle's state. The states already agree
  after every action, so this cross-checks `convergedE`.

The measure falling shows that the policy's steps are ones the termination proof covers, not
that each is a `PStep`. Hub-only work, such as storing a rejected push's upload, changes
nothing the measures read.

Two fixed runs check what random cases may reach only rarely. `regress_scenario_conformance`
drives the core through `RegressScenario.trace`, requires the actions it records to be that
trace, so that nodes A and B both merge heads `{1, 2}` (`duplicateMerge`), and then
quiesces. The trace restarts A and B before they fetch, so the test crashes them, rather
than have them restart on the hub's reply. `remade_hive_conformance` makes a hive again
under nodes that know heads it has lost, and requires each to take the hub's reply as
saying it went back (`NodeCore::handle_reply`) and fill it again. Their names end in
`conformance` because CI selects the tests that need the oracle by that name.

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

"Invariants" is `protocol_invariants`, which checks the safety properties directly on the
Rust state, without the oracle. `just mutants` runs cargo-mutants over `hub.rs` and
`node.rs`; the property and conformance tests should kill every mutant it makes.

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
([Liveness](#liveness)). The oracle also answers presence requests ([Presence](#presence)).

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

`headKind` is one of `head`, `accepted`, `rejected`, `incomplete`, `notify`.

### Replies

```json
{"ok": true, "state": <state>}
{"ok": false, "error": "casAccept: closure of 7 not stored at hub (missing op 6)"}
```

A rejected action leaves the oracle's state unchanged. The error names the action and the
guard that failed, as `"<action>: <guard>"`.

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

## Presence

`formal/Musubi/Presence.lean` proves which copies a hive shows when copies go away ([design.md,
"Copies that go away"](design.md#copies-that-go-away) defines copies, their work, and forgets).
musubi computes it with `Presence::merge` and `Presence::apply`
(`crates/musubi-jj/src/presence.rs`), from each operation's parents' presence alone. The chain has
three links:

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
the present copies' workspaces, and that realizing keeps a forgotten copy's own, is for the
race catalogue (`crates/musubi-sync/tests/races/forget.rs`) to check.

The oracle's presence request and reply:

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

In a colocated repository, each view records what jj last saw in this machine's `.git` (`git_refs`
and the `git` remote, such as `x@git`), and every `jj` command imports any difference as a change
made with git. musubi keeps that record per-machine ([design.md, "Per-machine state in a
replicated view"](design.md#per-machine-state-in-a-replicated-view)). `formal/Musubi/Refs.lean`
proves that an import changes a bookmark only if git moved the ref, whatever musubi realizes,
assuming jj's ref merge obeys three laws (`RefAlg`); that musubi realizes a merge as jj merges it;
that once musubi writes a conflicted remote bookmark's expected value, every machine's import
resolves it alike, a restore of the conflict included; and that `jj undo` and `jj op restore` keep
the invariant where jj's export can write what they restore, or restore a conflicted remote
bookmark ([formal/README.md, "Per-machine refs
(`Refs.lean`)"](../../formal/README.md#per-machine-refs-refslean) lists the theorems). Its state
is a few ref targets, so the tests keep a copy of the model in Rust rather than running an oracle.
The chain has three links:

1. **The laws.** `ref_laws::merge_ref_targets_obeys_ref_alg`, in
   `crates/musubi-jj/tests/it/ref_laws.rs`, checks `merge a b b = a`, `merge b b c = c` and
   `merge a b a = a` for jj-lib's `merge_ref_targets` on 300 triples of targets from a small
   real repository: absent, one commit (the root among them), or a conflict of three or five
   terms, any of them absent. jj resolves these before looking at commits
   (`trivial_merge`), so a failure means a jj upgrade changed that.
2. **The steps.** `refs::bookmarks_conform_to_refs_model`, in
   `crates/musubi-sync/tests/races/refs.rs`, is a Hegel state machine over two colocated
   repositories synced through an in-process hub, as in the race catalogue. It follows a
   local bookmark `x`, which git moves; a local bookmark `y`, which git doesn't; `y@origin`,
   which `y` tracks and which git and fetches move; and a tag `t`, which git moves, whose slot
   is a local bookmark's (`t`, `t@git`, `refs/tags/t`). Beside the real machine it keeps the
   model's `Machine` for each of the four, its slot a `TSlot` with the remote ref's tracking
   state, with jj's `merge_ref_targets` as the merge, and steps them as each real action does:

   | Real action | Model steps |
   | --- | --- |
   | `git update-ref` moves or deletes `refs/heads/x`, `refs/tags/t` or `refs/remotes/origin/y` | `gitMove` |
   | A `jj` command moves `x`, `y` or `t` (`jj bookmark set`, `jj bookmark delete`, `jj tag set`, `jj tag delete`), or changes nothing (`jj status`) | `jjImport` of every ref; `jjExport` of every ref if that changed the view; then, if the command moves a bookmark, `set` and `jjExport` of every ref |
   | `y` moves in `origin`, and `jj git fetch` fetches it | as a `jj` command, whose change is `RStep.fetch` |
   | A `jj` command at the operation before the latest action (`--at-op`) moves `x` or `y`, and `jj status` follows | on the older operation's slots, `set` and `jjExport` of every ref (it imports nothing); then `TSlot.merge` of the head with them against the older operation's, in the order of the merge operation's parents, then as a `jj` command that changes nothing |
   | `jj undo`, or `jj op restore` to the operation before the latest action or to the one both machines last synced at | as a `jj` command that imports; then, if it restored an operation, which its description names, every ref's slot but `K` from that operation's view (`restoreLocal`, `restoreRemote`), the expected value the head's (`restoreC`), and `jjExport` of every ref |
   | The other machine moves `x` or `t` or fetches `y`, and both sync, with `refs/heads/x.lock` held here or not | `LStep.advance` of `x`, `y` and `t` and `CStep.advance` of `y@origin`, with this machine's expected value, then `jjExport` of every ref, except where the lock makes `x`'s update fail, then `exportConflicted` of `y@origin`; nothing if there was nothing to realize |
   | The other machine moves `x` or `t` or fetches `y` before it has this machine's latest operations, merges them with its own as it syncs, and this machine syncs | the other's operation realized from the slots both last synced at, and `realizeMerge` of it with the head, against those slots, in the order of the merge's parents, which is `TSlot.merge`; then the exports, as above. Two fetches that moved `y@origin` to different values merge to a conflict, whose expected value is its side; a conflict from one parent keeps that parent's |

   The mapping follows what jj does. jj imports `x@git`, `y@git` and `y@origin` in that
   order, and the two refs of `y` share the bookmark, so an import of one that sets the
   bookmark is a `set` of the other. jj exports only a transaction with changes, which is
   why a `jj` command that imports nothing exports nothing, and a failed export waits for a
   command that changes something.

   After every action the test requires, for each ref, the bookmark, the remote bookmark
   and its tracking state, its `git_refs` entry and the git ref to be the model's, `LInv`
   (`CInv` for `y@origin`) to hold, and the repository to have one op head. A restore that
   isn't `Restorable` may leave a record behind `.git` until the next import, which only it
   may (the ghost `restored`). The test also checks that the other machine's command left its
   bookmarks and tag as the model says, its import resolving a conflicted `y@origin` as this
   machine's would (`conflicted_import_agrees`), so that its own refs reverted nothing
   either, and that its `.git` has the same expected value of a conflicted `y@origin`. Beside
   it, `undo_of_an_unexportable_bookmark_conflicts_it` shows `restore_reverts` with jj alone,
   and `restore_of_a_conflicted_remote_bookmark_resolves_alike` drives the state machine
   through `restore_import_agrees`: concurrent fetches conflict `y@origin`, a fetch here
   settles it, this machine restores the conflict, and both machines' commands resolve it to
   the fetched value.

   musubi's *shortcut* for merging per-machine fields (`PerMachine::merged_trivially`) takes
   the side that changed, where at most one did; otherwise, or where a side has a tracked
   remote ref with no target, it leaves the merge to jj. In the other machine's merge, that
   machine's own side always has the per-machine fields both machines last synced at, so the
   state machine reaches the shortcut, or jj's merge where a tracked `x@git` with no target is
   involved, but never a merge where both sides changed. The merges' test, next, covers that.
3. **The merges.** `node::view::tests::merges_conform_to_refs_model`, in
   `crates/musubi-jj/src/node/view.rs`, writes three operations whose views give a bookmark
   `x`, `x@git` and its tracking state, and `git_refs`, drawn from a small real repository,
   including views musubi's realization makes and jj doesn't, and merges them with jj's own
   merge, as `merged_by_jj` does. It requires jj's merge to be the model's `TSlot.merge`,
   and the shortcut, wherever it applies, to be jj's (`shortcut_agrees`). Beside it are
   tests of the two shapes of #56, where an unguarded shortcut disagrees with jj, and of a
   criss-cross merge, where musubi must merge against the heads' closest common ancestors
   merged, as jj does, not the first of them (`firstBase_reverts`). That test's commits are
   beside each other, since jj resolves such a conflict where they are in a line.

The tests have teeth: a model whose exports refuse an update to the value git already has
fails `refs`, and merging per-machine fields against the first of several closest common
ancestors (`firstBase_reverts`) fails `criss_cross_merges_per_machine_fields_as_jj`.

What the test relies on of jj, and what it leaves out:

- **An update to the value git already has succeeds.** jj's export counts an update of a
  ref a success if `.git` already has the new value (`move_git_ref`, `create_git_ref`,
  `delete_git_ref`), and records it, though `.git` didn't have `git_refs`'s value. That
  happens when git moves `refs/heads/x` to a commit and musubi then realizes another
  machine's move of `x` there. The model's `exportLocal` and `exportRemote` do the same.
- **Tracking.** The model merges into a bookmark as from a tracked remote bookmark. jj keeps
  a tracked remote bookmark with no target only while its bookmark exists, so once git or a
  fetch deletes `refs/remotes/origin/y` and the import deletes `y` with it, jj forgets that
  `y` tracked it. When `y@origin` comes back, jj imports it untracked and leaves `y` absent,
  where the model sets `y`. The test has both machines track `y` automatically
  (`remotes.origin.auto-track-bookmarks`), as the model assumes; without that, a deletion
  and a fetch fail it.
- **Creating a bookmark tracks it.** `jj bookmark set`, creating `y`, tracks `y@origin`,
  which `remotes.origin.auto-track-bookmarks` covers, even with no target there
  (`TSlot.track`). It changes no target, so only comparing tracking states shows it.
- **Merges.** jj merges each remote ref's target and tracking state separately, and drops a
  tracked remote ref with no target when its bookmark goes, so a merge can leave `x@git`
  untracked. So the shortcut leaves to jj any merge where a side has such a ref; without
  that guard it would disagree with jj (#56, `shortcutUnguarded_keeps_absent`,
  `shortcutUnguarded_untracks`). Where the heads have several closest common ancestors,
  musubi merges the per-machine fields against those ancestors merged, as jj does. Against
  only the first, the record could be left a conflict that the export can't correct, and the
  next import would move the bookmark with no `git` command having run (`firstBase_reverts`).
- **Concurrent records.** Two heads that each import or export can merge to a record that
  doesn't match `.git`, and the next import moves the bookmark
  (`concurrent_records_revert`). jj does this too, with or without musubi, and the test
  expects it.
- **Restores.** `jj undo` and `jj op restore` restore `x@git` with the bookmark but keep
  `git_refs`. Where jj's export can't write the restored bookmark, as for the root commit or
  a conflicted local bookmark, the record stays behind `.git`, and the next import takes the difference for a
  move made with git, though jj itself made it: a bookmark at the root, moved and undone,
  becomes a conflict (`restore_reverts`, and the test
  `undo_of_an_unexportable_bookmark_conflicts_it`, which runs only jj). That is jj's
  behaviour: no musubi step takes part, and other machines, which realize only the restored
  bookmark, keep their records. `jj undo` also refuses to undo a merge operation, or a
  realization of another machine's operation, which jj attributes to that machine's
  workspace.
- **Conflicted remote bookmarks.** Two machines' fetches merge to a conflicted `y@origin`,
  whose expected value is a side, which musubi writes to `.git`; a machine's next import
  resolves it to that side, as every other machine's does. A restore that brings such a
  conflict back writes nothing, so the restoring machine's `.git` keeps the value from before
  it, which is the restore's expected value, and every other machine keeps or writes that
  instead of the side. The model takes the expected value as given with each operation; the
  test computes it from the parents' as `export_conflicted_remote_bookmarks` does, and checks
  that both machines' `.git`s have it, but makes no joins, where musubi takes the side too,
  as the history before a join is only the joining machine's.
- **Not covered.** The state machine makes no merges of more than two heads and no
  criss-cross merges. It locks no remote ref, since `CStep.advance` admits only exports that
  can succeed (a failed one ends as `remote_reset_without_export` says). The realization
  keeps a tracked absent `x@git` that jj would drop when the canonical operation deletes `x`
  (`realize_not_WF`); the test's model does the same, so the test checks the code as it is.

```sh
cargo nextest run -p musubi-jj -E 'test(/^ref_laws::/) | test(/view::tests/)'
cargo nextest run -p musubi-sync -E 'test(/^refs::/)'
```

The state machine makes 12 cases of up to 10 actions, about 4 seconds on 32 cores;
`MUSUBI_CONFORMANCE_CASES` sets the number. Each case runs real `jj`, `git` and syncs, so
shrinking a failure takes minutes; `.config/nextest.toml` gives the test time for it, and
starts it early, as the longest test after the protocol's conformance test.

## Chunked blobs

`formal/Musubi/Chunks.lean` proves that a finished blob is the one sent, despite corrupt, stale or
duplicated chunks, and that every transfer finishes once chunks are delivered. It also models
musubi's narrower receiver, `BlobStore::receive` (`crates/musubi-sync/src/blobs.rs`), which keeps
only a contiguous prefix ([protocol.md, "Chunked blobs"](protocol.md#chunked-blobs)). The chain
has two links:

1. **Refinement.** `Chunks.receive` is the prefix receiver, and `PStep` its steps: a chunk
   delivered with any claimed length, and a sweep of the partial blob or the stored one.
   For an injective hash, as `stored_identical` assumes, each is a run of the model's
   `CStep`s (`preach_abs`): a chunk taken is `recv`, one dropped no step, a hash match is
   `finishOk` then `crashRecv`, a mismatch is `crashRecv`, a chunk of a stored blob is
   `finishStored`, and the sweeps are `crashRecv` and `evict`. So `stored_identical` holds
   of it. A sender that resends from the prefix it reports finishes (`prefix_finishes`).
2. **The steps.** The Hegel test `receive_follows_the_prefix_model`, in
   `crates/musubi-sync/src/blobs.rs`, delivers up to 40 chunks at any offset up to one past the
   blob's end, some corrupt, some running past the end, some claiming a length one short or one
   long, and among them sweeps that remove the partial blob, the stored one, or both, so that
   chunks also reach a stored blob. It sends the case's steps to the oracle, which takes them from
   `initP` with `Chunks.receive` itself and the sweeps, its hash telling the blob from every other
   byte string, as an injective hash does. After each step, the reply, the partial file's bytes
   and whether the blob is stored must be the oracle's. Then a sender resends from the prefix it
   was last told, and the blob must be stored, and be the one sent, within `2 ⌈len / chunk⌉ + 1`
   resends (3 for an empty blob): `⌈len / chunk⌉` to reach the end of a corrupt prefix and start
   over, as many again from the start (the steps of `prefix_finishes`'s measure), and one that
   finds the prefix gone after a sweep.

| `BlobStore` | Model |
| --- | --- |
| `partial/<id>` | `PState.pre` |
| `complete/<id>` | `PState.store` |
| `Received::Prefix(n)`, `Received::Complete` | `some n`, `none` |
| `sweep` of the partial blob, of the stored one | `sweepPartial` (`crashRecv`), `sweepStored` (`evict`) |
| A chunk in the middle of a write when the process dies | `inject` of the part written, claiming a length past it |

A model without `evict` fails the test, since the code sweeps stored blobs.

Not covered: a blob the receiver adds itself (`insert_file`, `insert_bytes`) during a
transfer, which only the uploading machine does; a stored blob a power cut left torn, which
`get` removes; and two receives of one blob at once, which the hub and the downloader don't
make. The proof's sender resends one chunk at a time, where musubi's senders send windows of
eight. A window from the prefix the receiver last reported starts with the proof's resend,
and the rest are chunks the safety proof allows any time. A window from a stale prefix, the
receiver having started over or swept the blob, puts nothing in the receiver, and its
replies give the real prefix: the test's extra resend.

```sh
cargo nextest run -p musubi-sync -E 'test(/^blobs::/)'
```

The test makes 200 cases, a few milliseconds each, one oracle serving them all. Dropping the
check that the prefix is the length the chunk claims, so that a blob is stored when a chunk
claims one byte too few, fails it at once, as does checking the hash a byte early.

The oracle's chunks request and reply, for a blob of three bytes:

```json
{"op": "chunks", "blob": [1, 2, 3], "steps": [{"off": 0, "data": [1, 2], "total": 3}, {"sweep": {"partial": true, "stored": false}}, {"off": 0, "data": [1, 2, 3], "total": 3}]}
{"ok": true, "steps": [{"received": 2, "pre": [1, 2], "stored": false}, {"pre": [], "stored": false}, {"received": null, "pre": [], "stored": true}]}
```

A step is a chunk, `off` and `data`, delivered claiming the blob is `total` bytes long, or a
sweep of the partial blob, the stored one, or both. The reply has, for each step, the
receiver's reply to a chunk (`n` for `Received::Prefix(n)`, `null` for `Received::Complete`),
the prefix it has, and whether it has stored the blob. A chunks request leaves the oracle's
session as it was.

## Copies

`formal/Musubi/Copies.lean` proves, for one machine, that musubi syncs only the copy of a key,
follows a moved copy, and makes keys only by joining ([copies.md](copies.md)). What it decides
from are pure functions, as in `crates/musubi/src/copy.rs`: which repository is the copy of a
key (`standing`), given the repository's record, key and config-id and this machine's entry
for its key; whether that holds up against what is at the entry's path (`refine`), given
whether the entry's path holds the copy the entry names and whether it is this repository's
directory; and whether a repository is the copy an entry names (`check`). The chain has two
links:

1. **The rules.** The model's machine moves, copies, deletes and replaces repositories, runs
   jj's config-id rule (`handle_metadata_path`) in them, joins them, and syncs and follows
   entries. It decides with `standing` then `refine`, as `copy::standing_of` does, and with
   `check`. With no aliases, another directory is another path. In every reachable state:
   - every push is of a repository joined to the hive pushed to, under its own key
     (`right_hive`);
   - while an entry's path holds its copy, no other repository with the key is the copy,
     whatever jj decides when it runs there (`duplicates_refused`);
   - a duplicate of a copy that left, or whose hive was removed, can't join, since its
     config-id isn't its record's (`join_refuses_duplicate`);
   - no step but `join` makes a key, though a repository the user puts in place may bring
     its own (`only_join_makes_keys`);
   - if an entry's path holds its copy, and jj last saw the copy's config-id there, then
     once the copy is moved and jj has run in it, the daemon follows it (`moves_followed`);
   - syncing and following a move change no repository and nothing jj records
     (`daemon_writes_nothing`).

   Two runs show what jj's rule leaves to musubi. In both, jj ran in the copy at another
   path, and the copy came back before jj ran in it again. In `duplicate_taken_for_moved`, jj
   then takes a duplicate for the copy moved: `standing` alone says it is the copy, and
   `refine` makes it a duplicate. In `move_taken_for_duplicate`, the other path is reused, jj
   takes the copy moved for a duplicate, and the daemon can't follow it, as copies.md says
   under "Out of scope".
2. **The decisions.** The test `copy::conformance::decisions_conformance`, in
   `crates/musubi/src/copy/conformance.rs`, asks the oracle for `standing`, `refine` and
   `check` of every combination of: no record, or one with either of two hives, either of
   two config-ids, and any state; no key, or either of two; no config-id, or either of two;
   no entry, or one with either of two keys, hives and config-ids; and both answers to each
   of `refine`'s two questions. That is 4212 cases, in one request. The test makes the ids
   uuids and strings, and requires `copy::standing`, `copy::refine` and `copy::check` to give
   the oracle's answer for each.

The test checks the decisions, not where musubi makes them: that `musubi join` and
`musubi list` have jj resolve the config-id first and look at the entry's path, and that the
daemon checks before each sync, is for the CLI tests (`crates/musubi/tests/cli.rs`) to check.

### Request and reply

```json
{"op": "copies", "cases": [{"repo": {"key": 0, "cid": 0, "record": {"hive": 0, "cid": 0, "state": "joined"}}, "entry": {"key": 0, "hive": 0, "cid": 0}, "elsewhereHolds": true, "sameDirectory": false}, {"repo": {"key": null, "cid": null, "record": null}, "entry": null}]}
{"ok": true, "copies": [{"standing": "copy", "refined": "duplicate", "check": true}, {"standing": "outside", "refined": "outside"}]}
```

A case is a repository, with its key, config-id (`cid`) and record, each `null` if it has
none; this machine's entry for its key, or `null`; and `refine`'s two questions, whether the
entry's path holds the copy the entry names (`elsewhereHolds`) and whether it is the
repository's directory (`sameDirectory`), each false if not given. A record's `state` is
`joined`, `left` or `removed`. The reply has, for each case, the repository's standing
(`outside`, `removed`, `copy`, `broken`, `duplicate` or `unknown`), that standing refined,
and, if the case has an entry, whether the repository passes its check. A copies request
leaves the oracle's session as it was.

```sh
cargo nextest run -p jj-musubi -E 'test(/^copy::conformance::/)'
```

The test takes under a second. Dropping, from the oracle's check, the comparison of the
record's config-id with the entry's fails 32 of the 4212 cases, and ignoring `sameDirectory`
in its `refine` fails 8.

## Workspace names

`formal/Musubi/Names.lean` proves that the names under which a machine shows a view's
workspaces are distinct: its own under their own names, and each other machine's as
`<prefix>/<workspace>` ([design.md, "Which workspaces are this machine's
own"](design.md#which-workspaces-are-this-machines-own)). Canonicalizing reads the names back as
machine-qualified keys, so two workspaces shown alike would be taken for one. The chain has two
links:

1. **The rule.** `assign` gives each machine, in order, the first of its candidate prefixes
   that is free: its name, if no other machine has it, then `name-1a2b`, `name-1a2b3c4d`, and
   that with ever more dashes. A prefix is free if no machine before took it and no name of
   this machine's own starts with it and `/`. One is always free (`choose_free`), and so the
   names are injective, whatever the machines and the names of this machine's own
   (`localName_injective`).
2. **The code.** `workspaces::display_names` makes the same choices. The Hegel test
   `workspaces::tests::names_conform`, in `crates/musubi-jj/src/workspaces.rs`, draws up to
   four machines and three names of this machine's own from names, suffixes and names of its
   own chosen to clash, and requires each machine's prefix to be the one the oracle's
   `assign` gives it. Letting a machine take a prefix an earlier one took, or one that starts
   a name of this machine's own, fails it. `longer_names_where_shorter_clash` pins the cases
   the rule before this one named alike, which `Names.lean` checks with `#guard`.

The test checks the rule, not where musubi applies it: that `local_names` and `canonical_view`
pass it every machine the history has known and this machine's own names is for the race
catalogue (`crates/musubi-sync/tests/races/forget.rs`) to check.

The oracle's names request and reply:

```json
{"op": "names", "machines": [{"name": "mac", "suffix": "aaaa1111"}, {"name": "mac", "suffix": "aaaa2222"}], "own": ["mac-aaaa2222/x"]}
{"ok": true, "prefixes": ["mac-aaaa", "mac-aaaa2222-"]}
```

The machines go in the order `display_names` takes them, their keys' order, each a key's name
and suffix, and `own` holds the names of this machine's own. The reply has each machine's
prefix, in the same order. A names request leaves the oracle's session as it was.
