# Bounded verification of storage retries

`storage_proofs::push_storage_retries` in
[`musubi-core`](../../crates/musubi-core/src/storage_proofs.rs) checks the production
`hub::Push::answer` against a small nondeterministic `HubStorage`. It supplements the Lean
models and their conformance tests, the storage-call fault tests, fuzzing and the end-to-end
search. It does not establish unbounded implementation refinement or asynchronous liveness.

## What this adds

The four other [Kani proofs](testing.md#kani-proofs) check arithmetic helpers: blob chunk
overlap, envelope capacity, download completion, and transfer windows. Their inputs range
over machine integers, but they exercise no storage failures or retries.

The Lean protocol models prove safety over arbitrary reachable histories. Conformance runs
the production core with generated histories against their executable oracle. The
[storage-error tests](conformance.md#storage-errors) target errors and their permitted effects
through those same storage traits. The bounded harness exhausts the choices below through
the Rust handler itself,
including independently failing calls on consecutive attempts and content retained by a
failed import. It needs no oracle process or real repositories.

After every attempt it checks:

- The hub's head is closed and descends from its previous head.
- Its sequence advances exactly once for the only possible new head, even across retries.
- An error leaves the logical `(seq, head)` unchanged; imported content may remain.
- A successful reply reports the actual head, sequence and records. An acceptance is about
  the requested new head. Only a newly accepted head is published, with matching contents.
- Once failures stop and the upload is complete, a matching push of a descendant is accepted;
  a stale expectation or sibling is rejected. Replaying that upload changes no head or
  sequence.

Five `kani::cover!` checks also require reachable paths for retained objects after an error,
an incomplete upload, a rejection, a new acceptance and an idempotent retry.

These are bounded safety and retry-completion checks, not a fairness claim about whether a
driver sends that retry. [Asynchronous liveness](conformance.md#liveness) has separate
source contracts and environmental assumptions.

## Bounds and adapter assumptions

The graph has exactly three operations: root `0`, operation `1` with parent `0`, and
operation `2` with parent either `0` or `1`. Each nonroot operation requires one distinct
object. Initially the closed head is `1`, sequence `1`; only its operation and object are
stored. There are no other writers during or between calls. Every push is from one fixed
machine, `n`, whose empty-record report is remembered even when the push fails.

Every push announces operations `[1, 2]` and carries both operations in its attachment, with
standalone views and no view deltas that could lack a base. The requested new head is `2`;
the expected head is either `0` (stale) or `1`. The first two
attempts resend the same upload, whose object attachment is any subset of the two objects.
Each fallible call may independently fail on either attempt. The third sends all objects with
failures disabled; the fourth replays it. There are exactly four handler calls, no crashes,
and no other requests. `#[kani::unwind(4)]` bounds loop expansion, with Kani's unwinding
assertions enabled: an insufficient bound is a failure, not a passing truncated search.

The adapter's choices follow these contracts, traced through
[`HubAdapter`](../../crates/musubi-sync/src/hub.rs),
[`HubStore`](../../crates/musubi-hub/src/store.rs),
[`CanonicalStore`](../../crates/musubi-jj/src/canonical.rs) and
[`SimpleStore`](../../crates/musubi-jj/src/objects/simple.rs):

| Boundary | Result and effect |
| --- | --- |
| `store_ops`, `store_objects` | On success, retain everything offered. On error, retain any subset offered, including none or all. Never remove existing content. |
| `is_closed`, `descends` | Return the graph's exact answer or an error; change no state. |
| `set_head` | Error with the logical head unchanged, or success setting the requested pair. Caller obligations (closed descendant, next sequence) are assertions, never assumptions. |
| `head`, `records`, `pruned`, `reported`, `is_dropped` | Exact, infallible observations. Records are always empty, and nothing is dropped or pruned. |
| `report` | Infallibly remembers the fixed machine's empty-record report, including on a failed push. |
| Fetch-only methods and `prune` | Unreachable assertions: this harness exercises only pushes. |

`HubAdapter::store_ops` imports operations before checking the announced ids; the harness
always supplies those ids. `CanonicalStore::import_operations` can store earlier batches
before a later batch fails. Simple-backend object import can store earlier objects before a
later error. The subset effects abstract that retained content, allowing any upload order;
they do not claim each backend has every subset outcome. An object upload may succeed while
still missing objects needed by the new head: the hub checks closure separately.

`HubAdapter::store_ops` can also succeed without every operation when a view delta lacks its
base. The harness excludes that input by requiring standalone views: its successful operation
import means everything offered was stored. This is a restriction on the operation attachment,
not an assumption that filters failing executions. Missing-delta handling stays with the
existing bundle and fault tests.

For an ordinary push, `HubStore::set_head` appends the head log and computes accepted ids
before changing its in-memory history. Errors there can leave log/index effects with the
logical head unchanged. The harness abstracts those effects away, retries against the same
logical adapter, and proves nothing about reopening it, torn files, power loss, or recovery.
It adds no hub durability requirement. No supersedes, record adoption or pruning are included;
the empty digest represents the unchanged empty-record state, and only equality is observed.

The graph, storage contents and closure/ancestry queries are the harness's trusted finite
abstraction. The production adapters, bundle validation, content hashes, real object graphs,
sequence exhaustion, other requests and longer histories are not verified here. Their
existing tests and proofs remain necessary.

## Mutation evidence and cost

On 2026-11-02, Kani 0.68.0 with CBMC 6.11.0 verified the unmodified harness, with all five
cover properties satisfied. Each of these independent changes to the production handler
made verification fail:

| Mutation in `hub::Push::answer` | Failing assertion |
| --- | --- |
| Replace the incomplete-closure guard with `if false` | `self.closed(*head)` at the `set_head` boundary: an incomplete upload can reach acceptance. |
| Replace `if *self.new == head` with `if false` | Accepted reply iff the hub holds the requested head: a retry of an accepted push is wrongly rejected. |
| Remove `storage.set_head(seq + 1, self.new, self.dropped)?` | The reply's `(seq, head)` equals storage's: acceptance reports a head it never installed. |
| Replace the same `set_head(...)?` with `let _ = set_head(...)` | The reply's `(seq, head)` equals storage's: a failed head write is wrongly reported as accepted. |

Each mutant changed only the stated production expression or statement in an isolated
scratch copy. The unmodified harness passed, all five cover properties were reached, and each
mutant failed its intended assertion. This checks sensitivity to the core, rather than only
to a broken assertion in the harness.

The success-only `FakeHub` cannot expose an ignored head-write error. Both this bounded
adapter and the [fallible conformance wrappers](conformance.md#storage-errors) can. All five
cover properties still passed for that mutant, so its failure comes from the safety assertion
rather than lost reachability.

On macOS arm64, that run took about 10 seconds in the solver and 18 seconds including
compilation; a warm full `just kani` took about 26 seconds under the 4096 MiB memory cap.
A first workspace-wide run also compiles the other crates' dependencies. Larger graphs or
retry depths need new cost measurements before expanding this opt-in check.

## Running and maintaining it

Install Kani as [testing.md](testing.md#kani-proofs) describes, then run from the repository
root:

```sh
just kani --harness push_storage_retries
just kani
```

Use the `just` recipe, which enforces `KANI_MEMORY_MB` (4096 by default), rather than invoking
Kani directly. The proof is opt-in; `just check` does not compile `cfg(kani)` modules.
Changes to this proof or the push handler it covers need `just kani` as well as the relevant
ordinary checks. Keep unwinding assertions enabled.
