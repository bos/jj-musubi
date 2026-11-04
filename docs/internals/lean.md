# Working on Lean proofs

[The formal guide](../../formal/README.md) lists the models and their assumptions.
[Conformance](conformance.md) describes their implementation checks. The
[testing philosophy](testing-philosophy.md) and [working agreement](../../AGENTS.md) cover
validation and review. The pitfalls below arose in the recent proof work.

## Check source assumptions before building on them

Embedding a policy step into an asynchronous safety model does not prove that an asynchronous
execution eventually makes policy progress. Check the simulation direction and the assembled
theorem's actual dependency path; compiling a component does not mean the assembly uses it.
Expand bundled premises and distinguish derived facts, native contracts and environment or
fairness assumptions. Watch for a premise that already assumes the intended progress;
`#print axioms` does not expose that mistake.

Read entire native calls before assigning them model steps. `advance` can merge heads and
replace an abandoned working copy, writing above a singleton target. Prelude and idle work
can write too. Errors can retain completed effects, and a fetch can update knowledge before
its object call completes. A completed-batch observation must account for those callbacks.
Use a small native trace to challenge these contracts before extending dependent proofs.

In [#78](https://github.com/bos/jj-musubi/issues/78), `autoWritesStop` remains an assumption
covering inline cleanup, prelude and idle writes. Their termination from finite user and
configuration changes is unproved. Resolve that scope before building a proof around it.

## Preserve the identities and ordering the implementation observes

Original operations, raw canonical bodies, local jj operations and model labels are distinct.
A content-addressed write may create a body, make an existing body local, or reuse one already
local. Different physical operations can have one canonical form. Count label allocation and
raw body creation separately; include every hash-visible field, such as presence attributes.

[Contraction identity, #73](https://github.com/bos/jj-musubi/issues/73), exposed a hidden
injectivity assumption: collision resistance does not make original-operation content
injective. Test equal nonparent fields and timestamps under different histories; unique
fixture descriptions concealed the counterexample.
Check identity correspondence through cache loss, garbage collection, restart and commands
still running during sync.

Parent order affects both hashed IDs and expected-value history walks. `Contract.Eqv`
preserves first-occurrence order after deduplication with any initial accumulator. Ref payloads
and saved expectations must come from the operations selected by the graph. Correct cached
answers may differ in availability across copies; derive agreement with the uncached walk
([#76](https://github.com/bos/jj-musubi/issues/76),
[#77](https://github.com/bos/jj-musubi/issues/77)).

Equal applied records do not equate complete normalizers when one node has extra pending
drops. A cached identity fallback does not witness a complete normal body. Check survival of
the actual sent head and its complete ancestry, including the head itself.

## Account for progress and test the observation boundary

Ordered records can differ while their dropped-original unions agree. `RecordLiveness.lean`
adds reconciliation debt after set-based progress; otherwise the model can declare convergence
while the executable push guard stays closed
([#75](https://github.com/bos/jj-musubi/issues/75)).

Bound old effects, allowing new messages and orphaned requests to remain. Reply slots and
id-less notifications have different lifetimes. Classify a packet by its send-time facts: its
sender can acquire new drops, and the hub can handle it after its reply slot is retired.
`SysFreshCuts.lean` and `NotificationControl.lean` give the credit arguments. Compose facts
about the same actual run, packet and handling event throughout the proof.

A graph read after a call returns includes its cleanup. It cannot establish internal
publication order; that needs its own observation or code/lock argument
([#74](https://github.com/bos/jj-musubi/issues/74)). Count target transitions reached as well
as generated cases. If ordinary runs miss the boundary, seed a reachable hard prefix and
continue the ordinary generator from there.

For jj-owned behavior, use actual jj observations. `RefsExec.lean` takes a table of jj merge
results because symbolic merging can miss resolution by commit ancestry. Require every
consulted entry. Oracle smoke output is compared line by line, including JSON key order.

## Lean and build traps

This package uses core Lean without Mathlib. Search the library selected by
`formal/lean-toolchain` before guessing APIs; another installed version can have different
lemmas. Run these commands from `formal/`:

```sh
lake env lean --version
lake env lean --print-prefix
lake build +Musubi.Contract
lake build +Musubi.FineAssembly
```

Imports use built artifacts. Build changed dependencies before inspecting declarations:

```sh
lake env lean --stdin <<'LEAN'
import Musubi.FineAssembly
#check Musubi.FineAssembly.hive_converges_observed
#print Musubi.SysAcceptance.HiveContracts
#print Musubi.FineAssembly.FineSource
#print axioms Musubi.FineAssembly.hive_converges_observed
LEAN
```

Add new main results to `Musubi/Axioms.lean` and the build's imports. The axiom list and the
expanded premises answer different questions.

For contraction proofs, simplify Boolean branches and list constructors before rewriting.
`Contract.flatMap_congr_mem` needs agreement only on list members. Generalize changing
accumulators in induction and expose `ParLt`'s decrease before using `omega` on parent bounds.

`lake build oracle` omits unrelated proofs and audit entries; `lake build` checks the full
formal package. Before parallel consumers, build the oracle once and supply its absolute path
through `MUSUBI_ORACLE`, as CI does. The Rust helper's `OnceLock` is per process. Rebuild after
Lean changes before reusing an explicitly supplied binary.

Check that edits succeeded before trusting a build: one failed path lookup was followed by a
successful build of the unchanged file. For parallel proof work, assign an integration owner
for `ExecJson.lean`, `Axioms.lean` and aggregate imports to avoid conflicting handoffs.
