# Working on Lean proofs

[The formal guide](../../formal/README.md) lists the models and their assumptions.
[Conformance](conformance.md) describes their implementation checks. The
[testing philosophy](testing-philosophy.md) and [working agreement](../../AGENTS.md) cover
validation and review.

## Check source assumptions before building on them

Embedding a policy step into an asynchronous safety model does not prove that an asynchronous
execution eventually makes policy progress. Check the simulation direction and the theorem's
actual dependency path; compiling a component does not mean a result uses it. Expand bundled
premises and distinguish derived facts, native contracts and environment or fairness
assumptions. Watch for a premise that already assumes the intended progress; `#print axioms`
does not expose that mistake.

Read entire native calls before assigning them model steps, including cleanup, callbacks and
completed effects retained after an error. An observation after a call returns cannot establish
its internal publication order.
[Conformance](conformance.md#a-repository-advance-that-also-merges) records the native advance
boundary. Challenge source contracts with small native traces before extending dependent proofs.

## Preserve the ordering the implementation observes

Parent order affects both hashed IDs and expected-value history walks. Ref payloads and saved
expectations must come from the operations selected by the graph. Correct cached answers may
differ in availability across copies; derive agreement with the uncached walk
([#76](https://github.com/bos/jj-musubi/issues/76),
[#77](https://github.com/bos/jj-musubi/issues/77)).

## Account for progress and test the observation boundary

Count target transitions reached as well as generated cases. If ordinary runs miss the boundary,
seed a reachable hard prefix and continue the ordinary generator from there.

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
lake build +Musubi.OpHeadsRace
```

Imports use built artifacts. Build changed dependencies before inspecting declarations:

```sh
lake env lean --stdin <<'LEAN'
import Musubi.Liveness
#check Musubi.State.pstep_reachable
#print axioms Musubi.State.pstep_reachable
LEAN
```

Add new main results to `Musubi/Axioms.lean` and the build's imports. The axiom list and the
expanded premises answer different questions: inspect the premises of a theorem as well as its
axioms.

For contraction proofs, simplify Boolean branches and list constructors before rewriting.
`Contract.flatMap_congr_mem` needs agreement only on list members. Generalize changing
accumulators in induction and expose `ParLt`'s decrease before using `omega` on parent bounds.

`lake build oracle` omits unrelated proofs and audit entries; `lake build` checks the full
formal package. Before parallel consumers, build the oracle once and supply its absolute path
through `MUSUBI_ORACLE`, as CI does. The Rust helper's `OnceLock` is per process. Rebuild after
Lean changes before reusing an explicitly supplied binary.

For parallel proof work, assign an integration owner for `ExecJson.lean`, `Axioms.lean` and
aggregate imports to avoid conflicting handoffs.
