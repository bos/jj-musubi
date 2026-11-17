# Reading the property tests

The Hegel suite checks small algebraic laws, implementation/model agreement, and generated
histories of real repositories. Start with the law being checked, then follow its generated
inputs and its independent answer. [Testing](testing.md) owns how to run each layer;
[conformance](conformance.md) owns the correspondence with Lean and its limits.

## Small laws

[Ref algebra](../../crates/musubi-jj/tests/it/ref_laws.rs) is the shortest example: generate
three targets, apply jj's merge, and check the three equations the model assumes. The small
pool of commit symbols makes equalities and conflicts common.

[Presence](../../crates/musubi-jj/tests/it/presence.rs) separates a generated history,
`computed` by the implementation, from `modelled` by the oracle. The same history also checks
that contraction preserves presence.

[Contraction](../../crates/musubi-jj/src/canonical/contract.rs) checks several laws on one
generated history and one store. `ContractionCase` describes the graph and the two drop sets;
`ContractedGraph` computes the expected parent expansion and structural identities directly
from that graph. It does not traverse rewritten store operations to obtain its answer. The
test composes image lists and compares sequential dropping with union for every operation,
including the root and dropped operations. It also checks lookup order, survivor identity,
parent expansion and presence. Sharing a case exercises the laws together without repeating
the fixture.

## Protocol histories

[The protocol machine](../../crates/musubi-core/tests/protocol.rs) chooses actions; its
[world](../../crates/musubi-core/tests/support/world.rs) executes the real cores and translates
their effects into model steps. `Environment` names the additional actions allowed in a run:

| Environment | Additional behavior | Independent check |
|---|---|---|
| `Protocol` | Network scheduling and crashes | Rust safety; optionally Lean steps |
| `FalseReplies` | Dishonest well-formed replies | Weaker safety assumptions; honest recovery |
| `StorageFailures` | Storage boundary faults | Lean where representable; Rust throughout |

[The safety laws](../../crates/musubi-core/tests/support/world/properties.rs) compose node
safety, hub monotonicity and drop consistency. Their exceptions sit beside the assumptions
that justify them. `quiesce` then makes delivery reliable and checks eventual convergence and
retention; with an oracle it also checks the model's decreasing progress measures. A targeted
prefix can feed a rare state into the same generated walk and the same final checks.

[Refs conformance](../../crates/musubi-sync/tests/races/refs.rs) composes a `Realization`
([scenario.rs](../../crates/musubi-sync/tests/races/refs/scenario.rs)) from the peer's
`RefCommand`, its order relative to local work, physical export access, and an optional local
command. The same scenarios serve the [regression
examples](../../crates/musubi-sync/tests/races/refs/examples.rs) and the generated rules.
Each phase captures its history, checks the peer's native command, then compares realization
with the model; a bookmark move cannot carry an unrelated fetch target. [The
model](../../crates/musubi-sync/tests/races/refs/model.rs) holds `SharedRefs`, which names the
shared fields being compared, and `judge`, which only compares the real repository with the
model; the state machine's `check` moves the snapshots on separately, and `ModelAtOperation`
pairs each model snapshot with its native operation. The one example that is not a scenario,
[taking another machine's abandon](../../crates/musubi-sync/tests/races/refs/abandon.rs),
drives the sync by hand, which `Realization` cannot express.

## Real repository histories

The end-to-end search has three boundaries:

1. [Rules](../../crates/musubi-sync/tests/e2e_search/machine.rs) draw actions from what a machine
   can do. Candidate selection and fault budgets belong here.
2. [The world](../../crates/musubi-sync/tests/e2e_search/world.rs) runs those actions and captures
   their source evidence in `NativeEvidence`, separate from the live actors. Native command
   inputs must be recorded before a later realization or abandonment can rewrite them. A
   canonical marker alone is not proof of native authorship.
3. [Checks](../../crates/musubi-sync/tests/e2e_search/checks.rs) judge the resulting history.
   [Imports](../../crates/musubi-sync/tests/e2e_search/imports.rs) checks each machine's private
   Git state; [the reference](../../crates/musubi-sync/tests/e2e_search/reference.rs) rebuilds
   the shared history with jj's own merges.

The reference separates structural comparison, native replay, rewrite evidence and workspace
certification into child modules. Its adjudication classifies each operation's source, checks
that source before replay, and names which independent native witness explains a differing
merge. The tests beside its public checks deliberately remove or forge evidence: they protect
the oracle itself from accepting an unsupported explanation.

[Coverage](../../crates/musubi-sync/tests/e2e_search/coverage.rs) separates rule activity from
race witnesses. Catalogue rule combinations are approximate exploration guidance: they do not
establish that the participants changed the same object concurrently. Currently, native
detectors cover descriptions of the same commit on two copies and independent squashes into
the same destination. Each requires distinct copy identities, exact common input ids and
captured native predecessor records showing actual rewrites. Only adjacent qualifying rules
can pair; synchronization, unrelated commands and history-rewrite rules break the interval.
Local preparation observations remain allowed: they may snapshot or reconcile, but cannot
receive the peer's newly written operation. A squash pair also needs disjoint, nonempty source
sets.

Witnesses count only after the complete case, including final convergence checks, succeeds.
Reports distinguish witnessed, not witnessed, not instrumented and excluded rows. A missing
detector is not a zero count. Each report belongs to one test execution and includes the
concrete native operations behind its first witness; old report files never contribute.
Under `target/tmp/e2e_search/`, `coverage-v2-<test>.txt` is the readable report and
`counts-v2-<test>.json` records the same evidence and statuses. Use the files emitted by the
current test command. `coverage.txt` contains a retirement notice for the former cross-test
total. The coverage negative controls check single actions, same-copy and different-object
pairs, causal barriers, absent native effects, failed cases, report isolation and stale files;
the native bridge test also exercises both detectors through real jj commands.

Private workspace replay pairs each canonical parent with its certificate in `CertifiedParent`.
It qualifies a candidate's source mappings and certificates, then projects every base and both
ordered parents into `ProjectedMergeInputs`. Replay consumes that value, keeping bases separate
from parents. The maker's result is read only after the native merge, so it cannot determine the
replay's inputs.

Native jj commands cross one recorded-command boundary: observation, workspace command or
command at an older operation. Each variant owns its capture and completion order, including
refusals; source recording sits between those phases. Rules select inputs and call complete
actors, including Git branch moves and deletes, which capture their import frontiers and ledger
effects themselves.

Preserving a publication's independently observed Git frontier requires an explicit
`GitRecordAuthorization`: either a root transition, or private workspaces whose names the
published carrier retains. The latter checks the carrier's view before accepting it.

[Operation identities](../../crates/musubi-sync/tests/e2e_search/identity.rs) distinguish the
metadata relations used by evidence joins:

| Key | What equality means |
|---|---|
| `SourceKey` | Same millisecond times and first description line |
| `HistoryKey` | Same normalized history metadata across copies |
| `SourceHeader` | Same normalized source key, hostname and username |
| `ImportIdentity` | Same full native import metadata despite later reparenting |

These correlate candidates; exact native/canonical ids and source-body collision checks remain
necessary. Native operation classification has one owner beside those key definitions.

[Workspace certificates](../../crates/musubi-sync/tests/e2e_search/reference/workspaces.rs)
keep each workspace's name authentication, binding, birth witness and presence together. Their
transition table states which facts each action changes or retains. Authenticating a name does
not authenticate its current binding. The derivation explicitly orders inheritance, observed
bindings, trim repair, command or merge evidence, membership reconciliation and authentication.
A rejected native witness carries its missing prerequisite into the final mismatch explanation,
so an absent source can be distinguished from a replay whose complete result differed.

A convergence checkpoint has an explicit order:

1. `settle` syncs, snapshots pending edits and loads stale workspaces, recording what those
   actors do. Its final fixture comparison can sync too.
2. `check_converged_history` checks heads, fresh translation, retained operations, tags,
   workspaces and the history's divergence/conflicts against the reference.
3. `exercise_workspace_visibility` makes new work in every workspace and checks what the other
   machines show. This phase intentionally changes the repositories.
4. Only then does the ledger reset for the next generated prefix.

Keep expected answers independent of the effects they judge. When extending an actor, follow
its existing evidence capture and recording path; when extending a check, state which captured
input justifies its expected answer. Read the existing negative controls before allowing a new
exception. [Testing philosophy](testing-philosophy.md) owns the required evidence for a change,
and [efficient tests](efficient-tests.md#make-generated-cases-replay-exactly) owns deterministic
replay.
