# Native lifecycle construction evidence

This is the owned #150 construction slice on top of the reviewed executable model
`d8baf00529952934b2b11123da888076bdf1c282`. It is not a native refinement or a completed
conformance increment. The shared oracle interfaces, Rust consumer and aggregate proof audit
remain with the coordinator. The accepted domain is
[#149 v2](https://github.com/bos/jj-musubi/issues/149#issuecomment-6872761199), including its
[raw U/I definitions](https://github.com/bos/jj-musubi/issues/149#issuecomment-6872763083).

## Computation and observations

`constructReceipt` takes raw records, saved responsibility and the captured native/canonical
graphs. It computes effective drops, ordered contraction images, hash-visible presence stamps,
native rewrites and the prepared base. Observed `Receipt.locals` is absent from this input.
`receiptInputMatches` then compares the observed sparse map extensionally, treating a missing
entry as the unchanged old operation, rejecting extra keys and missing changed mappings.
The raw observed map remains available for the prepared-source role after this comparison.
The current construction requires unique published templates; aliasful native successes remain
outside this constructor's U domain rather than becoming claimed runtime refusals.

`constructRender` computes a parents-first suffix, source choices, qualified ownership,
reserved names, kept common-base bindings, workspace names, private attributes, author
workspace, restore/revert source, inherited Git fields and the complete native body shape.
Only then does it look up the content-addressed result. Existing target Git fields are reused
only for exactly equal ordered physical parents. The prototype `receive`, `prepare`, `write`
and `helperHeads` actions remain for earlier observation examples and are excluded by
`constructedAction` from the proposed constructed-preparation theorem.

`EncodingTable` contains independent complete-body encoding observations. Lookup requires one
exact shape excluding only its hash; it neither mints a numeric identity nor accepts a
correct-render predicate. `FieldFact` keys multi-parent native inheritance by repository/index
context, full native graph and ordered physical parents. `HelperFact` binds the same raw
context, native graph, physical frontier and timestamp/id input order to explicit native writes
and the observed resulting frontier. A reference string is not authentication of any table.

`ownHelper` installs real helper-created native bodies and updates the native frontier without
misclassifying an adapter-owned call as an E1/E2 outsider. It checks that old native ancestry
remains reachable. New native bodies receive no invented canonical identity. Their later
canonical projection remains a separate obligation. Physical effects are tagged as a selected
ref or a complete snapshot. An absent physical observation makes the projection unknown; it
does not establish that Git remained unchanged.

Planning, each canonical/native write, and commit are separate actions. Named writes check
saved custody before the write. A restart retains completed immutable writes and custody while
discarding the plans. Body creation and model-label allocation remain separate counters.

## Exact native handoff map

The reviewed #151 slice is integrated at
`194c9d113fe040f84a239703802d202c37000a7b`, in
`crates/musubi-jj/src/node/realize/native_contract_tests.rs`. Its
[handoff](https://github.com/bos/jj-musubi/issues/151#issuecomment-6874082815) and
[custody disposition](https://github.com/bos/jj-musubi/issues/151#issuecomment-6874189861)
describe its scope. These fixtures support the following individual obligations; they do not
authenticate arbitrary `NativeFacts` entries or prove their universality.

- Raw observation: `complete_receipt_and_body_observation_is_pure` captures full readable
  bodies/views, receipt, expected observations and musubi bytes; checks repository bytes,
  clock and next actor RNG draw.
- Qualified ownership: `second_owned_name_survives_complete_native_capture` and
  `foreign_spelling_is_not_owned_overlap` retain the complete native map and distinguish
  observed empty from missing.
- Selected parent: `receipt_parent_precedes_preferred_alias` checks conditional renderer
  priority over supplied physical role maps; arbitrary prepared-map authentication is open.
- Git refresh: `changed_physical_parent_refreshes_git_fields` observes changed physical
  parents and inherited fields; it is a refresh case with different raw I.
- Capture retry: `native_command_before_validation_forces_refresh` observes capture,
  preparation, lock/reread mismatch and retry before publication.
- Private-current selection: `second_owned_name_selects_current_git` exercises the second
  owned name in real non-root publication, with no receipt.
- Export order: `current_git_merge_precedes_first_export` observes shared merge before first
  export and cleanup after lock release.
- Custody: `custody_is_saved_before_named_write` compares the exact incoming prefix/record/
  digest chain at actual native writes, including a multi-ID record.
- Move/restart: `move_intent_precedes_old_head_removal` observes saved intent at
  add-before-remove and real recovery.
- Alias visibility: `complete_candidates_keep_ambiguous_published_aliases` retains all
  physical bodies and unequal per-machine fields; it does not authenticate U from markers.

The current `Export`/`Exported` events are bookkeeping boundaries, not complete per-ref,
worktree-HEAD or failed-CAS observations. Physical bookmark `x` evidence can instantiate only
its selected-ref projection. No full-snapshot export law follows from it.

## Remaining theorem and correspondence gates

`ConstructionSound` proves successful encoding lookup returns an observed complete shape and
successful receipt comparison preserves every computed image and admits no extra source key.
It also proves that the owned helper preserves the external-actor list and canonical/label
counters, and that successful receipt/render planning produces actual constructor origins.
`ConstructionInvariant` states the next reachable-policy target: every pending plan has an
actual constructor execution as its origin, and every prepared result comes from such a render
plan. It is explicitly not yet a proved invariant or a step precondition. Its preservation
must connect those same runs to committed receipt maps, installed identity rows, publication,
cleanup and recovery; generic supplied correctness predicates cannot replace that work.

The eventual native simulation additionally needs:

- An exact codec for every separately represented field and remaining `content` bytes,
  including stamp durations and metadata, and order-preserving embeddings of physical and
  original IDs. Numeric IDs here are model labels, not proof of native hashing or tie order.
- Independent authentication and completeness of identity rows, input histories and every
  consulted encoding, field-merge, common-base order and helper-outcome observation.
- Executable comparison with the real receive path's template selection and sparse map, and
  the renderer's full output. #151's conditional role fixtures cannot discharge the first.
- Original-native authority for an unpublished original, and nonancestor restore/revert
  references. These currently give explicit evidence gaps in `constructRender`.
- The exact selected physical projection through native helper load, repair, explicit export,
  failed-CAS and worktree-HEAD effects. The optional helper fact does not assert those laws.
- Canonical projection of an actual helper-created native child, followed by any normalization
  operation. Aliases stay physical until an explicit operation changes them.
- Preservation over the constructed action sublanguage and its Rust observation simulation,
  then connection to the actual assembled safety theorem. N06b's broader overlap, #141 object
  lifetime and ignored Windows #67 remain outside this accepted increment.
- The outer interpretation of a model gap or source choice outside U, unknown pruned-prefix
  and freshness behavior, and cross-store write ordering. These are explicit simulation
  obligations, not additional accepted defects or grounds to call a model gap a Rust refusal.

E1 closes the final reread through publication and cleanup; E2 closes branch/count through
helper load/export; recovery closes capture through its own move. They are explicit schedule
restrictions, not a universal lock theorem. No arbitrary mid-call failure, automatic
normalization termination, refinement or convergence result is claimed.

## Validation of the reviewed parent

At `6450a1fe818b2c655351c9915167ee76e1af11d3`, the targeted command
`taskpolicy -b env LEAN_NUM_THREADS=2 lake build
+Musubi.NativeLifecycleTest` passed all 11 jobs and 82 executable guards. The 25 added guards
pin computed contraction/stamps (including forget-after), sparse-map comparison and custody,
partial-write restart, exact render fields and changed-parent Git refresh, owned helper body
creation, unknown/scoped physical effects, single-head load versus repair, and physical-ID tie
ordering. These are model examples, not independently captured native outcomes. The seven new
lemmas also compile. Shared imports, oracle/JSON, Rust correspondence and the final `just check`
are intentionally still pending coordinator integration.

## Accepted construction review fixes

The child of that snapshot addresses three accepted defects, preserving the reviewed parent:

- Accepted-base image: `constructBase` advances through each new incoming record using its
  actual contraction images, taking the first expansion image in parent order. It resets to
  the root after departed applied records and retains a missing stored base, as
  `supersede/receive.rs::rename_for` does. Local pending drops remain separate. Base-only
  canonical rewrites are retained even when that base is absent from captured native history.
- Unaffected join: `receiptRewriteDomain` derives the stored-drop generation floor, follows
  the affected native standing walk and then the affected canonical prefix before rebuilding
  native parents. Empty records leave an unaffected join's physical prejoin parent alone,
  even when a normalized encoding is available. Affected joins and unmarked surviving
  descendants still undergo the required contraction. Mapping original-named model drops to
  the native path's exact stored canonical versions remains an authentication/simulation gate.
- Custody phase: render planning, materialization and commit reject an uncommitted receipt
  plan. Fetching a contracted canonical body therefore cannot open a separate render route
  before the incoming responsibility has been saved and the receipt committed. Capture stays
  a pure observation. The valid custody/write/receipt-commit/render/restart route remains.

The child passed the same targeted low-priority, two-thread Lean command: all 11 jobs and
95 guards, including the 13 review regressions. All seven affected lemmas compile; the first
four axiom queries use only `propext`/`Quot.sound`, and the helper/planning lemmas additionally
use `Classical.choice`. No `sorryAx` or native-law axiom occurs. No Cargo, shared interfaces,
JSON or Rust files changed, and this targeted pass does not replace the coordinator's final
integration checks. The reachable invariant, native simulation and assembled claim remain
unproved.

## Captured render responsibility and attempt association

The next phase rereview accepted the selector fixes in `6d8dce5d`, but found the same P1
custody guarantee still open: a prior empty-record saved move could recover after a later
receipt had produced a render plan, and completion cleared only the current receipt. The old
write checked that mutable receipt rather than the plan's captured receipt.

Render writes now check the complete records captured in `RenderBuild.receipt`. Both writing
and commit require the active preparing phase, an open preparation interval, the matching
capture and exact current/captured receipt association. They can still materialize an existing
captured plan after heads change, before the final revalidation; changed heads are not a new
custody source. Starting a receipt, committing it, a new capture, interruption, recovery,
head-switch completion and attempt completion invalidate the appropriate preparation plans.
These phase checks exclude inadmissible model call order. They do not assert a new shipping
Rust refusal for an arbitrary model action sequence.

The focused regression constructs an actual empty-record interrupted publication, changes the
native frontier before recovery, commits the new receipt without named writes, and prepares a
new named render. Recovery retains the replacement frontier and discards that plan before a
later write. Other examples require custody for an active captured receipt, permit the valid
committed-receipt write/restart path with saved custody, and check capture/interruption
invalidation. Local executed-write, association and invalidation lemmas derive their results
from the actual step definitions, not a supplied correct-custody premise.

This focused child passed the targeted low-priority, two-thread Lean build: all 11 jobs and
103 guards, including eight new custody/attempt cases. Thirteen local lemmas compile, including
the six new executed-write, receipt-association and invalidation results. All thirteen axiom
queries passed with only the expected logical axioms; no `sorryAx` or native-law axiom occurs.
No Cargo, shared interfaces, JSON or Rust files changed. The native data bridge, same-run
preservation and assembled claim remain pending, with all earlier authentication, floor/header,
outside-U, cross-store and physical-effect gates unchanged.

## Finite native fixture bridge on current main

The next integration is a new child of main
`cd2e1b5374229c01161f5c6bd146252aab5e32bd`. The reviewed model snapshots remain untouched.
Only these two existing native fixtures are connected:

- A: `custody_is_saved_before_named_write`, using actual `prepare_records`, its incoming
  multi-ID record and prefix, exact stored custody at every native write, and the raw native
  receipt projection (not every internal Taking field). The model independently computes
  contraction and locals before the observed map or
  observed write sequence is consulted. Observed writes must have exactly the independently
  predicted body-ID set; their actual order selects the materialization sequence certified by
  `certifiedRun`. Parent readability is checked at every such model write. Canonical-store
  write ordering remains an explicit cross-store simulation obligation.
- B: `second_owned_name_selects_current_git`, using actual `advance`, complete `{a,b}` current
  and `{b}` target inputs, no active receipt and non-root policy. An explicit actor prelude
  canonicalizes the current native command before raw capture; observation itself never writes
  identities. The model computes source/ownership/render/Git policy and the publication-order
  cut. The test compares the actual source reread, native ordered merge parents, complete
  per-machine Git fields and physical bookmark `x`. The pre-export `with_per_machine` copy is
  independently computed and compared by complete shape; installing that later effect is not
  yet part of the certified action prefix, which ends at revalidation.

Schema 1 (`nativeLifecycle`) carries complete before/after raw body manifests and bodies,
ordered parent IDs, all metadata (both timestamp/offset pairs, author workspace, description,
user/host, snapshot flag and every attribute), exact predecessor option/lists and full views.
Views retain sorted head sets, all bookmarks/tags/remotes, signed ref removals/additions with
multiplicity and absent terms, Git refs/HEAD maps and all workspace bindings. Physical state
is expressly the selected `refs/heads/x` projection. Complete retained originals/join
fingerprints, native record names/digests and saved/expected observations accompany them.
The preferred translation map and Rust-selected ownership/overlap/source answers are absent.

The codec derives model branch fields from those raw bodies. Native original candidates come
from retained nonparent fingerprints plus ordered parent projection, not a chosen Rust map.
Physical, canonical, original and commit IDs use distinct deterministic pools. Physical pool
byte order represents ID order, not timestamp-tie order for publication operands. Full remaining
body/view
content and full Git fields are interned by exact structural content, not lossy scalar HEADs
or hash guesses. Post-call bodies are authenticated encoding observations consulted only after
expected shapes are computed. Incomplete manifests/graphs, unsorted/duplicate label pools,
malformed namespaces/stamps and unresolved originals are interpretation failures, not claimed
Rust refusals. Native/hash authentication beyond these actual fixtures remains gated.

Two representation additions preserve material the raw codec cannot omit: `Record.names`
keeps exact canonical record names apart from their immutable-original projection, and
`NativeBody.presenceStamp` retains the raw hash-visible stamp. Receipt template rewrites keep
that native stamp; canonical render construction copies the canonical stamp. All other
nonparent fields, including predecessor None versus empty and signed multiplicity, remain in
the exact raw content interning. Duration formats not exercised by this finite bridge, restore
references, arbitrary identity authentication and native version/floor matching stay explicit.

`RunSound` relates the actual executable action list to `Runs`, derives complete-record
responsibility for every constructed receipt/render write along that same list, and supplies
the proof-carrying `certifiedRun` used by the codec. No correct-source, correct-receipt or
native-refines premise is accepted. `ConstructionRun` states the further policy target over
that same trace: ConstructionInvariant at every prefix together with custody. Its full
preservation and the actual native observation simulation are still pending; the certificate
establishes the custody component only. This is not replaced by planning/frame facts.

The two certified lists and their boundaries are explicit in `Json.reply`:

- A runs `planReceipt`, `saveCustody`, all computed `writeReceiptCanonical` actions, the
  computed `writeReceiptNative` actions in the observed native order, and `commitReceipt`.
  The native body-ID set is checked against independently computed bodies before the observed
  order is used. The model's canonical write order precedes that native sequence; the actual
  cross-store order is not certified. Subsequent settling, publication, mutable identity-map
  installation and cleanup are outside this certificate. Native receipt-projection comparison
  and the raw custody file observed at each actual native write are finite test evidence.
- B runs `capture`, `planRender`, every computed `writeRender`, `commitRender` and
  `revalidate`. It ends before installing the refreshed incoming body, native merge, export,
  head publication, helper load/repair and working-copy cleanup. The computed Git refresh and
  ordered merge-parent comparison are additional finite comparisons beyond that prefix.
  Source reread and export observations do not extend the prefix's theorem to those effects.

For each list, `certifiedRun initial actions` returns a final state only with both
`Runs initial actions final` and `CustodyAlong initial actions final` for those exact actions.
`run_has_trace` constructs the first relation from successful execution;
`runs_named_custody` constructs the second from the actual accepted steps using
`step_named_custody`. No separate abstract sequence is selected by the tests. The absent
`ConstructionAlong` proof and native observation simulation remain required before this can
be used as a whole-call safety result.

The paired Rust module is `node/realize/native_lifecycle_conformance.rs`, registered only as a
child of the existing native fixture module. Shared changes are limited to the ExecJson
stateless dispatch, aggregate imports and axiom audit entries.

The frozen first bridge, `e63df1b44348`, compiled its codec, 103 model guards and oracle. Both
actual Rust fixtures ran but failed during eager whole-corpus identity interpretation before
either reached `certifiedRun`. Stored reconcile forms had the same retained nonparent
fingerprint as a canonical original but reversed ordered parents. The raw captures, logs,
patch and exact IDs are preserved in the coordinator's local evidence handoff. This was an
interpretation gap, not a product defect or successful correspondence. The serial phase ended
after 11 minutes 22 seconds, with no second oracle build or full suite.

## Strict partial identities and publication operand order

The child retains every raw native/canonical body, ordered parent and encoding candidate.
Raw decoding validates both manifests, graph closures, unique body IDs and typed retained
rows. Fatal structural errors still reject the snapshot. A separate total classification
returns a qualified positive identity, a graph-checked prejoin witness, or a typed unresolved
issue. Missing material is unresolved; it is never an absent counterpart or root identity.
The raw retained fingerprints remain in `Evidence`, and each identity query recomputes its
dependencies against current positive evidence. There is no cached negative result to erase.

`installIdentities` checks the native body, canonical body, immutable original, marker and
every existing positive classification before accepting a row. New evidence cannot replace
a conflicting positive or a proved prejoin classification. Derived dependency failures can
change only because a fresh query sees additional checked evidence; the retained raw corpus
does not shrink. Native cryptographic/semantic authentication remains a separate gate.

All optional-counterpart consumers now receive strict queries. This includes the receipt
rewrite domain, contraction walk, maximal-head pruning and recovery's exact-frontier cases.
An unresolved captured/recovery input is a model gap, not evidence that the physical head is
unchanged, preserved, removed or canonical root. These are model interpretation restrictions,
not new shipping Rust refusals. A helper can create an unqualified physical body, but that
does not make a later identity query succeed.

Source roles still enumerate full receipt locals, complete published ancestry and all stored
fallback bodies. Unresolved members stay in their role's gap list. The selection lemmas
derive a singleton qualified chosen role, no gaps in it, and empty, resolved higher roles
from the actual computed priority decision. Domain and gap-membership lemmas connect that
decision to the complete raw domains. Lower-role gaps remain unconsulted only when that
computed precedence applies. Full-shape encoding searches still use all pre/post bodies,
including unresolved bodies; native-fact applicability still uses its complete recorded graph.

Publication now orders exactly `beside ++ [incoming]` by `(endTime, operandIndex)` in both
the executable merge action and JSON comparison. Equal timestamps preserve operand order,
matching the native stable sort, without using physical IDs as a tie-break. The head-set
enumeration and broader `ownAtHeads` refinement are separate and unchanged in this slice.
The two reversed equal-time guards establish model behavior, not the native sorting law.

A can attempt construction beyond raw decoding, but may expose a further interpretation
gap. B's target has only a fallback realization, so its all-body fallback remains unavailable
while the reversed-parent forms lack independent identity/non-match evidence. Its expected
native policy and positive conformance assertion are unchanged; an unavailable result is not
a passing correspondence.

The child validation compiled the codec and six new identity/selection lemmas, passed all
122 model guards, and audited 18 declarations with only the expected logical axioms. One
oracle build passed 182 jobs. Both existing native targets ran and failed: A advanced past
raw decoding into `constructReceipt`, then lacked a matching computed canonical encoding;
B reported a typed `unresolvedIdentity/noMatch` from its consulted fallback. Neither returned
a completed construction or reached `certifiedRun`; no constructed-action prefix was
certified by these native checks. The Rust assertions and native policy were not weakened.
The serial window ran for 3 minutes 49 seconds, with no second oracle build, full suite or
campaign. Full construction preservation, native simulation, cross-store order and the
certified prefix limits above remain unchanged.

The subsequent diagnostic-only child captured A's exact failed canonical argument and every
candidate without changing shape equality. Its nearest actual body differed only because
the raw stamp decoder prepended owner-map rows, whereas `stampOf` orders them. The captured
stamp and actual stamp serialize to exactly the same native bytes, and the reconstructed raw
operation shape matches the actual body, including its full view and predecessor option/list.
This is a codec representation mismatch, not evidence of a native presence-policy defect.

The next child orders only decoded stamp map rows (`latest`, `worked`, `forgetAfter`) by the
construction's copy-key order, after the existing exact raw-byte roundtrip validation. Every
inner value, option and multiplicity remains untouched; duplicate/noncanonical byte rejection
is unchanged. Ordered operation parents, predecessor lists and signed reference terms are not
normalized. A single multiowner roundtrip guard includes every map and duration option. The
diagnostic reporting remains separate from final landing.

The corrected child passed 123 model guards and its single oracle build. The existing native
target then reported one pass and one interpretation failure. A completed receipt construction
and the `certifiedRun` action list through receipt commit; its Rust assertions checked the
computed native-write set, a nonempty actual write sequence and exact complete-record disk
custody at every such write. This gives finite, nonvacuous evidence for that prefix. Actual
cross-store order and the later native effects are still outside the certificate. B remained
unavailable in its consulted all-body fallback and never reached `certifiedRun`; its positive
policy assertion was not replaced with an expected-gap pass.

Validation stayed inside the original ten-minute window (5 minutes 10 seconds). The first
guard check exposed two assertions tied to the diagnostic parent's old error text and a
missing decidable comparison in the new codec guard. Routine corrections within the same
window check specifically the canonical diagnostic kind while retaining its details, and
compare the codec result's option against the full expected stamp so errors fail. The first
failure and corrected logs are preserved. There was one oracle build and one existing A/B
native-target run, with no new fixture, campaign or full suite. B's identity evidence and the
full preservation/native-simulation obligations remain open.

## Independently observed source routes and finite description exclusion

The next child captures `identitySourceState` alongside the complete raw corpus. Its durable
inputs are the exact optional checkpoint, framed `superseded` steps, `hub-renamings`, accepted
base and accepted push files from the precall `Inputs` snapshot. The separately supplied
memory observation names its provenance and contains actual `Records.sources`, superseded and
dropped relations, realign frontiers/canonical aliases, record history names and phase/fixup
state, plus joins, join points and prejoin bodies. `Taking.locals` and selected translations
remain comparison targets. An absent checkpoint never supplies an empty memory relation.

The codec independently parses the checkpoint and both framed logs, validates complete line
counts, canonical hash/number spelling, referenced bodies, relation keys and checkpoint step
replay. It retains every frame, including superseded frames; replay selects the last complete
frame per number exactly for the checkpoint's counted prefix. The finite parser rejects torn,
escaped or unsupported checkpoint/log forms as interpretation gaps. Nonempty fixup checkpoint
contents also remain unsupported. This is not the production parser or a new native refusal.

The executable negative check is intentionally restricted to an ordinary target and empty
alternative routes, checked independently on disk and in memory. Every nonempty retained step,
history, source, supersede, drop, realign, accepted, join or prejoin route keeps a gap. Missing
route observations do too. Exact descriptions are read from hash-checked full bodies. Canonical
versions sharing an immutable original must agree on description and author workspace. The
certificate pins the exact physical ID, canonical version and immutable original; contraction
to a different survivor cannot reuse it. Markers, non-parent source constructors, restore and
revert are unsupported. A target without an author workspace is also excluded from this slice.

The native law used is a necessary description projection of the ordinary constructor:
`translate.rs::canonical_form` clones metadata and changes descriptions only for restore or
revert targets. `canonical/origin.rs::identity` restores original parents and removes presence,
leaving description unchanged. Native jj reparenting copies metadata unchanged. In contrast,
`join.rs::create_join_operation_with_remotes` changes description and `record_join` maps the old
head; the retained and in-memory join gates account for that counterexample rather than treating
description mismatch alone as universal evidence. The ordinary target workspace requirement
also excludes the explicit join constructor, which clears its author workspace.

`ordinaryOriginalBody` overapproximates that ordinary constructor by allowing every other
canonical field to vary while copying description. The local negative theorem excludes every
such body from matching the target description. It has no correct-source or whole-preservation
premise. The candidate-accounting theorem retains all unresolved members and all checked
target-specific exclusions in the original complete domains. It does not assert a positive
identity, a universal native original classifier or the soundness of every native route.

The earlier diagnostic-only snapshots remain available. This child removes their large
canonical encoding diagnostic payload and keeps the stamp representation correction and its
guard. Full construction preservation, native-law authentication beyond these observations,
native simulation and all certified-prefix limits remain open.

This child passed 146 executable guards, 22 affected axiom queries and its one oracle build.
The queries use only the expected logical axioms, with no `sorryAx` or native-law axiom. The
single existing A/B native-target run passed both tests. A again checked its nonempty actual
write set and complete disk custody through the receipt-commit certificate. B constructed
one render node and reached its capture/render/revalidate certificate, then passed the
separate ownership, complete Git fields, stable ordered merge, physical bookmark and native
reread/export-order comparisons. The Rust policy assertions were unchanged.

For B's actual precall observation, all five durable route files were absent and every
separately captured memory relation/history was empty, with inactive phase/fixup flags. A
read-only audit of that saved input recomputed the full fallback domain: one qualified source,
two target-specific description exclusions and no unresolved members. Both excluded native
bodies say `reconcile divergent operations`; the exact ordinary target/original says
`create bookmark child pointing to commit ...`. Those bodies remain in the raw corpus and
remain globally unresolved; their exclusions apply only to this target. Same-description,
incomplete-route and explicit recorded-join cases continue to be gaps.

The original bounded phase began at 16:09:40 UTC on November 14, 2026. Native jobs had ended
by 16:18:10, releasing the heavy slot after 8 minutes 30 seconds. Saving pure oracle replies
and the read-only candidate audit completed by 16:19:49, within the same twenty-minute cap.
Routine elaboration and guard syntax corrections stayed inside that window, with failed
logs preserved. There was one oracle build, one native-target run, no native retry, no new
fixture, no full suite and no campaign. Coordinator integration still owns the final checks
and independent reviews; the full preservation/native-simulation obligations remain open.

## Staged source-route freshness and current-Git installation

The next source increment makes current-Git installation part of the executable B prefix.
`currentGitBody` reuses an equal field record verbatim. For different fields it copies the
complete per-machine projection and adds an explicit canonical marker, retaining every other
body field. `constructCurrentGit` derives current fields from the actual current heads, checks
the incoming identity against the prepared target, computes the complete body before encoding
lookup, and derives its identity row from that target's immutable original. No selected Rust
source, field, body or translation answer is a premise.

The `refreshCurrentGit` action installs that body and identity, updates the disposable preferred
translation entry, and replaces `Publication.incoming` with the constructed physical ID. A
changed write checks complete responsibility for the preparation's captured receipt. An equal
field record is reused, including an unmarked original, without inventing a write. A later
merge using current Git requires this installed operand; a missing action is an incomplete
model prefix, not a new Rust refusal. B's certificate now ends after this action and before
native merge/export. Ordered merge-input comparison reads the installed state directly.

Current source observations are framed only for explicitly classified body, translation/cache,
physical Git, planning and head-store effects. Receipt/record/checkpoint changes, recovery,
unclassified helper outcomes, evidence loss, external effects and partial failure discard the
snapshot. The action still completes normally; later negative queries report missing evidence.
Pure capture cannot resurrect an invalidated observation. Historical receipt/render inputs
remain construction provenance and do not substitute for the current source-route observation.
`step_source_routes` derives the frame/invalidation result from the successful actual step;
`runs_source_routes` lifts it along the same `Runs` list used by `certifiedRun`. The certificate
now includes `SourceRoutesAlong` as well as custody. This is a model transition result; full
native frame authentication and same-run `ConstructionAlong` preservation remain pending.

The source frame deliberately does not say that `insert_map` leaves all translation state
unchanged. The shipping function writes `musubi/translation`, updates both lookup directions
and can invalidate `published_history`. None of these is `Records.sources`, realign, the
superseded/dropped relation, checkpoint/history/fixup phase, or join/join-point/prejoin state in
`SourceRoutes`. The model installs its independently constructed positive identity and preferred
entry. A test-only boundary event observes the actual affected forward/preferred entries and
complete durable plus memory source snapshots before and after the shipping write/map update.
These observations are comparison targets only. The existing B target requires a changed
physical ID, matching constructed incoming/identity/preferred entry, unchanged complete source
observation at that boundary, and refresh before export. It does not infer an internal frame
from an observation made only after the entire call returned.

The ordinary body/frame/marker, exact encoding, constructor pinning, captured-receipt custody
and refresh-origin lemmas feed the existing construction/run proof path. The construction
invariant target now includes the actual computed refresh origin. A still supplies nonempty
record custody evidence. B still has no receipt records, so its custody component is vacuous;
its changed refresh installation and source-frame comparisons must be nonempty. The existing
two targets are unchanged in number. No production policy, protocol or testutil changes occur;
the shipping boundary additions are compiled only for tests and read snapshots only when an
observer is active.

The bounded validation passed all 162 executable guards, 32 affected axiom queries, one oracle
build and both existing native targets. No `sorryAx` or native-law axiom occurs. The new B
assertions observed different physical input/output IDs at the shipping refresh boundary,
matched the computed installed operand and forward/preferred translation entries, and checked
the complete durable/memory snapshot before and after that write against the initial raw
observation. The changed refresh comparison is nonvacuous. Its certificate contains the exact
six actions: capture, planRender, one writeRender, commitRender, revalidate, refreshCurrentGit.
Native merge/export and later effects remain outside it. B's custody component is still
vacuous. A retains its nonempty five-action receipt/custody prefix; its source observation is
discarded after custody/checkpoint and receipt changes, not falsely framed as empty.

The original twenty-minute window began at 17:50:27 UTC on November 14, 2026. All jobs ended
by 17:59:43, releasing the heavy slot after 9 minutes 16 seconds. The guard/proof elaboration
corrections and all failed logs stayed inside that window. There was one oracle build, one
native-target run, no retry, no third fixture, no full suite and no campaign. The actual native
run now saves both requests and model replies directly; no pure replay was needed. Independent
review, coordinator integration checks, full same-run ConstructionAlong preservation and
native observation/frame simulation remain pending. Adding refresh origin to the invariant
target is not a proof of that target.
