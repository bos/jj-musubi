/-
Executable model examples, not native evidence or Rust correspondence. They pin observable
decision differences: second-name overlap, concrete versus erased work, physical aliases,
record custody, stale captures and the separate schedule restrictions of accepted #149 v2.
-/
import Musubi.NativeLifecycle
import Musubi.NativeLifecycle.ConstructionSound
import Musubi.NativeLifecycle.Json

namespace Musubi.NativeLifecycle.Test

private def me : Copy := ⟨"alpha".toList, "1111".toList⟩
private def a : Name := "a".toList
private def b : Name := "b".toList
private def c (n : Nat) : Canonical := ⟨n⟩
private def p (n : Nat) : Physical := ⟨n⟩
private def o (n : Nat) : Original := ⟨n⟩
private def key (name : Name) : WorkspaceKey := ⟨me, name⟩
private def beta : Copy := ⟨"beta".toList, "2222".toList⟩
private def foreignName : Name := "beta/b".toList

private def evidence : Evidence :=
  { root := c 0, physicalRoot := p 0,
    canonical := [
      { id := c 0, original := o 0, originalParents := [], parents := [] },
      { id := c 1, original := o 1, originalParents := [o 0], parents := [c 0],
        work := some me, workspaces := [(key a, 10), (key b, 20)] },
      { id := c 2, original := o 2, originalParents := [o 1], parents := [c 1], forgets := [me] },
      { id := c 3, original := o 3, originalParents := [o 1], parents := [c 1],
        work := some me, workspaces := [(key a, 10)] },
      { id := c 4, original := o 4, originalParents := [o 0], parents := [c 0],
        stamp := some { known := [me], latest := [], worked := [(me, [o 77])] } }],
    native := [
      { id := p 0, parents := [] },
      { id := p 1, parents := [p 0], workspaces := [(a, 10), (b, 20)] },
      { id := p 2, parents := [p 1], workspaces := [(b, 20)], marker := some (c 2),
        context := some { source := me, known := [me], names := [(b, key b)] } },
      { id := p 3, parents := [p 1], workspaces := [(a, 10)] },
      { id := p 4, parents := [p 0], workspaces := [(a, 10), (b, 20)],
        marker := some (c 1), gitFields := 99 }],
    identities := [
      ⟨p 1, c 1, o 1, .original⟩, ⟨p 2, c 2, o 2, .markedBody⟩,
      ⟨p 3, c 3, o 3, .original⟩, ⟨p 4, c 1, o 1, .markedBody⟩,
      ⟨p 6, c 2, o 2, .markedBody⟩] }

private def saved : Persistent := { acceptedBase := some (c 1) }
private def receipt : Receipt :=
  { identity := 0, recordPrefix := 0, records := [], capturedHeads := [p 1], input := evidence,
    locals := [(p 1, [p 4])] }

-- Ownership is computed from complete native/canonical inputs, including the second name.
#guard (gitChoice evidence 30 me [p 1] (p 2) saved none).map (·.useCurrent) = .ok true
#guard (gitChoice evidence 30 me [p 3] (p 2) saved none).map (·.useCurrent) = .ok false
#guard (gitChoice evidence 30 me [p 1] (p 2) saved none).map
  (fun choice => (choice.currentOwned, choice.targetOwned, choice.known, choice.present)) =
    .ok ([(a, 10), (b, 20)], [(b, 20)], true, false)
#guard (gitChoice evidence 30 me [p 0] (p 2) saved none).map (·.useCurrent) = .ok false

private def foreignEvidence : Evidence :=
  { evidence with
    canonical := evidence.canonical ++ [
      { id := c 5, original := o 5, originalParents := [o 0], parents := [c 0],
        forgets := [me], workspaces := [(⟨beta, b⟩, 20)] },
      { id := c 6, original := o 6, originalParents := [o 0], parents := [c 0],
        work := some me, workspaces := [(key foreignName, 30)] }],
    native := evidence.native ++ [
      {
        id := p 5, parents := [p 0], marker := some (c 5), workspaces := [(foreignName, 20)],
        context := some {
          source := me, known := [me, beta],
          names := [(foreignName, ⟨beta, b⟩)] } },
      { id := p 7, parents := [p 0], workspaces := [(foreignName, 30)] }],
    identities := evidence.identities ++
      [⟨p 5, c 5, o 5, .markedBody⟩, ⟨p 7, c 6, o 6, .original⟩] }

-- An identical displayed spelling is not overlap when the target slot belongs to beta.
#guard (gitChoice foreignEvidence 30 me [p 7] (p 5) saved none).map
  (fun choice => (choice.currentOwned, choice.targetOwned, choice.useCurrent)) =
    .ok ([(foreignName, 30)], [], false)

-- Erased work is below concrete work in either parent order, never a new owner source.
#guard latestWorkParent evidence 30 me [c 4, c 3] = .ok 1
#guard latestWorkParent evidence 30 me [c 3, c 4] = .ok 0
#guard (selectOwn evidence 30 me (c 2) [p 3] [p 3] none) =
  .error (.malformed "parent vector identity")

-- A missing operation differs from an observed empty workspace map.
#guard ownOfNative evidence 30 me (p 0) = .ok []
#guard ownOfNative evidence 30 me (p 88) = .error (.physical (p 88))
#guard privateNames { evidence with native := evidence.native ++
  [{ id := p 8, parents := [p 0], source := .restore (p 88), workspaces := [(b, 20)] }] }
    me 30 (p 8) = .ok []

-- Exact same-receipt counterparts precede published/preferred local aliases.
#guard (candidates evidence 30 [p 1] (some receipt) (c 1)).map chooseSource =
  .ok (.selected .prepared (p 4))
#guard (selectParents evidence 30 [p 1] (some receipt) (c 2)).map (·.parents) =
  .ok (some [p 4])
#guard (candidates evidence 30 [p 1, p 4] none (c 1)).map chooseSource =
  .ok (.ambiguous .published [p 1, p 4])
#guard maximalPhysical evidence 30 [p 1, p 4] = .ok [p 1, p 4]

private def drop : Record := { before := 0, identity := 1, drops := [o 1] }
private def taking : Receipt := { receipt with identity := 1, records := [drop] }

-- Root classification comes from record transformation, not a supplied current-Git bit.
#guard preparedBase evidence 30 saved taking = .ok (some (c 0))
#guard rootBase evidence 30 saved (some taking) = .ok true
#guard rootBase evidence 30 saved (some { taking with switched := true }) = .ok false
#guard (gitChoice evidence 30 me [p 3] (p 2) saved
  (some { taking with capturedHeads := [p 3] })).map
    (fun choice => (choice.overlap, choice.rootBase, choice.useCurrent)) = .ok (false, true, true)

private def state : State :=
  { me, evidence, heads := [p 1], saved }
private def namedWrite : BodyWrite :=
  { body := { id := p 5, parents := [p 0] }, records := [drop] }

private def exported : NativeBody :=
  { id := p 6, parents := [p 1], workspaces := [(b, 20)], marker := some (c 2),
    context := some { source := me, known := [me], names := [(b, key b)] }, gitFields := 8 }

#guard run state [.receive taking, .write namedWrite] = .error .custody
#guard (run state [.receive taking, .saveCustody, .write namedWrite]).map
  (fun s => (s.saved.custody, s.createdBodies)) = .ok ([drop], 1)
#guard (takeResponsibility { saved with custody := [drop] } receipt
  ⟨[], [], []⟩).pending = [o 1]
#guard (takeResponsibility { saved with custody := [drop] } receipt
  ⟨[], [], []⟩).earlier = [drop]
#guard run state [.finish] = .error .phase

-- Allocating a label and creating a physical body are different effects; exact reuse is real.
#guard (run state [.receive taking, .saveCustody, .allocateLabel, .write namedWrite,
  .allocateLabel, .write namedWrite]).map
    (fun s => (s.allocatedLabels, s.createdBodies)) = .ok (2, 1)

-- A pre-validation command causes retry. After the successful reread E1 is explicit.
#guard (run state [.capture, .prepare (c 2) (p 2), .external [p 3] 0, .revalidate]).map
  (fun s => (s.phase, s.outside)) = .ok (.preparing, [])
#guard (run state [.capture, .prepare (c 2) (p 2), .revalidate,
  .external [p 3] 7]).map (fun s => (s.heads, s.physicalGit, s.outside)) =
    .ok ([p 3], 7, [.publicationOverlap])
#guard (run state [.helperEnter true, .external [p 1, p 3] 0]).map
  (fun s => (s.helper, s.outside)) = .ok (some .direct, [.helperOverlap])
#guard (run state [.startRecovery, .external [p 3] 0]).map (·.outside) = .ok [.recoveryOverlap]

-- Bookkeeping has no physical writer effect; the export event records that effect separately.
#guard (run state [.bookkeeping (p 1) 99]).map (·.physicalGit) = .ok 0
#guard (run state [.capture, .prepare (c 2) (p 2), .revalidate,
  .write ⟨exported, []⟩,
  .observeExport ⟨p 2, p 6, 0, 8, 8, 0⟩]).map (·.physicalGit) = .ok 8

private def unmovedReceipt : Receipt := { receipt with locals := [] }
private def beforeMove : List Action :=
  [.receive unmovedReceipt, .capture, .prepare (c 2) (p 2), .revalidate,
    .write ⟨exported, []⟩, .observeExport ⟨p 2, p 6, 0, 8, 8, 0⟩]

-- Publishing requires saved intent; interruption retains both physical heads and that intent.
#guard (run state (beforeMove ++ [.addHead (p 6)])) = .error .intent
#guard (run state (beforeMove ++ [.saveIntent (some (p 6)) none, .addHead (p 6),
  .interrupt, .restart])).map (fun s => (s.heads, s.saved.intent.map (·.to))) =
    .ok ([p 1, p 6], some [p 6])
#guard (run state (beforeMove ++ [.saveIntent (some (p 6)) none, .addHead (p 6),
  .interrupt, .restart, .startRecovery, .finishMove, .finishRecovery, .finish])).map
    (fun s => (s.heads, s.saved.intent.isNone, s.outside)) = .ok ([p 6], true, [])

-- A prejoin namespace does not turn an unmapped ancestor into a canonical root counterpart.
private def prejoinEvidence : Evidence :=
  { root := c 0, physicalRoot := p 0,
    canonical := [
      { id := c 0, original := o 0, originalParents := [], parents := [] },
      { id := c 1, original := o 1, originalParents := [o 0], parents := [c 0] }],
    native := [
      { id := p 0, parents := [] },
      { id := p 1, parents := [p 0] },
      { id := p 2, parents := [p 1] }],
    identities := [⟨p 2, c 1, o 1, .original⟩], joinInputs := [p 2] }

#guard namespaceCanonical prejoinEvidence 20 (p 1) = .ok (c 0)
#guard prejoinEvidence.counterpart (p 1) = .ok none
#guard (candidates prejoinEvidence 20 [p 2] none (c 0)).map (·.published) =
  .ok ⟨[p 0], [], []⟩
#guard (candidates prejoinEvidence 20 [p 2] none (c 0)).map chooseSource =
  .ok (.selected .published (p 0))
#guard (candidates { prejoinEvidence with native := prejoinEvidence.native ++
  [{ id := p 3, parents := [p 0] }] } 20 [p 2, p 3] none (c 0)).map chooseSource =
    .ok (.unavailable .published [(p 3, .unresolvedIdentity (p 3) .missingFingerprint)])

-- Hold keeps readable departed applied receipts, not merely the union of their drops.
private def secondDrop : Record := { before := 1, identity := 2, drops := [o 2] }
private def departed : Persistent :=
  takeResponsibility { saved with applied := [drop] } unmovedReceipt ⟨[], [], []⟩
private def olderReply : Persistent :=
  takeResponsibility { saved with applied := [drop, secondDrop] } taking ⟨[], [], []⟩

#guard (departed.earlier, departed.pending) = ([drop], [o 1])
#guard heldRecords departed 1 1 = some ⟨0, 0, [drop]⟩
#guard (olderReply.applied, olderReply.earlier, olderReply.pending) =
  ([drop], [secondDrop], [o 2])
#guard heldRecords olderReply 2 2 = some ⟨0, 0, [drop, secondDrop]⟩
#guard heldRecords olderReply 1 2 = none
#guard (takeResponsibility { saved with applied := [drop], earlier := [drop] }
  unmovedReceipt ⟨[], [], []⟩).earlier = [drop]
#guard (takeResponsibility departed taking ⟨[], [], []⟩).earlier = []

private def opaqueReceipt : Receipt :=
  { unmovedReceipt with identity := 1, recordPrefix := 1, prunedCount := 1 }
private def afterOpaque : Persistent :=
  takeResponsibility { saved with
    recordPrefix := 1, prunedCount := 1,
    applied := [secondDrop] } opaqueReceipt ⟨[], [], []⟩
private def lostOpaque : Persistent :=
  takeResponsibility afterOpaque unmovedReceipt ⟨[], [], []⟩

#guard heldRecords afterOpaque 2 2 = some ⟨1, 1, [secondDrop]⟩
#guard (lostOpaque.earlier, lostOpaque.pending) = ([], [o 2])
#guard heldRecords lostOpaque 2 2 = none

-- Recovery of A→A', B→B' moves classified heads. C is new native work replacing A;
-- missing independent identity material now leaves this model call explicitly unresolved.
private def recoveryEvidence : Evidence :=
  { root := c 0, physicalRoot := p 0,
    canonical := [
      { id := c 0, original := o 0, originalParents := [], parents := [] },
      { id := c 10, original := o 10, originalParents := [o 0], parents := [c 0] },
      { id := c 1, original := o 1, originalParents := [o 10], parents := [c 10] },
      { id := c 2, original := o 2, originalParents := [o 10], parents := [c 10] },
      { id := c 3, original := o 1, originalParents := [o 10], parents := [c 0] },
      { id := c 4, original := o 2, originalParents := [o 10], parents := [c 0] }],
    native := [
      { id := p 0, parents := [] }, { id := p 10, parents := [p 0] },
      { id := p 1, parents := [p 10] }, { id := p 2, parents := [p 10] },
      { id := p 3, parents := [p 0], marker := some (c 3) },
      { id := p 4, parents := [p 0], marker := some (c 4) },
      { id := p 5, parents := [p 1] }],
    identities := [
      ⟨p 10, c 10, o 10, .original⟩, ⟨p 1, c 1, o 1, .original⟩,
      ⟨p 2, c 2, o 2, .original⟩, ⟨p 3, c 3, o 1, .markedBody⟩,
      ⟨p 4, c 4, o 2, .markedBody⟩] }

private def recoveryIntent : Intent :=
  { fromHeads := [(p 1, [p 3]), (p 2, [p 4])], to := [p 3, p 4],
    identities := recoveryEvidence.identities }
private def interruptedMove : State :=
  { me, evidence := recoveryEvidence, heads := [p 1, p 2], phase := .interrupted,
    saved := { intent := some recoveryIntent } }

#guard (run interruptedMove [.external [p 5, p 2] 0, .startRecovery, .finishMove]).map
  (fun s => (s.heads, s.outside)) =
    .error (.evidence (.unresolvedIdentity (p 5) .missingFingerprint))
#guard (run interruptedMove [.external [p 5, p 2] 0, .startRecovery,
  .addHead (p 3)]) = .error (.evidence (.unresolvedIdentity (p 5) .missingFingerprint))
#guard (run interruptedMove [.external [p 5] 0, .startRecovery, .finishMove]).map
  (·.heads) = .error (.evidence (.unresolvedIdentity (p 5) .missingFingerprint))
#guard (run { interruptedMove with evidence := { recoveryEvidence with
  native := recoveryEvidence.native.filter (fun body => decide (body.id ≠ p 3)) } }
    [.external [p 5] 0, .startRecovery, .finishMove]).map (·.heads) =
      .error (.evidence (.unresolvedIdentity (p 5) .missingFingerprint))
#guard (run interruptedMove [.startRecovery, .finishMove]).map (·.heads) = .ok [p 3, p 4]
#guard (run interruptedMove [.external [p 4, p 3] 0, .startRecovery, .finishMove]).map
  (fun s => (s.heads, s.createdBodies)) = .ok ([p 4, p 3], 0)
#guard (run interruptedMove [.external [p 1, p 3, p 2] 0, .startRecovery, .finishMove]).map
  (·.heads) = .ok [p 3, p 4]
#guard (run interruptedMove [.addHead (p 3), .finishMove]).map (·.heads) = .ok [p 3, p 4]

-- These tables exercise computed shape lookup. They are model examples, not native hashes.
private def contracted : CanonicalBody :=
  { id := c 20, original := o 2, originalParents := [o 1], parents := [c 0], forgets := [me],
    stamp := some { known := [me], latest := [], worked := [(me, [o 1])] } }
private def rewritten : NativeBody :=
  { id := p 20, parents := [p 0], workspaces := [(b, 20)], marker := some (c 20),
    context := some { source := me, known := [me], names := [(b, key b)] } }
private def receiptFacts : NativeFacts :=
  { encodings := { canonical := [contracted], native := [rewritten] } }
private def request : ReceiptRequest := ⟨1, 0, 0, [drop]⟩
private def observedReceipt : Receipt :=
  { taking with
    input := evidence, capturedHeads := [p 2],
    locals := [(p 1, [p 0]), (p 2, [p 20])] }
private def receiptState : State :=
  { state with heads := [p 2], nativeFacts := receiptFacts }

-- Contraction derives both the presence stamp and physical map; raw locals are only compared.
#guard (constructReceipt evidence receiptFacts saved me [p 2] request).map
  (fun result => (result.canonicalWrites, result.nativeWrites, result.base)) =
    .ok ([contracted], [rewritten], some (c 0))
#guard (constructReceipt evidence receiptFacts saved me [p 2] request).map
  (fun result => receiptInputMatches result observedReceipt) = .ok true
#guard (constructReceipt evidence receiptFacts saved me [p 2] request).map
  (fun result => receiptInputMatches result { observedReceipt with locals := [] }) = .ok false
#guard (constructReceipt evidence receiptFacts saved me [p 2] request).map
  (fun result => receiptInputMatches result
    { observedReceipt with locals := observedReceipt.locals ++ [(p 88, [p 88])] }) = .ok false
#guard (constructReceipt evidence {} saved me [p 2] request) =
  .error (.encoding "canonical body")

-- The shared accepted base follows incoming contractions, independently of local drops.
#guard (constructReceipt evidence receiptFacts { saved with acceptedBase := some (c 2) }
  me [p 2] request).map (·.base) = .ok (some (c 20))
#guard (constructReceipt evidence receiptFacts
  { saved with acceptedBase := some (c 2), pending := [o 1] } me [p 2]
  ⟨0, 0, 0, []⟩).map (fun result => (result.base, result.canonicalWrites)) =
    .ok (some (c 2), [contracted])
#guard (constructReceipt evidence receiptFacts { saved with acceptedBase := some (c 2) }
  me [p 1] request).map (fun result => (result.base, result.canonicalWrites)) =
    .ok (some (c 20), [contracted])
#guard (constructReceipt evidence {} { saved with acceptedBase := some (c 88) }
  me [p 0] request).map (fun result => (result.base, result.canonicalWrites)) =
    .ok (some (c 88), [])
#guard (constructReceipt evidence {}
  { saved with acceptedBase := some (c 2), applied := [drop] } me [p 0]
  ⟨0, 0, 0, []⟩).map (·.base) = .ok (some (c 0))

private def forkBase : Evidence :=
  { evidence with canonical := evidence.canonical ++ [
      { id := c 50, original := o 50, originalParents := [o 4, o 1],
        parents := [c 4, c 1] }] }
#guard (constructReceipt forkBase {} { acceptedBase := some (c 50) } me [p 0]
  ⟨5, 0, 0, [⟨0, 5, [o 50], []⟩]⟩).map (·.base) = .ok (some (c 4))

private def normalizedJoin : NativeBody :=
  { id := p 41, parents := [p 0], marker := some (c 1) }
-- An unaffected join keeps its native parent even when a normalized encoding is available.
#guard (constructReceipt prejoinEvidence {} {} me [p 2] ⟨0, 0, 0, []⟩).map
  (fun result => (result.canonicalWrites, result.nativeWrites,
    lookup result.computed.locals (p 2))) = .ok ([], [], some [p 2])
#guard (constructReceipt prejoinEvidence
  { encodings := { native := [normalizedJoin] } } {} me [p 2] ⟨0, 0, 0, []⟩).map
  (fun result => (result.canonicalWrites, result.nativeWrites,
    lookup result.computed.locals (p 2))) = .ok ([], [], some [p 2])
-- The affected domain still drops a join and rewrites an unmarked surviving descendant.
#guard (constructReceipt prejoinEvidence {} {} me [p 2] request).map
  (fun result => lookup result.computed.locals (p 2)) = .ok (some [p 0])
private def unmarkedSurvivor : Evidence :=
  { evidence with
    native := evidence.native.map (fun body =>
      if body.id = p 2 then { body with marker := none, context := none } else body),
    identities := evidence.identities.map fun row =>
      if row.physical = p 2 then { row with kind := .original } else row }
#guard (constructReceipt unmarkedSurvivor receiptFacts saved me [p 2] request).map
  (fun result => (result.canonicalWrites, result.nativeWrites)) =
    .ok ([contracted], [rewritten])

private def durationEvidence : Evidence :=
  { evidence with canonical := evidence.canonical.map fun body =>
      if body.id = c 1 then { body with forgetAfter := some (some 10) } else body }
private def durationContracted : CanonicalBody :=
  { contracted with id := c 21, stamp := some {
      known := [me], latest := [], worked := [(me, [o 1])],
      forgetAfter := [(me, [(o 1, some 10)])] } }
-- Forget-after records change a contraction's hash even though ownership ignores duration.
#guard (contractOne durationEvidence { canonical := [durationContracted] } [o 1] 30
  (c 2) { evidence := durationEvidence }).map (fun result => result.1.writes) =
    .ok [durationContracted]
#guard contractOne durationEvidence { canonical := [contracted] } [o 1] 30
  (c 2) { evidence := durationEvidence } = .error (.encoding "canonical body")

#guard run receiptState [.planReceipt request, .writeReceiptCanonical 0] = .error .custody
#guard (run receiptState [.planReceipt request, .saveCustody, .writeReceiptCanonical 0,
  .writeReceiptNative 0, .commitReceipt observedReceipt]).map
    (fun s => (s.receipt, s.saved.custody, s.createdCanonicals, s.createdBodies)) =
      .ok (some observedReceipt, [drop], 1, 1)
#guard (run receiptState [.planReceipt request, .saveCustody, .writeReceiptCanonical 0,
  .writeReceiptNative 0, .restart]).map
    (fun s => (s.evidence.native.contains rewritten, s.saved.custody, s.receiptPlan)) =
      .ok (true, [drop], none)

private def fetchedSurvivor : State :=
  { receiptState with evidence := { evidence with canonical := evidence.canonical ++ [contracted] } }
-- Fetching a contracted body cannot bypass keep_custody via an uncommitted receipt plan.
#guard run fetchedSurvivor [.planReceipt request, .capture, .planRender (c 20)] = .error .phase
#guard run fetchedSurvivor [.planReceipt request, .capture, .planRender (c 20),
  .writeRender 0, .restart] = .error .phase
#guard (run receiptState [.planReceipt request, .saveCustody, .writeReceiptCanonical 0,
  .writeReceiptNative 0, .commitReceipt observedReceipt, .capture, .planRender (c 20),
  .commitRender, .restart]).map
    (fun s => (s.saved.custody, s.createdBodies, s.evidence.native.contains rewritten)) =
      .ok ([drop], 1, true)

private def rendered : NativeBody :=
  { id := p 22, parents := [p 1], workspaces := [(a, 10), (b, 20)], marker := some (c 2) }
private def refreshed : NativeBody :=
  { rendered with id := p 23, parents := [p 4], gitFields := 99 }
private def renderFacts : NativeFacts :=
  { encodings := { native := [rendered, refreshed] } }

-- Every field is computed. A stale target's Git fields survive only unchanged parents.
#guard (constructRender evidence renderFacts me [p 1] none (c 2)).map
  (fun result => (result.result, result.nodes.map (·.body))) = .ok (p 22, [rendered])
#guard (constructRender evidence renderFacts me [p 1] (some receipt) (c 2)).map
  (fun result => (result.result, result.nodes.map (·.body))) = .ok (p 23, [refreshed])
#guard (constructRender evidence { encodings := { native := [rendered] } } me
  [p 1] (some receipt) (c 2)) = .error (.encoding "native body")
#guard (run { state with nativeFacts := renderFacts }
  [.capture, .planRender (c 2), .commitRender]) = .error .phase
#guard (run { state with nativeFacts := renderFacts }
  [.capture, .planRender (c 2), .writeRender 0, .commitRender, .revalidate]).map
    (fun s => (s.prepared.map (·.rendered), s.createdBodies, s.closedPublication)) =
      .ok (some (p 22), 1, true)

private def constructedRender : List Action :=
  [.capture, .planRender (c 2), .writeRender 0, .commitRender, .revalidate]
private def associationChecks : Query (List Bool) := do
  let origin ← constructRender evidence renderFacts me [p 1] none (c 2)
  let checked ← (certifiedConstructionRun me evidence [p 1] saved renderFacts 0
    constructedRender).mapError (fun _ => .malformed "constructed render failed")
  let some prepared := checked.val.prepared | throw (.malformed "no committed preparation")
  return [prepared,
    { prepared with inputs := { prepared.inputs with me := beta } },
    { prepared with inputs :=
      { prepared.inputs with evidence := { evidence with native := [] } } },
    { prepared with inputs := { prepared.inputs with heads := [p 4] } },
    { prepared with inputs := { prepared.inputs with target := c 1 } },
    { prepared with inputs := { prepared.inputs with receipt := some receipt } }].map
      (preparedMatchesOrigin me · origin)

-- Equal result/suffix/reserved alone must not certify a different owner or planning input.
#guard associationChecks = .ok [true, false, false, false, false, false]

-- Historical preparation survives an actual external effect without adopting its new heads.
#guard (certifiedConstructionRun me evidence [p 1] saved renderFacts 0
  (constructedRender ++ [.external [p 4] 7])).map (fun checked =>
    (checked.val.heads, checked.val.prepared.map (·.inputs.heads))) =
      .ok ([p 4], some [p 1])
#guard (certifiedConstructionRun me evidence [p 2] saved receiptFacts 0
  [.planReceipt request, .saveCustody, .writeReceiptCanonical 0, .writeReceiptNative 0,
    .commitReceipt observedReceipt]).map (fun checked => checked.val.saved.custody) = .ok [drop]
#guard (certifiedConstructionRun me evidence [p 1] saved renderFacts 0
  [.capture, .prepare (c 2) (p 22)]).map (fun checked => checked.val.prepared.isSome) =
    .error (.evidence (.nativeFact "raw shortcut outside constructed program"))

private def reparentedLeaf : NativeBody :=
  { id := p 80, parents := [p 0], workspaces := [(a, 10)] }
private def reparentedEvidence : Evidence :=
  { evidence with native := evidence.native ++ [reparentedLeaf] }

-- A native parent-only rewrite retains the old physical corpus and supplies no identity.
#guard (Json.observedHeadReparent evidence reparentedEvidence [p 3] [p 80] (p 1) 0).map
  (fun observed => (observed.native, observed.identities, observed.heads)) =
    .ok ([reparentedLeaf], [], [p 80])
#guard (Json.observedHeadReparent evidence { reparentedEvidence with
  native := evidence.native ++ [{ reparentedLeaf with gitFields := 99 }] }
  [p 3] [p 80] (p 1) 0).toOption.isNone
#guard (Json.observedHeadReparent evidence { reparentedEvidence with
  native := reparentedEvidence.native.filter (fun body => body.id != p 4) }
  [p 3] [p 80] (p 1) 0).toOption.isNone
#guard (certifiedConstructionRun me evidence [p 1] saved renderFacts 0
  (constructedRender.take 4 ++ [.native {
    native := [reparentedLeaf], heads := [p 80], physicalGit := 0 }, .revalidate])).map
    (fun checked => (checked.val.phase, checked.val.prepared.isNone,
      checked.val.evidence.sourceRoutes.isNone, checked.val.heads)) =
        .ok (.preparing, true, true, [p 80])

private def staleWriteBody : NativeBody :=
  { id := p 60, parents := [p 0], marker := some (c 20), presenceStamp := contracted.stamp }
private def staleWriteStart : State :=
  { fetchedSurvivor with
    heads := [p 1], colocated := false,
    nativeFacts := { encodings := {
      canonical := [contracted], native := [rendered, refreshed, staleWriteBody] } } }
private def priorEmptyReceipt : Receipt :=
  requestReceipt ⟨0, 0, 0, []⟩ staleWriteStart.evidence [p 1]

-- Build the prior saved intent by an actual empty-record interrupted publication. Native
-- work replaces its old frontier before recovery starts; the next receipt needs no writes.
private def staleRenderAttempt : Except StepError State := do
  let previous ← run staleWriteStart [
    .planReceipt ⟨0, 0, 0, []⟩, .commitReceipt priorEmptyReceipt,
    .capture, .planRender (c 2), .writeRender 0, .commitRender, .revalidate,
    .saveIntent (some (p 22)) none, .interrupt, .restart, .external [p 0] 0]
  let observed := requestReceipt request previous.evidence previous.heads
  run previous [.planReceipt request, .commitReceipt observed, .capture, .planRender (c 20)]

#guard staleRenderAttempt.map (fun s =>
  (s.saved.custody, s.renderPlan.map (fun plan => plan.nodes.map (·.body.id)), s.outside)) =
    .ok ([], some [p 60], [])
#guard (staleRenderAttempt >>= fun s => run s [.startRecovery, .finishMove, .finish]).map
  (fun s => (s.heads, s.evidence.native.contains staleWriteBody, s.saved.custody, s.renderPlan)) =
    .ok ([p 0], false, [], none)
-- Clearing the current receipt cannot detach the captured plan's custody obligation.
#guard (staleRenderAttempt >>= fun s =>
  run s [.startRecovery, .finishMove, .finish, .writeRender 0, .restart]) = .error .phase
#guard (staleRenderAttempt >>= fun s => run s [.writeRender 0]) = .error .custody
#guard (staleRenderAttempt >>= fun s => run s [.saveCustody, .writeRender 0, .restart]).map
  (fun s => (s.saved.custody, s.evidence.native.contains staleWriteBody, s.renderPlan)) =
    .ok ([drop], true, none)
#guard (staleRenderAttempt >>= fun s =>
  run s [.saveCustody, .external [p 1] 0, .writeRender 0, .restart]).map
  (fun s => (s.saved.custody, s.evidence.native.contains staleWriteBody, s.outside)) =
    .ok ([drop], true, [])
#guard (staleRenderAttempt >>= fun s => run s [.saveCustody, .capture, .writeRender 0]) =
  .error .phase
#guard (staleRenderAttempt >>= fun s => run s [.saveCustody, .interrupt]).map
  (fun s => (s.saved.custody, s.renderPlan, s.receipt)) = .ok ([drop], none, none)

private def helperBody : NativeBody :=
  { id := p 30, parents := [p 1, p 4], workspaces := [(a, 10), (b, 20)] }
private def helperFact : HelperFact :=
  { reference := "model example only", kind := .load, repositoryContext := 0,
    nativeGraph := evidence.native, heads := [p 1, p 4], orderedInputs := [p 1, p 4],
    written := [helperBody], result := p 30, afterHeads := [p 30],
    physical := some ⟨.selectedRef 0, 0, 7⟩ }
private def helperState : State :=
  { state with
    heads := [p 1, p 4], closedPublication := true,
    nativeFacts := { helpers := [helperFact] } }

-- An owned helper creates real bodies inside E1/E2, without allocating canonical labels.
#guard (run helperState [.helperEnter true, .ownHelper 0, .helperExit]).map
  (fun s => (s.heads, s.outside, s.createdBodies, s.allocatedLabels,
    s.physicalGit, s.physicalKnown)) = .ok ([p 30], [], 1, 0, 7, true)
#guard (run helperState [.helperEnter true, .ownHelper 0, .helperExit]).map
  (fun s => s.evidence.counterpart (p 30)) =
    .ok (.error (.unresolvedIdentity (p 30) .missingFingerprint))
#guard (run { helperState with nativeFacts :=
    { helpers := [{ helperFact with physical := none }] } }
  [.helperEnter true, .ownHelper 0]).map
    (fun s => (s.physicalGit, s.physicalKnown)) = .ok (0, false)
#guard run { helperState with physicalScope := .completeSnapshot }
  [.helperEnter true, .ownHelper 0] = .error (.evidence (.nativeFact "helper physical scope/input"))
#guard run { helperState with nativeFacts :=
    { helpers := [{ helperFact with orderedInputs := [p 4, p 1] }] } }
  [.helperEnter true, .ownHelper 0] = .error (.evidence (.nativeFact "helper raw inputs"))
#guard run { helperState with nativeFacts := { helpers := [{ helperFact with
    afterHeads := [p 3], result := p 3, written := [] }] } }
  [.helperEnter true, .ownHelper 0] =
    .error (.evidence (.nativeFact "helper discards native ancestry"))

private def repairBody : NativeBody := { id := p 31, parents := [p 1] }
private def repairFact : HelperFact :=
  { helperFact with
    kind := .repair, heads := [p 1], orderedInputs := [p 1],
    written := [repairBody], result := p 31, afterHeads := [p 31], physical := none }
#guard (run { state with nativeFacts := { helpers := [repairFact] } }
  [.helperEnter true, .ownHelper 0]).map
    (fun s => (s.helper, s.heads, s.createdBodies, s.physicalKnown)) =
      .ok (some .direct, [p 31], 1, false)
#guard run { state with nativeFacts := { helpers := [{ repairFact with kind := .load }] } }
  [.helperEnter true, .ownHelper 0] = .error (.evidence (.nativeFact "single-head load"))

private def tied : Evidence :=
  { evidence with
    canonical := evidence.canonical ++ [
      { id := c 40, original := o 40, originalParents := [o 0], parents := [c 0],
        work := some me, workspaces := [(key a, 99)] }],
    native := evidence.native ++ [{ id := p 40, parents := [p 0], workspaces := [(a, 99)] }],
    identities := evidence.identities ++ [⟨p 40, c 40, o 40, .original⟩] }

-- Equal end times use native physical-id order, even when the raw frontier is reversed.
#guard ownAtHeads tied 30 me [p 40, p 1] = ownAtHeads tied 30 me [p 1, p 40]
#guard (ownAtHeads tied 30 me [p 40, p 1]).map (fun bindings => lookup bindings a) = .ok (some 10)

-- Publication has a supplied operand vector. Tied times preserve it in either direction;
-- these guards establish model behavior, not a native stable-sort law.
#guard orderedPublicationInputs tied [p 40, p 1] = .ok [p 40, p 1]
#guard orderedPublicationInputs tied [p 1, p 40] = .ok [p 1, p 40]

private def unknownBody : NativeBody := { id := p 50, parents := [p 0] }
private def partialIdentity : Evidence :=
  { evidence with
    native := evidence.native ++ [unknownBody, { id := p 51, parents := [p 50] }],
    canonical := evidence.canonical ++ [
      { id := c 50, original := o 50, originalParents := [o 0], parents := [c 0] },
      { id := c 51, original := o 51, originalParents := [o 50], parents := [c 50] }],
    nativeFingerprints := [(p 51, 51)], originalFingerprints := [(o 51, 51)] }

-- Raw decoding can retain both bodies without inventing identities or losing fallback
-- eligibility. Unknown identity is never a negative counterpart or a root namespace.
#guard classifyIdentity partialIdentity 30 (p 50) = .ok (.unresolved .missingFingerprint)
#guard classifyIdentity partialIdentity 30 (p 51) = .ok (.unresolved (.dependency (p 50)))
#guard partialIdentity.counterpart (p 50) =
  .error (.unresolvedIdentity (p 50) .missingFingerprint)
#guard namespaceCanonical partialIdentity 30 (p 50) =
  .error (.unresolvedIdentity (p 50) .missingFingerprint)
#guard maximalPhysical partialIdentity 30 [p 1, p 50] =
  .error (.unresolvedIdentity (p 50) .missingFingerprint)
#guard recoveryDestination partialIdentity 30 [p 50] ⟨[], [], []⟩ =
  .error (.unresolvedIdentity (p 50) .missingFingerprint)
#guard receiptRewriteDomain partialIdentity 30 [] [p 50] =
  .error (.unresolvedIdentity (p 50) .missingFingerprint)
#guard constructReceipt partialIdentity {} {} me [p 50] ⟨0, 0, 0, []⟩ =
  .error (.unresolvedIdentity (p 50) .missingFingerprint)
#guard encodeNative partialIdentity {} unknownBody = .ok unknownBody

-- Independent role priority can leave a lower tier unconsulted; consulting the same
-- full fallback, or encountering an unresolved published member, cannot select a source.
#guard (candidates partialIdentity 30 [p 1] none (c 1)).map chooseSource =
  .ok (.selected .published (p 1))
#guard (candidates partialIdentity 30 [p 0] none (c 1)).map chooseSource =
  .ok (.unavailable .fallback [
    (p 50, .unresolvedIdentity (p 50) .missingFingerprint),
    (p 51, .unresolvedIdentity (p 51) (.dependency (p 50)))])
#guard (candidates partialIdentity 30 [p 1, p 50] none (c 1)).map chooseSource =
  .ok (.unavailable .published [(p 50, .unresolvedIdentity (p 50) .missingFingerprint)])

-- New positive evidence is checked, and dependent classifications are recomputed from
-- the retained fingerprint/parent material rather than clearing an old failure entry.
#guard (partialIdentity.installIdentities [⟨p 50, c 50, o 50, .original⟩] >>= fun next =>
  classifyIdentity next 30 (p 51)) = .ok (.known ⟨p 51, c 51, o 51, .original⟩)
#guard (partialIdentity.installIdentities [⟨p 50, c 50, o 50, .original⟩] >>= fun next =>
  next.installIdentities [⟨p 51, c 1, o 1, .original⟩]) =
    .error (.malformed "new identity conflicts with established identity")
#guard partialIdentity.installIdentities [⟨p 50, c 50, o 1, .original⟩] =
  .error (.malformed "identity original differs")
#guard evidence.installIdentities [⟨p 1, c 3, o 3, .original⟩] =
  .error (.malformed "conflicting identity rows")
#guard evidence.installIdentities [⟨p 4, c 3, o 3, .original⟩] =
  .error (.malformed "identity differs from native marker")

private def stampCodecContext : Json.Context :=
  { physical := [], canonical := [],
    original := [String.ofList (List.replicate 128 '0'), String.ofList (List.replicate 128 '1')],
    commits := [], digests := [], contents := [], fields := [] }
private def stampCodecValue : Stamp :=
  { known := [me, beta], latest := [(me, [o 0, o 1]), (beta, [o 1])],
    worked := [(me, [o 0]), (beta, [o 0, o 1])],
    forgetAfter := [(me, [(o 0, none), (o 1, some 1000000007)]), (beta, [(o 0, some 0)])] }

-- A canonical wire stamp must decode to the construction's map representation, preserving
-- multiple owners, every set value, absent duration, zero and subsecond duration options.
#guard decide ((Json.stamp stampCodecContext (Lean.Json.mkObj [("attributes", Lean.Json.mkObj [
  ("musubi.presence", Lean.Json.str (Json.stampText stampCodecContext stampCodecValue))])])).toOption =
    some (some stampCodecValue))

private def emptySourceMemory : SourceMemory :=
  { steps := 0, sources := [], superseded := [], dropped := [], realign := none,
    moving := false, taking := false, fixup := false, recordCount := 0,
    recordNames := [], joins := [], joinPoints := [], prejoin := [] }
private def closedSourceRoutes : SourceRoutes :=
  { checkpoint := {}, frames := [], countedSources := [], memory := emptySourceMemory,
    accepted := [], hubRenamings := [] }
private def ordinaryTarget : CanonicalBody :=
  { id := c 52, original := o 52, originalParents := [o 0], parents := [c 0],
    authorWorkspace := some (key a), description := "create bookmark child" }
private def descriptionEvidence : Evidence :=
  { partialIdentity with
    sourceRoutes := some closedSourceRoutes,
    canonical := partialIdentity.canonical ++ [ordinaryTarget] }
private def exclusionProjection (e : Evidence) (target : Canonical := c 52) :=
  (descriptionExclusion e (p 50) target).map (fun result => result.map (·.val))

-- A target-specific negative needs complete, separately observed empty routes. It is not
-- an identity for the unknown body, and does not transfer to a different drop survivor.
#guard exclusionProjection descriptionEvidence = .ok (some {
  physical := p 50, target := c 52, targetOriginal := o 52,
  nativeDescription := "", originalDescription := "create bookmark child" })
#guard descriptionEvidence.counterpart (p 50) =
  .error (.unresolvedIdentity (p 50) .missingFingerprint)
#guard (matchingCandidates descriptionEvidence 30 [p 50] (c 52)).unresolved = []
#guard (matchingCandidates descriptionEvidence 30 [p 50] (c 52)).excluded.length = 1
#guard exclusionProjection { descriptionEvidence with sourceRoutes := none } =
  .error (.nativeFact "complete source-route snapshot missing")
#guard exclusionProjection { descriptionEvidence with
  sourceRoutes := some { closedSourceRoutes with
    memory := { emptySourceMemory with sources := [(p 50, c 52)] } } } =
    .error (.nativeFact "nonempty source/join/accepted route needs identity authentication")
#guard exclusionProjection { descriptionEvidence with
  sourceRoutes := some { closedSourceRoutes with checkpoint := { steps := 1 } } } =
    .error (.nativeFact "nonempty source/join/accepted route needs identity authentication")
#guard exclusionProjection { descriptionEvidence with
  sourceRoutes := some { closedSourceRoutes with
    memory := { emptySourceMemory with joins := [(50, c 52)] } } } =
    .error (.nativeFact "nonempty source/join/accepted route needs identity authentication")
#guard exclusionProjection { descriptionEvidence with joinInputs := [p 50] } =
  .error (.nativeFact "nonempty source/join/accepted route needs identity authentication")
#guard exclusionProjection { descriptionEvidence with canonical :=
  partialIdentity.canonical ++ [{ ordinaryTarget with authorWorkspace := none }] } = .ok none
#guard exclusionProjection { descriptionEvidence with canonical :=
  partialIdentity.canonical ++ [{ ordinaryTarget with description := "" }] } = .ok none
#guard exclusionProjection { descriptionEvidence with native :=
  evidence.native ++ [{ unknownBody with description := "restore to operation 123" }] } = .ok none
#guard exclusionProjection { descriptionEvidence with native :=
  evidence.native ++ [{ unknownBody with marker := some (c 52) }] } = .ok none
#guard exclusionProjection { descriptionEvidence with canonical :=
  descriptionEvidence.canonical ++ [{ ordinaryTarget with
    id := c 53, original := o 53, description := "" }] } (c 53) = .ok none

private def sourceHash0 := String.ofList (List.replicate 128 '0')
private def sourceHash1 := String.ofList (List.replicate 128 '1')
private def sourceContext : Json.Context :=
  { physical := [sourceHash0], canonical := [sourceHash0, sourceHash1],
    original := [], commits := [], digests := [], contents := [], fields := [] }
private def sourceFrameText (canonical : String) :=
  s!"step 00000000000000000001 00000000000000000001\nsource {sourceHash0} {canonical}\n"

-- Complete frames are retained; the checkpoint selects last-frame-per-number replay.
-- Torn/unrecognized input stays an interpretation gap instead of silently proving absence.
#guard decide (((Json.sourceFrames sourceContext evidence
  (sourceFrameText sourceHash0 ++ sourceFrameText sourceHash1)).map (·.length)).toOption = some 2)
#guard decide ((Json.sourceFrames sourceContext evidence
  (sourceFrameText sourceHash0 ++ sourceFrameText sourceHash1) >>= Json.sourceCounted 1).toOption =
    some [(p 0, c 1)])
#guard (Json.sourceFrames sourceContext evidence
  "step 00000000000000000001 00000000000000000001\n").toOption.isNone
#guard (Json.sourceCounted 1 []).toOption.isNone
#guard decide (((Json.sourceCheckpoint sourceContext evidence none).map (·.steps)).toOption = some 0)
#guard !({ closedSourceRoutes with memory := { emptySourceMemory with
  realign := some { fromHeads := [], to := [], canonical := [] } } }).closed
#guard (Json.sourceCheckpoint sourceContext evidence (some
  ("{\"applied\":[],\"pending\":[],\"fixup\":null," ++
    "\"fixup_written\":false,\"steps\":0,\"steps\":0}"))).toOption.isNone
#guard decide (((Json.sourceHubFrames sourceContext evidence
  s!"record {sourceHash0} 00000000000000000001\n{sourceHash1} {sourceHash0}\n").map
    (fun frames => frames.flatMap (·.renames))).toOption = some [(c 1, c 0)])
#guard (Json.sourceHubFrames sourceContext evidence
  s!"record {sourceHash0} 00000000000000000001\n").toOption.isNone

private def routeState : State := { state with evidence := descriptionEvidence }

-- Pure capture/body/cache effects frame the observation. Route writes and unknown effects
-- invalidate it, and another capture cannot silently resurrect an old empty relation.
#guard (run routeState [.capture, .eraseMemo]).map (·.evidence.sourceRoutes) =
  .ok (some closedSourceRoutes)
#guard (run routeState [.external [p 1] 0, .capture]).map (·.evidence.sourceRoutes) = .ok none
#guard (step { routeState with receipt := some taking } .saveCustody).map
  (·.evidence.sourceRoutes) = .ok none
#guard (step routeState .failedCall).map (·.evidence.sourceRoutes) = .ok none
#guard ((step routeState (.external [p 1] 0)).map fun s =>
  exclusionProjection s.evidence) =
    .ok (.error (.nativeFact "complete source-route snapshot missing"))

private def refreshInput : NativeBody :=
  { id := p 70, parents := [p 1], workspaces := [(b, 20)], marker := some (c 2),
    gitFields := 0, description := "ordinary render" }
private def refreshOutput : NativeBody :=
  { refreshInput with id := p 71, gitFields := 99 }
private def refreshEvidence : Evidence :=
  { descriptionEvidence with
    native := descriptionEvidence.native ++ [refreshInput],
    identities := descriptionEvidence.identities ++ [⟨p 70, c 2, o 2, .markedBody⟩] }
private def refreshFacts : NativeFacts := { encodings := { native := [refreshOutput] } }
private def refreshInputs : Inputs :=
  { me, evidence := refreshEvidence, heads := [p 4], colocated := true,
    physicalGit := 0, target := c 2, receipt := none, saved := {}, expected := [], exports := [] }
private def refreshState : State :=
  { me, evidence := refreshEvidence, nativeFacts := refreshFacts, heads := [p 4],
    phase := .validated, closedPublication := true,
    prepared := some {
      rendered := p 70, suffix := {},
      selections := { choices := [(c 1, .selected .published (p 1))] },
      own := { source := .canonicalSlots, bindings := [] }, reserved := [], inputs := refreshInputs },
    git := some {
      currentOwned := [], targetOwned := [], rootBase := false, known := true,
      present := false, overlap := true, useCurrent := true },
    publication := some { incoming := p 70, beside := [p 4], mergeBeforeExport := true } }

-- Equal fields reuse even an unmarked original. Changed fields make its identity explicit.
#guard currentGitBody unknownBody (c 50) 0 = unknownBody
#guard (constructCurrentGit evidence {} [p 1] (c 1) (p 1)).map
  (fun build => (build.body.id, build.body.marker, build.writes)) = .ok (p 1, none, false)
#guard (currentGitBody unknownBody (c 50) 99).marker = some (c 50)
#guard (constructCurrentGit refreshEvidence refreshFacts [p 4] (c 2) (p 70)).map
  (fun build => (build.body, build.identity, build.writes)) =
    .ok (refreshOutput, ⟨p 71, c 2, o 2, .markedBody⟩, true)
#guard (constructCurrentGit refreshEvidence {} [p 1] (c 2) (p 70)).map
  (fun build => (build.body.id, build.writes)) = .ok (p 70, false)
#guard constructCurrentGit refreshEvidence {} [p 4] (c 2) (p 70) =
  .error (.encoding "native body")
#guard (step refreshState .refreshCurrentGit).map (fun s =>
  (s.publication.map (·.incoming), lookup s.memo.preferred (c 2),
    s.evidence.native.contains refreshOutput, s.createdBodies, s.evidence.sourceRoutes)) =
      .ok (some (p 71), some (p 71), true, 1, some closedSourceRoutes)
#guard step refreshState (.merge [p 4, p 70] (p 4)) =
  .error (.evidence (.nativeFact "current Git refresh not installed in action prefix"))
#guard (run refreshState [.refreshCurrentGit, .merge [p 4, p 70] (p 4)]) =
  .error (.evidence (.malformed "native merge inputs"))

-- A real changed, record-named refresh requires the preparation's captured full receipt.
private def refreshTaking : Receipt := { taking with input := refreshEvidence }
private def namedRefreshState : State :=
  { refreshState with prepared := refreshState.prepared.map fun plan =>
    { plan with inputs := { plan.inputs with receipt := some refreshTaking } } }
#guard step namedRefreshState .refreshCurrentGit = .error .custody
#guard (step { namedRefreshState with saved := { custody := refreshTaking.records } }
  .refreshCurrentGit).map (·.createdBodies) = .ok 1

end Musubi.NativeLifecycle.Test
