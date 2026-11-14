/-
Executable model examples, not native evidence or Rust correspondence. They pin observable
decision differences: second-name overlap, concrete versus erased work, physical aliases,
record custody, stale captures and the separate schedule restrictions of accepted #149 v2.
-/
import Musubi.NativeLifecycle
import Musubi.NativeLifecycle.ConstructionSound

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
  .ok ⟨[p 0], []⟩
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

end Musubi.NativeLifecycle.Test
