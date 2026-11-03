/-
The hub's actual answer event in the joint system, using the packet that request carried.
The ledger's coverage theorem supplies that same packet; the hub's guards supply expected,
different target and raw ancestry. No abstract acceptance or progress event is a premise.
Coverage of the actual accepted request and the target's raw bound remain boundary laws.
-/
import Musubi.HubNodeSteps

namespace Musubi.Recovery.HubSys

open Musubi NodeSys HubSuffix

def nextHistory (g g' : Sys) (hist : Nat → Nat) : Nat → Nat :=
  if g.hub.seq < g'.hub.seq then upd hist g'.hub.seq g'.hub.head else hist

theorem anc_parents {g : Sys}
    (hdag : ∀ x, x < g.next → ∀ p ∈ g.par x, p < x)
    {a b : Nat} (h : Anc g.par a b) (hb : b < g.next) : Anc (parents g) a b := by
  induction h with
  | refl => exact Anc.refl
  | @step p x hp _ ih =>
    exact Anc.step (by simpa [parents, hb] using hp)
      (ih (Nat.lt_trans (hdag x hb p hp) hb))

theorem nextHistory_quiet {g g' : Sys} (hist : Nat → Nat) (h : g'.hub = g.hub) :
    nextHistory g g' hist = hist := by simp [nextHistory, h]

theorem nextHistory_accept {law : HubLaw} {g g' : Sys} (hist : Nat → Nat) {p : Pkt}
    (h : g'.hub = ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩) :
    nextHistory g g' hist = upd hist (g.hub.seq + 1) p.new := by
  simp [nextHistory, h]

/-- All nonaccepting decisions are frames of this view, including refusing a push with
different records. Their actual reply and queue effects are retained in the system. -/
theorem answer_frame {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {w : Nat} {g g' : Sys}
    (hs : SysStep N D law .answer g g') (hh : g'.hub = g.hub)
    (hist : Nat → Nat) (pk : List Packet) :
    HubSuffix.Step E w (view E g hist pk) (view E g' (nextHistory g g' hist) pk) := by
  cases hs with
  | answer _ _ _ _ _ _ _ hr _ =>
    apply HubSuffix.Step.frame
    · exact state_usame hr.2.1 (fun _ _ => congrFun hr.2.2.1 _)
    · exact state_hub_same hh (nextHistory_quiet hist hh)
    · intro n _; exact state_node_same (congrFun hr.1 n)
    · exact generations_same (fun n _ => congrArg NodeC.gen (congrFun hr.1 n))
    · rfl

/-- The actual accepted request, rather than a later reading of its sender, determines
the suffix's accept step. Coverage is the invariant derived from issue and request removal.
Coverage includes old packets regardless of their sender. For a fresh accepted packet,
record/drop coupling identifies the sender as eligible and the issue invariant covers it.
-/
theorem answer_step_expansion {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {w : Nat} {g g' : Sys}
    (hs : SysStep N D law .answer g g') (hist : Nat → Nat) (pk : List Packet)
    (hdag : ∀ x, x < g.next → ∀ p ∈ g.par x, p < x)
    (hbound : ∀ r ∈ g.reqs, ∀ p, r.body = .push p → p.new < g.next)
    (hcovered : ∀ r ∈ g.reqs, g'.reqs = g.reqs.erase r → ∀ p, r.body = .push p →
      law.accepts g.hub g.par p → g'.hub.seq = g.hub.seq + 1 →
      ∃ tag, packet p tag ∈ pk) :
    Nonempty (Expansion.Path (HubSuffix.Step E w) (view E g hist pk)
      (view E g' (nextHistory g g' hist) (nextLedger E g g' .answer pk))) := by
  have source := hs
  cases hs with
  | answer r ans hr _ acc hans _ hrest _ =>
    rcases hans with ⟨_, _, _, hh, _⟩ | ⟨_, _, _, hh, _⟩ | ⟨p, hp, haccept⟩
    · exact ⟨HubNodeSteps.single (answer_frame source hh hist pk)⟩
    · exact ⟨HubNodeSteps.single (answer_frame source hh hist pk)⟩
    · rcases haccept with ⟨ha, _, hh, _, _⟩ | ⟨_, _, _, _, hh, _⟩ | ⟨_, _, _, _, hh, _⟩
      · obtain ⟨tag, hpk⟩ := hcovered r hr ‹g'.reqs = g.reqs.erase r› p hp ha
          (congrArg Snap.seq hh)
        obtain ⟨_, he, hne, hanc, _⟩ := law.guards g.hub g.par p ha
        apply Nonempty.intro
        apply HubNodeSteps.single
        apply HubSuffix.Step.accept
          (g := view E g hist pk) (g' := view E g' (nextHistory g g' hist) pk)
          (packet p tag) hpk he hne
          (anc_parents hdag hanc (hbound r hr p hp))
        · exact state_usame hrest.2.1 (fun _ _ => congrFun hrest.2.2.1 _)
        · exact congrArg Snap.head hh
        · exact congrArg Snap.seq hh
        · exact nextHistory_accept hist hh
        · intro n _; exact state_node_same (congrFun hrest.1 n)
        · exact generations_same (fun n _ => congrArg NodeC.gen (congrFun hrest.1 n))
        · rfl
      · exact ⟨HubNodeSteps.single (answer_frame source hh hist pk)⟩
      · exact ⟨HubNodeSteps.single (answer_frame source hh hist pk)⟩

end Musubi.Recovery.HubSys
