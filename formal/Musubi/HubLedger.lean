/-
The packet ledger of the joint system. It retains immutable request fields, not a later
reading of a sender's state. Initial requests have no current generation. Every later
eligible push is recorded with its actual send generation; noneligible requests need not
be recorded once the record/drop cut excludes their acceptance.
-/
import Musubi.HubSys

namespace Musubi.Recovery.HubSys

open Musubi NodeSys HubSuffix

def collectPackets (tag : Pkt → Option Nat) (reqs : List Req) : List Packet :=
  reqs.filterMap fun r => match r.body with
    | .push p => some (packet p (tag p))
    | _ => none

theorem collect_has (tag : Pkt → Option Nat) {reqs : List Req} {r : Req} {p : Pkt}
    (hr : r ∈ reqs) (hp : r.body = .push p) : packet p (tag p) ∈ collectPackets tag reqs := by
  apply List.mem_filterMap.2
  exact ⟨r, hr, by simp [hp]⟩

def Covers (E : Nat → Prop) (g : Sys) (pk : List Packet) : Prop :=
  ∀ r ∈ g.reqs, ∀ p, r.body = .push p → E p.node → ∃ tag, packet p tag ∈ pk

theorem collect_covers (E : Nat → Prop) (g : Sys) : Covers E g (collectPackets (fun _ => none) g.reqs) :=
  fun _ hr _ hp _ => ⟨none, collect_has (fun _ => none) hr hp⟩

theorem covers_subset {E : Nat → Prop} {g g' : Sys} {pk : List Packet}
    (hc : Covers E g pk) (hr : ∀ r, r ∈ g'.reqs → r ∈ g.reqs) : Covers E g' pk :=
  fun r hm p hp he => hc r (hr r hm) p hp he

theorem bodies_push_owner {n gen : Nat} {post σ : NodeSettle.NS} {emb : Nat → Nat}
    {new : Nat} {k : Kind} {rq : List Req}
    (hb : Bodies σ k (pkt n gen post emb new) (rq.map Req.body))
    {r : Req} (hr : r ∈ rq) {p : Pkt} (hp : r.body = .push p) : p.node = n := by
  have hm : Body.push p ∈ rq.map Req.body := List.mem_map.2 ⟨r, hr, hp⟩
  cases k <;> simp only [Bodies] at hb
  · rw [hb] at hm; simp at hm
  · rcases hb with ⟨_, hb⟩ | ⟨_, hb⟩ <;> rw [hb] at hm <;> simp at hm
  · rw [hb] at hm; simp at hm
  · rw [hb] at hm; simp at hm
  · rw [hb] at hm
    have he : p = pkt n gen post emb new := by simpa using hm
    exact congrArg Pkt.node he
  · rw [hb] at hm; simp at hm

noncomputable def nextLedger (E : Nat → Prop) (g g' : Sys) (act : Act)
    (pk : List Packet) : List Packet := by
  classical
  exact match act with
    | .issue n _ => if E n then
        collectPackets (fun p => some p.gen) (g'.reqs.drop g.reqs.length) ++ pk else pk
    | _ => pk

theorem covers_issue {E : Nat → Prop} {g g' : Sys} {n gen : Nat}
    {post σ : NodeSettle.NS} {emb : Nat → Nat} {new : Nat} {k : Kind} {rq : List Req}
    {pk : List Packet} (hc : Covers E g pk) (hr : g'.reqs = g.reqs ++ rq)
    (hb : Bodies σ k (pkt n gen post emb new) (rq.map Req.body)) :
    Covers E g' (nextLedger E g g' (.issue n k) pk) := by
  classical
  intro r hm p hp he
  rw [hr, List.mem_append] at hm
  by_cases hn : E n
  · simp only [nextLedger, hn, ↓reduceIte, hr, List.drop_left] -- retain the exact new request fields
    rcases hm with hm | hm
    · obtain ⟨tag, ht⟩ := hc r hm p hp he
      exact ⟨tag, List.mem_append_right _ ht⟩
    · exact ⟨some p.gen, List.mem_append_left _ (collect_has (fun q => some q.gen) hm hp)⟩
  · simp only [nextLedger, hn, ↓reduceIte]
    rcases hm with hm | hm
    · exact hc r hm p hp he
    · exact False.elim (hn ((bodies_push_owner hb hm hp) ▸ he))

/-- Coverage is derived from the actual request-list changes of every system event. It is
not a premise that an accepted packet happens to occur in an unrelated abstract ledger. -/
theorem covers_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : NodeSys.HubLaw}
    {E : Nat → Prop} {g g' : Sys} {act : Act} {pk : List Packet}
    (hc : Covers E g pk) (hs : SysStep N D law act g g') :
    Covers E g' (nextLedger E g g' act pk) := by
  cases hs with
  | issue _ _ _ _ _ _ _ _ _ hb _ _ _ hr _ _ _ _ => exact covers_issue hc hr hb
  | answer _ _ _ hr _ _ _ _ _ =>
    apply covers_subset hc
    intro r hm
    rw [hr] at hm
    exact List.mem_of_mem_erase hm
  | busy _ _ _ _ _ _ _ _ hq _ | idle _ _ _ _ _ _ _ hq _ =>
    exact covers_subset hc (fun r hm => hq.reqs ▸ hm)
  | maint _ _ _ _ _ _ _ _ _ _ hq _ | env _ _ hq _ =>
    exact covers_subset hc (fun r hm => hq.reqs ▸ hm)
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ =>
    exact covers_subset hc (fun r hm => hr.2.1 ▸ hm)
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ =>
    exact covers_subset hc (fun r hm => hr.2.1 ▸ hm)
  | ignore _ _ _ _ _ _ _ _ _ hr _ =>
    exact covers_subset hc (fun r hm => hr.2.1 ▸ hm)

noncomputable def ledger (E : Nat → Prop) (run : Nat → Sys) (acts : Nat → Act) :
    Nat → List Packet
  | 0 => collectPackets (fun _ => none) (run 0).reqs
  | i + 1 => nextLedger E (run i) (run (i + 1)) (acts i) (ledger E run acts i)

theorem nextLedger_keeps {E : Nat → Prop} {g g' : Sys} {act : Act} {pk : List Packet}
    {p : Packet} (hp : p ∈ pk) : p ∈ nextLedger E g g' act pk := by
  classical
  cases act <;> try exact hp
  case issue n k =>
    by_cases hn : E n
    · simp only [nextLedger, hn, ↓reduceIte]
      exact List.mem_append_right _ hp
    · simpa [nextLedger, hn] using hp

theorem ledger_keeps_initial (E : Nat → Prop) (run : Nat → Sys) (acts : Nat → Act)
    {r : Req} (hr : r ∈ (run 0).reqs) {p : Pkt} (hp : r.body = .push p) :
    ∀ i, packet p none ∈ ledger E run acts i := by
  intro i
  induction i with
  | zero => exact collect_has (fun _ => none) hr hp
  | succ i ih => exact nextLedger_keeps ih

theorem ledger_covers {N : Nat} {D : Nat → Nat → Nat → Prop} {law : NodeSys.HubLaw}
    (E : Nat → Prop) (run : Nat → Sys) (acts : Nat → Act)
    (hs : ∀ i, SysStep N D law (acts i) (run i) (run (i + 1))) :
    ∀ i, Covers E (run i) (ledger E run acts i) := by
  intro i
  induction i with
  | zero => exact collect_covers E (run 0)
  | succ i ih => exact covers_step ih (hs i)

end Musubi.Recovery.HubSys
