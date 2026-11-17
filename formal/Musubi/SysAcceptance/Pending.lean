/-
Raw control cannot remain pending once the hub and its records have settled. The interfaces
live in `Pending.Contracts`; the proof here separates publication impossibility from the
control argument that eventually forces a push.
-/
import Musubi.SysAcceptance.Pending.Contracts

namespace Musubi.SysAcceptance

open Musubi NodeSettle EarlyEntry NodeSys NodeSysEntry SysFreshCuts EarlyEntry.Control

/-- The hub does not drop the head a push sends: it is no dropped name, no cached renaming key,
and not among the push's own drops. -/
theorem not_dropped_of {named cached : Nat → Bool} {x : Nat} {dropped : List Nat}
    (hnn : named x = false) (hnc : cached x = false) (hnot : x ∉ dropped) :
    ((named x || cached x) || decide (x ∈ dropped)) = false := by
  simpa [hnn, hnc] using hnot

/-- A head fixed by a renaming function is no cached key if every cached key changes under
that function. Together with exclusion from named and pending drops, this suffices for the
hub's dropped-head check. -/
theorem not_dropped_fixed {cur : Nat → List Nat} {named cached : Nat → Bool} {x : Nat}
    {dropped : List Nat} (hren : ∀ y, cached y = true → cur y ≠ [y]) (hfix : cur x = [x])
    (hnn : named x = false) (hnot : x ∉ dropped) :
    ((named x || cached x) || decide (x ∈ dropped)) = false := by
  cases hc : cached x
  · simpa [hnn] using hnot
  · exact absurd hfix (hren x hc)

/-- No round remains pending on a stable hub. A push would pass the publication checks and
move the hub; every other allowed action continues the round. Naming therefore stabilizes
inside that round, after which the checked calls force a push, giving a contradiction.

The survival interface is derived from native naming at the application boundary. Stability
through actual pushes and successful object replies are supplied separately, after their cuts.
The abstract round keeps the generality of independent raw and executable packet readings. -/
theorem no_forever_pending {ρ α : Type} [DecidableEq ρ] {hub : RawPublish.Hub}
    {R : PendingRun ρ α} (control : PendingControl hub R)
    (publication : PendingPublication hub R) (survival : PendingSurvival hub R)
    (h0 : R.active 0 = true)
    (hstable : ∀ i, R.active i = true → R.choice hub i = .push →
      RawPublish.after hub (R.pkt i) (R.checks i) = hub)
    (hserve : ∀ i, R.active i = true → ¬ R.failed i) : False := by
  -- a push at a step of the round has the hub accept it, so the hub would move
  have nopush : ∀ i, R.active i = true →
      rawControl R.raw (R.naming.images i) R.par R.anc hub.head (R.run i) (R.prims i) ≠ .push := by
    intro i hact hpush
    have hi : choose (rawReads R.raw (R.naming.images i) R.par R.anc hub.head
        (R.run i) (R.prims i)) = .push := hpush
    obtain ⟨hdesc, -, -⟩ := choose_push hi
    obtain ⟨-, -, hd, hp, hn⟩ := control.hguard i hact
    obtain ⟨he, hnk, hpend, habove⟩ := publication.hpkt i hact hpush
    have b : RawPublish.PendingPush (hub.seq, hub.head) (R.pkt i) := by
      refine ⟨he, ?_, ?_⟩
      · intro h
        rw [hn] at hnk
        exact absurd (decide_eq_true h) (by rw [← hnk]; exact Bool.false_ne_true)
      · intro h
        rw [hp, h] at hpend
        cases hpend
    have heq : R.current = R.offered i := by
      have hdi := publication.hdiffer i hact hpush
      rw [publication.hheard i hact hpush, hd] at hdi
      simp only at hdi
      cases h : decide (R.current = R.offered i)
      · rw [h] at hdi; cases hdi
      · exact of_decide_eq_true h
    have hr : (R.checks i).recordsMatch = true := by
      rw [publication.hmatch i hact hpush]
      exact decide_eq_true heq.symm
    -- the hub does not drop the sent head: no name, no cached key, not among its own drops
    have normalBody := publication.hwitness i hact hpush
    have notNamed := survival.hsurvive i hact hpush heq.symm _ normalBody
    have notCached := survival.hnoCache i hact hpush heq.symm _ normalBody
    have hnd : (R.checks i).dropped = false :=
      (publication.hdroppedB i hact hpush).trans
        (not_dropped_of notNamed notCached (publication.hassert i hact hpush))
    -- the sender's cache covers what the hub lacks of the uploaded packet
    have uploaded := Exec.packet_upload_closes_split (publication.hparF i hact hpush)
      (publication.hbases i hact hpush) (publication.hretained i hact hpush)
      (publication.hcovers i hact hpush)
    have hcl : (R.checks i).closed = true := by
      rw [publication.hclosedB i hact hpush, uploaded, publication.hvalid i hact hpush]
      rfl
    have hdescends : (R.checks i).descends = true := by
      rw [publication.hname i hact hpush]
      change (!(R.naming.images i).isEmpty && (R.run i).burst.heads.any fun h =>
        (R.naming.images i).all fun j => R.anc j h) = true at hdesc
      simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hdesc ⊢
      obtain ⟨hne, h, hh, hall⟩ := hdesc
      exact ⟨hne, fun x hx => control.trans x h _ (hall x hx) (habove h hh)⟩
    exact RawPublish.stable_no_pendingPush b rfl hr hnd hcl hdescends (hstable i hact hpush)
  -- so the round never ends: each of its steps is a burst step or a call, which goes on with it
  have hall : ∀ i, R.active i = true := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih =>
      obtain ⟨ha, hdh, hd, hp, hn⟩ := control.hguard i ih
      apply control.hnext i ih
      rcases rawControl_guarded (images := R.naming.images i) (anc := R.anc) (s := R.run i) (q := R.prims i)
          control.hlt control.hraw ha hdh hd hp hn with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hserve i ih⟩)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact absurd h (nopush i ih)
  -- the hub stays, so does the known head: naming settles, at a step derived here
  obtain ⟨T, hT⟩ := R.naming.settles control.hnaming hall
  have hwalk : ∀ (s : Control.State) x,
      Walk (rawSurvey surveyBase R.par s.burst.loc s.stg s.obj hub.head) x → x ∈ R.raw :=
    fun _ _ hw => walk_mem control.hraw hw
  have himg : ∀ j, R.naming.images (T + j) = R.naming.images T := fun j => (hT (T + j) (by omega)).2
  have hst : ∀ j, R.naming.Still (T + j) := fun j => (hT (T + j) (by omega)).1
  obtain ⟨j, hj⟩ := pending_push_reached R.raw (R.naming.images T) R.anc control.trans
    (fun j => R.run (T + j)) (fun j => R.after (T + j))
    (fun j => rawReads R.raw (R.naming.images T) R.par R.anc hub.head (R.run (T + j)) (R.prims (T + j)))
    (fun j => control.hframe (T + j) (hall _) (hall _) (hst j))
    (fun j => control.hguard (T + j) (hall _))
    (fun j => rawReads_survey control.hlt control.hraw)
    (fun j hc => by
      have hc' : rawControl R.raw (R.naming.images (T + j)) R.par R.anc hub.head (R.run (T + j))
          (R.prims (T + j)) = .merge ∨
          rawControl R.raw (R.naming.images (T + j)) R.par R.anc hub.head (R.run (T + j))
            (R.prims (T + j)) = .realize ∨
          rawControl R.raw (R.naming.images (T + j)) R.par R.anc hub.head (R.run (T + j))
            (R.prims (T + j)) = .advance := by
        rw [himg j]; exact hc
      obtain ⟨k, hk⟩ := control.hburst (T + j) (hall _) (hst j) hc'
      rw [himg j] at hk
      simp only [callB, Bool.and_eq_true] at hk
      exact ⟨Burst.stepB_sound hk.2, growsB_sound hk.1⟩)
    (fun j hc => by
      rcases hc with hc | hc
      · have hc' : rawControl R.raw (R.naming.images (T + j)) R.par R.anc hub.head (R.run (T + j))
            (R.prims (T + j)) = .fetch := by rw [himg j]; exact hc
        obtain ⟨hs, hh, hp, hg⟩ := control.hfetch (T + j) (hall _) (hst j) hc'
        exact fetch_call (base := surveyBase)
          ((missOpsB_iff control.hlt control.hraw).1 (choose_fetch_missOps hc))
          (hwalk (R.run (T + j))) hs hh hp (growsB_sound hg)
      · have hc' : rawControl R.raw (R.naming.images (T + j)) R.par R.anc hub.head (R.run (T + j))
            (R.prims (T + j)) = .objects := by rw [himg j]; exact hc
        obtain ⟨hb, hh, hp, hg⟩ :=
          (control.hobjects (T + j) (hall _) (hst j) hc').resolve_left (hserve _ (hall _))
        exact objects_call (base := surveyBase)
          ((missObjsB_iff control.hlt control.hraw).1 (choose_objects_missObjs hc)) (hwalk (R.run (T + j)))
          (fun x hw => hb x ((walkB_iff control.hlt).2 hw)) hh hp (growsB_sound hg))
  have hpush : rawControl R.raw (R.naming.images (T + j)) R.par R.anc hub.head (R.run (T + j))
      (R.prims (T + j)) = .push := by
    show choose _ = _
    rw [himg j]; exact hj
  exact nopush (T + j) (hall _) hpush


/-- Native source laws supply the control and publication interfaces, and derive survival.
On a hub stable through its actual pushes, with successful object replies, the round cannot
remain pending. -/
theorem PendingLaws.absurd {ρ α : Type} [DecidableEq ρ] {hub : RawPublish.Hub}
    {d : PendingData ρ α} (L : PendingLaws hub d) (h0 : d.active 0 = true)
    (hstable : ∀ i, d.pushes i → RawPublish.after hub (d.pkt i) (d.checks i) = hub)
    (hserve : ∀ i, d.active i = true → ¬ d.failed i) : False :=
  no_forever_pending L.toPendingControl L.toPendingPublication
    { hnoCache := L.hnoCacheOf, hsurvive := L.hsurviveOf }
    h0 (fun i active push => hstable i (L.hsend i active push)) hserve

end Musubi.SysAcceptance
