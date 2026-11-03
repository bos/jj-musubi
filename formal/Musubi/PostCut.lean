/-
Hub acceptance once the record list is fixed, over the complete executable recovery relation
`cexecAction`. Every hub movement then accepts a push against a ledgered supersede whose sent
dropped set is the hub's whole dropped set, and moves the head strictly along original
ancestry, with no new record. This classifies by what the push carried when it was sent, not
by its sender's current dropped set: a stale push from a node that has dropped more since
remains acceptable.

Two unledgered acceptance forms of the base model, `casAccept` and `hubPushAccept`, move the
hub with no supersede at all. The shipping hub never takes them: `hub::Push::answer` refuses a
push whose records are not the hub's before any acceptance, and the conformance harness maps
every acceptance to `hubSupAccept`. They are excluded by an explicit premise, as is rollback.

This is a statement about the finite original-operation model. Its native counterpart on the
hub's raw store, without any version-to-original projection, is listed at the end.
-/
import Musubi.ContractedRecordCut

namespace Musubi.Exec

open Musubi Contract

/-! ## The base model's hub -/

theorem execStep_parOK {N : Nat} {es es' : EState} {a : Action}
    (h : execStep N es a = .ok es') : es.parOK = true :=
  (req_ok h).1

/-- No executable action but an acceptance or a rollback moves the hub's head or sequence. -/
theorem execStep_hub_fixed {N : Nat} {es es' : EState} {a : Action}
    (h : execStep N es a = .ok es')
    (hc : ∀ n e d, a ≠ .casAccept n e d)
    (hp : ∀ n S O e d, a ≠ .hubPushAccept n S O e d)
    (hr : a.goesBack = false) :
    es'.hub.head = es.hub.head ∧ es'.hub.seq = es.hub.seq := by
  obtain ⟨-, h⟩ := req_ok h
  cases a with
  | casAccept n e d => exact absurd rfl (hc n e d)
  | hubPushAccept n S O e d => exact absurd rfl (hp n S O e d)
  | hubRegress i => simp [Action.goesBack] at hr
  | _ =>
    simp only [execCore, req] at h
    repeat' split at h
    all_goals
      first
      | (simp at h; done)
      | (cases h; simp [send_hub, EState.userOp, EState.mergeOp, EState.createOp,
          EState.setNode, EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs,
          EState.forget])

theorem execStep_hubPushAccept_guards {N : Nat} {es es' : EState} {n : Nat}
    {S O : List Nat} {e d : Nat} (h : execStep N es (.hubPushAccept n S O e d) = .ok es') :
    es.hub.head ≠ d ∧ es.hub.head = e ∧ ancB es.parF e d = true ∧
      es'.hub.head = d ∧ es'.hub.seq = es.hub.seq + 1 := by
  have hm := execStep_hubPushAccept h
  obtain ⟨-, h⟩ := req_ok h
  simp only [execCore] at h
  obtain ⟨-, h⟩ := req_ok h
  obtain ⟨hne, h⟩ := req_ok h
  obtain ⟨he, h⟩ := req_ok h
  obtain ⟨ha, -⟩ := req_ok h
  exact ⟨of_decide_eq_true hne, of_decide_eq_true he, ha, hm.2, hm.1⟩

/-! ## The premises -/

/-- An acceptance with no ledgered supersede (`casAccept`, `hubPushAccept`): never a shipping
`Push::answer` acceptance, which checks the push's records first. -/
def CAction.unledgeredAccept : CAction → Bool
  | .old (.base (.casAccept ..)) => true
  | .old (.base (.hubPushAccept ..)) => true
  | _ => false

/-! ## One step -/

/-- What one step that is neither an unledgered acceptance nor a rollback does to the hub, its
records and the supersede ledger: nothing, a ledger entry for a push about to be sent, or the
acceptance of a pushed head against a ledgered supersede. -/
inductive StepShape (N : Nat) (s t : SEState) : Prop
  | quiet (hsups : t.sups = s.sups) (hrecs : t.recs = s.recs)
      (hhead : t.es.hub.head = s.es.hub.head) (hseq : t.es.hub.seq = s.es.hub.seq)
  | send (n d : Nat) (hn : n < N) (hsups : t.sups = s.sups ++ [(n, s.appliedF n, s.nodeDF n, d)])
      (hd : d ∉ flat (s.appliedF n)) (hrecs : t.recs = s.recs)
      (hhead : t.es.hub.head = s.es.hub.head) (hseq : t.es.hub.seq = s.es.hub.seq)
  | accept (n e d : Nat) (A : List Rec) (D : List Nat)
      (hsups : t.sups = s.sups) (hrecs : t.recs = s.takeRecs D)
      (hhead : t.es.hub.head = d) (hseq : t.es.hub.seq = s.es.hub.seq + 1)
      (he : s.es.hub.head = e) (hne : e ≠ d) (hpar : ParLt s.es.parF)
      (hledger : ∃ p ∈ s.sups, p.1 = n ∧ recEq p.2.1 A = true ∧ seteq p.2.2.1 D = true ∧
        p.2.2.2 = d)
      (hrec : recEq A s.recs = true) (hpend : d ∉ pendingOf A D)
      (hcmp : Anc s.es.parF e d ∨ belowB s.es.parF (acceptDrops s A D).contains e d = true)

theorem ledger_of_any {s : SEState} {n d : Nat} {A : List Rec} {D : List Nat}
    (h : (s.sups.any fun p => p.1 == n && recEq p.2.1 A && seteq p.2.2.1 D && p.2.2.2 == d)
      = true) :
    ∃ p ∈ s.sups, p.1 = n ∧ recEq p.2.1 A = true ∧ seteq p.2.2.1 D = true ∧ p.2.2.2 = d := by
  obtain ⟨p, hp, hq⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  exact ⟨p, hp, hq.1.1.1, hq.1.1.2, hq.1.2, hq.2⟩

theorem not_mem_of_contains_false {l : List Nat} {x : Nat} (h : (!l.contains x) = true) :
    x ∉ l := by
  intro hx
  simp at h
  exact h hx

/-- A base step that neither accepts unledgered nor rolls back keeps the ledger, the records
and the hub's head and sequence. -/
theorem base_quiet {N : Nat} {s t : SEState} {b : Action}
    (h : sexecStep N s (.base b) = .ok t)
    (hu : (CAction.old (.base b)).unledgeredAccept = false)
    (hr : b.goesBack = false) : StepShape N s t := by
  obtain ⟨-, h⟩ := sreq_ok h
  simp only [sexecCore] at h
  split at h
  · cases h
  · rename_i es' hes
    split at h
    · rename_i i hi
      have := regressSeq_some hi
      subst this
      simp [Action.goesBack] at hr
    · obtain ⟨-, h⟩ := sreq_ok h
      obtain ⟨-, h⟩ := sreq_ok h
      cases h
      have hf := execStep_hub_fixed hes
        (fun n e d hb => by subst hb; simp [CAction.unledgeredAccept] at hu)
        (fun n S O e d hb => by subst hb; simp [CAction.unledgeredAccept] at hu) hr
      exact .quiet rfl rfl hf.1 hf.2

/-- Every allowed step has one of the three shapes. -/
theorem step_shape {N : Nat} {s t : SEState} {a : CAction}
    (h : cexecAction N s a = .ok t)
    (hu : a.unledgeredAccept = false) (hr : a.goesBack = false) : StepShape N s t := by
  cases a with
  | old a =>
    simp only [cexecAction, cexecStep] at h
    split at h
    · rename_i t' hs
      split at h
      · cases h
        cases a with
        | base b => exact base_quiet hs hu hr
        | abandon n D =>
          obtain ⟨-, hs⟩ := sreq_ok hs
          simp only [sexecCore] at hs
          obtain ⟨-, hs⟩ := sreq_ok hs; obtain ⟨-, hs⟩ := sreq_ok hs
          obtain ⟨-, hs⟩ := sreq_ok hs; obtain ⟨-, hs⟩ := sreq_ok hs
          cases hs
          exact .quiet rfl rfl rfl rfl
        | sendSup n d =>
          obtain ⟨-, hs⟩ := sreq_ok hs
          simp only [sexecCore] at hs
          obtain ⟨hn, hs⟩ := sreq_ok hs; obtain ⟨hd, hs⟩ := sreq_ok hs
          cases hs
          exact .send n d (of_decide_eq_true hn) rfl (not_mem_of_contains_false hd) rfl rfl rfl
        | sendD n =>
          obtain ⟨-, hs⟩ := sreq_ok hs
          simp only [sexecCore] at hs
          obtain ⟨-, hs⟩ := sreq_ok hs
          cases hs
          exact .quiet rfl rfl rfl rfl
        | adopt n R =>
          obtain ⟨-, hs⟩ := sreq_ok hs
          simp only [sexecCore] at hs
          obtain ⟨-, hs⟩ := sreq_ok hs; obtain ⟨-, hs⟩ := sreq_ok hs
          obtain ⟨-, hs⟩ := sreq_ok hs
          cases hs
          exact .quiet rfl rfl rfl rfl
        | hubSupAccept n S O e d A D =>
          obtain ⟨hok, hs⟩ := sreq_ok hs
          simp only [sexecCore] at hs
          obtain ⟨hl, hs⟩ := sreq_ok hs; obtain ⟨hrec, hs⟩ := sreq_ok hs
          obtain ⟨hdr, hs⟩ := sreq_ok hs
          split at hs
          · cases hs
          · rename_i es' hes
            obtain ⟨-, hs⟩ := sreq_ok hs
            cases hs
            obtain ⟨hne, he, ha, hh, hq⟩ := execStep_hubPushAccept_guards hes
            have hlt := parOK_parLt hok
            simp only [Bool.and_eq_true] at hdr
            refine .accept n e d A D rfl rfl hh hq he ?_ hlt (ledger_of_any hl) hrec
              (not_mem_of_contains_false hdr.2) (.inl ((ancB_iff hlt).1 ha))
            exact fun h' => hne (he.trans h')
        | hubPushRefuse n S O e d A D =>
          obtain ⟨-, hs⟩ := sreq_ok hs
          simp only [sexecCore] at hs
          obtain ⟨-, hs⟩ := sreq_ok hs; obtain ⟨-, hs⟩ := sreq_ok hs
          obtain ⟨-, hs⟩ := sreq_ok hs
          cases hs
          exact .quiet rfl rfl rfl rfl
        | prune k =>
          obtain ⟨-, hs⟩ := sreq_ok hs
          simp only [sexecCore] at hs
          obtain ⟨-, hs⟩ := sreq_ok hs; obtain ⟨-, hs⟩ := sreq_ok hs
          obtain ⟨-, hs⟩ := sreq_ok hs
          cases hs
          exact .quiet rfl rfl rfl rfl
      · cases h
    · split at h
      · split at h
        · cases h
          exact .quiet rfl rfl rfl rfl
        · cases h
      · rename_i n S O e d A D _
        split at h
        · rename_i hb
          cases h
          simp only [imageAcceptB, Bool.and_eq_true, decide_eq_true_eq] at hb
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hok, hl⟩, hrec⟩, -⟩, hpd⟩, -⟩, hne⟩, he⟩, hbel⟩, -⟩, -⟩ := hb
          refine .accept n e d A D rfl rfl ?_ ?_ he (fun h' => hne (he.trans h'))
            (parOK_parLt hok) (ledger_of_any hl) hrec (not_mem_of_contains_false hpd) (.inr hbel)
          · simp [SEState.imageAccept, SEState.supAccept, send_hub, EState.hubAccept,
              EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs]
          · simp [SEState.imageAccept, SEState.supAccept, send_hub, EState.hubAccept,
              EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs]
        · cases h
      · cases h
  | advancePrepared n R =>
    simp only [cexecAction] at h
    split at h
    · cases h
      exact .quiet rfl rfl rfl rfl
    · cases h
  | reject n S O e d A D =>
    simp only [cexecAction] at h
    split at h
    · exact base_quiet h (by simp [CAction.unledgeredAccept]) rfl
    · cases h

/-! ## The invariant -/

/-- What the classification needs of a state, and no more: record custody, a hub head the hub
has not dropped, and ledger entries consistent with their sender's records when sent. -/
structure CutInv (s : SEState) : Prop where
  ok : SEOK s
  head : s.es.hub.head ∉ s.hubDL
  ledgerApplied : ∀ p ∈ s.sups, ∀ x, x ∈ flat p.2.1 → x ∈ p.2.2.1
  ledgerHead : ∀ p ∈ s.sups, p.2.2.2 ∉ flat p.2.1

theorem cutInv_init : CutInv initSE where
  ok := seok_init
  head := by simp [initSE, initE, SEState.hubDL, flat]
  ledgerApplied := by simp [initSE]
  ledgerHead := by simp [initSE]

theorem mem_flat_of_recEq {A B : List Rec} (h : recEq A B = true) (x : Nat) :
    x ∈ flat A ↔ x ∈ flat B := by
  have e := congrFun (recEq_flat h) x
  simp only [setP] at e
  exact Iff.of_eq e

theorem mem_of_seteq {a b : List Nat} (h : seteq a b = true) (x : Nat) : x ∈ a ↔ x ∈ b := by
  have e := congrFun (seteq_setP h) x
  simp only [setP] at e
  exact Iff.of_eq e

/-- A ledgered acceptance's new head is not one the hub has dropped, nor one its push drops. -/
theorem accept_head_fresh {s : SEState} {n d : Nat} {A : List Rec} {D : List Nat}
    (hI : CutInv s)
    (hledger : ∃ p ∈ s.sups, p.1 = n ∧ recEq p.2.1 A = true ∧ seteq p.2.2.1 D = true ∧
      p.2.2.2 = d)
    (hrec : recEq A s.recs = true) (hpend : d ∉ pendingOf A D) :
    d ∉ s.hubDL ∧ d ∉ D := by
  obtain ⟨p, hp, -, hpa, -, hpd⟩ := hledger
  have hA : ∀ x, x ∈ flat A ↔ x ∈ s.hubDL := mem_flat_of_recEq hrec
  have hnot : d ∉ s.hubDL := fun hd =>
    hI.ledgerHead p hp (hpd ▸ (mem_flat_of_recEq hpa d).2 ((hA d).2 hd))
  refine ⟨hnot, fun hdD => hpend ?_⟩
  unfold pendingOf
  rw [List.mem_filter]
  refine ⟨hdD, ?_⟩
  have : d ∉ flat A := fun h => hnot ((hA d).1 h)
  simpa [List.contains_iff_mem] using this

/-- The invariant holds after every allowed step. -/
theorem cutInv_step {N : Nat} {s t : SEState} {a : CAction} (hI : CutInv s)
    (h : cexecAction N s a = .ok t)
    (hu : a.unledgeredAccept = false) (hr : a.goesBack = false) : CutInv t := by
  have hok := cexecAction_ok hI.ok h
  rcases step_shape h hu hr with
    ⟨hsups, hrecs, hhead, -⟩ | ⟨n, d, _, hsups, hd, hrecs, hhead, -⟩ |
    ⟨n, e, d, A, D, hsups, hrecs, hhead, -, -, -, -, hledger, hrec, hpend, -⟩
  · refine ⟨hok, ?_, ?_, ?_⟩
    · simpa [SEState.hubDL, hrecs, hhead] using hI.head
    · rw [hsups]; exact hI.ledgerApplied
    · rw [hsups]; exact hI.ledgerHead
  · refine ⟨hok, ?_, ?_, ?_⟩
    · simpa [SEState.hubDL, hrecs, hhead] using hI.head
    · intro p hp
      rw [hsups, List.mem_append] at hp
      rcases hp with hp | hp
      · exact hI.ledgerApplied p hp
      · rw [List.mem_singleton] at hp
        subst hp
        exact hI.ok.applied n
    · intro p hp
      rw [hsups, List.mem_append] at hp
      rcases hp with hp | hp
      · exact hI.ledgerHead p hp
      · rw [List.mem_singleton] at hp
        subst hp
        exact hd
  · refine ⟨hok, ?_, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := accept_head_fresh hI hledger hrec hpend
      intro hm
      simp only [SEState.hubDL, hrecs, hhead] at hm
      rcases (mem_takeRecs s D d).1 hm with hm | hm
      · exact h1 hm
      · exact h2 hm
    · rw [hsups]; exact hI.ledgerApplied
    · rw [hsups]; exact hI.ledgerHead

/-- **Post-cut acceptance, one step.** If the step leaves the record list as it was, the hub's
head and sequence stay; or the step accepts the push of node `n` against a ledgered supersede
of `n`'s whose sent records are the hub's, and whose sent dropped set is exactly the hub's
dropped set, whatever `n` has dropped since; and the head moves strictly up original ancestry,
with the sequence. -/
theorem post_cut_step {N : Nat} {s t : SEState} {a : CAction} (hI : CutInv s)
    (h : cexecAction N s a = .ok t)
    (hu : a.unledgeredAccept = false) (hr : a.goesBack = false)
    (hfix : t.recs = s.recs) :
    (t.es.hub.head = s.es.hub.head ∧ t.es.hub.seq = s.es.hub.seq) ∨
      ((∃ p ∈ s.sups, p.2.2.2 = t.es.hub.head ∧
          (∀ x, x ∈ flat p.2.1 ↔ x ∈ s.hubDL) ∧ (∀ x, x ∈ p.2.2.1 ↔ x ∈ s.hubDL)) ∧
        Anc s.es.parF s.es.hub.head t.es.hub.head ∧ s.es.hub.head < t.es.hub.head ∧
        t.es.hub.seq = s.es.hub.seq + 1) := by
  rcases step_shape h hu hr with
    ⟨-, -, hhead, hseq⟩ | ⟨-, -, -, -, -, -, hhead, hseq⟩ |
    ⟨n, e, d, A, D, -, hrecs, hhead, hseq, he, hne, hpar, hledger, hrec, hpend, hcmp⟩
  · exact .inl ⟨hhead, hseq⟩
  · exact .inl ⟨hhead, hseq⟩
  · right
    have hsub : ∀ x ∈ D, x ∈ s.hubDL := (takeRecs_eq_iff s D).1 (hrecs.symm.trans hfix)
    have hA : ∀ x, x ∈ flat A ↔ x ∈ s.hubDL := mem_flat_of_recEq hrec
    obtain ⟨p, hp, -, hpa, hpD, hpd⟩ := hledger
    have hanc : Anc s.es.parF e d := by
      rcases hcmp with hanc | hbel
      · exact hanc
      · have he' : (acceptDrops s A D).contains e = false := by
          cases hc : (acceptDrops s A D).contains e
          · rfl
          · have hm := List.contains_iff_mem.1 hc
            unfold acceptDrops at hm
            rcases mem_union.1 hm with hm | hm
            · exact absurd (he ▸ hm) hI.head
            · exact absurd (he ▸ hsub e hm) hI.head
        exact (belowB_survivor_iff hpar he').1 hbel
    rw [hhead, he, hseq]
    refine ⟨⟨p, hp, hpd, fun x => (mem_flat_of_recEq hpa x).trans (hA x), fun x => ?_⟩, hanc,
      Anc.lt_of_ne hpar hanc hne, rfl⟩
    constructor
    · intro hx
      exact hsub x ((mem_of_seteq hpD x).1 hx)
    · intro hx
      exact hI.ledgerApplied p hp x ((mem_flat_of_recEq hpa x).2 ((hA x).2 hx))

/-! ## Runs -/

section Run

variable {N : Nat} (run : Nat → SEState) (acts : Nat → CAction)
  (h0 : CutInv (run 0)) (hs : ∀ i, cexecAction N (run i) (acts i) = .ok (run (i + 1)))
  (hu : ∀ i, (acts i).unledgeredAccept = false) (hr : ∀ i, (acts i).goesBack = false)

include h0 hs hu hr in
theorem cutInv_run : ∀ i, CutInv (run i)
  | 0 => h0
  | i + 1 => cutInv_step (cutInv_run i) (hs i) (hu i) (hr i)

include h0 hs hu hr in
/-- After the record cut, every step keeps the hub's head and sequence, or accepts a ledgered
supersede as `post_cut_step` says. -/
theorem post_cut_run (k : Nat) (hrec : ∀ i, k ≤ i → (run i).recs = (run k).recs)
    (i : Nat) (hi : k ≤ i) :
    ((run (i + 1)).es.hub.head = (run i).es.hub.head ∧
        (run (i + 1)).es.hub.seq = (run i).es.hub.seq) ∨
      ((∃ p ∈ (run i).sups, p.2.2.2 = (run (i + 1)).es.hub.head ∧
          (∀ x, x ∈ flat p.2.1 ↔ x ∈ (run k).hubDL) ∧
          (∀ x, x ∈ p.2.2.1 ↔ x ∈ (run k).hubDL)) ∧
        Anc (run i).es.parF (run i).es.hub.head (run (i + 1)).es.hub.head ∧
        (run i).es.hub.head < (run (i + 1)).es.hub.head ∧
        (run (i + 1)).es.hub.seq = (run i).es.hub.seq + 1) := by
  have hfix : (run (i + 1)).recs = (run i).recs :=
    (hrec (i + 1) (by omega)).trans (hrec i hi).symm
  have hdl : (run i).hubDL = (run k).hubDL := by
    simp only [SEState.hubDL, hrec i hi]
  rw [← hdl]
  exact post_cut_step (cutInv_run run acts h0 hs hu hr i) (hs i) (hu i) (hr i) hfix

include h0 hs hu hr in
theorem post_cut_head_le (k : Nat) (hrec : ∀ i, k ≤ i → (run i).recs = (run k).recs)
    (i : Nat) (hi : k ≤ i) : (run i).es.hub.head ≤ (run (i + 1)).es.hub.head := by
  rcases post_cut_run run acts h0 hs hu hr k hrec i hi with h | h
  · exact Nat.le_of_eq h.1.symm
  · exact Nat.le_of_lt h.2.2.1

theorem le_sum_of_mem : ∀ {L : List Nat} {x : Nat}, x ∈ L → x ≤ L.sum
  | _ :: L, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem h
      simp only [List.sum_cons]
      omega

include h0 hs hu hr in
/-- **Stale accepts stop.** After the record cut, the hub accepts a new head that a ledger entry
already present at the cut names only finitely often: the head only grows, strictly at each
accept, and those entries name finitely many heads. A pushing node that has dropped more
since its push still has that push accepted until then; this bounds such accepts without
assuming the hub stops accepting or any node's dropped set is fixed. -/
theorem stale_accepts_stop (k : Nat) (hrec : ∀ i, k ≤ i → (run i).recs = (run k).recs) :
    ∃ k', k ≤ k' ∧ ∀ i, k' ≤ i → (run (i + 1)).es.hub.head ≠ (run i).es.hub.head →
      ∀ p ∈ (run k).sups, p.2.2.2 ≠ (run (i + 1)).es.hub.head := by
  let M := ((run k).sups.map fun p => p.2.2.2).sum
  let f := fun j => M + 1 - (run (k + j)).es.hub.head
  have hle : ∀ j, (run (k + j)).es.hub.head ≤ (run (k + j + 1)).es.hub.head :=
    fun j => post_cut_head_le run acts h0 hs hu hr k hrec (k + j) (by omega)
  obtain ⟨k0, hk0⟩ := nat_trace_stabilizes f (fun j => by
    have := hle j
    show M + 1 - (run (k + (j + 1))).es.hub.head ≤ M + 1 - (run (k + j)).es.hub.head
    rw [show k + (j + 1) = k + j + 1 by omega]
    omega)
  refine ⟨k + k0, by omega, fun i hi hmove p hp hpd => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ i by omega)
  have hlt : (run (k + j)).es.hub.head < (run (k + j + 1)).es.hub.head :=
    Nat.lt_of_le_of_ne (hle j) (Ne.symm hmove)
  have hM : (run (k + j + 1)).es.hub.head ≤ M :=
    hpd ▸ le_sum_of_mem (List.mem_map.2 ⟨p, hp, rfl⟩)
  have e1 := hk0 j (by omega)
  have e2 := hk0 (j + 1) (by omega)
  have hf : f (j + 1) < f j := by
    show M + 1 - (run (k + (j + 1))).es.hub.head < M + 1 - (run (k + j)).es.hub.head
    rw [show k + (j + 1) = k + j + 1 by omega]
    omega
  rw [e1, e2] at hf
  exact Nat.lt_irrefl _ hf

include hs hu hr in
/-- A ledger entry present at `i` but not at `k ≤ i` was appended at a step `j` in between, from
its node's records and dropped set at `j`. -/
theorem ledger_appended (k : Nat) :
    ∀ i, k ≤ i → ∀ p ∈ (run i).sups, p ∉ (run k).sups →
      ∃ j, k ≤ j ∧ j < i ∧ p.2.1 = (run j).appliedF p.1 ∧ p.2.2.1 = (run j).nodeDF p.1 ∧ p.1 < N
  | 0, hi, p, hp, hn => by
    have : k = 0 := by omega
    subst this
    exact absurd hp hn
  | i + 1, hi, p, hp, hn => by
    by_cases hk : k = i + 1
    · subst hk
      exact absurd hp hn
    have hi' : k ≤ i := by omega
    have older : p ∈ (run i).sups →
        ∃ j, k ≤ j ∧ j < i + 1 ∧ p.2.1 = (run j).appliedF p.1 ∧
          p.2.2.1 = (run j).nodeDF p.1 ∧ p.1 < N := fun hp' => by
      obtain ⟨j, h1, h2, h3, h4, h5⟩ := ledger_appended k i hi' p hp' hn
      exact ⟨j, h1, by omega, h3, h4, h5⟩
    rcases step_shape (hs i) (hu i) (hr i) with
      ⟨hsups, -, -, -⟩ | ⟨n, d, hnode, hsups, -, -, -, -⟩ | ⟨_, _, _, _, _, hsups, -⟩
    · exact older (hsups ▸ hp)
    · rw [hsups, List.mem_append] at hp
      rcases hp with hp | hp
      · exact older hp
      · rw [List.mem_singleton] at hp
        subst hp
        exact ⟨i, hi', by omega, rfl, rfl, hnode⟩
    · exact older (hsups ▸ hp)

include h0 hs hu hr in
/-- **Fresh accepts come from aligned nodes.** After the record cut, an accepted new head that no
ledger entry present at the cut names is covered by an entry appended since, from a node that
had then dropped exactly what the hub has. If that node's dropped set is fixed from the cut
on, as `node_drop_sets_eventually_stabilize` provides for each node, it is the hub's from the
cut on. -/
theorem fresh_accept_aligned (k : Nat) (hrec : ∀ i, k ≤ i → (run i).recs = (run k).recs)
    (i : Nat) (hi : k ≤ i) (hmove : (run (i + 1)).es.hub.head ≠ (run i).es.hub.head)
    (hfresh : ∀ p ∈ (run k).sups, p.2.2.2 ≠ (run (i + 1)).es.hub.head) :
    ∃ p ∈ (run i).sups, p.1 < N ∧ p.2.2.2 = (run (i + 1)).es.hub.head ∧ p ∉ (run k).sups ∧
      (∃ j, k ≤ j ∧ j < i ∧ ∀ x, x ∈ (run j).nodeDF p.1 ↔ x ∈ (run k).hubDL) ∧
      ((∀ j, k ≤ j → ∀ x, x ∈ (run j).nodeDF p.1 ↔ x ∈ (run k).nodeDF p.1) →
        ∀ x, x ∈ (run k).nodeDF p.1 ↔ x ∈ (run k).hubDL) := by
  rcases post_cut_run run acts h0 hs hu hr k hrec i hi with h | ⟨⟨p, hp, hpd, -, hpD⟩, -⟩
  · exact absurd h.1 hmove
  have hn : p ∉ (run k).sups := fun h => hfresh p h hpd
  obtain ⟨j, hj1, hj2, -, hjD, hpN⟩ := ledger_appended run acts hs hu hr k i hi p hp hn
  have hal : ∀ x, x ∈ (run j).nodeDF p.1 ↔ x ∈ (run k).hubDL := fun x => by
    rw [← hjD]; exact hpD x
  refine ⟨p, hp, hpN, hpd, hn, ⟨j, hj1, hj2, hal⟩, fun hnode x => ?_⟩
  exact (hnode j hj1 x).symm.trans (hal x)

end Run

/-! ## What this does not discharge

* The native boundary. No version-to-original projection is used or claimed. Carrying
  `post_cut_step`'s ancestry over to the shipping hub's raw store chain needs three facts about
  that store, none proved here:
  - R1: once its records stop changing, `hub::Push::answer` writes no renamed version, since it
    contracts only by drops it hasn't taken;
  - R2: with the expected head a current id the hub hasn't dropped, and every pushed drop
    already taken, `HubAdapter::descends` is ancestry in the hub store's current parent graph;
  - R3: the accepted closure is finite and acyclic. Import does not require parents to have
    been stored first, so storage order alone cannot establish that premise.
* Request correlation. The model matches an accepted push to ledger entries by node and new
  head, not by request. `fresh_accept_aligned` speaks of the entries naming that new head, not
  of which request carried which entry; production request correlation does not follow from
  it.
* The premises. No unledgered acceptance and no rollback, from the shipping hub's records check
  and the end of rollback. The record cut itself, which `cexec_record_prefix_stabilizes`
  provides under bounded drops. For alignment, a node dropped set fixed from the cut on.
* What remains. A measure for accepts of fresh pushes, whose sender may have moved on since
  sending; the alignment of nodes that do not hold the hub's records; and convergence.
-/

end Musubi.Exec
