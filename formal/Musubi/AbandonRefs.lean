/-
The boundary between original operations, contracted survivors and one remote ref. This is
not another network model: Supersede handles record delivery. Here a delivered dropped set
renames *the current heads*, including work published since preparation, before realization
is merged and published. Expected values are snapshots, not recomputed from contracted parents.
-/
import Musubi.Contract
import Musubi.ExecSound
import Musubi.Refs

namespace Musubi.AbandonRefs

open Contract Refs

/-- Original-operation names are ghost identities. Actual names are `Contract.cid` under
the party's dropped set. Expanding a dropped head retains every surviving branch below it. -/
def candidates (par : Nat → List Nat) (D : Nat → Bool) (heads : List Nat)
    (incoming : Nat) : List Nat := incoming :: heads.flatMap (exp par D)

/-- `taken_beside` and `switch_to_taken`: normalize before deciding what is concurrent. -/
def takeHeads (par : Nat → List Nat) (D : Nat → Bool) (heads : List Nat)
    (incoming : Nat) : List Nat := Exec.maxL (cpar par D) (candidates par D heads incoming)

/-- The original-operation abstraction is unambiguous, even across different dropped sets.
This is the immutable-content premise enforced by original identity validation (#73). -/
theorem abstraction_unique {par : Nat → List Nat} (hlt : ParLt par)
    {content : Nat → Nat} (hi : Function.Injective content) {D E : Nat → Bool} {x y : Nat}
    (h : cid content par D x = cid content par E y) : x = y :=
  (cid_eq hlt hi h).1

/-- Preparing an old record prefix and then the rest has the same canonical names as
adopting their union. This is about graph contraction, not ordered-record liveness (#75). -/
theorem adoption_composes {par : Nat → List Nat} (hlt : ParLt par)
    (content : Nat → Nat) (D E : Nat → Bool) (x : Nat) :
    cid content (cpar par D) E x = cid content par (union D E) x :=
  cid_union hlt D E x

/-- Every element of a finite candidate list is below a maximal candidate. -/
theorem max_covers {par : Nat → List Nat} (hlt : ParLt par) (xs : List Nat)
    {a : Nat} (ha : a ∈ xs) : ∃ h ∈ Exec.maxL par xs, Anc par a h := by
  let ys := xs.filter (fun b => Exec.ancB par a b)
  have hay : a ∈ ys := by simp [ys, ha, Exec.ancB_iff hlt, Anc.refl]
  let h := ys.max (List.ne_nil_of_mem hay)
  have hh := List.mem_filter.1 (List.max_mem (List.ne_nil_of_mem hay))
  have hah := (Exec.ancB_iff hlt).1 hh.2
  refine ⟨h, ?_, hah⟩
  have he := congrFun (Exec.setP_maxL hlt xs) h
  apply (Iff.of_eq he).mpr
  refine ⟨hh.1, fun y hy hhy => ?_⟩
  exact Nat.le_antisymm (hhy.le hlt)
    (List.le_max_of_mem (l := ys)
      (List.mem_filter.2 ⟨hy, (Exec.ancB_iff hlt).2 (hah.trans hhy)⟩))

/-- Record adoption, incoming realization and merge publication preserve *every* surviving
ancestor of the old published heads, including a head arriving after record preparation.
Only the merge is fresh; realization and renaming allocate no original-operation identity. -/
theorem publish_retains {par : Nat → List Nat} {D : Nat → Bool} (hlt : ParLt par)
    {heads : List Nat} {incoming fresh : Nat}
    (hf : ∀ p ∈ takeHeads par D heads incoming, p < fresh)
    {a h : Nat} (hh : h ∈ heads) (ha : Anc par a h) (hD : D a = false) :
    Anc (upd (cpar par D) fresh (takeHeads par D heads incoming)) a fresh := by
  obtain ⟨p, hp, hap⟩ := exp_covers hlt ha hD
  have hp' : p ∈ candidates par D heads incoming :=
    List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨h, hh, hp⟩)
  obtain ⟨q, hq, hpq⟩ := max_covers (parLt_cpar hlt) _ hp'
  exact (anc_upd_new (parLt_cpar hlt) hf).2
    (Or.inr ⟨q, hq, ((anc_cpar_iff hlt hD).2 hap).trans hpq⟩)

variable {T : Type} [DecidableEq T] [RefAlg T] [Sides T]

/-- Ref data is attached to an original operation. Rewrites preserve the local slot;
expected values are saved snapshots rather than inferred again from contracted parents. -/
structure Payload (T : Type) where
  slot : Slot T
  expected : T

structure History (T : Type) where
  next : Nat
  par : Nat → List Nat
  dropped : Nat → Bool
  heads : List Nat
  incoming : Nat
  refs : Nat → Payload T
  git : T

namespace History

def own (h : History T) : Nat := h.heads.headD h.incoming

def parents (h : History T) : List Nat := takeHeads h.par h.dropped h.heads h.incoming

/-- Compute common bases after contraction. The one-ref boundary requires one maximal base;
multiple bases require jj's merge of bases, outside this model. -/
def bases (h : History T) : List Nat :=
  let cp := cpar h.par h.dropped
  Exec.maxL cp ((List.range h.next).filter fun x =>
    !h.dropped x && Exec.ancB cp x h.incoming && Exec.ancB cp x h.own)

def current (h : History T) : CMachine T :=
  ⟨⟨(h.refs h.own).slot, h.git, false⟩, (h.refs h.own).expected⟩

def realized (h : History T) : CMachine T :=
  let incoming := h.refs h.incoming
  realizeBesideRemote incoming.slot.L incoming.slot.R incoming.expected
    (h.refs (h.bases.headD 0)).slot h.current

def merged (h : History T) (first : Bool) : CMachine T :=
  let w := h.realized
  let b := (h.refs (h.bases.headD 0)).slot
  { w with v := Slot.mergeBeside first b h.current.v w.v }

/-- Install the merged slot and expectation at the newly published original identity. -/
def publish (h : History T) (first : Bool) (mergeExpected : T) : History T × CMachine T :=
  let m := exportC mergeExpected (h.merged first)
  ({ h with next := h.next + 1,
            par := upd (cpar h.par h.dropped) h.next h.parents,
            heads := [h.next], git := m.G,
            refs := upd (upd h.refs h.incoming ⟨h.realized.v, h.realized.E⟩)
              h.next ⟨m.v, m.E⟩ }, m)

/-- Install a saved pre-abandon expectation in a fresh fix-up. The parent can have a different
inferred expectation in the shortened history; the saved value overrides that inference. -/
def fixup (h : History T) (head : Nat) (saved : T) : History T :=
  { h with next := h.next + 1, par := upd h.par h.next [head], heads := [h.next],
           refs := upd h.refs h.next ⟨(h.refs head).slot, saved⟩ }

end History

/-- The returned graph-indexed state observes the same exported ref state as the machine. -/
theorem publish_current (h : History T) (first : Bool) (e : T) (hs : CInv h.current) :
    (h.publish first e).1.current = (h.publish first e).2 := by
  have hx : ∀ (m : CMachine T) (e : T), (exportC e m).moved = m.moved := by
    intro m e
    unfold exportC exportConflicted exportRemote
    split <;> split <;> rfl
  have hm : (exportC e (h.merged first)).moved = false := by
    rw [hx]
    exact (realizeBesideRemote_cases (h.refs h.incoming).slot.L
      (h.refs h.incoming).slot.R (h.refs h.incoming).expected
      (h.refs (h.bases.headD 0)).slot hs).1
  have heq : ∀ m : CMachine T, m.moved = false →
      (⟨⟨m.v, m.G, false⟩, m.E⟩ : CMachine T) = m := by
    intro ⟨⟨v, g, moved⟩, expected⟩ hm
    cases hm
    rfl
  simpa [History.publish, History.current, History.own] using heq _ hm

/-- The combined boundary uses operation-indexed payloads and the normalized graph's base.
Every surviving branch remains, the ref action is a CStep, and the new published identity
carries exactly the resulting slot and expectation. Expected-value derivation remains #76. -/
theorem publish_refines (h : History T) (first : Bool) (e : T)
    (hlt : ParLt h.par) (hf : ∀ p ∈ h.parents, p < h.next)
    {base : Nat} (hb : h.bases = [base]) (hs : CInv h.current)
    (hre : RefAlg.resolved (h.merged first).v.R = true → e = (h.merged first).v.R)
    (he : e = (h.merged first).G ∨ RefAlg.writable e = true) :
    let (t, m) := h.publish first e
    (∀ a head, head ∈ h.heads → Anc h.par a head → h.dropped a = false →
      Anc t.par a h.next) ∧ CInv m ∧ CStep h.current m ∧ t.heads = [h.next] ∧
    (t.refs h.next).slot = m.v ∧ (t.refs h.next).expected = m.E ∧
    (h.refs (h.bases.headD 0)).slot = (h.refs base).slot ∧ t.current = m := by
  have href : CStep h.current (exportC e (h.merged first)) := by
    exact CStep.beside h.current first (h.refs h.incoming).slot.L
      (h.refs h.incoming).slot.R (h.refs h.incoming).expected e
      (h.refs (h.bases.headD 0)).slot hre he
  exact ⟨fun _ _ hh ha hd => publish_retains hlt hf hh ha hd,
    href.inv hs, href, rfl, by simp, by simp,
    by simp [hb], publish_current h first e hs⟩

omit [DecidableEq T] [RefAlg T] [Sides T] in
theorem fixup_retains (h : History T) (hlt : ParLt h.par) {head : Nat}
    (hf : head < h.next) (saved : T) {a : Nat} (ha : Anc h.par a head) :
    let t := h.fixup head saved
    Anc t.par a h.next ∧ (t.refs h.next).slot = (h.refs head).slot ∧
      (t.refs h.next).expected = saved ∧ t.heads = [h.next] := by
  exact ⟨(anc_upd_new hlt (by simpa using hf)).2 (Or.inr ⟨head, by simp, ha⟩),
    by simp [History.fixup], by simp [History.fixup], rfl⟩

end Musubi.AbandonRefs
