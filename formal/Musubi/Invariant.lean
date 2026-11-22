/-
The inductive invariant of the asynchronous model, and basic consequences.
-/
import Musubi.Model

namespace Musubi

/-- What a `Cas(_, d)` from node `n`, alone or in a `push`, guarantees: `d` is in `anc*` of
one of the node's heads, or accepted. -/
def CasOK (s : State) (n d : Nat) : Prop :=
  (∃ h, (s.node n).heads h ∧ Anc s.U.par d h) ∨ Anc s.U.par d s.hub.head

/-- What every in-flight message guarantees. -/
def MsgOK (s : State) : Msg → Prop
  | .getOps _ S => ∀ x, S x → Anc s.U.par x s.hub.head
  | .ops _ S => ∀ x, S x → Anc s.U.par x s.hub.head
  | .cas n _ d => CasOK s n d
  | .push n _ _ _ d => CasOK s n d
  | .head _ _ sq h => sq ≤ s.hub.seq ∧ s.hub.hist sq = h
  | _ => True

/-- Node `n`'s `known` is a head in the hub's current history, at its sequence number. -/
def Consistent (s : State) (n : Nat) : Prop :=
  (s.node n).known.seq ≤ s.hub.seq ∧ s.hub.hist (s.node n).known.seq = (s.node n).known.head

/-- What every state satisfies, whether or not the hub can go back to an earlier head: the
universe is a DAG rooted at `root`; the hub's history ends in its head, and the hub holds that head's closure (`hubClosed`: every ancestor
of it, with its objects); and every node's repository is closed under parents, with a nonempty
antichain of heads. -/
structure Base (N : Nat) (s : State) : Prop where
  -- universe
  parLt : ParLt s.U.par
  nextPos : 0 < s.U.next
  rootAnc : ∀ x, x < s.U.next → Anc s.U.par root x
  creatorSome : ∀ x, 0 < x → x < s.U.next → ∃ n, n < N ∧ s.U.creator x = some n
  creatorRoot : s.U.creator root = none
  -- hub
  headLt : s.hub.head < s.U.next
  histHead : s.hub.hist s.hub.seq = s.hub.head
  hist0 : s.hub.hist 0 = root
  hubClosed : ClosedAt s s.hub.head
  -- nodes
  lroot : ∀ n, (s.node n).lops root
  lLt : ∀ n x, (s.node n).lops x → x < s.U.next
  lParents : ∀ n x p, (s.node n).lops x → p ∈ s.U.par x → (s.node n).lops p
  lObjs : ∀ n x o, (s.node n).lops x → o ∈ s.U.objs x → (s.node n).lobj o
  headsLocal : ∀ n x, (s.node n).heads x → (s.node n).lops x
  headsAnti : ∀ n x y, (s.node n).heads x → (s.node n).heads y → Anc s.U.par x y → x = y
  headsNonempty : ∀ n, ∃ h, (s.node n).heads h

/-- `Base`, with the hub's history a chain of heads in original ancestry, and every operation
a node made below one of its heads. The first fails once the hub can go back. -/
structure Core (N : Nat) (s : State) : Prop extends Base N s where
  histStep : ∀ i, i < s.hub.seq →
    Anc s.U.par (s.hub.hist i) (s.hub.hist (i + 1)) ∧ s.hub.hist i ≠ s.hub.hist (i + 1)
  ownInHeads : ∀ n x, x < s.U.next → s.U.creator x = some n →
    ∃ h, (s.node n).heads h ∧ Anc s.U.par x h

namespace Base

variable {N : Nat} {s : State}

theorem accLt (hI : Base N s) {x : Nat} (h : Anc s.U.par x s.hub.head) : x < s.U.next :=
  Nat.lt_of_le_of_lt (h.le hI.parLt) hI.headLt

theorem headsLt (hI : Base N s) {n x : Nat} (h : (s.node n).heads x) : x < s.U.next :=
  hI.lLt n x (hI.headsLocal n x h)

theorem lopsAnc (hI : Base N s) {n x a : Nat} (hx : (s.node n).lops x)
    (ha : Anc s.U.par a x) : (s.node n).lops a :=
  Anc.closed (S := (s.node n).lops) (fun y p hy hp => hI.lParents n y p hy hp) ha hx

end Base

namespace Core

variable {N : Nat} {s : State}

theorem chain (hI : Core N s) {i j : Nat} (hij : i ≤ j) (hj : j ≤ s.hub.seq) :
    Anc s.U.par (s.hub.hist i) (s.hub.hist j) := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Anc.refl
  | succ j ih =>
    by_cases h : i = j + 1
    · subst h; exact Anc.refl
    · exact (ih (by omega) (by omega)).trans (hI.histStep j (by omega)).1

theorem histAnc (hI : Core N s) {i : Nat} (hi : i ≤ s.hub.seq) :
    Anc s.U.par (s.hub.hist i) s.hub.head := by
  have := hI.chain hi (Nat.le_refl _)
  rwa [hI.histHead] at this

theorem histLt (hI : Core N s) {i : Nat} (hi : i ≤ s.hub.seq) : s.hub.hist i < s.U.next :=
  hI.accLt (hI.histAnc hi)

/-- History is strictly increasing in id order. -/
theorem histLtStrict (hI : Core N s) {i j : Nat} (hij : i < j) (hj : j ≤ s.hub.seq) :
    s.hub.hist i < s.hub.hist j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hs := hI.histStep j (by omega)
    have h1 : s.hub.hist j < s.hub.hist (j + 1) := hs.1.lt_of_ne hI.parLt hs.2
    by_cases h : i = j
    · subst h; exact h1
    · exact Nat.lt_trans (ih (by omega) (by omega)) h1

theorem histInj (hI : Core N s) {i j : Nat} (hi : i ≤ s.hub.seq) (hj : j ≤ s.hub.seq)
    (h : s.hub.hist i = s.hub.hist j) : i = j := by
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have := hI.histLtStrict hlt hj; omega
  · exact heq
  · have := hI.histLtStrict hgt hi; omega

end Core

/-- The inductive invariant: `Core`, plus `known` (each node's known head is in the hub's
current history), cross-cutting properties of the nodes' operations and heads relative to the
hub's head and history, ghost records of where merges were made, and a guarantee for every
in-flight message. -/
structure Inv (N : Nat) (s : State) : Prop extends Core N s where
  known : ∀ n, Consistent s n
  -- cross-cutting
  locality : ∀ n x, (s.node n).lops x → s.U.creator x = some n ∨ Anc s.U.par x s.hub.head
  staged : ∀ n x, (s.node n).sops x → Anc s.U.par x s.hub.head
  accHeads : ∀ n x y, (s.node n).heads x → (s.node n).heads y →
    Anc s.U.par x s.hub.head → Anc s.U.par y s.hub.head → x = y
  comparable : ∀ n x i, (s.node n).heads x → Anc s.U.par x s.hub.head → i ≤ s.hub.seq →
    Anc s.U.par x (s.hub.hist i) ∨ Anc s.U.par (s.hub.hist i) x
  -- ghost merge records
  mergeOwn : ∀ m, m < s.U.next → s.U.isMerge m = true →
    ∃ p ∈ s.U.par m, s.U.creator p = s.U.creator m ∧
      ¬ Anc s.U.par p (s.hub.hist (s.U.birth m))
  mergeForeign : ∀ m, m < s.U.next → s.U.isMerge m = true → ∀ p ∈ s.U.par m,
    s.U.creator p ≠ s.U.creator m → Anc s.U.par p (s.hub.hist (s.U.birth m))
  birthLe : ∀ m, m < s.U.next → s.U.birth m ≤ s.hub.seq
  birthMono : ∀ x y, x < y → y < s.U.next → s.U.birth x ≤ s.U.birth y
  -- messages
  msgs : ∀ m, s.net m → MsgOK s m

namespace Inv

variable {N : Nat} {s : State}

theorem knownAnc (hI : Inv N s) (n : Nat) :
    Anc s.U.par (s.node n).known.head s.hub.head := by
  have := hI.histAnc (hI.known n).1
  rwa [(hI.known n).2] at this

theorem knownLt (hI : Inv N s) (n : Nat) : (s.node n).known.head < s.U.next :=
  Nat.lt_of_le_of_lt ((hI.knownAnc n).le hI.parLt) hI.headLt

/-- A node whose `known` head is not the hub's head knows a sequence number below the hub's. -/
theorem knownSeqLt (hI : Inv N s) {n : Nat} (h : s.hub.head ≠ (s.node n).known.head) :
    (s.node n).known.seq < s.hub.seq := by
  rcases Nat.lt_or_eq_of_le (hI.known n).1 with h1 | h1
  · exact h1
  · exfalso; apply h; rw [← hI.histHead, ← h1, (hI.known n).2]

/-- An operation reachable from a node's heads but not accepted was created by that node. -/
theorem ownOfUnacc (hI : Inv N s) {n x : Nat} (hx : (s.node n).lops x)
    (hna : ¬ Anc s.U.par x s.hub.head) : s.U.creator x = some n := by
  rcases hI.locality n x hx with h | h
  · exact h
  · exact absurd h hna

end Inv

/-- In the initial state the only ancestor of an operation is itself. -/
theorem anc_init {a x : Nat} (h : Anc init.U.par a x) : a = x := by
  cases h with
  | refl => rfl
  | step hp _ => simp [init] at hp

theorem core_init (N : Nat) : Core N init := by
  refine
    { parLt := ?_, nextPos := ?_, rootAnc := ?_, creatorSome := ?_, creatorRoot := ?_,
      headLt := ?_, histHead := ?_, hist0 := ?_, histStep := ?_, hubClosed := ?_,
      lroot := ?_, lLt := ?_, lParents := ?_, lObjs := ?_, headsLocal := ?_,
      headsAnti := ?_, headsNonempty := ?_, ownInHeads := ?_ }
  all_goals simp [init, initNode, ClosedAt, HubHas]
  · intro y p hp; simp at hp
  · exact Anc.refl
  · intro x hx h; omega
  · intro y h; exact anc_init h

theorem inv_init (N : Nat) : Inv N init := by
  refine
    { toCore := core_init N, known := ?_, locality := ?_, staged := ?_, accHeads := ?_,
      comparable := ?_, mergeOwn := ?_, mergeForeign := ?_, birthLe := ?_, birthMono := ?_,
      msgs := ?_ }
  all_goals simp [init, initNode, Consistent]
  · exact Anc.refl
  · intro x i hx _ _; subst hx; exact Or.inl Anc.refl

end Musubi
