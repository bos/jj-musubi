/-
The expected-value history walk in `node/git.rs`, independently of jj's ref algebra.
Operation names may differ on two machines. Ordered parent targets, join boundaries and
fix-up checkpoints are the observations relevant to the walk; private history before a
boundary is irrelevant. `ExpectedExec.lean` supplies finite tables to the oracle.
-/
import Musubi.Refs

namespace Musubi.Refs.Expected

/-- A missing checkpoint differs from a checkpoint saying there is no expected value. -/
structure Observation (I T : Type) where
  target : T
  known : Option (Option T) := none
  recorded : Option (Option T) := none
  boundary : Bool := false
  parents : List (I × T) := []
  deriving DecidableEq, Repr

/-- One history step either stops with an optional value or follows one parent. -/
inductive Decision (I T : Type) where
  | done (value : Option T)
  | follow (parent : I)
  deriving DecidableEq, Repr

def Decision.rename (f : I → J) : Decision I T → Decision J T
  | .done e => .done e
  | .follow i => .follow (f i)

variable [DecidableEq T]

/-- Parent order matters: the first unchanged parent wins, even at a merge. -/
def inherited (target : T) : List (I × T) → Option I
  | [] => none
  | (i, t) :: ps => if t = target then some i else inherited target ps

/-- `side` chooses among positive conflict terms, using commit time then commit id.
`resolved` and `side` are shared observations of jj targets, not a model of jj merging. -/
def decide (resolved : T → Bool) (side : T → Option T) (o : Observation I T) : Decision I T :=
  match o.known.or o.recorded with
  | some e => .done e
  | none =>
    if o.boundary then .done (side o.target)
    else match inherited o.target o.parents with
    | some i => .follow i
    | none => match o.parents with
      | [(i, t)] => if resolved t then .done (some t) else .follow i
      | _ => .done (side o.target)

/-- Boundaries hide the parents the walk never reads. A cache entry hides the recorded value
as well. This is deliberately stronger than equality of the final expected values. -/
def relevant (o : Observation I T) : Observation I T :=
  match o.known.or o.recorded with
  | some e => { target := o.target, known := some e }
  | none => if o.boundary then { target := o.target, boundary := true } else o

def Observation.rename (f : I → J) (o : Observation I T) : Observation J T :=
  { target := o.target, known := o.known, recorded := o.recorded, boundary := o.boundary,
    parents := o.parents.map fun (i, t) => (f i, t) }

/-- Fuel exhaustion is outer `none`; a successful walk with no side is `some none`.
A finite acyclic history needs at most its number of operations plus one units of fuel. -/
def eval (resolved : T → Bool) (side : T → Option T) (h : I → Observation I T) :
    Nat → I → Option (Option T)
  | 0, _ => none
  | n + 1, i => match decide resolved side (h i) with
    | .done e => some e
    | .follow p => eval resolved side h n p

theorem inherited_rename (f : I → J) (target : T) (ps : List (I × T)) :
    inherited target (ps.map fun (i, t) => (f i, t)) = (inherited target ps).map f := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨i, t⟩
    simp only [List.map_cons, inherited]
    split <;> simp_all

theorem decide_rename (resolved : T → Bool) (side : T → Option T)
    (f : I → J) (o : Observation I T) :
    decide resolved side (o.rename f) = (decide resolved side o).rename f := by
  cases hc : o.known.or o.recorded with
  | some e => simp [decide, Observation.rename, hc, Decision.rename]
  | none =>
    by_cases hb : o.boundary = true
    · simp [decide, Observation.rename, hc, hb, Decision.rename]
    · simp only [decide, Observation.rename, hc, hb]
      rw [inherited_rename]
      cases hi : inherited o.target o.parents with
      | some i => rfl
      | none =>
        simp only [Option.map_none]
        cases hp : o.parents with
        | nil => rfl
        | cons p ps =>
          rcases p with ⟨i, t⟩
          cases ps with
          | nil =>
            simp only [List.map_cons, List.map_nil]
            by_cases hr : resolved t = true <;> simp [hr, Decision.rename]
          | cons q qs => rfl

theorem decide_relevant (resolved : T → Bool) (side : T → Option T)
    (o : Observation I T) : decide resolved side (relevant o) = decide resolved side o := by
  cases hc : o.known.or o.recorded with
  | some e => simp [relevant, decide, hc]
  | none =>
    by_cases hb : o.boundary = true <;> simp [relevant, decide, hc, hb]

/-- Equivalent relevant observations under an operation renaming give equal computations.
This requires the chosen parent order, shared target/commit data and checkpoint values;
it does not assume equality of the computed expectations. -/
theorem eval_congr_on (resolved : T → Bool) (side : T → Option T)
    (h : I → Observation I T) (h' : J → Observation J T) (f : I → J)
    (domain : I → Prop)
    (closed : ∀ i p, domain i → decide resolved side (h i) = .follow p → domain p)
    (heq : ∀ i, domain i → relevant (h' (f i)) = (relevant (h i)).rename f)
    (n : Nat) (i : I) (start : domain i) :
    eval resolved side h' n (f i) = eval resolved side h n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have hd : decide resolved side (h' (f i)) = (decide resolved side (h i)).rename f := by
      rw [← decide_relevant resolved side (h' (f i)), heq i start, decide_rename,
        decide_relevant]
    simp only [eval, hd]
    cases choice : decide resolved side (h i) with
    | done e => rfl
    | follow p => exact ih p (closed i p start choice)

/-- A convenient whole-history instance of the path-local theorem. -/
theorem eval_congr (resolved : T → Bool) (side : T → Option T)
    (h : I → Observation I T) (h' : J → Observation J T) (f : I → J)
    (heq : ∀ i, relevant (h' (f i)) = (relevant (h i)).rename f) (n : Nat) (i : I) :
    eval resolved side h' n (f i) = eval resolved side h n i :=
  eval_congr_on resolved side h h' f (fun _ => True) (by simp)
    (fun i _ => heq i) n i trivial

/-- A well-founded parent walk finishes. This is a hypothesis about the operation DAG,
not a silent assumption that fuel exhaustion means there is no expected value. -/
theorem eval_terminates (resolved : T → Bool) (side : T → Option T)
    (h : I → Observation I T) (rank : I → Nat)
    (decreases : ∀ i p, decide resolved side (h i) = .follow p → rank p < rank i)
    (n : Nat) (i : I) (bound : rank i < n) :
    ∃ e, eval resolved side h n i = some e := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases hd : decide resolved side (h i) with
    | done e => exact ⟨e, by simp [eval, hd]⟩
    | follow p =>
      obtain ⟨e, he⟩ := ih p (by have := decreases i p hd; omega)
      exact ⟨e, by simpa [eval, hd] using he⟩

/-- Extra fuel cannot change a successful computation. -/
theorem eval_stable (resolved : T → Bool) (side : T → Option T)
    (h : I → Observation I T) (n : Nat) (i : I) (e : Option T)
    (success : eval resolved side h n i = some e) (extra : Nat) :
    eval resolved side h (n + extra) i = some e := by
  induction n generalizing i with
  | zero => simp [eval] at success
  | succ n ih =>
    cases hd : decide resolved side (h i) with
    | done value => simpa [Nat.succ_add, eval, hd] using success
    | follow p =>
      simp only [eval, hd] at success
      simpa [Nat.succ_add, eval, hd] using ih p success

/-- The unbounded relation computed by a successful finite walk. -/
inductive Computes (resolved : T → Bool) (side : T → Option T) (h : I → Observation I T) :
    I → Option T → Prop where
  | done (i e) : decide resolved side (h i) = .done e → Computes resolved side h i e
  | follow (i p e) : decide resolved side (h i) = .follow p →
      Computes resolved side h p e → Computes resolved side h i e

theorem eval_computes (resolved : T → Bool) (side : T → Option T)
    (h : I → Observation I T) (n : Nat) (i : I) (e : Option T)
    (success : eval resolved side h n i = some e) : Computes resolved side h i e := by
  induction n generalizing i with
  | zero => simp [eval] at success
  | succ n ih =>
    cases hd : decide resolved side (h i) with
    | done value =>
      have he : value = e := by simpa [eval, hd] using success
      exact .done i e (he ▸ hd)
    | follow p => exact .follow i p e hd (ih p (by simpa [eval, hd] using success))

theorem Computes.unique {resolved : T → Bool} {side : T → Option T}
    {h : I → Observation I T} {i : I} {e e' : Option T}
    (he : Computes resolved side h i e) (he' : Computes resolved side h i e') : e = e' := by
  induction he generalizing e' with
  | done i e hd =>
    cases he' with
    | done _ e' hd' => rw [hd] at hd'; exact Decision.done.inj hd'
    | follow _ p e' hd' hp => rw [hd] at hd'; contradiction
  | follow i p e hd hp ih =>
    cases he' with
    | done _ e' hd' => rw [hd] at hd'; contradiction
    | follow _ p' e' hd' hp' =>
      rw [hd] at hd'
      cases Decision.follow.inj hd'
      exact ih hp'

/-- Remove only memoized expectations; recorded fix-up checkpoints remain authoritative. -/
def withoutKnown (h : I → Observation I T) (i : I) : Observation I T :=
  { h i with known := none }

/-- A machine may have different memoization from another. Correct cached answers can be
removed without changing a successful computation. Pending pre-contraction values must
instead correspond to authoritative history checkpoints; this lemma does not justify them. -/
theorem Computes.without_known {resolved : T → Bool} {side : T → Option T}
    {h : I → Observation I T} {i : I} {e : Option T}
    (sound : ∀ i value, (h i).known = some value →
      Computes resolved side (withoutKnown h) i value)
    (he : Computes resolved side h i e) : Computes resolved side (withoutKnown h) i e := by
  induction he with
  | done i e hd =>
    cases hc : (h i).known with
    | none =>
      have hh : withoutKnown h i = h i := by unfold withoutKnown; rw [← hc]
      exact .done i e (by rw [hh]; exact hd)
    | some value =>
      have hv : value = e := by simpa [decide, hc] using hd
      exact hv ▸ sound i value hc
  | follow i p e hd hp ih =>
    have hc : (h i).known = none := by
      cases hc : (h i).known with
      | none => rfl
      | some value => simp [decide, hc] at hd
    have hh : withoutKnown h i = h i := by unfold withoutKnown; rw [← hc]
    exact .follow i p e (by rw [hh]; exact hd) ih

/-- Cold and correctly memoized walks agree even if they use different amounts of fuel. -/
theorem eval_without_known_agrees (resolved : T → Bool) (side : T → Option T)
    (h : I → Observation I T)
    (sound : ∀ i value, (h i).known = some value →
      Computes resolved side (withoutKnown h) i value)
    (n m : Nat) (i : I) (e e' : Option T)
    (warm : eval resolved side h n i = some e)
    (cold : eval resolved side (withoutKnown h) m i = some e') : e = e' :=
  ((eval_computes resolved side h n i e warm).without_known sound).unique
    (eval_computes resolved side (withoutKnown h) m i e' cold)

/-- A recorded fix-up value preserves a pre-contraction expectation without retaining the
old parents. Establishing that the record contains that value belongs to the fix-up bridge. -/
theorem checkpoint (resolved : T → Bool) (side : T → Option T)
    (h : I → Observation I T) (i : I) (e : Option T)
    (hc : (h i).known.or (h i).recorded = some e) :
    eval resolved side h (n + 1) i = some e := by
  simp [eval, decide, hc]

/-- Discharge `conflicted_import_agrees`'s ghost equality at the history boundary. The
bindings state that each machine uses the successfully computed, present expectation.
Reachability and successful export are still the slot model's hypotheses. -/
theorem conflicted_import_agrees_of_history [RefAlg T] [Sides T]
    {s s' : CMachine T} (hs : CReach s) (hs' : CReach s')
    (hm : s.moved = false) (hm' : s'.moved = false)
    (hL : s.v.L = s'.v.L) (hR : s.v.R = s'.v.R)
    (h : I → Observation I T) (h' : J → Observation J T) (f : I → J)
    (domain : I → Prop)
    (closed : ∀ i p, domain i → decide RefAlg.resolved Sides.side (h i) = .follow p → domain p)
    (heq : ∀ i, domain i → relevant (h' (f i)) = (relevant (h i)).rename f)
    (n : Nat) (i : I) (start : domain i)
    (bind : eval RefAlg.resolved Sides.side h n i = some (some s.E))
    (bind' : eval RefAlg.resolved Sides.side h' n (f i) = some (some s'.E)) :
    (s.v.import s.G).L = (s'.v.import s'.G).L ∧ (s.v.import s.G).R = (s'.v.import s'.G).R := by
  have he := eval_congr_on RefAlg.resolved Sides.side h h' f domain closed heq n i start
  rw [bind, bind'] at he
  exact conflicted_import_agrees hs hs' hm hm' hL hR (Option.some.inj (Option.some.inj he.symm))

end Musubi.Refs.Expected
