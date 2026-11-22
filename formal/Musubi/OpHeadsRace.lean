/-
musubi moving jj operation heads that it read earlier, among jj's commands and the lockless
`jj op abandon` and `jj op integrate` (`docs/internals/design.md`, "Moving op heads"; the rows of
`docs/internals/races.md` for #168).

The state is the set of op heads, the operations (`OpHeads.Graph`: their parents) and jj's
op-heads lock. A jj command *loads* an operation and later *publishes* its own on it, under the
lock, in place of the one it loaded; a command that loads several op heads *merges* them first,
under the lock, so none writes on an op head with another beside it, but one run `--at-op`
(`cmdLoadAt`), which loads any operation. `jj op abandon` and `jj op integrate` *begin* by writing
an operation, which nothing can reach yet, and later *land* it: they add it to the op heads and
remove what they replace, with no lock, and ignore what is gone already.

musubi's own move is one actor: it *plans* (reads the op heads, writes the operations it will
put in), *locks*, *checks* that the op heads are those it read, writes each head one at a time,
and lets go of the lock. musubi's writes are a file system call each. A landing, which
`update_op_heads` makes as an add and then a removal, is one step here, as is a command's publish
or merge, which holds the lock: a read of the op heads between a landing's two calls is not a
state of the model.

The ghost `ev` counts how many commands and landings changed the op heads.

What is proved is in the theorems of the last sections: that no command's operation lands
between musubi's read and its move once it has checked (`check_no_event`), so that a move that
goes on to write puts its heads in place of exactly those it read; and that no command runs while
musubi holds the lock (`locked_blocks_commands`). `Trace` builds the cases the check is for:
`landing_before_the_lock` and `landing_during_the_move`.
-/
import Musubi.OpHeads

namespace Musubi.OpHeads.Race

open Musubi.OpHeads

/-- A write to the op heads, one file system call. -/
inductive Act where
  | add (n : Nat)
  | del (n : Nat)
deriving DecidableEq, Repr

/-- The op heads after one write; adding one that is there, or removing one that isn't, does
nothing. -/
def Act.apply (heads : List Nat) : Act → List Nat
  | .add n => if heads.contains n then heads else n :: heads
  | .del n => heads.filter (· != n)

/-- A write musubi can make: nothing is added that isn't there to see. -/
def Act.ok (next : Nat) (pend : Nat → Option (List Nat)) : Act → Prop
  | .add n => n < next ∧ pend n = none
  | .del _ => True

/-- A move planned: the op heads read, the op heads to put in their place, whether to take the
old ones out. -/
structure Plan where
  read : List Nat
  new : List Nat
  remove : Bool
  /-- Ghost: how many events had changed the op heads when they were read. -/
  ev0 : Nat

/-- Where musubi is. -/
inductive Mv where
  | idle
  | planned (p : Plan)
  | held (p : Plan)
  | writing (p : Plan) (todo : List Act)
  /-- Letting go of the lock. -/
  | releasing

/-- In these musubi holds the lock. -/
def Mv.locked : Mv → Bool
  | .held _ | .writing _ _ | .releasing => true
  | .idle | .planned _ => false

structure S where
  next : Nat
  g : Graph
  heads : List Nat
  lock : Bool
  /-- Ghost: how many commands and landings have changed the op heads. -/
  ev : Nat
  /-- Operations commands have loaded, that they will publish on. -/
  jc : List Nat
  /-- The operations that `jj op abandon` and `jj op integrate` have written and not landed,
  each with what it replaces. -/
  pend : Nat → Option (List Nat)
  /-- The operations musubi wrote. -/
  made : List Nat
  mv : Mv

/-- Not an operation written and not landed yet: nothing is built on one. -/
def S.free (s : S) (p : Nat) : Prop := s.pend p = none

/-- What a plan writes: the new heads, then the old heads out. -/
def Plan.todo (p : Plan) : List Act :=
  p.new.map Act.add ++ (if p.remove then (oldOf p.read p.new).map Act.del else [])

/-- One step. -/
inductive Step : S → S → Prop
  /-- A jj command loads the one op head, and runs. -/
  | cmdLoad {s : S} {L : Nat} (h : s.heads = [L]) :
      Step s { s with jc := L :: s.jc }
  /-- A command run `--at-op` loads any operation there is, whatever the op heads are, and
  merges nothing before it writes. -/
  | cmdLoadAt {s : S} {L : Nat} (hL : L < s.next) (hf : s.free L) :
      Step s { s with jc := L :: s.jc }
  /-- It publishes its operation under the lock, on what it loaded, which may not be an op
  head by now. -/
  | cmdPublish {s : S} {L : Nat} (hL : L ∈ s.jc) (hl : s.lock = false) :
      Step s { s with
        next := s.next + 1, g := s.g.add s.next [L],
        heads := s.next :: s.heads.filter (· != L), jc := s.jc.erase L, ev := s.ev + 1 }
  /-- A command that loads several op heads merges them, under the lock. -/
  | cmdMerge {s : S} (hl : s.lock = false) (h2 : 2 ≤ s.heads.length) :
      Step s { s with
        next := s.next + 1, g := s.g.add s.next s.heads,
        heads := [s.next], ev := s.ev + 1 }
  /-- `jj op abandon` or `jj op integrate` writes an operation on `ps`, to replace `gone`. -/
  | locklessBegin {s : S} {ps gone : List Nat} (hps : ∀ p ∈ ps, p < s.next ∧ s.free p) :
      Step s { s with
        next := s.next + 1, g := s.g.add s.next ps,
        pend := fun r => if r = s.next then some gone else s.pend r }
  /-- Either lands its operation, with no lock: adds it, removes what it replaces. -/
  | land {s : S} {r : Nat} {gone : List Nat} (h : s.pend r = some gone) :
      Step s { s with
        heads := r :: s.heads.filter (fun x => !gone.contains x),
        pend := fun r' => if r' = r then none else s.pend r', ev := s.ev + 1 }
  /-- musubi writes an operation it will put in, with parents it can see. -/
  | mkOp {s : S} {ps : List Nat} (hi : s.mv = .idle)
      (hps : ∀ p ∈ ps, p < s.next ∧ s.free p) :
      Step s { s with
        next := s.next + 1, g := s.g.add s.next ps, made := s.next :: s.made }
  /-- It reads the op heads and plans to put `new` in their place. -/
  | plan {s : S} {keep chosen : List Nat} {remove : Bool}
      (hi : s.mv = .idle) (hk : ∀ k ∈ keep, k ∈ s.heads) (hc : ∀ c ∈ chosen, c ∈ s.made)
      (hne : keep ++ chosen ≠ []) :
      Step s { s with mv := .planned {
        read := s.heads, new := keep ++ chosen, remove := remove, ev0 := s.ev } }
  /-- Takes the lock. -/
  | lock {s : S} {p : Plan} (h : s.mv = .planned p) (hl : s.lock = false) :
      Step s { s with lock := true, mv := .held p }
  /-- Checks the op heads are those it read: if so, writes; if not, moves nothing. -/
  | check {s : S} {p : Plan} (h : s.mv = .held p) :
      Step s { s with mv :=
        if (OpHeads.same s.heads p.read) = true then .writing p p.todo else .releasing }
  /-- One write. musubi only adds an operation that exists and that no `jj op abandon` or
  `jj op integrate` has written and not landed: one it wrote, or an op head or an ancestor it
  read. -/
  | write {s : S} {p : Plan} {a : Act} {rest : List Act} (h : s.mv = .writing p (a :: rest))
      (ha : a.ok s.next s.pend) :
      Step s { s with heads := a.apply s.heads, mv := .writing p rest }
  /-- Done writing. -/
  | written {s : S} {p : Plan} (h : s.mv = .writing p []) :
      Step s { s with mv := .releasing }
  | release {s : S} (h : s.mv = .releasing) :
      Step s { s with lock := false, mv := .idle }

/-- A jj command can take its step: it needs the lock free. -/
def CmdEnabled (s : S) : Prop := s.lock = false ∧ ((∃ L, L ∈ s.jc) ∨ 2 ≤ s.heads.length)

/-- The start. -/
def init : S where
  next := 1
  g := { parents := fun _ => [] }
  heads := [0]
  lock := false
  ev := 0
  jc := []
  pend := fun _ => none
  made := []
  mv := .idle

inductive Reachable : S → Prop
  | init : Reachable init
  | step {s s' : S} : Reachable s → Step s s' → Reachable s'


/-! ## What holds in every reachable state -/

/-- While musubi is between planning and checking, what it read has not been given back, and
nothing has happened to the op heads unless they differ. -/
def KInv (s : S) : Prop :=
  ∀ p, (s.mv = .planned p ∨ s.mv = .held p) →
    (∀ x ∈ p.read, x < s.next) ∧ (∀ r gone, s.pend r = some gone → r ∉ p.read) ∧
      (s.ev ≠ p.ev0 → ¬ OpHeads.same s.heads p.read = true)

structure Inv (s : S) : Prop where
  dag : s.g.Dag
  headsLt : ∀ x ∈ s.heads, x < s.next
  pendLt : ∀ r gone, s.pend r = some gone → r < s.next ∧ r ∉ s.heads
  jcLt : ∀ L ∈ s.jc, L < s.next
  lock : s.mv.locked = true → s.lock = true
  k : KInv s

theorem Inv.init : Inv Race.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x p hp; simp [Race.init] at hp
  · intro x hx; simpa [Race.init] using hx
  · intro r gone h; simp [Race.init] at h
  · intro L hL; simp [Race.init] at hL
  · intro h; simp [Race.init, Mv.locked] at h
  · intro p hp; simp [Race.init] at hp

theorem dag_add {g : Graph} (hg : g.Dag) (n : Nat) (ps : List Nat)
    (hps : ∀ p ∈ ps, p < n) : (g.add n ps).Dag := by
  intro x p hp
  simp only [Graph.add] at hp
  split at hp
  · rename_i hx; subst hx; exact hps p hp
  · exact hg x p hp


/-- `x` is not among the op heads musubi read, so a step that adds it to them has changed
them. -/
theorem not_same_of_add {heads read : List Nat} {x : Nat} (hx : x ∈ heads) (hr : x ∉ read) :
    ¬ OpHeads.same heads read = true := by
  intro h
  exact hr ((same_iff.1 h x).1 hx)

theorem apply_lt {a : Act} {next : Nat} {pend : Nat → Option (List Nat)} {heads : List Nat}
    (ha : a.ok next pend) (hlt : ∀ x ∈ heads, x < next) : ∀ x ∈ a.apply heads, x < next := by
  intro x hx
  cases a with
  | add n =>
    simp only [Act.apply] at hx
    split at hx
    · exact hlt x hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ha.1
      · exact hlt x hx
  | del n =>
    simp only [Act.apply] at hx
    exact hlt x (List.mem_filter.1 hx).1

theorem apply_pend {a : Act} {next : Nat} {pend : Nat → Option (List Nat)} {heads : List Nat}
    {r : Nat} {gone : List Nat} (ha : a.ok next pend) (hr : pend r = some gone)
    (h : r ∉ heads) : r ∉ a.apply heads := by
  cases a with
  | add n =>
    simp only [Act.apply]
    split
    · exact h
    · intro hm
      rcases List.mem_cons.1 hm with rfl | hm
      · have := ha.2; simp [hr] at this
      · exact h hm
  | del n =>
    simp only [Act.apply]
    intro hm
    exact h (List.mem_filter.1 hm).1

theorem Inv.step {s s' : S} (hi : Inv s) (hs : Step s s') : Inv s' := by
  obtain ⟨dag, hlt, hpl, hjc, hlk, hk⟩ := hi
  cases hs with
  | cmdLoad h =>
    rename_i L
    refine ⟨dag, hlt, hpl, ?_, hlk, hk⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hlt x (by simp [h])
    · exact hjc x hx
  | cmdLoadAt hL hf =>
    rename_i L
    refine ⟨dag, hlt, hpl, ?_, hlk, hk⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hL
    · exact hjc x hx
  | cmdPublish hL hl =>
    rename_i L
    have hLn := hjc L hL
    refine ⟨dag_add dag _ _ (by simpa using hLn), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      dsimp only at hx ⊢
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := hlt x (List.mem_filter.1 hx).1; omega
    · intro r gone h
      obtain ⟨h1, h2⟩ := hpl r gone h
      refine ⟨by dsimp only; omega, fun hr => ?_⟩
      dsimp only at hr
      rcases List.mem_cons.1 hr with rfl | hr
      · omega
      · exact h2 (List.mem_filter.1 hr).1
    · intro x hx
      dsimp only at hx ⊢
      have := hjc x (List.mem_of_mem_erase hx); omega
    · exact hlk
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hk p hp
      refine ⟨fun x hx => by have := h1 x hx; dsimp only; omega, h2, ?_⟩
      intro _
      exact not_same_of_add (x := s.next) (by simp) (fun hr => by have := h1 _ hr; omega)
  | cmdMerge hl h2 =>
    refine ⟨dag_add dag _ _ (fun p hp => hlt p hp), ?_, ?_, ?_, hlk, ?_⟩
    · intro x hx
      dsimp only at hx ⊢
      simp at hx; omega
    · intro r gone h
      obtain ⟨h1, h2⟩ := hpl r gone h
      refine ⟨by dsimp only; omega, fun hr => ?_⟩
      dsimp only at hr
      simp at hr; omega
    · intro x hx; dsimp only at hx ⊢; have := hjc x hx; omega
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hk p hp
      refine ⟨fun x hx => by have := h1 x hx; dsimp only; omega, h2, ?_⟩
      intro _
      exact not_same_of_add (x := s.next) (by simp) (fun hr => by have := h1 _ hr; omega)
  | locklessBegin hps =>
    refine ⟨dag_add dag _ _ (fun p hp => (hps p hp).1), ?_, ?_, ?_, hlk, ?_⟩
    · intro x hx; dsimp only at hx ⊢; have := hlt x hx; omega
    · intro r gone hr
      dsimp only at hr
      by_cases e : r = s.next
      · subst e
        refine ⟨by dsimp only; omega, fun hm => ?_⟩
        have := hlt _ hm; omega
      · simp only [e, ↓reduceIte] at hr
        obtain ⟨h1, h2⟩ := hpl r gone hr
        exact ⟨by dsimp only; omega, h2⟩
    · intro x hx; dsimp only at hx ⊢; have := hjc x hx; omega
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hk p hp
      refine ⟨fun x hx => by have := h1 x hx; dsimp only; omega, ?_, h3⟩
      intro r gone hr
      dsimp only at hr
      by_cases e : r = s.next
      · subst e; intro hm; have := h1 _ hm; omega
      · simp only [e, ↓reduceIte] at hr
        exact h2 r gone hr
  | land h =>
    rename_i r gone
    obtain ⟨hr1, hr2⟩ := hpl r gone h
    refine ⟨dag, ?_, ?_, hjc, hlk, ?_⟩
    · intro x hx
      dsimp only at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hr1
      · exact hlt x (List.mem_filter.1 hx).1
    · intro r' gone' hr'
      dsimp only at hr'
      by_cases e : r' = r
      · simp [e] at hr'
      · simp only [e, ↓reduceIte] at hr'
        obtain ⟨h1, h2⟩ := hpl r' gone' hr'
        refine ⟨h1, fun hm => ?_⟩
        dsimp only at hm
        rcases List.mem_cons.1 hm with hm | hm
        · exact e hm
        · exact h2 (List.mem_filter.1 hm).1
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hk p hp
      refine ⟨h1, ?_, ?_⟩
      · intro r' gone' hr'
        dsimp only at hr'
        by_cases e : r' = r
        · simp [e] at hr'
        · simp only [e, ↓reduceIte] at hr'
          exact h2 r' gone' hr'
      · intro _
        exact not_same_of_add (x := r) (by simp) (h2 r gone h)
  | mkOp hi' hps =>
    refine ⟨dag_add dag _ _ (fun p hp => (hps p hp).1), ?_, ?_, ?_, hlk, ?_⟩
    · intro x hx; dsimp only at hx ⊢; have := hlt x hx; omega
    · intro r gone hr
      obtain ⟨h1, h2⟩ := hpl r gone hr
      exact ⟨by dsimp only; omega, h2⟩
    · intro x hx; dsimp only at hx ⊢; have := hjc x hx; omega
    · intro p hp
      dsimp only at hp
      rw [hi'] at hp
      simp at hp
  | plan hi' hk' hc hne =>
    refine ⟨dag, hlt, hpl, hjc, ?_, ?_⟩
    · intro h; simp [Mv.locked] at h
    · intro p hp
      simp only [Mv.planned.injEq] at hp
      rcases hp with hp | hp
      · subst hp
        exact ⟨hlt, fun r gone hr hm => (hpl r gone hr).2 hm, fun h => (h rfl).elim⟩
      · cases hp
  | lock h hl =>
    refine ⟨dag, hlt, hpl, hjc, ?_, ?_⟩
    · intro _; rfl
    · intro p' hp
      simp only [Mv.held.injEq] at hp
      rcases hp with hp | hp
      · cases hp
      · subst hp
        exact hk _ (Or.inl h)
  | check h =>
    refine ⟨dag, hlt, hpl, hjc, fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    intro p' hp
    dsimp only at hp
    split at hp <;> simp at hp
  | write h ha =>
    rename_i p a rest
    refine ⟨dag, fun x hx => apply_lt ha hlt x hx, fun r gone hr => ?_, hjc,
      fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    · obtain ⟨h1, h2⟩ := hpl r gone hr
      exact ⟨h1, apply_pend ha hr h2⟩
    · intro p' hp; simp at hp
  | written h =>
    refine ⟨dag, hlt, hpl, hjc, fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    intro p' hp; simp at hp
  | release h =>
    refine ⟨dag, hlt, hpl, hjc, fun hm => by simp [Mv.locked] at hm, ?_⟩
    intro p' hp; simp at hp

theorem Reachable.inv {s : S} (h : Reachable s) : Inv s := by
  induction h with
  | init => exact Inv.init
  | step _ hs ih => exact ih.step hs

/-! ## 1. The lock and the check keep commands out of a move -/

/-- No jj command publishes or merges while musubi holds the lock, from taking it to letting it
go: the checking and every write. -/
theorem locked_blocks_commands {s : S} (hr : Reachable s) (hm : s.mv.locked = true) :
    ¬ CmdEnabled s := by
  intro ⟨hl, _⟩
  have := hr.inv.lock hm
  rw [hl] at this
  cases this

/-- Once musubi has taken the lock, jj's lock is held, whichever way musubi goes. -/
theorem held_has_lock {s : S} (hr : Reachable s) {p : Plan} (h : s.mv = .held p) :
    s.lock = true := hr.inv.lock (by simp [h, Mv.locked])

theorem writing_has_lock {s : S} (hr : Reachable s) {p : Plan} {todo : List Act}
    (h : s.mv = .writing p todo) : s.lock = true := hr.inv.lock (by simp [h, Mv.locked])

/-- **The check.** If the op heads are still those musubi read when it checks them, under the
lock, no command has published or merged, and no `jj op abandon` or `jj op integrate` has landed,
since it read them. The op heads can't have changed and changed back: what a command or a landing
puts in is an operation written since, or one musubi didn't read. So no operation a command wrote
is among those musubi takes out. -/
theorem check_no_event {s : S} (hr : Reachable s) {p : Plan} (h : s.mv = .held p)
    (hs : OpHeads.same s.heads p.read = true) : s.ev = p.ev0 := by
  have := hr.inv.k p (Or.inr h)
  exact Classical.byContradiction fun hne => this.2.2 hne hs

/-- The same of the check that starts the writes: a move that goes on to write has had no event
since it read the op heads, and holds the lock. -/
theorem check_step {s s' : S} (hr : Reachable s) (hs : Step s s') {p : Plan}
    (h : s.mv = .held p) {p' : Plan} {todo : List Act} (h' : s'.mv = .writing p' todo) :
    s.ev = p.ev0 ∧ s'.lock = true ∧ s'.ev = s.ev := by
  cases hs with
  | check h2 =>
    rename_i p2
    rw [h] at h2
    cases h2
    simp only at h'
    split at h'
    · rename_i hsame
      exact ⟨check_no_event (s := s) hr h hsame, held_has_lock (s := s) hr h, rfl⟩
    · simp at h'
  | _ => simp_all

namespace Trace

/-- The plan of moving the op head `0` to `1`. -/
def plan : Plan := { read := [0], new := [1], remove := true, ev0 := 0 }

/-- **A landing before the lock.** `jj op integrate` lands the operation `2` after musubi has
read the op heads and before it takes the lock. Its check finds them changed and moves nothing:
`1` never goes in, and `2` and `0` stay. -/
theorem landing_before_the_lock :
    ∃ s, Reachable s ∧ s.heads = [2, 0] ∧ s.mv = .idle ∧ s.lock = false := by
  have b1 := Reachable.step Reachable.init
    (Step.mkOp (s := Race.init) (ps := []) (by rfl) (fun p hp => by simp at hp))
  have b2 := Reachable.step b1 (Step.plan (keep := []) (chosen := [1]) (remove := true)
    (by rfl) (by simp) (by decide) (by simp))
  have b3 := Reachable.step b2 (Step.locklessBegin (ps := []) (gone := [])
    (fun p hp => by simp at hp))
  have b4 := Reachable.step b3 (Step.land (r := 2) (gone := []) (by rfl))
  have b5 := Reachable.step b4 (Step.lock (p := plan) (by rfl) (by rfl))
  have b6 := Reachable.step b5 (Step.check (p := plan) (by rfl))
  have b7 := Reachable.step b6 (Step.release (by rfl))
  exact ⟨_, b7, by rfl, by rfl, by rfl⟩

/-- **A landing during the move.** The same operation lands between musubi's two writes, with no
lock. musubi takes out only the op head it read: `2` stays beside the new head `1`. -/
theorem landing_during_the_move :
    ∃ s, Reachable s ∧ s.heads = [2, 1] ∧ s.mv = .idle ∧ s.lock = false := by
  have c1 := Reachable.step Reachable.init
    (Step.mkOp (s := Race.init) (ps := []) (by rfl) (fun p hp => by simp at hp))
  have c2 := Reachable.step c1 (Step.plan (keep := []) (chosen := [1]) (remove := true)
    (by rfl) (by simp) (by decide) (by simp))
  have c3 := Reachable.step c2 (Step.lock (p := plan) (by rfl) (by rfl))
  have c4 := Reachable.step c3 (Step.check (p := plan) (by rfl))
  have c5 := Reachable.step c4 (Step.write (p := plan) (a := .add 1) (rest := [.del 0])
    (by rfl) (show _ ∧ _ from ⟨by decide, by rfl⟩))
  have c6 := Reachable.step c5 (Step.locklessBegin (ps := []) (gone := [])
    (fun p hp => by simp at hp))
  have c7 := Reachable.step c6 (Step.land (r := 2) (gone := []) (by rfl))
  have c8 := Reachable.step c7 (Step.write (p := plan) (a := .del 0) (rest := [])
    (by rfl) (by simp [Act.ok]))
  have c9 := Reachable.step c8 (Step.written (p := plan) (by rfl))
  have c10 := Reachable.step c9 (Step.release (by rfl))
  exact ⟨_, c10, by rfl, by rfl, by rfl⟩

end Trace

end Musubi.OpHeads.Race
