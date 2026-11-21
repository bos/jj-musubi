/-
musubi moving jj operation heads that it read earlier, among jj's commands and the lockless
`jj op abandon` and `jj op integrate` (`docs/internals/design.md`, "Moving op heads"; the rows of
`docs/internals/races.md` for #168).

The state is the set of op heads, the operations (`OpHeads.Graph`: parents, fingerprint, and
whether musubi's translation cache knows each), jj's op-heads lock and musubi's watch of what it
took out. A jj command *loads* an operation and later *publishes* its own on it, under the lock,
in place of the one it loaded; a command that loads several op heads *merges* them first, under
the lock, so none writes on an op head with another beside it, but one run `--at-op`
(`cmdLoadAt`), which loads any operation. `jj op abandon` and `jj op integrate` *begin* by writing
an operation, which nothing can reach yet, and later *land* it: they add it to the op heads and
remove what they replace, with no lock, and ignore what is gone already. jj's rewrite of an
operation is an operation with its fingerprint and another id, made after what it rewrites (`rew`,
`RewInv`); the look takes only an op head for one (`overtaken_congr`, `regression_trace`).

musubi's own move is one actor: it *plans* (reads the op heads, writes the operations it will
put in), *locks*, *checks* that the op heads are those it read, writes each head one at a time,
*watches* what it took out, and *rechecks* before it lets go, taking out again what it put in
if the op heads aren't as it left them (a *look*). A look is also a step of its own. It can
*save* what it watches, as `records.json` is written with what else musubi saves, and *restart*,
which forgets what it saved nothing of. musubi's writes are a file system call each. A landing,
which `update_op_heads` makes as an add and then a removal, is one step here, as is a command's
publish or merge, which holds the lock: a read of the op heads between a landing's two calls,
which sees the rewrite beside the head it replaces, is not a state of the model.

The ghosts: `ev`, how many commands and landings changed the op heads, and `owed`, whether a
look is owed: set by what can put a rewrite beside what musubi replaced, cleared by a look that
finds nothing.

What is proved is in the theorems of the last sections: that no command's operation lands
between musubi's read and its move once it has checked (`check_no_event`); that no command runs
while musubi holds the lock (`locked_blocks_commands`); that a look finds everything of what it
watches, so that no look is owed where musubi's replacement sits beside a rewrite of what it
replaced (`quiet_of_clear`, `bad_merge_owed`); and the cases that remain, which `Trace` builds:
`remaining_case`, `at_op_case`, `abandon_both_case`, `unsaved_watch_lost` and
`read_during_the_move`.
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

/-- A move planned: the op heads read, the op heads to put in their place, what to watch,
whether to take the old ones out. -/
structure Plan where
  read : List Nat
  new : List Nat
  ents : List Replaced
  remove : Bool
  /-- Ghost: how many events had changed the op heads when they were read. -/
  ev0 : Nat

/-- Where musubi is. -/
inductive Mv where
  | idle
  | planned (p : Plan)
  | held (p : Plan)
  | writing (p : Plan) (todo : List Act)
  | watched (p : Plan)
  | rechecking (p : Plan)
  /-- Letting go of the lock. -/
  | releasing
  /-- Taking out again: about to read the op heads; whether under a move's lock. -/
  | lookRead (nested : Bool)
  | lookPlanned (nested : Bool) (heads out back : List Nat) (kept : List Replaced)
  | lookHeld (nested : Bool) (heads out back : List Nat) (kept : List Replaced)
  | lookWriting (todo : List Act) (kept : List Replaced)
  /-- The op heads changed since they were read: let go, and read again. -/
  | lookAbort (nested : Bool)

/-- In these musubi holds the lock. -/
def Mv.locked : Mv → Bool
  | .held _ | .writing _ _ | .watched _ | .rechecking _ | .releasing => true
  | .lookHeld _ _ _ _ _ | .lookWriting _ _ => true
  | .lookPlanned nested _ _ _ _ => nested
  | .lookRead nested => nested
  | .lookAbort _ => true
  | .idle | .planned _ => false

structure S where
  next : Nat
  g : Graph
  heads : List Nat
  lock : Bool
  /-- Ghost: how many commands and landings have changed the op heads. -/
  ev : Nat
  /-- Ghost: a look is owed. -/
  owed : Bool
  W : List Replaced
  /-- What `records.json` has. -/
  P : List Replaced
  /-- Operations commands have loaded, that they will publish on. -/
  jc : List Nat
  /-- The operations that `jj op abandon` and `jj op integrate` have written and not landed,
  each with what it replaces. -/
  pend : Nat → Option (List Nat)
  /-- The operations musubi wrote, known to its cache. -/
  made : List Nat
  /-- Ghost: the operation each of jj's rewrites was written from, by `jj op abandon`. A
  rewrite is made after what it rewrites, which is why the one has the other's fingerprint and a
  later id. -/
  rew : Nat → Option Nat
  mv : Mv

/-- Not an operation written and not landed yet: nothing is built on one. -/
def S.free (s : S) (p : Nat) : Prop := s.pend p = none

def Mv.isIdle : Mv → Bool
  | .idle => true
  | _ => false

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
        next := s.next + 1, g := s.g.add s.next [L] s.next false,
        heads := s.next :: s.heads.filter (· != L), jc := s.jc.erase L, ev := s.ev + 1,
        owed := true }
  /-- A command that loads several op heads merges them, under the lock. -/
  | cmdMerge {s : S} (hl : s.lock = false) (h2 : 2 ≤ s.heads.length) :
      Step s { s with
        next := s.next + 1, g := s.g.add s.next s.heads s.next false,
        heads := [s.next], ev := s.ev + 1, owed := true }
  /-- `jj op abandon` rewrites the op head `h`: writes an operation with its fingerprint. -/
  | abandonBegin {s : S} {h : Nat} {ps : List Nat} (hh : h ∈ s.heads)
      (hps : ∀ p ∈ ps, p < s.next ∧ s.free p) :
      Step s { s with
        next := s.next + 1, g := s.g.add s.next ps (s.g.fp h) false,
        pend := fun r => if r = s.next then some [h] else s.pend r,
        rew := fun r => if r = s.next then some h else s.rew r }
  /-- `jj op integrate` writes an operation on `ps`, to replace them. -/
  | integrateBegin {s : S} {ps : List Nat} (hps : ∀ p ∈ ps, p < s.next ∧ s.free p) :
      Step s { s with
        next := s.next + 1, g := s.g.add s.next ps s.next false,
        pend := fun r => if r = s.next then some ps else s.pend r }
  /-- Either lands its operation, with no lock: adds it, removes what it replaces. -/
  | land {s : S} {r : Nat} {gone : List Nat} (h : s.pend r = some gone) :
      Step s { s with
        heads := r :: s.heads.filter (fun x => !gone.contains x),
        pend := fun r' => if r' = r then none else s.pend r', ev := s.ev + 1, owed := true }
  /-- musubi writes an operation it will put in, with parents it can see. -/
  | mkOp {s : S} {ps : List Nat} {fp : Nat} (hi : s.mv = .idle)
      (hps : ∀ p ∈ ps, p < s.next ∧ s.free p) (hfp : fp ≤ s.next) :
      Step s { s with
        next := s.next + 1, g := s.g.add s.next ps fp true, made := s.next :: s.made }
  /-- It reads the op heads and plans to put `new` in their place. -/
  | plan {s : S} {keep chosen : List Nat} {from_ : List (Nat × List Nat)} {remove : Bool}
      (hi : s.mv = .idle) (hk : ∀ k ∈ keep, k ∈ s.heads) (hc : ∀ c ∈ chosen, c ∈ s.made)
      (hne : keep ++ chosen ≠ []) :
      Step s { s with mv := .planned {
        read := s.heads, new := keep ++ chosen, remove := remove, ev0 := s.ev,
        ents := entries s.g s.heads (keep ++ chosen) from_ } }
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
      Step s { s with heads := a.apply s.heads, owed := true, mv := .writing p rest }
  /-- Done writing: watches what it took out, if it did. -/
  | written {s : S} {p : Plan} (h : s.mv = .writing p []) :
      Step s { s with mv := if p.remove then .watched p else .releasing }
  | watch {s : S} {p : Plan} (h : s.mv = .watched p) :
      Step s { s with W := compose s.W p.ents, owed := true, mv := .rechecking p }
  /-- Reads the op heads again, still under the lock. If they are as it left them, it is done;
  if not, it takes out again. -/
  | recheck {s : S} {p : Plan} (h : s.mv = .rechecking p) :
      Step s { s with mv := if (OpHeads.same s.heads p.new) = true then .releasing else .lookRead true }
  | release {s : S} (h : s.mv = .releasing) :
      Step s { s with lock := false, mv := .idle }
  /-- A look, begun on its own. -/
  | lookStart {s : S} (h : s.mv = .idle) : Step s { s with mv := .lookRead false }
  /-- It reads the op heads and works out what to do. -/
  | lookNothing {s : S} {nested : Bool} {k : List Replaced} (h : s.mv = .lookRead nested)
      (hl : lookPlan s.g s.heads s.W = .nothing k) :
      Step s { s with W := k, owed := false, mv := if nested then .releasing else .idle }
  | lookFound {s : S} {nested : Bool} {out back : List Nat} {kept : List Replaced} {n : Nat}
      (h : s.mv = .lookRead nested)
      (hl : lookPlan s.g s.heads s.W = .retire out back kept n) :
      Step s { s with mv := .lookPlanned nested s.heads out back kept }
  /-- Takes the lock, unless it holds it. -/
  | lookLock {s : S} {nested : Bool} {H out back : List Nat} {kept : List Replaced}
      (h : s.mv = .lookPlanned nested H out back kept) (hl : nested = true ∨ s.lock = false) :
      Step s { s with lock := true, mv := .lookHeld nested H out back kept }
  /-- Acts only if the op heads are those it read. -/
  | lookCheck {s : S} {nested : Bool} {H out back : List Nat} {kept : List Replaced}
      (h : s.mv = .lookHeld nested H out back kept) :
      Step s { s with mv :=
        if (OpHeads.same s.heads H) = true then .lookWriting (back.map Act.add ++ out.map Act.del) kept
        else .lookAbort nested }
  | lookAbort {s : S} {nested : Bool} (h : s.mv = .lookAbort nested) :
      Step s { s with lock := nested, mv := .lookRead nested }
  | lookWrite {s : S} {a : Act} {rest : List Act} {kept : List Replaced}
      (h : s.mv = .lookWriting (a :: rest) kept) (ha : a.ok s.next s.pend) :
      Step s { s with heads := a.apply s.heads, owed := true, mv := .lookWriting rest kept }
  | lookWritten {s : S} {kept : List Replaced} (h : s.mv = .lookWriting [] kept) :
      Step s { s with W := kept, owed := true, mv := .releasing }
  /-- `records.json` is written with what musubi watches. -/
  | save {s : S} : Step s { s with P := s.W }
  /-- musubi stops, and starts again with what it saved. The lock goes with it. -/
  | restart {s : S} : Step s { s with mv := .idle, lock := false, W := s.P, owed := true }

/-- A jj command can take its step: it needs the lock free. -/
def CmdEnabled (s : S) : Prop := s.lock = false ∧ ((∃ L, L ∈ s.jc) ∨ 2 ≤ s.heads.length)

/-- The start. -/
def init : S where
  next := 1
  g := { parents := fun _ => [], fp := fun _ => 0, known := fun _ => true }
  heads := [0]
  lock := false
  ev := 0
  owed := false
  W := []
  P := []
  jc := []
  pend := fun _ => none
  made := []
  rew := fun _ => none
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
  pendLt : ∀ r gone, s.pend r = some gone → r < s.next ∧ r ∉ s.heads ∧ s.g.known r = false
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

theorem dag_add {g : Graph} (hg : g.Dag) (n : Nat) (ps : List Nat) (fp : Nat) (kn : Bool)
    (hps : ∀ p ∈ ps, p < n) : (g.add n ps fp kn).Dag := by
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
    refine ⟨dag_add dag _ _ _ _ (by simpa using hLn), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      dsimp only at hx ⊢
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := hlt x (List.mem_filter.1 hx).1; omega
    · intro r gone h
      obtain ⟨h1, h2, h3⟩ := hpl r gone h
      refine ⟨by dsimp only; omega, ?_, ?_⟩
      · intro hr
        dsimp only at hr
        rcases List.mem_cons.1 hr with rfl | hr
        · omega
        · exact h2 (List.mem_filter.1 hr).1
      · simp [Graph.add, show r ≠ s.next by omega, h3]
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
    refine ⟨dag_add dag _ _ _ _ (fun p hp => hlt p hp), ?_, ?_, ?_, hlk, ?_⟩
    · intro x hx
      dsimp only at hx ⊢
      simp at hx; omega
    · intro r gone h
      obtain ⟨h1, h2, h3⟩ := hpl r gone h
      refine ⟨by dsimp only; omega, ?_, ?_⟩
      · intro hr
        dsimp only at hr
        simp at hr; omega
      · simp [Graph.add, show r ≠ s.next by omega, h3]
    · intro x hx; dsimp only at hx ⊢; have := hjc x hx; omega
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hk p hp
      refine ⟨fun x hx => by have := h1 x hx; dsimp only; omega, h2, ?_⟩
      intro _
      exact not_same_of_add (x := s.next) (by simp) (fun hr => by have := h1 _ hr; omega)
  | abandonBegin hh hps =>
    rename_i h ps
    refine ⟨dag_add dag _ _ _ _ (fun p hp => (hps p hp).1), ?_, ?_, ?_, hlk, ?_⟩
    · intro x hx; dsimp only at hx ⊢; have := hlt x hx; omega
    · intro r gone hr
      dsimp only at hr
      by_cases e : r = s.next
      · subst e
        refine ⟨by dsimp only; omega, fun hm => ?_, by simp [Graph.add]⟩
        have := hlt _ hm; omega
      · simp only [e, ↓reduceIte] at hr
        obtain ⟨h1, h2, h3⟩ := hpl r gone hr
        exact ⟨by dsimp only; omega, h2, by simp [Graph.add, e, h3]⟩
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
  | integrateBegin hps =>
    refine ⟨dag_add dag _ _ _ _ (fun p hp => (hps p hp).1), ?_, ?_, ?_, hlk, ?_⟩
    · intro x hx; dsimp only at hx ⊢; have := hlt x hx; omega
    · intro r gone hr
      dsimp only at hr
      by_cases e : r = s.next
      · subst e
        refine ⟨by dsimp only; omega, fun hm => ?_, by simp [Graph.add]⟩
        have := hlt _ hm; omega
      · simp only [e, ↓reduceIte] at hr
        obtain ⟨h1, h2, h3⟩ := hpl r gone hr
        exact ⟨by dsimp only; omega, h2, by simp [Graph.add, e, h3]⟩
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
    obtain ⟨hr1, hr2, hr3⟩ := hpl r gone h
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
        obtain ⟨h1, h2, h3⟩ := hpl r' gone' hr'
        refine ⟨h1, fun hm => ?_, h3⟩
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
  | mkOp hi' hps hfp =>
    refine ⟨dag_add dag _ _ _ _ (fun p hp => (hps p hp).1), ?_, ?_, ?_, hlk, ?_⟩
    · intro x hx; dsimp only at hx ⊢; have := hlt x hx; omega
    · intro r gone hr
      obtain ⟨h1, h2, h3⟩ := hpl r gone hr
      exact ⟨by dsimp only; omega, h2, by simp [Graph.add, show r ≠ s.next by omega, h3]⟩
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
        exact ⟨hlt, fun r gone hr hm => (hpl r gone hr).2.1 hm, fun h => (h rfl).elim⟩
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
    · obtain ⟨h1, h2, h3⟩ := hpl r gone hr
      exact ⟨h1, apply_pend ha hr h2, h3⟩
    · intro p' hp; simp at hp
  | written h =>
    refine ⟨dag, hlt, hpl, hjc, fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    intro p' hp
    dsimp only at hp
    split at hp <;> simp at hp
  | watch h =>
    refine ⟨dag, hlt, hpl, hjc, fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    intro p' hp; simp at hp
  | recheck h =>
    refine ⟨dag, hlt, hpl, hjc, fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    intro p' hp
    dsimp only at hp
    split at hp <;> simp at hp
  | release h =>
    refine ⟨dag, hlt, hpl, hjc, fun hm => by simp [Mv.locked] at hm, ?_⟩
    intro p' hp; simp at hp
  | lookStart h =>
    refine ⟨dag, hlt, hpl, hjc, fun hm => by simp [Mv.locked] at hm, ?_⟩
    intro p' hp; simp at hp
  | lookNothing h hl =>
    rename_i nested k
    refine ⟨dag, hlt, hpl, hjc, ?_, ?_⟩
    · intro hm
      cases nested
      · simp [Mv.locked] at hm
      · exact hlk (by simp [h, Mv.locked])
    · intro p' hp
      dsimp only at hp
      split at hp <;> simp at hp
  | lookFound h hl =>
    rename_i nested out back kept n
    refine ⟨dag, hlt, hpl, hjc, ?_, ?_⟩
    · intro hm
      simp [Mv.locked] at hm
      exact hlk (by simp [h, Mv.locked, hm])
    · intro p' hp; simp at hp
  | lookLock h hl =>
    refine ⟨dag, hlt, hpl, hjc, fun _ => rfl, ?_⟩
    intro p' hp; simp at hp
  | lookCheck h =>
    refine ⟨dag, hlt, hpl, hjc, fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    intro p' hp
    dsimp only at hp
    split at hp <;> simp at hp
  | lookAbort h =>
    rename_i nested
    refine ⟨dag, hlt, hpl, hjc, ?_, ?_⟩
    · intro hm
      simpa [Mv.locked] using hm
    · intro p' hp; simp at hp
  | lookWrite h ha =>
    rename_i a rest kept
    refine ⟨dag, fun x hx => apply_lt ha hlt x hx, fun r gone hr => ?_, hjc,
      fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hpl r gone hr
      exact ⟨h1, apply_pend ha hr h2, h3⟩
    · intro p' hp; simp at hp
  | lookWritten h =>
    refine ⟨dag, hlt, hpl, hjc, fun _ => hlk (by simp [h, Mv.locked]), ?_⟩
    intro p' hp; simp at hp
  | save => exact ⟨dag, hlt, hpl, hjc, hlk, hk⟩
  | restart =>
    refine ⟨dag, hlt, hpl, hjc, fun hm => by simp [Mv.locked] at hm, ?_⟩
    intro p' hp; simp at hp


theorem Reachable.inv {s : S} (h : Reachable s) : Inv s := by
  induction h with
  | init => exact Inv.init
  | step _ hs ih => exact ih.step hs

/-! ## 1. The lock and the check keep commands out of a move -/

/-- No jj command publishes or merges while musubi holds the lock, from taking it to letting it
go: the checking, every write, the watch, the recheck and a look that takes out again. -/
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
puts in is an operation written since, or one musubi didn't read. -/
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


/-! ## 2. A look finds what is owed -/

/-- musubi's replacement of an op head sits beside a rewrite of it, in this state. -/
def Overtaken' (s : S) : Prop := Overtaken s.g s.heads s.W

instance (s : S) : Decidable (Overtaken' s) := by unfold Overtaken'; infer_instance

/-- Operations added above everything there is change nothing of the op heads. -/
theorem overtaken_ext {g g' : Graph} {heads : List Nat} {W : List Replaced} {N : Nat}
    (hk : ∀ i < N, g'.known i = g.known i) (hf : ∀ i < N, g'.fp i = g.fp i)
    (hh : ∀ x ∈ heads, x < N) (h : Overtaken g' heads W) : Overtaken g heads W := by
  obtain ⟨w, hw, x, hx, hkn, hfp, hne⟩ := h
  have hxN := hh x (List.mem_filter.1 hx).1
  exact ⟨w, hw, x, hx, by rw [← hk x hxN]; exact hkn, by rw [← hf x hxN]; exact hfp, hne⟩

/-- A look is owed, or nothing sits beside a rewrite. -/
def OwedInv (s : S) : Prop := s.owed = false → ¬ Overtaken' s

theorem OwedInv.init : OwedInv Race.init := by
  intro _ ⟨w, hw, _⟩
  simp [Race.init, liveOf] at hw

theorem OwedInv.step {s s' : S} (hi : Inv s) (ho : OwedInv s) (hs : Step s s') :
    OwedInv s' := by
  have key : ∀ (h1 : s'.owed = s.owed) (h2 : s'.heads = s.heads) (h3 : s'.W = s.W)
      (h4 : s'.g = s.g), OwedInv s' := by
    intro h1 h2 h3 h4 hf
    rw [h1] at hf
    have := ho hf
    simpa [Overtaken', h2, h3, h4] using this
  cases hs with
  | cmdLoad h => exact key rfl rfl rfl rfl
  | cmdLoadAt hL hf => exact key rfl rfl rfl rfl
  | cmdPublish hL hl => intro h; simp at h
  | cmdMerge hl h2 => intro h; simp at h
  | abandonBegin hh hps =>
    intro hf hov
    refine ho hf (overtaken_ext (N := s.next) (fun i hi' => ?_)
      (fun i hi' => ?_) hi.headsLt hov) <;> simp [Graph.add, show i ≠ s.next by omega]
  | integrateBegin hps =>
    intro hf hov
    refine ho hf (overtaken_ext (N := s.next) (fun i hi' => ?_)
      (fun i hi' => ?_) hi.headsLt hov) <;> simp [Graph.add, show i ≠ s.next by omega]
  | land h => intro h; simp at h
  | mkOp hi' hps hfp =>
    intro hf hov
    refine ho hf (overtaken_ext (N := s.next) (fun i hi' => ?_)
      (fun i hi' => ?_) hi.headsLt hov) <;> simp [Graph.add, show i ≠ s.next by omega]
  | plan hi' hk' hc hne => exact key rfl rfl rfl rfl
  | lock h hl => exact key rfl rfl rfl rfl
  | check h => exact key rfl rfl rfl rfl
  | write h ha => intro h; simp at h
  | written h => exact key rfl rfl rfl rfl
  | watch h => intro h; simp at h
  | recheck h => exact key rfl rfl rfl rfl
  | release h => exact key rfl rfl rfl rfl
  | lookStart h => exact key rfl rfl rfl rfl
  | lookNothing h hl =>
    rename_i nested k
    intro _ hov
    have hq := (lookPlan_nothing_iff (heads := s.heads) s.W).1 ⟨k, hl⟩
    have hk := lookPlan_nothing hl
    apply hq
    have hl2 : Overtaken s.g s.heads (liveOf s.heads s.W) → Overtaken s.g s.heads s.W := by
      unfold Overtaken
      rw [liveOf_liveOf]
      exact id
    apply hl2
    simpa [Overtaken', hk] using hov
  | lookFound h hl => exact key rfl rfl rfl rfl
  | lookLock h hl => exact key rfl rfl rfl rfl
  | lookCheck h => exact key rfl rfl rfl rfl
  | lookAbort h => exact key rfl rfl rfl rfl
  | lookWrite h ha => intro h; simp at h
  | lookWritten h => intro h; simp at h
  | save => exact key rfl rfl rfl rfl
  | restart => intro h; simp at h

/-- A rewrite is made after what it rewrites, and has its fingerprint: the direction of the
relation the look depends on. What a head was rewritten from is older than the head. -/
def RewInv (s : S) : Prop := ∀ x h, s.rew x = some h → x < s.next ∧ h < x ∧ s.g.fp x = s.g.fp h

theorem RewInv.init : RewInv Race.init := by
  intro x h hx; simp [Race.init] at hx

theorem RewInv.step {s s' : S} (hi : Inv s) (ho : RewInv s) (hs : Step s s') : RewInv s' := by
  have ext : ∀ (n : Nat) (ps : List Nat) (f : Nat) (kn : Bool),
      n = s.next → s'.next = s.next + 1 → s'.g = s.g.add n ps f kn → s'.rew = s.rew →
      RewInv s' := by
    intro n ps f kn hn h1 h2 h3 x h hx
    rw [h3] at hx
    obtain ⟨a, b, c⟩ := ho x h hx
    refine ⟨by omega, b, ?_⟩
    rw [h2]
    simp [Graph.add, show x ≠ n by omega, show h ≠ n by omega, c]
  cases hs with
  | cmdPublish hL hl => exact ext _ _ _ _ rfl rfl rfl rfl
  | cmdMerge hl h2 => exact ext _ _ _ _ rfl rfl rfl rfl
  | mkOp hi' hps hfp => exact ext _ _ _ _ rfl rfl rfl rfl
  | integrateBegin hps => exact ext _ _ _ _ rfl rfl rfl rfl
  | abandonBegin hh hps =>
    rename_i h0 ps
    intro x h hx
    dsimp only at hx
    have hlt0 := hi.headsLt h0 hh
    by_cases e : x = s.next
    · subst e
      simp only [↓reduceIte, Option.some.injEq] at hx
      subst hx
      refine ⟨by dsimp only; omega, hlt0, ?_⟩
      simp [Graph.add, show h0 ≠ s.next by omega]
    · simp only [e, ↓reduceIte] at hx
      obtain ⟨a, b, c⟩ := ho x h hx
      refine ⟨by dsimp only; omega, b, ?_⟩
      simp [Graph.add, show x ≠ s.next by omega, show h ≠ s.next by omega, c]
  | _ => exact ho

theorem reachable_rew {s : S} (h : Reachable s) : RewInv s := by
  induction h with
  | init => exact RewInv.init
  | step hr hs ih => exact ih.step hr.inv hs

/-- What an operation was rewritten from is older than it: a replaced head's pre-image is below
the head, never a later op head to be taken for a rewrite made since. -/
theorem pre_image_older {s : S} (h : Reachable s) {x o : Nat} (hx : s.rew x = some o) : o < x :=
  (reachable_rew h x o hx).2.1

/-- Both invariants hold in every reachable state. -/
theorem reachable_owed {s : S} (h : Reachable s) : OwedInv s := by
  induction h with
  | init => exact OwedInv.init
  | step hr hs ih => exact ih.step hr.inv hs

/-- **A look finds everything.** In a reachable state with no look owed, nothing sits beside a
rewrite of what musubi replaced. -/
theorem quiet_of_clear {s : S} (h : Reachable s) (ho : s.owed = false) : ¬ Overtaken' s :=
  reachable_owed h ho


/-! ## 3. What remains -/

/-- A jj command that loads the op heads would merge them, and a look would have found a rewrite
beside what musubi put in. -/
def BadMerge (s : S) : Prop := CmdEnabled s ∧ 2 ≤ s.heads.length ∧ Overtaken' s

/-- **Only where a look is owed.** A command merges musubi's replacement with a rewrite of what it
replaced, among those replacements musubi still watches, only where a look is owed: since musubi
last looked and found nothing, a command, a landing, musubi's own write or a restart has changed
the op heads or what is watched. It says nothing of a rewrite of what musubi no longer watches:
`unsaved_watch_lost` and `read_during_the_move`. -/
theorem bad_merge_owed {s : S} (hr : Reachable s) (hb : BadMerge s) : s.owed = true := by
  cases h : s.owed
  · exact absurd hb.2.2 (quiet_of_clear hr h)
  · rfl

/-- And never while musubi holds the lock: from checking to letting go, which includes its
recheck and a look that takes out again. -/
theorem no_bad_merge_locked {s : S} (hr : Reachable s) (hm : s.mv.locked = true) :
    ¬ BadMerge s := fun hb => locked_blocks_commands hr hm hb.1

/-- A look that finds nothing makes the merge harmless, until something changes. -/
theorem no_bad_merge_after_look {s : S} (hr : Reachable s) (ho : s.owed = false) :
    ¬ BadMerge s := fun hb => by rw [bad_merge_owed hr hb] at ho; cases ho

namespace Trace

/-- The plan of moving the op head `0` to `2`. -/
def plan : Plan :=
  { read := [0], new := [2], ents := [{ head := 0, fp := 0, images := [2], put := [2] }],
    remove := true, ev0 := 0 }

/-- `jj op abandon` has written its rewrite `1` of the op head `0`. -/
def t1 : S :=
  { Race.init with
    next := 2
    g := Race.init.g.add 1 ([] : List Nat) 0 false
    pend := fun r => if r = 1 then some [0] else none
    rew := fun r => if r = 1 then some 0 else none }

/-- musubi has written the operation `2`. -/
def t2 : S := { t1 with next := 3, g := t1.g.add 2 ([] : List Nat) 2 true, made := [2] }

def t3 : S := { t2 with mv := .planned plan }
def t4 : S := { t3 with lock := true, mv := .held plan }
def t5 : S := { t4 with mv := .writing plan [.add 2, .del 0] }
/-- Both op heads, as a jj command would find them if it could. -/
def t6 : S := { t5 with heads := [2, 0], owed := true, mv := .writing plan [.del 0] }
def t7 : S := { t6 with heads := [2], mv := .writing plan [] }
def t8 : S := { t7 with mv := .watched plan }
def t9 : S := { t8 with W := plan.ents, mv := .rechecking plan }
def t10 : S := { t9 with mv := .releasing }
def t11 : S := { t10 with lock := false, mv := .idle }
/-- The abandon lands: its rewrite is beside musubi's replacement. -/
def t12 : S :=
  { t11 with
    heads := [1, 2]
    pend := fun r' => if r' = 1 then none else t11.pend r'
    ev := 1 }

theorem r5 : Reachable t5 := by
  have r1 : Reachable t1 := .step .init
    (Step.abandonBegin (h := 0) (ps := []) (by decide) (fun p hp => by simp at hp))
  have r2 : Reachable t2 := .step r1
    (Step.mkOp (ps := []) (fp := 2) (by rfl) (fun p hp => by simp at hp) (by simp [t1]))
  have r3 : Reachable t3 := .step r2
    (Step.plan (keep := []) (chosen := [2]) (from_ := [(0, [2])]) (remove := true)
      (by rfl) (by simp) (by simp [t2]) (by simp))
  have r4 : Reachable t4 := .step r3 (Step.lock (p := plan) (by rfl) (by rfl))
  exact .step r4 (Step.check (p := plan) (by rfl))

theorem r6 : Reachable t6 :=
  .step r5 (Step.write (p := plan) (a := .add 2) (rest := [.del 0])
    (by rfl) (by simp [Act.ok, t5, t4, t3, t2, t1]))

theorem r11 : Reachable t11 := by
  have r7 : Reachable t7 := .step r6 (Step.write (p := plan) (a := .del 0) (rest := [])
    (by rfl) (by simp [Act.ok]))
  have r8 : Reachable t8 := .step r7 (Step.written (p := plan) (by rfl))
  have r9 : Reachable t9 := .step r8 (Step.watch (p := plan) (by rfl))
  have r10 : Reachable t10 := .step r9 (Step.recheck (p := plan) (by rfl))
  exact .step r10 (Step.release (by rfl))

theorem r12 : Reachable t12 :=
  .step r11 (Step.land (s := t11) (r := 1) (gone := [0]) (by rfl))

/-- **The one case a look cannot prevent.** The abandon lands after the move, and a jj command
that loads the op heads finds musubi's replacement and the abandon's rewrite to merge: `t12`
is reachable, a command can merge there, and musubi's replacement `2` of the op head `0` sits
beside `1`, which has the fingerprint of `0`. A look would take `2` out; none has run. -/
theorem remaining_case : Reachable t12 ∧ BadMerge t12 ∧ t12.owed = true := by
  refine ⟨r12, ⟨⟨rfl, Or.inr (by decide)⟩, by decide, ?_⟩, rfl⟩
  exact ⟨⟨0, 0, [2], [2]⟩, by decide, 1, by decide, by decide, by decide, by decide⟩

/-- A landing during the move: the abandon lands between musubi's two writes. musubi's recheck
finds the op heads changed, and takes `2` out again, still holding the lock, which no command
can take meanwhile. -/
theorem landing_during_the_move :
    ∃ s, Reachable s ∧ s.heads = [1] ∧ s.W = [] ∧ s.mv = .idle ∧ s.lock = false := by
  have a1 := Reachable.step r6 (Step.land (s := t6) (r := 1) (gone := [0]) (by rfl))
  have a2 := Reachable.step a1 (Step.write (p := plan) (a := .del 0) (rest := [])
    (by rfl) (by simp [Act.ok]))
  have a3 := Reachable.step a2 (Step.written (p := plan) (by rfl))
  have a4 := Reachable.step a3 (Step.watch (p := plan) (by rfl))
  have a5 := Reachable.step a4 (Step.recheck (p := plan) (by rfl))
  have a6 := Reachable.step a5 (Step.lookFound (nested := true) (out := [2]) (back := [])
    (kept := []) (n := 1) (by rfl) (by decide))
  have a7 := Reachable.step a6 (Step.lookLock (nested := true) (H := [1, 2]) (out := [2])
    (back := []) (kept := []) (by rfl) (Or.inl rfl))
  have a8 := Reachable.step a7 (Step.lookCheck (nested := true) (H := [1, 2]) (out := [2])
    (back := []) (kept := []) (by rfl))
  have a9 := Reachable.step a8 (Step.lookWrite (a := .del 2) (rest := []) (kept := [])
    (by rfl) (by simp [Act.ok]))
  have a10 := Reachable.step a9 (Step.lookWritten (kept := []) (by rfl))
  have a11 := Reachable.step a10 (Step.release (by rfl))
  exact ⟨_, a11, by rfl, by rfl, by rfl, by rfl⟩

/-- Nothing sits beside a rewrite when nothing is watched. -/
theorem quiet_of_unwatched {s : S} (h : liveOf s.heads s.W = []) : ¬ Overtaken' s := by
  rintro ⟨w, hw, -⟩
  rw [h] at hw
  cases hw

/-- **The regression the walk below the op heads made** (musubi once took what a replaced head was
rewritten from for a rewrite made since). The op head `1` is an unpublished operation. A command
loads it; `jj op abandon` rewrites it to `2`, which becomes the op head; musubi replaces `2` with
`3` and watches it. The command then lands `4` on `1`, beside `3`. `4` is no rewrite of `2`: it is
a new operation on what `2` was rewritten from (`rew 2 = 1`, and `1` is older). The look at the op
heads finds nothing; the walk below them found `1`, with the fingerprint of `2`, and took `3` out
(`OvertakenBelow`). -/
theorem regression_trace :
    ∃ s, Reachable s ∧ s.heads = [4, 3] ∧ s.rew 2 = some 1 ∧ ¬ Overtaken' s ∧
      OvertakenBelow s.g s.heads s.W := by
  let plan : Plan :=
    { read := [2], new := [3], ents := [{ head := 2, fp := 1, images := [3], put := [3] }],
      remove := true, ev0 := 2 }
  have a1 := Reachable.step Reachable.init
    (Step.cmdLoad (s := Race.init) (L := 0) (by rfl))
  have a2 := Reachable.step a1 (Step.cmdPublish (L := 0) (by decide) (by rfl))
  have a3 := Reachable.step a2 (Step.cmdLoad (L := 1) (by rfl))
  have a4 := Reachable.step a3 (Step.abandonBegin (h := 1) (ps := []) (by decide)
    (fun p hp => by simp at hp))
  have a5 := Reachable.step a4 (Step.land (r := 2) (gone := [1]) (by rfl))
  have a6 := Reachable.step a5 (Step.mkOp (ps := []) (fp := 3) (by rfl)
    (fun p hp => by simp at hp) (by decide))
  have a7 := Reachable.step a6 (Step.plan (keep := []) (chosen := [3]) (from_ := [(2, [3])])
    (remove := true) (by rfl) (by simp) (by decide) (by simp))
  have a8 := Reachable.step a7 (Step.lock (p := plan) (by rfl) (by rfl))
  have a9 := Reachable.step a8 (Step.check (p := plan) (by rfl))
  have a10 := Reachable.step a9 (Step.write (p := plan) (a := .add 3) (rest := [.del 2])
    (by rfl) (show _ ∧ _ from ⟨by decide, by rfl⟩))
  have a11 := Reachable.step a10 (Step.write (p := plan) (a := .del 2) (rest := [])
    (by rfl) (by simp [Act.ok]))
  have a12 := Reachable.step a11 (Step.written (p := plan) (by rfl))
  have a13 := Reachable.step a12 (Step.watch (p := plan) (by rfl))
  have a14 := Reachable.step a13 (Step.recheck (p := plan) (by rfl))
  have a15 := Reachable.step a14 (Step.release (by rfl))
  have a16 := Reachable.step a15 (Step.cmdPublish (L := 1) (by decide) (by rfl))
  refine ⟨_, a16, by rfl, by rfl, ?_, ?_⟩
  · -- `4` is unknown, has a fingerprint of its own, and is the only op head beside
    decide
  · exact ⟨⟨2, 1, [3], [3]⟩, by decide, 4, by decide, 1,
      .step (by decide) (by decide) (show 1 ∈ _ by decide) (.here (by decide) (by decide)),
      by decide, by decide⟩

/-- **`--at-op`.** A command run at the rewrite `1` beside musubi's replacement `2` of the op head
`0` loads it whatever the op heads are, and writes its operation `3` on it with no merge. It is
the only op head beside `2` then, an operation of its own: the look finds nothing, and a command
merges `3` and `2`. -/
theorem at_op_case :
    ∃ s, Reachable s ∧ s.heads = [3, 2] ∧ s.rew 1 = some 0 ∧ ¬ Overtaken' s ∧ CmdEnabled s := by
  have b1 := Reachable.step r12 (Step.cmdLoadAt (s := t12) (L := 1) (by decide) (by rfl))
  have b2 := Reachable.step b1 (Step.cmdPublish (L := 1) (by decide) (by rfl))
  exact ⟨_, b2, by rfl, by rfl, by decide, ⟨rfl, Or.inr (by decide)⟩⟩

/-- **Another abandon that rewrites both.** After the move and the first abandon's landing, the
op heads are musubi's replacement `2` and the rewrite `1`; a second `jj op abandon` reads them
both and lands its own rewrites `3` of `2` and `4` of `1`. Neither is musubi's, so nothing it
watches is an op head, and a look finds nothing while a command merges them. -/
theorem abandon_both_case :
    ∃ s, Reachable s ∧ s.heads = [4, 3] ∧ s.rew 3 = some 2 ∧ s.rew 4 = some 1 ∧
      ¬ Overtaken' s ∧ CmdEnabled s := by
  have c1 := Reachable.step r12 (Step.abandonBegin (s := t12) (h := 2) (ps := [])
    (by decide) (fun p hp => by simp at hp))
  have c2 := Reachable.step c1 (Step.abandonBegin (h := 1) (ps := []) (by decide)
    (fun p hp => by simp at hp))
  have c3 := Reachable.step c2 (Step.land (r := 3) (gone := [2]) (by rfl))
  have c4 := Reachable.step c3 (Step.land (r := 4) (gone := [1]) (by rfl))
  exact ⟨_, c4, by decide, by rfl, by rfl, quiet_of_unwatched (by decide), ⟨rfl, Or.inr (by decide)⟩⟩

/-- **Restart.** musubi stops after the move and starts again before the abandon lands. If
`records.json` was written after the move, the watch survives, and a look finds the rewrite. -/
theorem saved_watch_survives : ∃ s, Reachable s ∧ Overtaken' s ∧ s.mv = .idle := by
  have b1 := Reachable.step r11 (Step.save (s := t11))
  have b2 := Reachable.step b1 (Step.restart (s := _))
  have b3 := Reachable.step b2 (Step.land (r := 1) (gone := [0]) (by rfl))
  exact ⟨_, b3, ⟨⟨0, 0, [2], [2]⟩, by decide, 1, by decide, by decide, by decide, by decide⟩,
    by rfl⟩

/-- If it was not, the watch is gone, the abandon lands, and a look has nothing to find while
a command merges the two. -/
theorem unsaved_watch_lost :
    ∃ s, Reachable s ∧ s.heads = [1, 2] ∧ ¬ Overtaken' s ∧ CmdEnabled s := by
  have b1 := Reachable.step r11 (Step.restart (s := t11))
  have b2 := Reachable.step b1 (Step.land (r := 1) (gone := [0]) (by rfl))
  exact ⟨_, b2, by decide, quiet_of_unwatched (by decide), ⟨rfl, Or.inr (by decide)⟩⟩

/-- **A second window.** `jj op abandon` reads every op head and replaces each with no lock, so
one that reads them while musubi moves them, after it has put the new head `1` in and before it
has taken the old head `0` out, rewrites both, and lands the two rewrites. The abandon begins at
once for the two op heads it reads; its rewrites are `2` of `1`, musubi's replacement, and `3` of
`0`, the old head. musubi watches an op head it took out while its replacement is an op head;
`1` is none by then, and a look finds nothing; a command merges `3` and `2`. -/
theorem read_during_the_move :
    ∃ s, Reachable s ∧ s.heads = [3, 2] ∧ ¬ Overtaken' s ∧ CmdEnabled s ∧
      s.g.fp 3 = s.g.fp 0 ∧ s.g.fp 2 = s.g.fp 1 := by
  let plan : Plan :=
    { read := [0], new := [1], ents := [{ head := 0, fp := 0, images := [1], put := [1] }],
      remove := true, ev0 := 0 }
  have e1 := Reachable.step Reachable.init
    (Step.mkOp (s := Race.init) (ps := []) (fp := 1) (by rfl) (fun p hp => by simp at hp)
      (by simp [Race.init]))
  have e2 := Reachable.step e1 (Step.plan (keep := []) (chosen := [1]) (from_ := [(0, [1])])
    (remove := true) (by rfl) (by simp) (by decide) (by simp))
  have e3 := Reachable.step e2 (Step.lock (p := plan) (by rfl) (by rfl))
  have e4 := Reachable.step e3 (Step.check (p := plan) (by rfl))
  have e5 := Reachable.step e4 (Step.write (p := plan) (a := .add 1) (rest := [.del 0])
    (by rfl) (show _ ∧ _ from ⟨by decide, by rfl⟩))
  have e6 := Reachable.step e5 (Step.abandonBegin (h := 1) (ps := []) (by decide)
    (fun p hp => by simp at hp))
  have e7 := Reachable.step e6 (Step.abandonBegin (h := 0) (ps := []) (by decide)
    (fun p hp => by simp at hp))
  have e8 := Reachable.step e7 (Step.write (p := plan) (a := .del 0) (rest := [])
    (by rfl) (by simp [Act.ok]))
  have e9 := Reachable.step e8 (Step.written (p := plan) (by rfl))
  have e10 := Reachable.step e9 (Step.watch (p := plan) (by rfl))
  have e11 := Reachable.step e10 (Step.recheck (p := plan) (by rfl))
  have e12 := Reachable.step e11 (Step.release (by rfl))
  have e13 := Reachable.step e12 (Step.land (r := 2) (gone := [1]) (by rfl))
  have e14 := Reachable.step e13 (Step.land (r := 3) (gone := [0]) (by rfl))
  exact ⟨_, e14, by decide, quiet_of_unwatched (by decide), ⟨rfl, Or.inr (by decide)⟩, by rfl,
    by rfl⟩

end Trace

end Musubi.OpHeads.Race
