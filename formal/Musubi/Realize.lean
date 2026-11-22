/-
Realization against jj (docs/internals/design.md, "Translation" and "Moving op heads"): musubi
writes other machines' work into this machine's jj repository as operations, while the user's
`jj` commands run when they like and musubi can crash between any two steps.

The model is of jj, not of musubi's code. It has jj's operation store, whose operations never
change once written, each with its parents and its view; the op heads; jj's op-heads lock; and
jj's merge of several op heads into one view (`Jj.load`), abstract, with the laws jj's merge obeys
(`Jj`), which `node::realize_laws` pins against jj. A `jj` command publishes on an operation it
loaded, under the lock, in place of it (`Step.cmd`), and a command that loads several op heads
drops those below another (`Step.collapse`) and merges the rest, under the lock (`Step.merge`).

Of musubi the model assumes three things about the op heads, and what it writes:

* (R1) It writes an operation before it touches the op heads with it: it adds only operations
  that exist.
* (R2) It adds its new op head before it removes any old one (`Step.del` needs it added).
* (R3) It removes op heads only under jj's lock, after checking that the op heads are still
  those it read (`Step.check`), and only op heads below the one it added (`Plan.drop`).
* What it writes: a realization of received work, whose view the hive gives (`Step.realize`,
  `real`, marked as received), or jj's merge of a realization with the op heads (`Step.mergeWith`,
  `merged`), as jj would make it; and it publishes one of those (`Step.plan`).

Everything else musubi does is free: when it writes, which realization, whether it merges before
publishing or publishes beside the op heads, and when it gives up and starts again. The code
writes the merge, and the copies of the realization and the merge that exporting to `.git`
makes, under the lock after its check; the model has them written before it reads the op heads.
Writing an operation touches neither the op heads nor the lock, and a check that passes means
the op heads haven't changed since they were read, since an operation taken out of them never
comes back; so a run of the code is a run of the model with those writes moved earlier. An
exported copy has the same parents and view but for this machine's record of `.git`.

The promises, in the user's words, and their theorems:

1. Nothing you did is lost: every operation your `jj` commands wrote stays in the op log
   (`nothing_lost`).
2. You see what jj would show: every step but a command of yours leaves what jj shows as it was,
   or shows jj's merge of the op heads with a realization, at the step that publishes it
   (`shown_step`, `publish_shows_merge`).
3. Crashes are harmless: every state a run with crashes reaches, a run without them reaches too,
   with the same operations, op log and view, but for op heads below another op head, which jj
   drops when it next loads (`crash_harmless`).
4. Received work isn't sent back as yours: musubi writes only realizations, which carry their
   mark, and jj's merges of a realization with op heads beside it (`musubi_writes`, `ops_known`).
   This follows from what the model assumes musubi writes; the theorems record it.
5. It finishes: an attempt that no command or jj load interrupts passes its check
   (`quiet_check_passes`), and from every state musubi and jj alone can reach one op head with the
   received work in it (`finishes`): nothing in the repository can stop it finishing.
6. Other machines' workspaces appear, and realization never moves one of your own: with one op
   head, where the realization leaves your workspace and its commit alone, publishing it leaves
   the workspace where the op head has it (`own_workspace_kept`), and a workspace the realization
   records that the op head left alone appears as it records it (`others_workspace_appears`).
   With two op heads of yours that moved your workspace apart, the strict reading is false:
   `concurrent_tests` has the case, ignored.

Left out: `jj op abandon` and `jj op integrate`, which take no lock (`OpHeadsRace.lean` has them
against musubi's check); a crash of a `jj` command, which leaves only an operation nothing names;
this machine's record of `.git` in a view, which `Refs.lean` models; and translation, which
decides what a realization's view is and which `Names.lean` and the protocol model cover in part.
`settledE` is what the oracle's `realization` request answers, the operations whose merge jj must
show once a realization is published (`settled_sound`).
-/
import Musubi.Dag
import Musubi.OpHeadsRace

namespace Musubi.Realize

open Musubi.OpHeads (same same_iff)
open Musubi.OpHeads.Race (Act Act.apply)

/-! ## jj -/

/-- jj, as far as realization needs it. `load par view hs` is the view jj shows at the op heads
`hs`: it drops the op heads below another and merges the rest, in the order the operations ended
(`resolve_op_heads` and `merge_operations`). `ws v n` is the commit of workspace `n` in the view
`v`, and `keeps v b n c` says that `v` records no change since `b` that jj's merge carries to
workspace `n` at commit `c`: neither a move of `n` nor a rewrite or abandonment of `c`.

The laws are what jj does, pinned by `node::realize_laws` but for `load_single` and `load_local`,
which are how jj loads at all: one op head is its own view; the order jj finds op heads in
doesn't matter, as it sorts them by when they ended, which assumes they ended at different
times; an op head below another is dropped; jj reads nothing but the operations below the op
heads; and an operation `r` beside one op head `h` that descends from `r`'s parents leaves alone a
workspace that `r` keeps at `h`'s commit, and takes `r`'s change to one that `h` keeps at `r`'s
commit. With several op heads, jj's merge can go through a common ancestor below some of them
that changed the workspace and changed it back, so these two laws are for one op head. -/
structure Jj (V N C : Type) where
  load : (Nat → List Nat) → (Nat → V) → List Nat → V
  ws : V → N → Option C
  keeps : V → V → N → Option C → Prop
  load_single : ∀ par view h, load par view [h] = view h
  load_congr : ∀ par view (hs hs' : List Nat), (∀ x, x ∈ hs ↔ x ∈ hs') →
    load par view hs = load par view hs'
  load_drop : ∀ par view (hs : List Nat) a b, ParLt par → a ∈ hs → b ∈ hs → a ≠ b →
    Anc par a b → load par view hs = load par view (hs.filter (· != a))
  load_local : ∀ par par' view view' (hs : List Nat),
    (∀ x, (∃ h ∈ hs, Anc par x h) → par x = par' x ∧ view x = view' x) →
    load par view hs = load par' view' hs
  load_keeps : ∀ par view h r n, ParLt par → (∀ p ∈ par r, Anc par p h) → ¬ Anc par r h →
    keeps (view r) (load par view (par r)) n (ws (view h) n) →
    ws (load par view [h, r]) n = ws (view h) n
  load_takes : ∀ par view h r n, ParLt par → (∀ p ∈ par r, Anc par p h) → ¬ Anc par r h →
    keeps (view h) (load par view (par r)) n (ws (view r) n) →
    ws (load par view [h, r]) n = ws (view r) n

/-- The laws don't contradict each other: a view with nothing in it obeys them. That is all this
shows. -/
def Jj.trivial : Jj Unit Unit Unit where
  load _ _ _ := ()
  ws _ _ := none
  keeps _ _ _ _ := True
  load_single _ _ _ := rfl
  load_congr _ _ _ _ _ := rfl
  load_drop _ _ _ _ _ _ _ _ _ _ := rfl
  load_local _ _ _ _ _ _ := rfl
  load_keeps _ _ _ _ _ _ _ _ _ := rfl
  load_takes _ _ _ _ _ _ _ _ _ := rfl

variable {V N C : Type} (J : Jj V N C)

/-- jj shows the same at op heads `A` as at `B ⊆ A` when everything in `A` is below something in
`B`: it drops the rest. -/
theorem load_dom {par : Nat → List Nat} {view : Nat → V} (hlt : ParLt par) :
    ∀ (n : Nat) (A B : List Nat), A.length ≤ n → (∀ x ∈ B, x ∈ A) →
      (∀ x ∈ A, ∃ y ∈ B, Anc par x y) → J.load par view A = J.load par view B := by
  intro n
  induction n with
  | zero =>
    intro A B hn hBinA _
    have hA : A = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hn)
    subst hA
    apply J.load_congr
    intro x
    exact ⟨fun h => by simp at h, fun h => hBinA x h⟩
  | succ n ih =>
    intro A B hn hBinA hAinB
    by_cases hx : ∃ x ∈ A, x ∉ B
    · obtain ⟨x, hxA, hxB⟩ := hx
      obtain ⟨y, hyB, hxy⟩ := hAinB x hxA
      have hne : x ≠ y := fun e => hxB (e ▸ hyB)
      rw [J.load_drop par view A x y hlt hxA (hBinA y hyB) hne hxy]
      apply ih
      · have : (A.filter (· != x)).length < A.length :=
          List.length_filter_lt_length_iff_exists.2 ⟨x, hxA, by simp⟩
        omega
      · intro z hz
        refine List.mem_filter.2 ⟨hBinA z hz, ?_⟩
        have : z ≠ x := fun e => hxB (e ▸ hz)
        simpa using this
      · intro z hz
        exact hAinB z (List.mem_filter.1 hz).1
    · apply J.load_congr
      intro z
      refine ⟨fun h => ?_, fun h => hBinA z h⟩
      exact Classical.byContradiction fun hn => hx ⟨z, h, hn⟩

theorem load_dom' {par : Nat → List Nat} {view : Nat → V} (hlt : ParLt par) {A B : List Nat}
    (hBinA : ∀ x ∈ B, x ∈ A) (hAinB : ∀ x ∈ A, ∃ y ∈ B, Anc par x y) :
    J.load par view A = J.load par view B :=
  load_dom J hlt A.length A B (Nat.le_refl _) hBinA hAinB

/-- Adding an operation below an op head changes nothing jj shows. -/
theorem load_below {par : Nat → List Nat} {view : Nat → V} (hlt : ParLt par) {hs : List Nat}
    {r h : Nat} (hh : h ∈ hs) (hr : Anc par r h) :
    J.load par view (hs ++ [r]) = J.load par view hs := by
  apply load_dom' J hlt
  · intro x hx; exact List.mem_append.2 (Or.inl hx)
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ⟨x, hx, Anc.refl⟩
    · simp at hx; subst hx; exact ⟨h, hh, hr⟩

/-! ### The operations jj merges -/

/-- The maximal elements of a list of operations. -/
abbrev Max (par : Nat → List Nat) (hs : List Nat) : OSet := maxSet par (· ∈ hs)

theorem le_foldr_max {y : Nat} : ∀ {hs : List Nat}, y ∈ hs → y ≤ hs.foldr max 0
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

theorem max_covers {par : Nat → List Nat} (hlt : ParLt par) {hs : List Nat} {x : Nat}
    (hx : x ∈ hs) : ∃ y, Max par hs y ∧ Anc par x y :=
  maxSet_covers hlt (B := hs.foldr max 0 + 1)
    (fun _ hy => Nat.lt_succ_of_le (le_foldr_max hy)) hx

/-- jj shows at op heads what it shows at their maximal elements. -/
theorem load_max {par : Nat → List Nat} {view : Nat → V} (hlt : ParLt par) {hs ps : List Nat}
    (hps : ∀ x, x ∈ ps ↔ Max par hs x) : J.load par view hs = J.load par view ps := by
  apply load_dom' J hlt
  · intro x hx; exact ((hps x).1 hx).1
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := max_covers hlt hx
    exact ⟨y, (hps y).2 hy, hxy⟩

/-- Two lists of op heads, one inside the other and everything in the larger below something in
the smaller, have the same maximal elements. -/
theorem max_dom {par : Nat → List Nat} (hlt : ParLt par) {A B : List Nat}
    (hBinA : ∀ x ∈ B, x ∈ A) (hAinB : ∀ x ∈ A, ∃ y ∈ B, Anc par x y) (x : Nat) :
    Max par A x ↔ Max par B x := by
  constructor
  · rintro ⟨hxA, hmax⟩
    obtain ⟨y, hyB, hxy⟩ := hAinB x hxA
    have e := hmax y (hBinA y hyB) hxy
    subst e
    exact ⟨hyB, fun z hz hxz => hmax z (hBinA z hz) hxz⟩
  · rintro ⟨hxB, hmax⟩
    refine ⟨hBinA x hxB, fun z hz hxz => ?_⟩
    obtain ⟨w, hwB, hzw⟩ := hAinB z hz
    have e := hmax w hwB (hxz.trans hzw)
    subst e
    exact Anc.antisymm hlt hxz hzw

/-- `max_dom` with one more operation on both. -/
theorem max_dom_append {par : Nat → List Nat} (hlt : ParLt par) {A B : List Nat}
    (hBinA : ∀ x ∈ B, x ∈ A) (hAinB : ∀ x ∈ A, ∃ y ∈ B, Anc par x y) (r x : Nat) :
    Max par (A ++ [r]) x ↔ Max par (B ++ [r]) x := by
  apply max_dom hlt
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact List.mem_append.2 (Or.inl (hBinA y hy))
    · exact List.mem_append.2 (Or.inr hy)
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨z, hz, hyz⟩ := hAinB y hy
      exact ⟨z, List.mem_append.2 (Or.inl hz), hyz⟩
    · exact ⟨y, List.mem_append.2 (Or.inr hy), Anc.refl⟩

/-- Ancestry below the next fresh id doesn't change when the fresh id is written. -/
theorem anc_upd {par : Nat → List Nat} (hlt : ParLt par) {o : Nat} {L : List Nat}
    (hL : ∀ p ∈ L, p < o) {a x : Nat} (hx : x < o) : Anc (upd par o L) a x ↔ Anc par a x :=
  anc_upd_iff hlt hL hx

theorem max_upd {par : Nat → List Nat} (hlt : ParLt par) {o : Nat} {L : List Nat}
    (hL : ∀ p ∈ L, p < o) {hs : List Nat} (hhs : ∀ h ∈ hs, h < o) (x : Nat) :
    Max (upd par o L) hs x ↔ Max par hs x := by
  constructor
  · rintro ⟨hx, hm⟩
    exact ⟨hx, fun y hy hxy => hm y hy ((anc_upd hlt hL (hhs y hy)).2 hxy)⟩
  · rintro ⟨hx, hm⟩
    exact ⟨hx, fun y hy hxy => hm y hy ((anc_upd hlt hL (hhs y hy)).1 hxy)⟩

/-- Writing a fresh operation changes nothing jj shows at older op heads. -/
theorem load_upd {par : Nat → List Nat} {view : Nat → V} (hlt : ParLt par) {o : Nat}
    (L : List Nat) (v : V) {hs : List Nat} (hhs : ∀ h ∈ hs, h < o) :
    J.load (upd par o L) (upd view o v) hs = J.load par view hs := by
  symm
  apply J.load_local
  rintro x ⟨h, hh, hxh⟩
  have : x < o := Nat.lt_of_le_of_lt (hxh.le hlt) (hhs h hh)
  exact ⟨(upd_lt _ _ this).symm, (upd_lt _ _ this).symm⟩

/-! ## The repository, your commands and musubi -/

theorem mem_add {hs : List Nat} {n x : Nat} : x ∈ Act.apply hs (.add n) ↔ x = n ∨ x ∈ hs := by
  simp only [Act.apply]
  split
  · rename_i h
    constructor
    · exact Or.inr
    · rintro (rfl | hx)
      · exact List.contains_iff_mem.1 h
      · exact hx
  · simp

theorem mem_del {hs : List Nat} {d x : Nat} : x ∈ Act.apply hs (.del d) ↔ x ∈ hs ∧ x ≠ d := by
  simp [Act.apply]

/-- A publication musubi has planned: the op heads it read, the realization it publishes, the
operation it adds, which is the realization or jj's merge of it with those op heads, and the op
heads it takes out once that is in, each below it. `ev0` is a ghost: how many changes the op
heads had seen when it read them. -/
structure Plan where
  read : List Nat
  rz : Nat
  new : Nat
  drop : List Nat
  ev0 : Nat

/-- Where musubi is in a publication. -/
inductive Mv where
  | idle
  | planned (p : Plan)
  | held (p : Plan)
  /-- Holding jj's lock, having checked the op heads: `added` once the new op head is in, with
  the op heads still to take out. -/
  | writing (p : Plan) (added : Bool) (todo : List Nat)

/-- In these musubi holds jj's op-heads lock. -/
def Mv.locked : Mv → Bool
  | .held _ | .writing _ _ _ => true
  | .idle | .planned _ => false

/-- The repository and musubi. The operations are those below `next`, each with its parents and
view, which never change once written; the root is `0`. `mine`, `real`, `merged` and `jjm` are
ghosts: the operations your commands wrote, the realizations musubi wrote, the merges musubi
wrote, and those jj's own loads wrote. `ev` is a ghost too: how many times a command or jj's
load changed the op heads. -/
structure S (V : Type) where
  next : Nat
  par : Nat → List Nat
  view : Nat → V
  heads : List Nat
  mv : Mv
  mine : List Nat
  real : List Nat
  merged : List Nat
  jjm : List Nat
  ev : Nat

/-- jj's op-heads lock is held: only musubi holds it across steps, since a command's locked
work is one step here. -/
def S.locked (s : S V) : Bool := s.mv.locked

/-- `s` with the operation `s.next` written, on `ps`, with the view `v`. -/
def S.fresh (s : S V) (ps : List Nat) (v : V) : S V :=
  { s with next := s.next + 1, par := upd s.par s.next ps, view := upd s.view s.next v }

/-- What musubi may publish, given the op heads it read: the realization `r`, or a merge of it
with them, whose parents are what jj merges (`Max`). -/
def Target (par : Nat → List Nat) (merged read : List Nat) (r n : Nat) : Prop :=
  n = r ∨ (n ∈ merged ∧ ∀ x, x ∈ par n ↔ Max par (read ++ [r]) x)

/-- The steps. `crashes` says whether musubi can crash. -/
inductive Step (crashes : Bool) : S V → S V → Prop
  /-- A `jj` command of yours, run on the operation `L` it loaded (the op head, or any operation
  `--at-op`), publishes its operation on it with the view it likes, under the lock, in place of
  `L`. -/
  | cmd {s : S V} {L : Nat} (v : V) (hL : L < s.next) (hl : s.locked = false) :
      Step crashes s { s.fresh [L] v with
        heads := s.next :: Act.apply s.heads (.del L), mine := s.next :: s.mine, ev := s.ev + 1 }
  /-- jj, loading several op heads with one above all the others, drops the others, under the
  lock. Whoever runs it, a command of yours or musubi. -/
  | collapse {s : S V} {m : Nat} (hl : s.locked = false)
      (hm : ∀ x, Max s.par s.heads x ↔ x = m) (h1 : s.heads ≠ [m]) :
      Step crashes s { s with heads := [m], ev := s.ev + 1 }
  /-- jj, loading several op heads, merges those not below another, under the lock. -/
  | merge {s : S V} {ps : List Nat} (hl : s.locked = false)
      (hps : ∀ x, x ∈ ps ↔ Max s.par s.heads x) (h2 : ∃ a ∈ ps, ∃ b ∈ ps, a ≠ b) :
      Step crashes s { s.fresh ps (J.load s.par s.view ps) with
        heads := [s.next], jjm := s.next :: s.jjm, ev := s.ev + 1 }
  /-- musubi writes a realization of received work: parents that exist, and the view the hive
  gives it. -/
  | realize {s : S V} {ps : List Nat} (v : V) (hi : s.mv = .idle) (hps : ∀ p ∈ ps, p < s.next) :
      Step crashes s { s.fresh ps v with real := s.next :: s.real }
  /-- musubi writes jj's merge of a realization not yet in the op log with the op heads, some
  beside it, as jj would merge them. -/
  | mergeWith {s : S V} {r : Nat} {ps : List Nat} (hi : s.mv = .idle) (hr : r ∈ s.real)
      (hnew : ∀ h ∈ s.heads, ¬ Anc s.par r h) (hbeside : ∃ h ∈ s.heads, ¬ Anc s.par h r)
      (hps : ∀ x, x ∈ ps ↔ Max s.par (s.heads ++ [r]) x) :
      Step crashes s { s.fresh ps (J.load s.par s.view ps) with merged := s.next :: s.merged }
  /-- musubi reads the op heads and plans to publish. -/
  | plan {s : S V} {r n : Nat} {drop : List Nat} (hi : s.mv = .idle) (hr : r ∈ s.real)
      (ht : Target s.par s.merged s.heads r n) (hd : ∀ d ∈ drop, d ≠ n ∧ Anc s.par d n) :
      Step crashes s { s with mv := .planned ⟨s.heads, r, n, drop, s.ev⟩ }
  /-- It takes jj's lock. -/
  | lock {s : S V} {p : Plan} (h : s.mv = .planned p) : Step crashes s { s with mv := .held p }
  /-- It checks the op heads are those it read; if not, it lets go and moves nothing. -/
  | check {s : S V} {p : Plan} (h : s.mv = .held p) :
      Step crashes s
        { s with mv := if same s.heads p.read then .writing p false p.drop else .idle }
  /-- It adds its new op head. -/
  | add {s : S V} {p : Plan} {todo : List Nat} (h : s.mv = .writing p false todo) :
      Step crashes s
        { s with heads := Act.apply s.heads (.add p.new), mv := .writing p true todo }
  /-- Then takes out one op head. -/
  | del {s : S V} {p : Plan} {d : Nat} {todo : List Nat}
      (h : s.mv = .writing p true (d :: todo)) :
      Step crashes s { s with heads := Act.apply s.heads (.del d), mv := .writing p true todo }
  /-- And lets go of the lock. -/
  | done {s : S V} {p : Plan} (h : s.mv = .writing p true []) :
      Step crashes s { s with mv := .idle }
  /-- musubi crashes: it forgets where it was, and the lock goes with the process. -/
  | crash {s : S V} (hc : crashes = true) : Step crashes s { s with mv := .idle }

/-- A repository with only its root operation, whose view is `v0`. -/
def init (v0 : V) : S V := ⟨1, fun _ => [], fun _ => v0, [0], .idle, [], [], [], [], 0⟩

inductive Reach (crashes : Bool) (v0 : V) : S V → Prop
  | init : Reach crashes v0 (init v0)
  | step {s s' : S V} : Reach crashes v0 s → Step J crashes s s' → Reach crashes v0 s'

/-- What jj shows: its merge of the op heads. -/
def shown (s : S V) : V := J.load s.par s.view s.heads

/-- `x` is in the op log: below an op head. -/
def InLog (s : S V) (x : Nat) : Prop := ∃ h ∈ s.heads, Anc s.par x h

/-! ## What holds in every reachable state -/

/-- A planned publication, as far as the store goes. -/
def PlanOk (s : S V) (p : Plan) : Prop :=
  (∀ x ∈ p.read, x < s.next) ∧ p.rz ∈ s.real ∧ Target s.par s.merged p.read p.rz p.new ∧
    (∀ d ∈ p.drop, d ≠ p.new ∧ Anc s.par d p.new) ∧ p.ev0 ≤ s.ev

/-- Where musubi is: from reading the op heads until checking them, they are unchanged unless
a command or jj's load ran; from the check until the new op head is in, they are those read; and
then the new op head stays in. -/
def CtlOk (s : S V) : Mv → Prop
  | .idle => True
  | .planned p => PlanOk s p ∧ (s.ev = p.ev0 → same s.heads p.read = true)
  | .held p => PlanOk s p ∧ (s.ev = p.ev0 → same s.heads p.read = true)
  | .writing p added todo => p.new < s.next ∧ (∀ d ∈ todo, d ≠ p.new ∧ Anc s.par d p.new) ∧
      (added = false → same s.heads p.read = true ∧ PlanOk s p) ∧
      (added = true → p.new ∈ s.heads)

structure Inv (s : S V) : Prop where
  dag : ParLt s.par
  heads_lt : ∀ h ∈ s.heads, h < s.next
  heads_ne : s.heads ≠ []
  mine_lt : ∀ x ∈ s.mine, x < s.next
  real_lt : ∀ x ∈ s.real, x < s.next
  jjm_lt : ∀ x ∈ s.jjm, x < s.next
  merged : ∀ m ∈ s.merged, m < s.next ∧ s.view m = J.load s.par s.view (s.par m) ∧
    ∃ r ∈ s.real, r ∈ s.par m ∧ ∃ h ∈ s.par m, h ≠ r
  known : ∀ x, 0 < x → x < s.next → x ∈ s.mine ∨ x ∈ s.real ∨ x ∈ s.merged ∨ x ∈ s.jjm
  kept : ∀ u ∈ s.mine, InLog s u
  ctl : CtlOk s s.mv

/-! ### Facts about ancestry as the store grows -/

theorem anc_agree {p₁ p₂ : Nat → List Nat} (hlt : ParLt p₁) {n : Nat}
    (hagree : ∀ y < n, p₂ y = p₁ y) {a x : Nat} (hx : x < n) : Anc p₂ a x ↔ Anc p₁ a x :=
  (anc_local (fun b hb => (hagree b (Nat.lt_of_le_of_lt (hb.le hlt) hx)).symm)).symm

theorem max_agree {p₁ p₂ : Nat → List Nat} (hlt : ParLt p₁) {n : Nat}
    (hagree : ∀ y < n, p₂ y = p₁ y) {hs : List Nat} (hhs : ∀ h ∈ hs, h < n) (x : Nat) :
    Max p₂ hs x ↔ Max p₁ hs x := by
  constructor
  · rintro ⟨hx, hm⟩
    exact ⟨hx, fun y hy hxy => hm y hy ((anc_agree hlt hagree (hhs y hy)).2 hxy)⟩
  · rintro ⟨hx, hm⟩
    exact ⟨hx, fun y hy hxy => hm y hy ((anc_agree hlt hagree (hhs y hy)).1 hxy)⟩

theorem fresh_agree (s : S V) (ps : List Nat) (v : V) :
    ∀ y < s.next, (s.fresh ps v).par y = s.par y := fun _ hy => upd_lt _ _ hy

/-- What a plan says survives the store growing, and more changes to the op heads. -/
theorem PlanOk.mono {s t : S V} (hi : Inv J s) {p : Plan} (hp : PlanOk s p)
    (hagree : ∀ y < s.next, t.par y = s.par y) (hnext : s.next ≤ t.next)
    (hreal : ∀ x ∈ s.real, x ∈ t.real) (hmerged : ∀ x ∈ s.merged, x ∈ t.merged)
    (hev : s.ev ≤ t.ev) : PlanOk t p := by
  obtain ⟨hread, hrz, ht, hd, hev0⟩ := hp
  have hrzlt := hi.real_lt _ hrz
  have hnlt : p.new < s.next := by
    rcases ht with h | ⟨h, _⟩
    · rw [h]; exact hrzlt
    · exact (hi.merged _ h).1
  refine ⟨fun x hx => Nat.lt_of_lt_of_le (hread x hx) hnext, hreal _ hrz, ?_, ?_, by omega⟩
  · rcases ht with h | ⟨h, hps⟩
    · exact Or.inl h
    · refine Or.inr ⟨hmerged _ h, fun x => ?_⟩
      rw [hagree _ hnlt, hps x]
      refine (max_agree hi.dag hagree (fun y hy => ?_) x).symm
      rcases List.mem_append.1 hy with hy | hy
      · exact hread y hy
      · simp at hy; subst hy; exact hrzlt
  · intro d hdd
    exact ⟨(hd d hdd).1, (anc_agree hi.dag hagree hnlt).2 (hd d hdd).2⟩

theorem InLog.mono {s : S V} (hi : Inv J s) {par' : Nat → List Nat}
    (hagree : ∀ y < s.next, par' y = s.par y) {u : Nat} (hu : InLog s u) :
    ∃ h ∈ s.heads, Anc par' u h := by
  obtain ⟨h, hh, huh⟩ := hu
  exact ⟨h, hh, (anc_agree hi.dag hagree (hi.heads_lt h hh)).2 huh⟩

/-- An unlocked step that changes the op heads and counts it keeps what musubi's place says. -/
theorem ctl_unlocked {s t : S V} (hi : Inv J s) (hl : s.mv.locked = false) (hmv : t.mv = s.mv)
    (hev : t.ev = s.ev + 1) (hplan : ∀ p, PlanOk s p → PlanOk t p) : CtlOk t t.mv := by
  have hc := hi.ctl
  rw [hmv]
  cases hm : s.mv with
  | idle => trivial
  | planned p =>
    rw [hm] at hc
    refine ⟨hplan p hc.1, fun he => ?_⟩
    have := hc.1.2.2.2.2; omega
  | held p => rw [hm] at hl; cases hl
  | writing p a todo => rw [hm] at hl; cases hl

theorem Inv.init (v0 : V) : Inv J (Realize.init v0) := by
  refine ⟨fun _ _ h => by simp [Realize.init] at h, fun h hh => ?_, by simp [Realize.init],
    fun _ h => by simp [Realize.init] at h, fun _ h => by simp [Realize.init] at h,
    fun _ h => by simp [Realize.init] at h, fun _ h => by simp [Realize.init] at h,
    fun x h0 h1 => ?_, fun _ h => by simp [Realize.init] at h, trivial⟩
  · simp [Realize.init] at hh ⊢; omega
  · simp [Realize.init] at h1; omega

theorem Inv.step {b : Bool} {s s' : S V} (hi : Inv J s) (hs : Step J b s s') : Inv J s' := by
  cases hs with
  | @cmd L v hL hl =>
    have hL' : ∀ p ∈ [L], p < s.next := by simp [hL]
    have hag := fresh_agree s [L] v
    refine ⟨parLt_upd hi.dag hL', ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h hh
      rcases List.mem_cons.1 hh with rfl | hh
      · show s.next < s.next + 1; omega
      · have := hi.heads_lt h (mem_del.1 hh).1; show h < s.next + 1; omega
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · show s.next < s.next + 1; omega
      · have := hi.mine_lt x hx; show x < s.next + 1; omega
    · intro x hx; have := hi.real_lt x hx; show x < s.next + 1; omega
    · intro x hx; have := hi.jjm_lt x hx; show x < s.next + 1; omega
    · intro m hm
      obtain ⟨hmlt, hv, hr⟩ := hi.merged m hm
      refine ⟨by show m < s.next + 1; omega, ?_, ?_⟩
      · show upd s.view s.next v m =
          J.load (upd s.par s.next [L]) (upd s.view s.next v) (upd s.par s.next [L] m)
        rw [upd_lt _ _ hmlt, upd_lt _ _ hmlt, hv,
          load_upd J hi.dag _ _ (fun p hp => Nat.lt_trans (hi.dag m p hp) hmlt)]
      · show ∃ r ∈ s.real, r ∈ upd s.par s.next [L] m ∧ ∃ h ∈ upd s.par s.next [L] m, h ≠ r
        rw [upd_lt _ _ hmlt]; exact hr
    · intro x h0 hx
      by_cases e : x = s.next
      · exact Or.inl (by subst e; simp)
      · have hx' : x < s.next := by change x < s.next + 1 at hx; omega
        rcases hi.known x h0 hx' with h | h | h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact ⟨s.next, List.mem_cons_self, Anc.refl⟩
      · obtain ⟨h, hh, huh⟩ := InLog.mono J hi hag (hi.kept u hu)
        by_cases e : h = L
        · subst e
          exact ⟨s.next, List.mem_cons_self, Anc.step (by simp [S.fresh]) huh⟩
        · exact ⟨h, List.mem_cons_of_mem _ (mem_del.2 ⟨hh, e⟩), huh⟩
    · exact ctl_unlocked J hi hl rfl rfl fun p hp =>
        PlanOk.mono J hi hp hag (by simp [S.fresh]) (fun _ h => h) (fun _ h => h) (by simp)
  | @collapse m hl hm h1 =>
    have hmh : m ∈ s.heads := ((hm m).2 rfl).1
    refine ⟨hi.dag, ?_, by simp, hi.mine_lt, hi.real_lt, hi.jjm_lt, hi.merged, hi.known,
      ?_, ?_⟩
    · intro h hh; simp at hh; subst hh; exact hi.heads_lt _ hmh
    · intro u hu
      obtain ⟨h, hh, huh⟩ := hi.kept u hu
      obtain ⟨y, hy, hhy⟩ := max_covers hi.dag hh
      rw [(hm y).1 hy] at hhy
      exact ⟨m, by simp, huh.trans hhy⟩
    · exact ctl_unlocked J hi hl rfl rfl fun p hp =>
        PlanOk.mono J hi hp (fun _ _ => rfl) (Nat.le_refl _) (fun _ h => h) (fun _ h => h)
          (by simp)
  | @merge ps hl hps h2 =>
    have hpsl : ∀ p ∈ ps, p < s.next := fun p hp => hi.heads_lt p ((hps p).1 hp).1
    have hag := fresh_agree s ps (J.load s.par s.view ps)
    refine ⟨parLt_upd hi.dag hpsl, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h hh; simp at hh; subst hh; show s.next < s.next + 1; omega
    · intro x hx; have := hi.mine_lt x hx; show x < s.next + 1; omega
    · intro x hx; have := hi.real_lt x hx; show x < s.next + 1; omega
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · show s.next < s.next + 1; omega
      · have := hi.jjm_lt x hx; show x < s.next + 1; omega
    · intro m hm
      obtain ⟨hmlt, hv, hr⟩ := hi.merged m hm
      refine ⟨by show m < s.next + 1; omega, ?_, ?_⟩
      · show upd s.view s.next _ m = J.load (upd s.par s.next ps) (upd s.view s.next _)
          (upd s.par s.next ps m)
        rw [upd_lt _ _ hmlt, upd_lt _ _ hmlt, hv,
          load_upd J hi.dag _ _ (fun p hp => Nat.lt_trans (hi.dag m p hp) hmlt)]
      · show ∃ r ∈ s.real, r ∈ upd s.par s.next ps m ∧ ∃ h ∈ upd s.par s.next ps m, h ≠ r
        rw [upd_lt _ _ hmlt]; exact hr
    · intro x h0 hx
      by_cases e : x = s.next
      · exact Or.inr (Or.inr (Or.inr (by subst e; simp)))
      · have hx' : x < s.next := by change x < s.next + 1 at hx; omega
        rcases hi.known x h0 hx' with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (List.mem_cons_of_mem _ h)))
    · intro u hu
      obtain ⟨h, hh, huh⟩ := hi.kept u hu
      obtain ⟨y, hy, hhy⟩ := max_covers hi.dag hh
      have hyn := hi.heads_lt h hh
      refine ⟨s.next, by simp, Anc.step (p := y) (by simp [S.fresh]; exact (hps y).2 hy) ?_⟩
      exact (anc_agree hi.dag hag (hi.heads_lt y hy.1)).2 (huh.trans hhy)
    · exact ctl_unlocked J hi hl rfl rfl fun p hp =>
        PlanOk.mono J hi hp hag (by simp [S.fresh]) (fun _ h => h) (fun _ h => h) (by simp)
  | @realize ps v hidle hps =>
    have hag := fresh_agree s ps v
    refine ⟨parLt_upd hi.dag hps, fun h hh => ?_, hi.heads_ne, fun x hx => ?_, fun x hx => ?_,
      fun x hx => ?_, fun m hm => ?_, fun x h0 hx => ?_, fun u hu => InLog.mono J hi hag
      (hi.kept u hu), ?_⟩
    · have := hi.heads_lt h hh; show h < s.next + 1; omega
    · have := hi.mine_lt x hx; show x < s.next + 1; omega
    · rcases List.mem_cons.1 hx with rfl | hx
      · show s.next < s.next + 1; omega
      · have := hi.real_lt x hx; show x < s.next + 1; omega
    · have := hi.jjm_lt x hx; show x < s.next + 1; omega
    · obtain ⟨hmlt, hv, r, hr, hr'⟩ := hi.merged m hm
      refine ⟨by show m < s.next + 1; omega, ?_, r, List.mem_cons_of_mem _ hr, ?_⟩
      · show upd s.view s.next v m = J.load (upd s.par s.next ps) (upd s.view s.next v)
          (upd s.par s.next ps m)
        rw [upd_lt _ _ hmlt, upd_lt _ _ hmlt, hv,
          load_upd J hi.dag _ _ (fun p hp => Nat.lt_trans (hi.dag m p hp) hmlt)]
      · show r ∈ upd s.par s.next ps m ∧ ∃ h ∈ upd s.par s.next ps m, h ≠ r
        rw [upd_lt _ _ hmlt]; exact hr'
    · by_cases e : x = s.next
      · exact Or.inr (Or.inl (by subst e; simp))
      · have hx' : x < s.next := by change x < s.next + 1 at hx; omega
        rcases hi.known x h0 hx' with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
    · show CtlOk _ s.mv; rw [hidle]; trivial
  | @mergeWith r ps hidle hr hnew hbeside hps =>
    have hrl := hi.real_lt r hr
    have hmem : ∀ x ∈ ps, x ∈ s.heads ++ [r] := fun x hx => ((hps x).1 hx).1
    have hpsl : ∀ p ∈ ps, p < s.next := by
      intro p hp
      rcases List.mem_append.1 (hmem p hp) with h | h
      · exact hi.heads_lt p h
      · simp at h; subst h; exact hrl
    have hag := fresh_agree s ps (J.load s.par s.view ps)
    refine ⟨parLt_upd hi.dag hpsl, fun h hh => ?_, hi.heads_ne, fun x hx => ?_, fun x hx => ?_,
      fun x hx => ?_, fun m hm => ?_, fun x h0 hx => ?_, fun u hu => InLog.mono J hi hag
      (hi.kept u hu), ?_⟩
    · have := hi.heads_lt h hh; show h < s.next + 1; omega
    · have := hi.mine_lt x hx; show x < s.next + 1; omega
    · have := hi.real_lt x hx; show x < s.next + 1; omega
    · have := hi.jjm_lt x hx; show x < s.next + 1; omega
    · rcases List.mem_cons.1 hm with rfl | hm
      · refine ⟨by show s.next < s.next + 1; omega, ?_, r, hr, ?_⟩
        · show upd s.view s.next _ s.next = J.load (upd s.par s.next ps) (upd s.view s.next _)
            (upd s.par s.next ps s.next)
          rw [upd_same, upd_same, load_upd J hi.dag _ _ hpsl]
        · show r ∈ upd s.par s.next ps s.next ∧ ∃ h ∈ upd s.par s.next ps s.next, h ≠ r
          rw [upd_same]
          refine ⟨(hps r).2 ⟨by simp, fun y hy hry => ?_⟩, ?_⟩
          · rcases List.mem_append.1 hy with hy | hy
            · exact absurd hry (hnew y hy)
            · simp at hy; exact hy.symm
          · obtain ⟨h, hh, hhr⟩ := hbeside
            obtain ⟨y, hy, hhy⟩ := max_covers hi.dag (List.mem_append.2 (Or.inl hh) :
              h ∈ s.heads ++ [r])
            refine ⟨y, (hps y).2 hy, fun e => ?_⟩
            subst e; exact hhr hhy
      · obtain ⟨hmlt, hv, r', hr', hr''⟩ := hi.merged m hm
        refine ⟨by show m < s.next + 1; omega, ?_, r', hr', ?_⟩
        · show upd s.view s.next _ m = J.load (upd s.par s.next ps) (upd s.view s.next _)
            (upd s.par s.next ps m)
          rw [upd_lt _ _ hmlt, upd_lt _ _ hmlt, hv,
            load_upd J hi.dag _ _ (fun p hp => Nat.lt_trans (hi.dag m p hp) hmlt)]
        · show r' ∈ upd s.par s.next ps m ∧ ∃ h ∈ upd s.par s.next ps m, h ≠ r'
          rw [upd_lt _ _ hmlt]; exact hr''
    · by_cases e : x = s.next
      · exact Or.inr (Or.inr (Or.inl (by subst e; simp)))
      · have hx' : x < s.next := by change x < s.next + 1 at hx; omega
        rcases hi.known x h0 hx' with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ h)))
        · exact Or.inr (Or.inr (Or.inr h))
    · show CtlOk _ s.mv; rw [hidle]; trivial
  | @plan r n drop hidle hr ht hd =>
    refine ⟨hi.dag, hi.heads_lt, hi.heads_ne, hi.mine_lt, hi.real_lt, hi.jjm_lt, hi.merged,
      hi.known, hi.kept, ⟨⟨hi.heads_lt, hr, ht, hd, Nat.le_refl _⟩, fun _ =>
      same_iff.2 fun _ => Iff.rfl⟩⟩
  | @lock p h =>
    have hc := hi.ctl
    rw [h] at hc
    exact ⟨hi.dag, hi.heads_lt, hi.heads_ne, hi.mine_lt, hi.real_lt, hi.jjm_lt, hi.merged,
      hi.known, hi.kept, hc⟩
  | @check p h =>
    have hc := hi.ctl
    rw [h] at hc
    obtain ⟨hp, hsame⟩ := hc
    refine ⟨hi.dag, hi.heads_lt, hi.heads_ne, hi.mine_lt, hi.real_lt, hi.jjm_lt, hi.merged,
      hi.known, hi.kept, ?_⟩
    show CtlOk _ (if same s.heads p.read then _ else _)
    split
    · rename_i hsm
      have hnlt : p.new < s.next := by
        rcases hp.2.2.1 with e | ⟨e, _⟩
        · rw [e]; exact hi.real_lt _ hp.2.1
        · exact (hi.merged _ e).1
      exact ⟨hnlt, hp.2.2.2.1, fun _ => ⟨hsm, hp⟩, (fun e => nomatch e)⟩
    · trivial
  | @add p todo h =>
    have hc := hi.ctl
    rw [h] at hc
    obtain ⟨hnlt, htodo, hfalse, _⟩ := hc
    refine ⟨hi.dag, fun x hx => ?_, List.ne_nil_of_mem (mem_add.2 (Or.inl rfl)), hi.mine_lt,
      hi.real_lt, hi.jjm_lt, hi.merged, hi.known, fun u hu => ?_,
      ⟨hnlt, htodo, (fun e => nomatch e), fun _ => mem_add.2 (Or.inl rfl)⟩⟩
    · rcases mem_add.1 hx with rfl | hx
      · exact hnlt
      · exact hi.heads_lt x hx
    · obtain ⟨h', hh, huh⟩ := hi.kept u hu
      exact ⟨h', mem_add.2 (Or.inr hh), huh⟩
  | @del p d todo h =>
    have hc := hi.ctl
    rw [h] at hc
    obtain ⟨hnlt, htodo, _, hin⟩ := hc
    have hin := hin rfl
    have hdn := htodo d List.mem_cons_self
    have hnew : p.new ∈ Act.apply s.heads (.del d) := mem_del.2 ⟨hin, fun e => hdn.1 e.symm⟩
    refine ⟨hi.dag, fun x hx => hi.heads_lt x (mem_del.1 hx).1, List.ne_nil_of_mem hnew,
      hi.mine_lt,      hi.real_lt, hi.jjm_lt, hi.merged, hi.known, fun u hu => ?_,
      ⟨hnlt, fun e he => htodo e (List.mem_cons_of_mem _ he), (fun e => nomatch e),
        fun _ => hnew⟩⟩
    · obtain ⟨h', hh, huh⟩ := hi.kept u hu
      by_cases e : h' = d
      · subst e; exact ⟨p.new, hnew, huh.trans hdn.2⟩
      · exact ⟨h', mem_del.2 ⟨hh, e⟩, huh⟩
  | @done p h =>
    exact ⟨hi.dag, hi.heads_lt, hi.heads_ne, hi.mine_lt, hi.real_lt, hi.jjm_lt, hi.merged,
      hi.known, hi.kept, trivial⟩
  | crash hc =>
    exact ⟨hi.dag, hi.heads_lt, hi.heads_ne, hi.mine_lt, hi.real_lt, hi.jjm_lt, hi.merged,
      hi.known, hi.kept, trivial⟩

theorem Reach.inv {b : Bool} {v0 : V} {s : S V} (h : Reach J b v0 s) : Inv J s := by
  induction h with
  | init => exact Inv.init J v0
  | step _ hs ih => exact ih.step J hs

/-! ## 1. Nothing you did is lost -/

/-- Nothing in the op log ever leaves it, whatever runs: commands, jj's loads, musubi, crashes. -/
theorem log_kept {b : Bool} {v0 : V} {s s' : S V} (hr : Reach J b v0 s) (hs : Step J b s s')
    {x : Nat} (hx : InLog s x) : InLog s' x := by
  have hi := hr.inv
  cases hs with
  | @cmd L v hL hl =>
    obtain ⟨h, hh, hxh⟩ := InLog.mono J hi (fresh_agree s [L] v) hx
    by_cases e : h = L
    · subst e; exact ⟨s.next, List.mem_cons_self, Anc.step (by simp [S.fresh]) hxh⟩
    · exact ⟨h, List.mem_cons_of_mem _ (mem_del.2 ⟨hh, e⟩), hxh⟩
  | @collapse m hl hm h1 =>
    obtain ⟨h, hh, hxh⟩ := hx
    obtain ⟨y, hy, hhy⟩ := max_covers hi.dag hh
    rw [(hm y).1 hy] at hhy
    exact ⟨m, by simp, hxh.trans hhy⟩
  | @merge ps hl hps h2 =>
    obtain ⟨h, hh, hxh⟩ := hx
    obtain ⟨y, hy, hhy⟩ := max_covers hi.dag hh
    refine ⟨s.next, by simp, Anc.step (p := y) (by simp [S.fresh]; exact (hps y).2 hy) ?_⟩
    exact (anc_agree hi.dag (fresh_agree s ps (J.load s.par s.view ps)) (hi.heads_lt y hy.1)).2
      (hxh.trans hhy)
  | @realize ps v _ _ => exact InLog.mono J hi (fresh_agree s ps v) hx
  | @mergeWith r ps _ _ _ _ _ =>
    exact InLog.mono J hi (fresh_agree s ps (J.load s.par s.view ps)) hx
  | plan => exact hx
  | lock => exact hx
  | check => exact hx
  | @add p todo h =>
    obtain ⟨h', hh, hxh⟩ := hx
    exact ⟨h', mem_add.2 (Or.inr hh), hxh⟩
  | @del p d todo h =>
    have hc := hi.ctl
    rw [h] at hc
    obtain ⟨_, htodo, _, hin⟩ := hc
    have hdn := htodo d List.mem_cons_self
    obtain ⟨h', hh, hxh⟩ := hx
    by_cases e : h' = d
    · subst e
      exact ⟨p.new, mem_del.2 ⟨hin rfl, fun e => hdn.1 e.symm⟩, hxh.trans hdn.2⟩
    · exact ⟨h', mem_del.2 ⟨hh, e⟩, hxh⟩
  | done => exact hx
  | crash => exact hx

/-- **Promise 1.** Every operation your `jj` commands wrote stays in the op log, however
realization interleaves with them and wherever musubi crashes. -/
theorem nothing_lost {b : Bool} {v0 : V} {s : S V} (hr : Reach J b v0 s) {u : Nat}
    (hu : u ∈ s.mine) : InLog s u := hr.inv.kept u hu

/-! ## 2. You see what jj would show -/

theorem max_congr {par : Nat → List Nat} {A B : List Nat} (h : ∀ x, x ∈ A ↔ x ∈ B) (x : Nat) :
    Max par A x ↔ Max par B x := by
  simp only [Max, maxSet, h]

/-- **Promise 2, at publication.** When musubi adds its op head, jj shows its merge of the op
heads there were with the realization: just what jj would show had the realization been put
beside them. -/
theorem publish_shows_merge {b : Bool} {v0 : V} {s : S V} (hr : Reach J b v0 s) {p : Plan}
    {todo : List Nat} (h : s.mv = .writing p false todo) :
    shown J { s with heads := Act.apply s.heads (.add p.new), mv := .writing p true todo } =
      J.load s.par s.view (s.heads ++ [p.rz]) := by
  have hi := hr.inv
  have hc := hi.ctl
  rw [h] at hc
  obtain ⟨_, _, hfalse, _⟩ := hc
  obtain ⟨hsame, hp⟩ := hfalse rfl
  have hread : ∀ x, x ∈ s.heads ↔ x ∈ p.read := same_iff.1 hsame
  show J.load s.par s.view (Act.apply s.heads (.add p.new)) = _
  rcases hp.2.2.1 with e | ⟨hm, hps⟩
  · rw [e]
    apply J.load_congr
    intro x
    rw [mem_add, List.mem_append]
    simp only [List.mem_singleton]
    exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩
  · have hmem : ∀ x, x ∈ s.heads ++ [p.rz] ↔ x ∈ p.read ++ [p.rz] := by
      intro x; simp only [List.mem_append, hread]
    have hps' : ∀ x, x ∈ s.par p.new ↔ Max s.par (s.heads ++ [p.rz]) x :=
      fun x => (hps x).trans (max_congr hmem x).symm
    have hbelow : ∀ x ∈ s.heads ++ [p.rz], Anc s.par x p.new := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := max_covers hi.dag hx
      exact hxy.trans (Anc.parent ((hps' y).2 hy))
    rw [load_dom' J hi.dag (B := [p.new]) (by simpa using mem_add.2 (Or.inl rfl))
      (fun x hx => by
        rcases mem_add.1 hx with e | hx
        · exact ⟨p.new, by simp, e ▸ Anc.refl⟩
        · exact ⟨p.new, by simp, hbelow x (List.mem_append.2 (Or.inl hx))⟩),
      J.load_single, (hi.merged _ hm).2.1]
    exact (load_max J hi.dag hps').symm

/-- **Promise 2.** Every step but a command of yours leaves what jj shows as it was, or is
musubi's publication, which shows jj's merge of the op heads with the realization. -/
theorem shown_step {b : Bool} {v0 : V} {s s' : S V} (hr : Reach J b v0 s) (hs : Step J b s s') :
    s'.mine ≠ s.mine ∨ shown J s' = shown J s ∨
      ∃ p todo, s.mv = .writing p false todo ∧
        shown J s' = J.load s.par s.view (s.heads ++ [p.rz]) := by
  have hi := hr.inv
  cases hs with
  | cmd => exact Or.inl (List.cons_ne_self _ _)
  | @collapse m hl hm h1 =>
    refine Or.inr (Or.inl (load_max J hi.dag (hs := s.heads) (ps := [m]) ?_).symm)
    intro x; simp only [List.mem_singleton]; exact (hm x).symm
  | @merge ps hl hps h2 =>
    refine Or.inr (Or.inl ?_)
    show J.load (upd s.par s.next ps) (upd s.view s.next _) [s.next] = J.load s.par s.view s.heads
    rw [J.load_single, upd_same]
    exact (load_max J hi.dag hps).symm
  | @realize ps v _ hps => exact Or.inr (Or.inl (load_upd J hi.dag _ _ hi.heads_lt))
  | @mergeWith r ps _ _ _ _ _ => exact Or.inr (Or.inl (load_upd J hi.dag _ _ hi.heads_lt))
  | plan => exact Or.inr (Or.inl rfl)
  | lock => exact Or.inr (Or.inl rfl)
  | check => exact Or.inr (Or.inl rfl)
  | @add p todo h => exact Or.inr (Or.inr ⟨p, todo, h, publish_shows_merge J hr h⟩)
  | @del p d todo h =>
    refine Or.inr (Or.inl ?_)
    have hc := hi.ctl
    rw [h] at hc
    obtain ⟨_, htodo, _, hin⟩ := hc
    have hdn := htodo d List.mem_cons_self
    show J.load s.par s.view (Act.apply s.heads (.del d)) = J.load s.par s.view s.heads
    by_cases hd : d ∈ s.heads
    · exact (J.load_drop _ _ _ d p.new hi.dag hd (hin rfl) hdn.1 hdn.2).symm
    · apply J.load_congr
      intro x
      rw [mem_del]
      exact ⟨fun h => h.1, fun h => ⟨h, fun e => hd (e ▸ h)⟩⟩
  | done => exact Or.inr (Or.inl rfl)
  | crash => exact Or.inr (Or.inl rfl)

/-- Once realization has settled on one op head, jj shows its view. -/
theorem settled_shows {s : S V} {h : Nat} (hh : s.heads = [h]) : shown J s = s.view h := by
  rw [shown, hh, J.load_single]

/-! ## 4. Received work isn't sent back as yours -/

/-- **Promise 4.** Every operation musubi writes is a realization of received work (`real`,
which translation marks as received), or a merge whose view is jj's merge of its parents, a
realization among them and something beside it: what jj itself writes on loading those op
heads. -/
theorem musubi_writes {b : Bool} {v0 : V} {s : S V} (hr : Reach J b v0 s) {m : Nat}
    (hm : m ∈ s.merged) : s.view m = J.load s.par s.view (s.par m) ∧
      ∃ r ∈ s.real, r ∈ s.par m ∧ ∃ h ∈ s.par m, h ≠ r := (hr.inv.merged m hm).2

/-- Every operation is the root, yours, a realization, musubi's merge or jj's: nothing else
writes. -/
theorem ops_known {b : Bool} {v0 : V} {s : S V} (hr : Reach J b v0 s) {x : Nat} (h0 : 0 < x)
    (hx : x < s.next) : x ∈ s.mine ∨ x ∈ s.real ∨ x ∈ s.merged ∨ x ∈ s.jjm :=
  hr.inv.known x h0 hx

/-! ## 5. It finishes -/

/-- **Promise 5, every attempt.** Musubi's check, under the lock, finds the op heads it read
unless a command or jj's load changed them since: an attempt nothing interrupts goes on to
publish. -/
theorem quiet_check_passes {b : Bool} {v0 : V} {s : S V} (hr : Reach J b v0 s) {p : Plan}
    (h : s.mv = .held p) (hq : s.ev = p.ev0) : same s.heads p.read = true := by
  have hc := hr.inv.ctl
  rw [h] at hc
  exact hc.2 hq

theorem Step.lift {s s' : S V} {b : Bool} (h : Step J false s s') : Step J b s s' := by
  cases h with
  | cmd v hL hl => exact .cmd v hL hl
  | collapse hl hm h1 => exact .collapse hl hm h1
  | merge hl hps h2 => exact .merge hl hps h2
  | realize v hi hps => exact .realize v hi hps
  | mergeWith hi hr hnew hb hps => exact .mergeWith hi hr hnew hb hps
  | plan hi hr ht hd => exact .plan hi hr ht hd
  | lock h => exact .lock h
  | check h => exact .check h
  | add h => exact .add h
  | del h => exact .del h
  | done h => exact .done h
  | crash hc => cases hc

theorem Reach.steps {b : Bool} {v0 : V} {s t : S V} (hr : Reach J b v0 s)
    (h : Steps (Step J false) s t) : Reach J b v0 t := by
  induction h with
  | refl => exact hr
  | tail _ hst ih => exact ih.step (Step.lift J hst)

theorem Steps.trans' {α : Type} {step : α → α → Prop} {a b c : α} (h1 : Steps step a b)
    (h2 : Steps step b c) : Steps step a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hst ih => exact ih.tail hst

theorem same_refl (l : List Nat) : same l l = true := same_iff.2 fun _ => Iff.rfl

/-- Musubi's own steps and jj's loads: no command of yours, no crash. -/
def Quiet (s t : S V) : Prop := Step J false s t ∧ t.mine = s.mine ∧ t.real = s.real

theorem Quiet.steps {s t : S V} (h : Steps (Quiet J) s t) : Steps (Step J false) s t := by
  induction h with
  | refl => exact .refl _
  | tail _ hst ih => exact ih.tail hst.1

theorem Quiet.real {s t : S V} (h : Steps (Quiet J) s t) : t.real = s.real := by
  induction h with
  | refl => rfl
  | tail _ hst ih => rw [hst.2.2, ih]

/-- Taking out the op heads still to take out, and letting go. -/
theorem drain {p : Plan} : ∀ (todo : List Nat) (s : S V), s.mv = .writing p true todo →
    ∃ t, Steps (Quiet J) s t ∧ t.mv = .idle
  | [], s, h => ⟨_, Steps.tail (.refl _) ⟨.done h, rfl, rfl⟩, rfl⟩
  | d :: todo, s, h => by
    obtain ⟨t, ht, hm⟩ :=
      drain todo { s with heads := Act.apply s.heads (.del d), mv := .writing p true todo } rfl
    exact ⟨t, Steps.head ⟨.del h, rfl, rfl⟩ ht, hm⟩

/-- From anywhere, musubi finishes or abandons what it was doing. -/
theorem to_idle (s : S V) : ∃ t, Steps (Quiet J) s t ∧ t.mv = .idle := by
  have writing : ∀ (s : S V) p a todo, s.mv = .writing p a todo →
      ∃ t, Steps (Quiet J) s t ∧ t.mv = .idle := by
    intro s p a todo h
    cases a with
    | true => exact drain J todo s h
    | false =>
      obtain ⟨t, ht, hm⟩ := drain J todo
        { s with heads := Act.apply s.heads (.add p.new), mv := .writing p true todo } rfl
      exact ⟨t, Steps.head ⟨.add h, rfl, rfl⟩ ht, hm⟩
  have held : ∀ (s : S V) p, s.mv = .held p → ∃ t, Steps (Quiet J) s t ∧ t.mv = .idle := by
    intro s p h
    by_cases hsm : same s.heads p.read = true
    · obtain ⟨t, ht, hm⟩ := writing { s with mv := .writing p false p.drop } p false p.drop rfl
      refine ⟨t, Steps.head (t := { s with mv := .writing p false p.drop }) ⟨?_, rfl, rfl⟩ ht, hm⟩
      have := Step.check (J := J) (crashes := false) h
      simp only [hsm, ↓reduceIte] at this
      exact this
    · refine ⟨{ s with mv := .idle }, Steps.tail (.refl _) ⟨?_, rfl, rfl⟩, rfl⟩
      have := Step.check (J := J) (crashes := false) h
      simp only [hsm, ↓reduceIte, Bool.false_eq_true] at this
      exact this
  cases hm : s.mv with
  | idle => exact ⟨s, .refl _, hm⟩
  | planned p =>
    obtain ⟨t, ht, hm'⟩ := held { s with mv := .held p } p rfl
    exact ⟨t, Steps.head ⟨.lock hm, rfl, rfl⟩ ht, hm'⟩
  | held p => exact held s p hm
  | writing p a todo => exact writing s p a todo hm

/-- jj's load, from op heads with one of them above `r`, makes one op head above `r`. -/
theorem load_one {b : Bool} {v0 : V} {s : S V} (hr : Reach J b v0 s) (hidle : s.mv = .idle)
    {r : Nat} (hrin : InLog s r) :
    ∃ t, Steps (Quiet J) s t ∧ t.mv = .idle ∧ ∃ h, t.heads = [h] ∧ Anc t.par r h := by
  have hi := hr.inv
  have hl : s.locked = false := by simp [S.locked, hidle, Mv.locked]
  obtain ⟨h0, hh0, hrh0⟩ := hrin
  obtain ⟨m0, hm0, hrm0⟩ := max_covers hi.dag hh0
  by_cases two : ∃ a b, Max s.par s.heads a ∧ Max s.par s.heads b ∧ a ≠ b
  · obtain ⟨a, b', ha, hb, hab⟩ := two
    let ps := s.heads.filter fun x => @decide (Max s.par s.heads x) (Classical.propDecidable _)
    have hps : ∀ x, x ∈ ps ↔ Max s.par s.heads x := by
      intro x
      simp only [ps, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    refine ⟨_, Steps.tail (.refl _) ⟨Step.merge (J := J) (crashes := false) hl hps
      ⟨a, (hps a).2 ha, b', (hps b').2 hb, hab⟩, rfl, rfl⟩, hidle, s.next, rfl, ?_⟩
    refine Anc.step (p := m0) (by simp [S.fresh]; exact (hps m0).2 hm0) ?_
    exact (anc_agree hi.dag (fresh_agree s ps (J.load s.par s.view ps))
      (hi.heads_lt m0 hm0.1)).2 (hrh0.trans hrm0)
  · have hm : ∀ x, Max s.par s.heads x ↔ x = m0 := by
      intro x
      refine ⟨fun hx => Classical.byContradiction fun hne => two ⟨x, m0, hx, hm0, hne⟩, ?_⟩
      rintro rfl; exact hm0
    by_cases h1 : s.heads = [m0]
    · exact ⟨s, .refl _, hidle, m0, h1, hrh0.trans hrm0⟩
    · exact ⟨_, Steps.tail (.refl _) ⟨Step.collapse (J := J) (crashes := false) hl hm h1, rfl,
        rfl⟩, hidle, m0, rfl, hrh0.trans hrm0⟩

/-- **Promise 5.** From every state, musubi's steps and jj's loads alone, with no command of
yours and no crash, reach one op head with the realization `r` in it. -/
theorem finishes {b : Bool} {v0 : V} {s : S V} (hr : Reach J b v0 s) {r : Nat}
    (hrr : r ∈ s.real) :
    ∃ t, Steps (Quiet J) s t ∧ t.mv = .idle ∧ ∃ h, t.heads = [h] ∧ Anc t.par r h := by
  obtain ⟨t1, h1, hidle⟩ := to_idle J s
  have hr1 := hr.steps J (Quiet.steps J h1)
  have hrr1 : r ∈ t1.real := by rw [Quiet.real J h1]; exact hrr
  -- Publish `r` beside the op heads.
  let p : Plan := ⟨t1.heads, r, r, [], t1.ev⟩
  have s2 : Quiet J t1 { t1 with mv := .planned p } :=
    ⟨Step.plan (J := J) (crashes := false) (r := r) (n := r) (drop := []) hidle hrr1
      (Or.inl rfl) (by simp), rfl, rfl⟩
  have s3 : Quiet J { t1 with mv := .planned p } { t1 with mv := .held p } :=
    ⟨Step.lock (J := J) (crashes := false) rfl, rfl, rfl⟩
  have s4 : Quiet J { t1 with mv := .held p } { t1 with mv := .writing p false [] } := by
    refine ⟨?_, rfl, rfl⟩
    have := Step.check (J := J) (crashes := false) (s := { t1 with mv := .held p }) (p := p) rfl
    simp only [p, same_refl, ↓reduceIte] at this
    exact this
  have s5 : Quiet J { t1 with mv := .writing p false [] }
      { t1 with heads := Act.apply t1.heads (.add r), mv := .writing p true [] } :=
    ⟨Step.add (J := J) (crashes := false) (p := p) (todo := []) rfl, rfl, rfl⟩
  have s6 : Quiet J { t1 with heads := Act.apply t1.heads (.add r), mv := .writing p true [] }
      { t1 with heads := Act.apply t1.heads (.add r), mv := .idle } :=
    ⟨Step.done (J := J) (crashes := false) (p := p) rfl, rfl, rfl⟩
  have h6 : Steps (Quiet J) s { t1 with heads := Act.apply t1.heads (.add r), mv := .idle } :=
    h1.tail s2 |>.tail s3 |>.tail s4 |>.tail s5 |>.tail s6
  obtain ⟨t, ht, hidle', hh⟩ := load_one J (hr.steps J (Quiet.steps J h6)) rfl
    ⟨r, mem_add.2 (Or.inl rfl), Anc.refl⟩
  exact ⟨t, Steps.trans' h6 ht, hidle', hh⟩

/-! ## 3. Crashes are harmless

A run with crashes is matched by one without, step by step. The run without holds back each of
musubi's attempts until the run with crashes adds its op head: an attempt a crash cuts short
before then has left nothing behind but operations, which the run without writes too. A crash
after the op head is in is matched by the run without finishing the attempt; the run with crashes
keeps op heads below the new one, which jj drops when it next loads. -/

/-- Where musubi is in the run with crashes and in the run without: the same once the new op head
is in, and before that, the run without hasn't started. -/
def CtlSim (a c : Mv) : Prop :=
  match a with
  | .writing p true todo => ∃ p', c = .writing p' true todo ∧ p'.new = p.new
  | _ => c = .idle

/-- The run without crashes `t` matches `s`: the same operations, and the same op heads but for
some of `s`'s below another. -/
structure Sim (s t : S V) : Prop where
  next : t.next = s.next
  par : t.par = s.par
  view : t.view = s.view
  mine : t.mine = s.mine
  real : t.real = s.real
  merged : t.merged = s.merged
  sub : ∀ x ∈ t.heads, x ∈ s.heads
  dom : ∀ x ∈ s.heads, ∃ y ∈ t.heads, Anc s.par x y
  ctl : CtlSim s.mv t.mv

theorem Sim.shape {s t : S V} (h : Sim s t) :
    t = { s with heads := t.heads, mv := t.mv, jjm := t.jjm, ev := t.ev } := by
  cases s; cases t
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _, _⟩ := h
  simp_all

theorem CtlSim.idle_of_unlocked {a c : Mv} (h : CtlSim a c) (hl : a.locked = false) :
    c = .idle := by
  cases a with
  | writing p added todo => cases added <;> simp_all [CtlSim, Mv.locked]
  | _ => exact h

/-- Taking out the op heads still to take out, and letting go, in the run without crashes. -/
theorem drain_heads {p : Plan} : ∀ (todo : List Nat) (t : S V), t.mv = .writing p true todo →
    p.new ∈ t.heads → (∀ d ∈ todo, d ≠ p.new) →
    ∃ t', Steps (Step J false) t t' ∧ t' = { t with heads := t'.heads, mv := .idle } ∧
      (∀ x ∈ t'.heads, x ∈ t.heads) ∧ (∀ x ∈ t.heads, x ∉ todo → x ∈ t'.heads) ∧
      p.new ∈ t'.heads
  | [], t, h, hn, _ =>
    ⟨_, Steps.tail (.refl _) (.done h), rfl, fun _ h => h, fun _ h _ => h, hn⟩
  | d :: todo, t, h, hn, hd => by
    obtain ⟨t', ht, he, hsub, hkeep, hn'⟩ := drain_heads todo
      { t with heads := Act.apply t.heads (.del d), mv := .writing p true todo } rfl
      (mem_del.2 ⟨hn, fun e => hd d List.mem_cons_self e.symm⟩)
      (fun e he => hd e (List.mem_cons_of_mem _ he))
    refine ⟨t', Steps.head (.del h) ht, ?_, fun x hx => (mem_del.1 (hsub x hx)).1,
      fun x hx hnot => hkeep x (mem_del.2 ⟨hx, fun e => hnot (e ▸ List.mem_cons_self)⟩)
        (fun h' => hnot (List.mem_cons_of_mem _ h')), hn'⟩
    rw [he]

/-- One step of the run with crashes is matched by steps of the run without. -/
theorem sim_step {v0 : V} {s s' t : S V} (hrs : Reach J true v0 s) (hrt : Reach J false v0 t)
    (hsim : Sim s t) (hs : Step J true s s') :
    ∃ t', Steps (Step J false) t t' ∧ Sim s' t' := by
  have hi := hrs.inv
  have hit := hrt.inv
  have hshape := hsim.shape
  obtain ⟨_, _, _, _, _, _, hsub, hdom, hctl⟩ := hsim
  generalize t.heads = th at hshape hsub hdom
  generalize t.mv = tm at hshape hctl
  generalize t.jjm = tj at hshape
  generalize t.ev = te at hshape
  subst hshape
  let t0 : S V := { s with heads := th, mv := .idle, jjm := tj, ev := te }
  have hag : ∀ {ps : List Nat} {v : V} {x y : Nat}, y ∈ s.heads →
      (Anc (s.fresh ps v).par x y ↔ Anc s.par x y) :=
    fun hy => anc_agree hi.dag (fresh_agree s _ _) (hi.heads_lt _ hy)
  cases hs with
  | @cmd L v hL hl =>
    have htm := hctl.idle_of_unlocked hl
    subst htm
    have hstep := Step.cmd (J := J) (crashes := false) (s := t0) v hL rfl
    refine ⟨_, Steps.tail (.refl _) hstep, ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, hctl⟩⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · obtain ⟨hx, hne⟩ := mem_del.1 hx
        exact List.mem_cons_of_mem _ (mem_del.2 ⟨hsub x hx, hne⟩)
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨_, List.mem_cons_self, Anc.refl⟩
      · obtain ⟨hx, hne⟩ := mem_del.1 hx
        obtain ⟨y, hy, hxy⟩ := hdom x hx
        have hxy' := (hag (ps := [L]) (v := v) (hsub y hy)).2 hxy
        by_cases e : y = L
        · subst e
          exact ⟨s.next, List.mem_cons_self, Anc.step (by simp [S.fresh]) hxy'⟩
        · exact ⟨y, List.mem_cons_of_mem _ (mem_del.2 ⟨hy, e⟩), hxy'⟩
  | @collapse m hl hm h1 =>
    have htm := hctl.idle_of_unlocked hl
    subst htm
    have hm' : ∀ x, Max s.par th x ↔ x = m := fun x => (max_dom hi.dag hsub hdom x).symm.trans
      (hm x)
    have hsim' : ∀ e,
        Sim { s with heads := [m], ev := s.ev + 1 } { t0 with heads := [m], ev := e } := by
      intro e
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun x hx => hx, fun x hx => ⟨x, hx, Anc.refl⟩, hctl⟩
    by_cases e : th = [m]
    · subst e; exact ⟨_, .refl _, hsim' te⟩
    · exact ⟨_, Steps.tail (.refl _) (Step.collapse (s := t0) rfl hm' e), hsim' _⟩
  | @merge ps hl hps h2 =>
    have htm := hctl.idle_of_unlocked hl
    subst htm
    have hps' : ∀ x, x ∈ ps ↔ Max s.par th x := fun x => (hps x).trans
      (max_dom hi.dag hsub hdom x)
    exact ⟨_, Steps.tail (.refl _) (Step.merge (s := t0) rfl hps' h2),
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun x hx => hx, fun x hx => ⟨x, hx, Anc.refl⟩, hctl⟩⟩
  | @realize ps v hidle hps =>
    have htm : tm = .idle := by rw [hidle] at hctl; exact hctl
    subst htm
    refine ⟨_, Steps.tail (.refl _) (Step.realize (s := t0) v rfl hps),
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsub, ?_, hctl⟩⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hdom x hx
    exact ⟨y, hy, (hag (ps := ps) (v := v) (hsub y hy)).2 hxy⟩
  | @mergeWith r ps hidle hr hnew hbeside hps =>
    have htm : tm = .idle := by rw [hidle] at hctl; exact hctl
    subst htm
    have hbeside' : ∃ h ∈ th, ¬ Anc s.par h r := by
      obtain ⟨h, hh, hhr⟩ := hbeside
      obtain ⟨y, hy, hhy⟩ := hdom h hh
      exact ⟨y, hy, fun hyr => hhr (hhy.trans hyr)⟩
    have hps' : ∀ x, x ∈ ps ↔ Max s.par (th ++ [r]) x := fun x => (hps x).trans
      (max_dom_append hi.dag hsub hdom r x)
    refine ⟨_, Steps.tail (.refl _)
      (Step.mergeWith (s := t0) rfl hr (fun h hh => hnew h (hsub h hh)) hbeside' hps'),
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsub, ?_, hctl⟩⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hdom x hx
    exact ⟨y, hy, (hag (ps := ps) (v := J.load s.par s.view ps) (hsub y hy)).2 hxy⟩
  | @plan r n drop hidle _ _ _ =>
    have htm : tm = .idle := by rw [hidle] at hctl; exact hctl
    exact ⟨_, .refl _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsub, hdom, htm⟩⟩
  | @lock p h =>
    have htm : tm = .idle := by rw [h] at hctl; exact hctl
    exact ⟨_, .refl _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsub, hdom, htm⟩⟩
  | @check p h =>
    have htm : tm = .idle := by rw [h] at hctl; exact hctl
    refine ⟨_, .refl _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsub, hdom, ?_⟩⟩
    show CtlSim (if same s.heads p.read then _ else _) tm
    split <;> exact htm
  | @add p todo h =>
    have htm : tm = .idle := by rw [h] at hctl; exact hctl
    subst htm
    have hc := hi.ctl
    rw [h] at hc
    obtain ⟨_, htodo, hfalse, _⟩ := hc
    obtain ⟨hsame, _, hrz, ht, _, _⟩ := hfalse rfl
    have hread : ∀ x, x ∈ p.read ++ [p.rz] ↔ x ∈ s.heads ++ [p.rz] := by
      intro x; simp only [List.mem_append, (same_iff.1 hsame x).symm]
    have ht' : Target s.par s.merged th p.rz p.new := by
      rcases ht with e | ⟨hm, hps⟩
      · exact Or.inl e
      · exact Or.inr ⟨hm, fun x => (hps x).trans ((max_congr hread x).trans
          (max_dom_append hi.dag hsub hdom p.rz x))⟩
    let p' : Plan := ⟨th, p.rz, p.new, todo, te⟩
    have s1 : Step J false t0 { t0 with mv := .planned p' } :=
      Step.plan (s := t0) (r := p.rz) (n := p.new) (drop := todo) rfl hrz ht' htodo
    have s2 : Step J false { t0 with mv := .planned p' } { t0 with mv := .held p' } :=
      Step.lock rfl
    have s3 :
        Step J false { t0 with mv := .held p' } { t0 with mv := .writing p' false todo } := by
      have := Step.check (J := J) (crashes := false) (s := { t0 with mv := .held p' }) (p := p')
        rfl
      simp only [p', t0, same_refl, ↓reduceIte] at this
      exact this
    have s4 : Step J false { t0 with mv := .writing p' false todo }
        { t0 with heads := Act.apply th (.add p.new), mv := .writing p' true todo } :=
      Step.add (p := p') (todo := todo) rfl
    refine ⟨_, ((((Steps.refl _).tail s1).tail s2).tail s3).tail s4,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ⟨p', rfl, rfl⟩⟩⟩
    · intro x hx
      rcases mem_add.1 hx with e | hx
      · exact mem_add.2 (Or.inl e)
      · exact mem_add.2 (Or.inr (hsub x hx))
    · intro x hx
      rcases mem_add.1 hx with e | hx
      · exact ⟨p.new, mem_add.2 (Or.inl rfl), e ▸ Anc.refl⟩
      · obtain ⟨y, hy, hxy⟩ := hdom x hx
        exact ⟨y, mem_add.2 (Or.inr hy), hxy⟩
  | @del p d todo h =>
    rw [h] at hctl
    obtain ⟨p', htm, hpn⟩ := hctl
    subst htm
    have hc := hi.ctl
    rw [h] at hc
    obtain ⟨_, htodo, _, _⟩ := hc
    have hct := hit.ctl
    have hnt : p'.new ∈ th := hct.2.2.2 rfl
    have hdn := htodo d List.mem_cons_self
    refine ⟨_, Steps.tail (.refl _)
      (Step.del (s := { t0 with mv := .writing p' true (d :: todo) }) rfl),
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ⟨p', rfl, hpn⟩⟩⟩
    · intro x hx
      obtain ⟨hx, hne⟩ := mem_del.1 hx
      exact mem_del.2 ⟨hsub x hx, hne⟩
    · intro x hx
      obtain ⟨hx, hne⟩ := mem_del.1 hx
      obtain ⟨y, hy, hxy⟩ := hdom x hx
      by_cases e : y = d
      · subst e
        refine ⟨p'.new, mem_del.2 ⟨hnt, fun e => hdn.1 (hpn ▸ e).symm⟩, ?_⟩
        rw [hpn]; exact hxy.trans hdn.2
      · exact ⟨y, mem_del.2 ⟨hy, e⟩, hxy⟩
  | @done p h =>
    rw [h] at hctl
    obtain ⟨p', htm, hpn⟩ := hctl
    subst htm
    exact ⟨_, Steps.tail (.refl _) (Step.done (s := { t0 with mv := .writing p' true [] }) rfl),
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsub, hdom, rfl⟩⟩
  | crash _ =>
    cases hm : s.mv with
    | writing p added todo =>
      cases added with
      | false =>
        rw [hm] at hctl
        exact ⟨_, .refl _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsub, hdom, hctl⟩⟩
      | true =>
        rw [hm] at hctl
        obtain ⟨p', htm, hpn⟩ := hctl
        subst htm
        have hc := hi.ctl
        rw [hm] at hc
        obtain ⟨_, htodo, _, _⟩ := hc
        have hct := hit.ctl
        have hnt : p'.new ∈ th := hct.2.2.2 rfl
        obtain ⟨t', ht', he, hsub', hkeep, hn'⟩ := drain_heads J todo
          { t0 with mv := .writing p' true todo } rfl hnt
          (fun d hd => hpn ▸ (htodo d hd).1)
        refine ⟨t', ht', ?_⟩
        rw [he]
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun x hx => hsub x (hsub' x hx), ?_, rfl⟩
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hdom x hx
        by_cases hyt : y ∈ todo
        · exact ⟨p'.new, hn', by rw [hpn]; exact hxy.trans (htodo y hyt).2⟩
        · exact ⟨y, hkeep y hy hyt, hxy⟩
    | _ =>
      rw [hm] at hctl
      exact ⟨_, .refl _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsub, hdom, hctl⟩⟩

theorem sim_reach {v0 : V} {s : S V} (hr : Reach J true v0 s) :
    ∃ t, Reach J false v0 t ∧ Sim s t := by
  induction hr with
  | init =>
    exact ⟨_, .init, ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun x hx => hx,
      fun x hx => ⟨x, hx, Anc.refl⟩, rfl⟩⟩
  | step hr hs ih =>
    obtain ⟨t, hrt, hsim⟩ := ih
    obtain ⟨t', ht', hsim'⟩ := sim_step J hr hrt hsim hs
    exact ⟨t', hrt.steps J ht', hsim'⟩

/-- **Promise 3.** Every state a run with crashes reaches, a run without crashes reaches too, with
the same operations, the same op log and the same view shown, and musubi idle in it wherever it
is idle after the crash. They differ only in op heads below another op head, which jj drops when
it next loads: what a crash between adding a new op head and taking the old ones out leaves. -/
theorem crash_harmless {v0 : V} {s : S V} (hr : Reach J true v0 s) :
    ∃ t, Reach J false v0 t ∧ t.next = s.next ∧ t.par = s.par ∧ t.view = s.view ∧
      t.mine = s.mine ∧ t.real = s.real ∧ shown J t = shown J s ∧
      (∀ x, InLog t x ↔ InLog s x) ∧ (∀ h ∈ t.heads, h ∈ s.heads) ∧
      (∀ h ∈ s.heads, ∃ h' ∈ t.heads, Anc s.par h h') ∧ (s.mv = .idle → t.mv = .idle) := by
  obtain ⟨t, hrt, hsim⟩ := sim_reach J hr
  have hi := hr.inv
  refine ⟨t, hrt, hsim.next, hsim.par, hsim.view, hsim.mine, hsim.real, ?_, ?_, hsim.sub,
    hsim.dom, ?_⟩
  · show J.load t.par t.view t.heads = J.load s.par s.view s.heads
    rw [hsim.par, hsim.view]
    exact (load_dom' J hi.dag hsim.sub hsim.dom).symm
  · intro x
    constructor
    · rintro ⟨h, hh, hxh⟩
      rw [hsim.par] at hxh
      exact ⟨h, hsim.sub h hh, hxh⟩
    · rintro ⟨h, hh, hxh⟩
      obtain ⟨y, hy, hhy⟩ := hsim.dom h hh
      exact ⟨y, hy, by rw [hsim.par]; exact hxh.trans hhy⟩
  · intro hm
    have := hsim.ctl
    rw [hm] at this
    exact this

/-- A crash itself changes nothing jj shows, nor the op log. -/
theorem crash_invisible (s : S V) :
    shown J { s with mv := .idle } = shown J s ∧
      ∀ x, InLog { s with mv := .idle } x ↔ InLog s x :=
  ⟨rfl, fun _ => Iff.rfl⟩

/-! ## 6. Workspaces -/

/-- **Promise 6, your workspaces.** With one op head, a step that is not a command of yours leaves
your workspace `n` where it was, given that the realization musubi publishes descends from what
the op head descends from and records no change to `n`, nor a rewrite of its commit (`keeps`).
Where your own op heads moved the workspace apart, jj's merge with the realization can keep the
other move: `concurrent_tests` has the case, ignored. -/
theorem own_workspace_kept {b : Bool} {v0 : V} {s s' : S V} (hr : Reach J b v0 s)
    (hs : Step J b s s') (hyours : s'.mine = s.mine) {n : N}
    (hW : ∀ p todo, s.mv = .writing p false todo → ∃ h, s.heads = [h] ∧
      (∀ q ∈ s.par p.rz, Anc s.par q h) ∧
        J.keeps (s.view p.rz) (J.load s.par s.view (s.par p.rz)) n (J.ws (s.view h) n)) :
    J.ws (shown J s') n = J.ws (shown J s) n := by
  have hi := hr.inv
  rcases shown_step J hr hs with h | h | ⟨p, todo, hm, h⟩
  · exact absurd hyours h
  · rw [h]
  · rw [h]
    by_cases hin : ∃ h ∈ s.heads, Anc s.par p.rz h
    · obtain ⟨h', hh, hrh⟩ := hin
      rw [load_below J hi.dag hh hrh]; rfl
    · obtain ⟨h', hh, hbase, hkeep⟩ := hW p todo hm
      rw [shown, hh, J.load_single]
      exact J.load_keeps _ _ _ _ _ hi.dag hbase (fun hrh => hin ⟨h', by simp [hh], hrh⟩) hkeep

/-- **Promise 6, other machines' workspaces.** With one op head, which descends from the
realization's parents and has left workspace `n` alone since (`keeps`, at the realization's
commit for it), `n` shows as the realization records it once musubi publishes it: another
machine's workspace, under the name the realization gives it. -/
theorem others_workspace_appears {b : Bool} {v0 : V} {s : S V} (hr : Reach J b v0 s) {p : Plan}
    {todo : List Nat} (h : s.mv = .writing p false todo) {n : N} {hd : Nat}
    (hone : s.heads = [hd]) (hbase : ∀ q ∈ s.par p.rz, Anc s.par q hd)
    (hnew : ¬ Anc s.par p.rz hd)
    (hleft : J.keeps (s.view hd) (J.load s.par s.view (s.par p.rz)) n (J.ws (s.view p.rz) n)) :
    J.ws (shown J { s with heads := Act.apply s.heads (.add p.new), mv := .writing p true todo })
      n = J.ws (s.view p.rz) n := by
  have hi := hr.inv
  rw [publish_shows_merge J hr h, hone]
  exact J.load_takes _ _ _ _ _ hi.dag hbase hnew hleft

/-! ## What the oracle answers

Given the operations below the op heads musubi read and its realization, `settledE` is the
operations whose merge jj shows once musubi has published the realization (`settled_sound`, by
`publish_shows_merge`), and `keptE` those that stay in the op log (`mem_keptE`, by `log_kept`). A
test runs real jj and musubi, with commands and crashes where it likes, and compares the
repository with jj's own merge of `settledE`. -/

/-- Whether `x` is `y` or below it, looking `fuel` parents deep. -/
def ancB (par : Nat → List Nat) (x : Nat) : Nat → Nat → Bool
  | 0, y => x == y
  | f + 1, y => x == y || (par y).any (ancB par x f)

theorem ancB_sound {par : Nat → List Nat} {x : Nat} :
    ∀ {f y : Nat}, ancB par x f y = true → Anc par x y
  | 0, y, h => by simp [ancB] at h; subst h; exact Anc.refl
  | f + 1, y, h => by
    simp only [ancB, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with rfl | ⟨p, hp, hxp⟩
    · exact Anc.refl
    · exact Anc.step hp (ancB_sound hxp)

theorem ancB_complete {par : Nat → List Nat} (hlt : ParLt par) {x y : Nat} (h : Anc par x y) :
    ∀ {f : Nat}, y ≤ f → ancB par x f y = true := by
  induction h with
  | refl => intro f _; cases f <;> simp [ancB]
  | @step p y hp _ ih =>
    intro f hf
    have := hlt y p hp
    cases f with
    | zero => omega
    | succ f =>
      simp only [ancB, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨p, hp, ih (by omega)⟩

/-- The operations of `hs` below no other, each once. -/
def maxE (par : Nat → List Nat) (hs : List Nat) : List Nat :=
  (hs.filter fun x => hs.all fun y => x == y || !ancB par x y y).eraseDups

theorem mem_maxE {par : Nat → List Nat} (hlt : ParLt par) {hs : List Nat} {x : Nat} :
    x ∈ maxE par hs ↔ Max par hs x := by
  simp only [maxE, List.mem_eraseDups, List.mem_filter, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun y hy hxy => ?_⟩
    rcases hall y hy with e | hn
    · exact e
    · rw [ancB_complete hlt hxy (Nat.le_refl _)] at hn; cases hn
  · rintro ⟨hx, hm⟩
    refine ⟨hx, fun y hy => ?_⟩
    cases h : ancB par x y y with
    | false => exact Or.inr rfl
    | true => exact Or.inl (hm y hy (ancB_sound h))

/-- What jj shows once the realization `r` is published beside the op heads `heads`: its merge of
these operations. -/
def settledE (par : Nat → List Nat) (heads : List Nat) (r : Nat) : List Nat :=
  maxE par (heads ++ [r])

theorem settled_sound {par : Nat → List Nat} {view : Nat → V} (hlt : ParLt par)
    (heads : List Nat) (r : Nat) :
    J.load par view (heads ++ [r]) = J.load par view (settledE par heads r) :=
  load_max J hlt fun _ => mem_maxE hlt

/-- The operations below `hs`. -/
def keptE (par : Nat → List Nat) (hs : List Nat) : List Nat :=
  (List.range (hs.foldr max 0 + 1)).filter fun x => hs.any fun h => ancB par x h h

theorem mem_keptE {par : Nat → List Nat} (hlt : ParLt par) {hs : List Nat} {x : Nat} :
    x ∈ keptE par hs ↔ ∃ h ∈ hs, Anc par x h := by
  simp only [keptE, List.mem_filter, List.mem_range, List.any_eq_true]
  constructor
  · rintro ⟨_, h, hh, hx⟩
    exact ⟨h, hh, ancB_sound hx⟩
  · rintro ⟨h, hh, hx⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_trans (hx.le hlt) (le_foldr_max hh)),
      h, hh, ancB_complete hlt hx (Nat.le_refl _)⟩

end Musubi.Realize
