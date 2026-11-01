/-
Replicated `jj op abandon` (docs/internals/design.md, "Abandoning operations").

A machine that abandons operations drops them from the hive's history. Its canonical
operations after them get new ids, contracted as `Contract.lean` defines: each survivor's id is
a function of its original and of the dropped set. So the protocol is modeled over the
original operations, as `Model.lean` has them, with each copy identified with its original,
and each party keeping a set of dropped operations that only grows. Dropping changes no
operation and no head here: the hub and every node go on with the operations they had, and
what changes is which of them each party shows, and under which ids. A *supersede*, which
publishes a node's dropped set, rides on an ordinary push, which moves the hub's head to an
operation the set leaves, the abandoning machine's own work or the fix-up operation it writes.

`SState` adds to a `State` of `Model.lean`:

- `hubD`, `nodeD n`: the hub's and each node's dropped sets;
- `hubP`: what of `hubD` the hub has pruned, keeping no id of it, so that it can neither check
  a head against it nor announce it;
- `hubDHist`, `hubPHist`: ghost, the hub's dropped and pruned sets as of each accepted head,
  which a hub that goes back returns to with the head;
- `sups`, `dmsgs`: the supersedes nodes have sent, each with what the records its node took
  drop and the head of the push it rides on, and the dropped sets the hub has announced.

`SStep` is any `Step` of the protocol, guarded so that the hub takes no new head it remembers
dropping and, once it has pruned anything, only one pushed with the hub's records, and a node
never takes a head it dropped (both refuse superseded ids), plus: `sup`, the hub taking a
supersede with the push it rides on, to a head the push doesn't drop; `abandon`, `jj op
abandon` on a node, which drops operations below its heads but none of them; `sendSup`, with a
head no record its node took drops; `sendD`, of at least what the hub remembers; `adopt`, a
node taking a dropped set the hub announced once no head of its own is in it; and `prune`, the
hub deleting the ids of some of what it dropped. `SRStep` adds the hub going back, to a head
it accepted and the dropped and pruned sets it had then (`Regress.lean`).

A hub that has pruned an operation can't refuse a push to it by its id, so the guard is what it
can check: the push's records are the hub's, so they drop everything it pruned (here, the
supersede's records drop `hubP`; `SupersedeExec.lean` has the records themselves), its head
isn't among the push's pending drops, and the hub doesn't remember dropping it. That no record
its node took drops the head is up to the node, which never names such an operation: a buggy
node that did could make the hub take back an operation it pruned.

What holds:

- The protocol's states are those of `Model.lean` (`SReachable.base`) or `Regress.lean`
  (`SRReachable.base`), so every theorem there holds as stated: `noDuplicateMerge` among
  them. Copies are no new operations, so they make no merge.
- Dropped sets only grow on every node (`nodeD_grows`), and on the hub while it doesn't go back
  (`hubD_grows`). With `Contract.superseded_ne`, an id that a node's dropped set has superseded
  never reappears on that node (`superseded_never_returns`), nor on the hub while it doesn't go
  back (`superseded_never_returns_hub`).
- The hub's head and every node's heads survive their dropped sets, and every dropped
  operation is below a head of a node that dropped it (`SInv`), whatever the hub prunes. So
  while the hub doesn't go back, it never takes a head it dropped, though it may have pruned it
  (`dropped_never_head`); and a node that hasn't dropped an operation the hub pruned has no
  supersede the hub takes (`behind_not_carried`).
- Liveness, once the hub stops going back, from a state where every node has dropped what the
  hub pruned (`AllPruned`): the policy with supersedes (`SPStepR`) ends with every node at the
  hub's head and with the hub's dropped set, which then holds every operation any node dropped
  (`eventually_convergesS`), though the hub announces only what it remembers. A step keeps
  `AllPruned` as long as what it prunes, every node had dropped (`allPruned_step`); the
  executable hub, which prunes only records every node has taken, keeps it in every state it
  reaches (`Exec.sexec_allPruned`).
-/
import Musubi.Regress
import Musubi.Contract
import Musubi.Presence

namespace Musubi

variable {N : Nat}

/-! ## State and steps -/

/-- The protocol over original operations, with each party's dropped set. -/
structure SState where
  s : State
  /-- The operations the hub has dropped. -/
  hubD : OSet
  /-- Ghost: the hub's dropped set as of the head accepted at each sequence number. -/
  hubDHist : Nat → OSet
  /-- The operations of `hubD` the hub has pruned: it knows none of their ids, so refuses a
  push of one only by the push's records. -/
  hubP : OSet
  /-- Ghost: the hub's pruned set as of the head accepted at each sequence number. -/
  hubPHist : Nat → OSet
  /-- The operations each node has dropped, by its own `jj op abandon` or the hub's. -/
  nodeD : Nat → OSet
  /-- Supersedes sent: the node, what the records it took drop, what it dropped then, and the
  head of the push it rides on. -/
  sups : Nat → OSet → OSet → Nat → Prop
  /-- The hub's dropped set, as announced to a node. -/
  dmsgs : Nat → OSet → Prop

namespace SState

def init : SState where
  s := Musubi.init
  hubD := fun _ => False
  hubDHist := fun _ _ => False
  hubP := fun _ => False
  hubPHist := fun _ _ => False
  nodeD := fun _ _ => False
  sups := fun _ _ _ _ => False
  dmsgs := fun _ _ => False

/-- A step of the protocol to `t`, recording the hub's dropped and pruned sets as of a head it
accepts. -/
def withBase (S : SState) (t : State) : SState :=
  { S with s := t,
           hubDHist := if t.hub.seq = S.s.hub.seq then S.hubDHist
                       else upd S.hubDHist t.hub.seq S.hubD,
           hubPHist := if t.hub.seq = S.s.hub.seq then S.hubPHist
                       else upd S.hubPHist t.hub.seq S.hubP }

/-- The hub goes back to the head it accepted at sequence number `i`, and to the dropped and
pruned sets it had then. -/
def regress (S : SState) (i : Nat) : SState :=
  { S with s := S.s.regress i, hubD := S.hubDHist i, hubP := S.hubPHist i }

/-- Node `n` sends a supersede, records dropping `T` and its dropped set, with a push to `h`. -/
def sendSupS (S : SState) (n h : Nat) (T : OSet) : SState :=
  { S with sups := fun m T' Δ g =>
      S.sups m T' Δ g ∨ (m = n ∧ T' = T ∧ Δ = S.nodeD n ∧ g = h) }

end SState

/-- The hub remembers dropping `x`: it dropped it and hasn't pruned it. -/
def Remembered (S : SState) (x : Nat) : Prop := S.hubD x ∧ ¬ S.hubP x

/-- A push to `h` carries a supersede whose records drop every operation the hub has pruned:
the hub checks the push's records are its own. -/
def Carried (S : SState) (h : Nat) : Prop :=
  ∃ n T Δ, S.sups n T Δ h ∧ ∀ x, S.hubP x → T x

/-- A protocol step from `S` to `t` keeps the hub's head, or moves it as the hub accepts a
push: to a head it doesn't remember dropping, and, once it has pruned anything, with records
that are its own. -/
def HeadOK (S : SState) (t : State) : Prop :=
  t.hub.head = S.s.hub.head ∨
    (¬ Remembered S t.hub.head ∧ (Carried S t.hub.head ∨ ∀ x, ¬ S.hubP x))

/-- A protocol step keeps each node's heads, or gives it only heads it hasn't dropped: a node
refuses to advance to a head it has superseded, and the operations it writes are new. -/
def HeadsOK (S : SState) (t : State) : Prop :=
  ∀ n x, (t.node n).heads x → (S.s.node n).heads x ∨ ¬ S.nodeD n x

inductive SStep (N : Nat) : SState → SState → Prop
  /-- A step of the protocol. -/
  | base (S : SState) (t : State) (hs : Step N S.s t) (hh : HeadOK S t) (hn : HeadsOK S t) :
      SStep N S (S.withBase t)
  /-- The hub takes a supersede from node `n` with the push it rides on, which it accepts:
  the push's records are the hub's, so they drop all it pruned, and its head is neither one
  the hub remembers dropping nor one of the push's pending drops. -/
  | sup (S : SState) (t : State) (n : Nat) (T Δ : OSet) (hs : Step N S.s t)
      (hseq : t.hub.seq = S.s.hub.seq + 1) (hm : S.sups n T Δ t.hub.head)
      (hP : ∀ x, S.hubP x → T x) (hh : ¬ Remembered S t.hub.head)
      (hp : ¬ (Δ t.hub.head ∧ ¬ T t.hub.head)) (hn : HeadsOK S t) :
      SStep N S { S with s := t, hubD := fun x => S.hubD x ∨ Δ x,
                         hubDHist := upd S.hubDHist t.hub.seq (fun x => S.hubD x ∨ Δ x),
                         hubPHist := upd S.hubPHist t.hub.seq S.hubP }
  /-- `jj op abandon` on node `n` drops operations below its heads, none of the heads (jj
  refuses to abandon the current operation), and not the root. -/
  | abandon (S : SState) (n : Nat) (D : OSet) (hn : n < N)
      (hD : ∀ x, D x → ∃ h, (S.s.node n).heads h ∧ Anc S.s.U.par x h)
      (hheads : ∀ h, (S.s.node n).heads h → ¬ D h) (hroot : ¬ D root) :
      SStep N S { S with nodeD := upd S.nodeD n (fun x => S.nodeD n x ∨ D x) }
  /-- Node `n` sends a supersede, records dropping `T`, which it dropped, and its dropped set,
  with a push to `h`, which no record it took drops: it never names one. -/
  | sendSup (S : SState) (n h : Nat) (T : OSet) (hn : n < N) (hT : ∀ x, T x → S.nodeD n x)
      (hh : ¬ T h) :
      SStep N S (S.sendSupS n h T)
  /-- The hub announces to node `n` what it dropped: at least what it remembers dropping. -/
  | sendD (S : SState) (n : Nat) (Δ : OSet) (hlo : ∀ x, Remembered S x → Δ x)
      (hhi : ∀ x, Δ x → S.hubD x) :
      SStep N S { S with dmsgs := fun m Δ' => S.dmsgs m Δ' ∨ (m = n ∧ Δ' = Δ) }
  /-- Node `n` takes a dropped set the hub announced, once none of its heads is in it. -/
  | adopt (S : SState) (n : Nat) (Δ : OSet) (hn : n < N) (hm : S.dmsgs n Δ)
      (hheads : ∀ h, (S.s.node n).heads h → ¬ Δ h) :
      SStep N S { S with nodeD := upd S.nodeD n (fun x => S.nodeD n x ∨ Δ x) }
  /-- The hub prunes `F`, of what it dropped: it deletes their ids, and what it dropped as of
  its head is as it is. Whether every node has dropped `F` matters only for liveness
  (`AllPruned`). -/
  | prune (S : SState) (F : OSet) (hF : ∀ x, F x → S.hubD x) :
      SStep N S { S with hubP := fun x => S.hubP x ∨ F x,
                         hubPHist := upd S.hubPHist S.s.hub.seq (fun x => S.hubP x ∨ F x),
                         hubDHist := upd S.hubDHist S.s.hub.seq S.hubD }

/-- A step, or the hub going back. -/
def SRStep (N : Nat) (S S' : SState) : Prop :=
  SStep N S S' ∨ ∃ i, i ≤ S.s.hub.seq ∧ S' = S.regress i

inductive SReachable (N : Nat) : SState → Prop
  | init : SReachable N SState.init
  | step {S S' : SState} : SReachable N S → SStep N S S' → SReachable N S'

inductive SRReachable (N : Nat) : SState → Prop
  | init : SRReachable N SState.init
  | step {S S' : SState} : SRReachable N S → SRStep N S S' → SRReachable N S'

theorem SReachable.sr {S : SState} (h : SReachable N S) : SRReachable N S := by
  induction h with
  | init => exact SRReachable.init
  | step _ hs ih => exact ih.step (Or.inl hs)

/-! ## The protocol is the protocol of `Model.lean` -/

/-- A step leaves the protocol's state as it was, or takes a step of it. -/
theorem SStep.base_step {S S' : SState} (h : SStep N S S') : S'.s = S.s ∨ Step N S.s S'.s := by
  cases h with
  | base t hs => exact Or.inr hs
  | sup t n T Δ hs => exact Or.inr hs
  | _ => exact Or.inl rfl

/-- **The protocol is unchanged**: every state the system with supersedes reaches is reachable
in `Model.lean`, so every theorem there holds of it. -/
theorem SReachable.base {S : SState} (h : SReachable N S) : Reachable N S.s := by
  induction h with
  | init => exact Reachable.init
  | step _ hs ih =>
    rcases SStep.base_step hs with e | e
    · rw [e]; exact ih
    · exact ih.step e

/-- With the hub going back, every state is one of `Regress.lean`. -/
theorem SRReachable.base {S : SState} (h : SRReachable N S) : RReachable N S.s := by
  induction h with
  | init => exact RReachable.init
  | step _ hs ih =>
    rcases hs with hs | ⟨i, hi, rfl⟩
    · rcases SStep.base_step hs with e | e
      · rw [e]; exact ih
      · exact ih.step (Or.inl e)
    · exact ih.step (Or.inr ⟨i, hi, rfl⟩)

/-- **No duplicate merges** with supersedes, while the hub doesn't go back: merges created by
different nodes have different parents (`noDuplicateMerge`). -/
theorem noDuplicateMergeS {S : SState} (h : SReachable N S) {m1 m2 : Nat}
    (h1 : m1 < S.s.U.next) (h2 : m2 < S.s.U.next) (hm1 : S.s.U.isMerge m1 = true)
    (hm2 : S.s.U.isMerge m2 = true) (hc : S.s.U.creator m1 ≠ S.s.U.creator m2) :
    ¬ ∀ x, x ∈ S.s.U.par m1 ↔ x ∈ S.s.U.par m2 :=
  noDuplicateMerge h.base h1 h2 hm1 hm2 hc

/-! ## Facts about protocol steps -/

/-- A step of the protocol keeps the hub's sequence number, or adds one; history up to the old
number stays. -/
theorem step_hub {s t : State} (hs : Step N s t) :
    (t.hub.seq = s.hub.seq ∧ t.hub.head = s.hub.head ∧ t.hub.hist = s.hub.hist) ∨
      (t.hub.seq = s.hub.seq + 1 ∧ ∀ i, i ≤ s.hub.seq → t.hub.hist i = s.hub.hist i) := by
  rcases hs with hs | hs
  · cases hs <;> exact Or.inl ⟨rfl, rfl, rfl⟩
  · cases hs with
    | casAccept => exact Or.inr ⟨rfl, fun i hi => upd_ne _ _ (by omega)⟩
    | hubPushAccept => exact Or.inr ⟨rfl, fun i hi => upd_ne _ _ (show i ≠ s.hub.seq + 1 by omega)⟩
    | _ => exact Or.inl ⟨rfl, rfl, rfl⟩

/-- A step of the protocol keeps the operations created so far as they were. -/
theorem step_par {s t : State} (hs : Step N s t) :
    s.U.next ≤ t.U.next ∧ ∀ y, y < s.U.next → t.U.par y = s.U.par y := by
  rcases hs with hs | hs
  · cases hs with
    | userOp n p O => exact ⟨Nat.le_succ _, fun y hy => upd_ne _ _ (Nat.ne_of_lt hy)⟩
    | merge n L O => exact ⟨Nat.le_succ _, fun y hy => upd_ne _ _ (Nat.ne_of_lt hy)⟩
  · have := noFeedback hs
    rw [this]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-- Every element of a bounded set is below one of its maximal elements. -/
theorem below_max {par : Nat → List Nat} (hlt : ParLt par) {S : OSet} {B : Nat}
    (hB : ∀ y, S y → y < B) {x : Nat} (hx : S x) : ∃ y, maxSet par S y ∧ Anc par x y := by
  obtain ⟨m, ⟨hSm, hAm⟩, hmax⟩ :=
    Musubi.Presence.exists_max_le (Q := fun m => S m ∧ Anc par x m) (x := B)
      ⟨hx, Anc.refl⟩ (fun m hm => Nat.le_of_lt (hB m hm.1))
  refine ⟨m, ⟨hSm, fun y hy hmy => ?_⟩, hAm⟩
  have := hmax y ⟨hy, hAm.trans hmy⟩
  exact Nat.le_antisymm (hmy.le hlt) this

-- Each sync step's node update unfolds through a different few of these definitions.
set_option linter.unusedSimpArgs false in
/-- What a node's heads reach only grows: every protocol step keeps each operation below some
head of each node. -/
theorem step_heads_cover {s t : State} (hI : InvR N s) (hs : Step N s t) {m x : Nat}
    (hx : ∃ h, (s.node m).heads h ∧ Anc s.U.par x h) :
    ∃ h, (t.node m).heads h ∧ Anc t.U.par x h := by
  obtain ⟨h, hh, hA⟩ := hx
  rcases hs with hs | hs
  · cases hs with
    | userOp n p O hn hp =>
      have hLlt : ∀ q ∈ [p], q < s.U.next := by
        intro q hq; simp at hq; rw [hq]; exact hI.lLt n p hp
      have hlt' := parLt_upd hI.parLt hLlt
      have hA' : Anc (upd s.U.par s.U.next [p]) x h :=
        (anc_upd_iff hI.parLt hLlt (hI.headsLt hh)).2 hA
      by_cases hmn : m = n
      · subst hmn
        let S' : OSet := fun y => ((s.node m).heads y ∧ y ≠ p) ∨ y = s.U.next
        have hB : ∀ y, S' y → y < s.U.next + 1 := by
          rintro y (⟨hy, -⟩ | rfl)
          · exact Nat.lt_succ_of_lt (hI.headsLt hy)
          · exact Nat.lt_succ_self _
        by_cases hhp : h = p
        · subst hhp
          obtain ⟨y, hy, hAy⟩ := below_max hlt' hB (x := s.U.next) (Or.inr rfl)
          refine ⟨y, by simpa [State.userOp, State.createOp] using hy, ?_⟩
          exact hA'.trans ((Anc.parent (by simp)).trans hAy)
        · obtain ⟨y, hy, hAy⟩ := below_max hlt' hB (x := h) (Or.inl ⟨hh, hhp⟩)
          exact ⟨y, by simpa [State.userOp, State.createOp] using hy, hA'.trans hAy⟩
      · refine ⟨h, ?_, hA'⟩
        simpa [State.userOp, State.createOp, hmn] using hh
    | merge n L O hn hL h2 =>
      have hLlt : ∀ q ∈ L, q < s.U.next := fun q hq => hI.headsLt ((hL q).1 hq)
      have hA' : Anc (upd s.U.par s.U.next L) x h :=
        (anc_upd_iff hI.parLt hLlt (hI.headsLt hh)).2 hA
      by_cases hmn : m = n
      · subst hmn
        refine ⟨s.U.next, by simp [State.mergeOp, State.createOp], ?_⟩
        exact hA'.trans (Anc.parent (by simp; exact (hL h).2 hh))
      · exact ⟨h, by simpa [State.mergeOp, State.createOp, hmn] using hh, hA'⟩
  · have hU := noFeedback hs
    cases hs with
    | advance n hn hk hna =>
      by_cases hmn : m = n
      · subst hmn
        have hB : ∀ y, ((s.node m).heads y ∨ y = (s.node m).known.2) → y < s.U.next := by
          rintro y (hy | rfl)
          · exact hI.headsLt hy
          · exact hI.knownLt m
        obtain ⟨y, hy, hAy⟩ := below_max hI.parLt hB (Or.inl hh)
        exact ⟨y, by simpa [State.advance, State.setNode] using hy, hA.trans hAy⟩
      · exact ⟨h, by simpa [State.advance, State.setNode, upd, hmn] using hh, hA⟩
    | _ =>
      refine ⟨h, ?_, hA⟩
      first
        | exact hh
        | (simp only [State.learn, State.recvOps, State.recvObjs, State.realize,
            State.setNode, State.send, State.hubStoreOps, State.hubStoreObjs, State.hubStore,
            State.hubAccept, State.notifyAll]
           unfold upd; split <;> (try subst_vars) <;> exact hh)

/-! ## The invariant -/

/-- `x` is dropped by some node, below one of its heads: so some node can always publish a
head that leaves it. -/
def Kept (N : Nat) (S : SState) (x : Nat) : Prop :=
  ∃ m, m < N ∧ S.nodeD m x ∧ ∃ h, (S.s.node m).heads h ∧ Anc S.s.U.par x h

/-- What every dropped set satisfies: the root survives, and every operation in it exists and
is kept. -/
def DOK (N : Nat) (S : SState) (Δ : OSet) : Prop :=
  ∀ x, Δ x → x ≠ root ∧ x < S.s.U.next ∧ Kept N S x

structure SInv (N : Nat) (S : SState) : Prop where
  base : InvR N S.s
  hub : DOK N S S.hubD
  hist : ∀ i, i ≤ S.s.hub.seq → DOK N S (S.hubDHist i)
  histCur : ∀ x, S.hubDHist S.s.hub.seq x ↔ S.hubD x
  histHead : ∀ i, i ≤ S.s.hub.seq → ¬ S.hubDHist i (S.s.hub.hist i)
  prunedCur : ∀ x, S.hubPHist S.s.hub.seq x ↔ S.hubP x
  prunedHist : ∀ i, i ≤ S.s.hub.seq → ∀ x, S.hubPHist i x → S.hubDHist i x
  node : ∀ n, DOK N S (S.nodeD n)
  sups : ∀ n T Δ h, S.sups n T Δ h → DOK N S Δ
  /-- The records a supersede carries drop no head of the push it rides on. -/
  supsHead : ∀ n T Δ h, S.sups n T Δ h → ¬ T h
  /-- What the records a node's supersede carries drop, the node has dropped. -/
  supsNode : ∀ n T Δ h, S.sups n T Δ h → ∀ x, T x → S.nodeD n x
  dmsgs : ∀ n Δ, S.dmsgs n Δ → DOK N S Δ
  headsOK : ∀ n x, (S.s.node n).heads x → ¬ S.nodeD n x

namespace SInv

variable {S : SState}

/-- The hub's head survives the hub's dropped set. -/
theorem headOK (hI : SInv N S) : ¬ S.hubD S.s.hub.head := by
  intro h
  apply hI.histHead S.s.hub.seq (Nat.le_refl _)
  rw [hI.base.histHead]; exact (hI.histCur _).2 h

/-- What the hub has pruned, it dropped. -/
theorem pruned (hI : SInv N S) {x : Nat} (hx : S.hubP x) : S.hubD x :=
  (hI.histCur x).1 (hI.prunedHist _ (Nat.le_refl _) x ((hI.prunedCur x).2 hx))


/-- A head the hub accepts with a push carrying its records, and doesn't remember dropping, it
didn't drop: the records drop every operation the hub pruned, and the push's node never names
an operation they drop. -/
theorem not_dropped (hI : SInv N S) {h : Nat} (hc : Carried S h) (hr : ¬ Remembered S h) :
    ¬ S.hubD h := by
  obtain ⟨n, T, Δ, hm, hP⟩ := hc
  intro hd
  by_cases hf : S.hubP h
  · exact hI.supsHead n T Δ h hm (hP h hf)
  · exact hr ⟨hd, hf⟩

/-- So a step keeps the hub's head, or moves it to one the hub hasn't dropped. -/
theorem head_step (hI : SInv N S) {t : State} (hh : HeadOK S t) :
    t.hub.head = S.s.hub.head ∨ ¬ S.hubD t.hub.head := by
  refine hh.imp id fun ⟨hr, hc⟩ => ?_
  rcases hc with hc | hnone
  · exact hI.not_dropped hc hr
  · exact fun hd => hr ⟨hd, hnone _⟩

end SInv

theorem sinv_init (N : Nat) : SInv N SState.init where
  base := invR_init N
  hub := fun _ h => h.elim
  hist := fun _ _ _ h => h.elim
  histCur := fun _ => Iff.rfl
  histHead := fun _ _ h => h
  prunedCur := fun _ => Iff.rfl
  prunedHist := fun _ _ _ h => h.elim
  node := fun _ _ h => h.elim
  sups := fun _ _ _ _ h => h.elim
  supsHead := fun _ _ _ _ h => h.elim
  supsNode := fun _ _ _ _ h => h.elim
  dmsgs := fun _ _ h => h.elim
  headsOK := fun _ _ _ h => h

/-- A dropped set stays good when the protocol moves on, what each node has dropped only grows,
and so does what its heads reach. -/
theorem DOK.mono {S S' : SState} {Δ : OSet} (h : DOK N S Δ) (hn : S.s.U.next ≤ S'.s.U.next)
    (hD : ∀ m x, S.nodeD m x → S'.nodeD m x)
    (hc : ∀ m x, (∃ g, (S.s.node m).heads g ∧ Anc S.s.U.par x g) →
      ∃ g, (S'.s.node m).heads g ∧ Anc S'.s.U.par x g) : DOK N S' Δ := by
  intro x hx
  obtain ⟨hr, hlt, m, hm, hDm, hcov⟩ := h x hx
  exact ⟨hr, Nat.lt_of_lt_of_le hlt hn, m, hm, hD m x hDm, hc m x hcov⟩

/-- Part of a good dropped set is good. -/
theorem DOK.sub {S : SState} {Δ Δ' : OSet} (h : DOK N S Δ) (hs : ∀ x, Δ' x → Δ x) :
    DOK N S Δ' := fun x hx => h x (hs x hx)

theorem sinv_base {S : SState} (hI : SInv N S) {t : State} (hs : Step N S.s t)
    (hn : HeadsOK S t) {D' : OSet} (hD' : DOK N S D') {H' : Nat → OSet}
    (hH : ∀ i, i ≤ t.hub.seq → DOK N S (H' i) ∧ ¬ H' i (t.hub.hist i))
    (hcur : ∀ x, H' t.hub.seq x ↔ D' x) {FH' : Nat → OSet}
    (hFH : ∀ i, i ≤ t.hub.seq → ∀ x, FH' i x → H' i x)
    (hfcur : ∀ x, FH' t.hub.seq x ↔ S.hubP x) :
    SInv N { S with s := t, hubD := D', hubDHist := H', hubPHist := FH' } := by
  have hIt : InvR N t := invR_rstep hI.base (Or.inl hs)
  obtain ⟨hnext, -⟩ := step_par hs
  have mono : ∀ {Δ}, DOK N S Δ →
      DOK N { S with s := t, hubD := D', hubDHist := H', hubPHist := FH' } Δ :=
    fun h => h.mono hnext (fun _ _ h => h) (fun _ _ hc => step_heads_cover hI.base hs hc)
  exact
    { base := hIt
      hub := mono hD'
      hist := fun i hi => mono (hH i hi).1
      histCur := hcur
      histHead := fun i hi => (hH i hi).2
      prunedCur := hfcur
      prunedHist := hFH
      node := fun n => mono (hI.node n)
      sups := fun n T Δ h hm => mono (hI.sups n T Δ h hm)
      supsHead := hI.supsHead
      supsNode := hI.supsNode
      dmsgs := fun n Δ h => mono (hI.dmsgs n Δ h)
      headsOK := fun n x hx => (hn n x hx).elim (hI.headsOK n x) id }

/-- The history obligations of `sinv_base` for a step that accepts a head, recording `D'` as
the hub's dropped set as of it. -/
theorem hist_upd_ok {S : SState} (hI : SInv N S) {t : State} (hs : Step N S.s t)
    (hseq : t.hub.seq = S.s.hub.seq + 1) {D' : OSet} (hD' : DOK N S D')
    (hD'h : ¬ D' t.hub.head) :
    ∀ i, i ≤ t.hub.seq → DOK N S (upd S.hubDHist t.hub.seq D' i) ∧
      ¬ upd S.hubDHist t.hub.seq D' i (t.hub.hist i) := by
  have hIt : InvR N t := invR_rstep hI.base (Or.inl hs)
  have hhist : ∀ i, i ≤ S.s.hub.seq → t.hub.hist i = S.s.hub.hist i := by
    rcases step_hub hs with ⟨e, -⟩ | ⟨-, h⟩
    · omega
    · exact h
  intro i hi
  by_cases hit : i = t.hub.seq
  · subst hit; rw [upd_same, hIt.histHead]; exact ⟨hD', hD'h⟩
  · rw [upd_ne _ _ hit]
    have hle : i ≤ S.s.hub.seq := by omega
    rw [hhist i hle]; exact ⟨hI.hist i hle, hI.histHead i hle⟩

/-- The obligations of `sinv_base` for the pruned sets, for a step that accepts a head,
recording `D'`, which holds what the hub has pruned, as the hub's dropped set as of it. -/
theorem phist_upd_ok {S : SState} (hI : SInv N S) {t : State}
    (hseq : t.hub.seq = S.s.hub.seq + 1) {D' : OSet} (hFD : ∀ x, S.hubP x → D' x) :
    ∀ i, i ≤ t.hub.seq →
      ∀ x, upd S.hubPHist t.hub.seq S.hubP i x → upd S.hubDHist t.hub.seq D' i x := by
  intro i hi
  by_cases hit : i = t.hub.seq
  · subst hit; simp only [upd_same]; exact hFD
  · simp only [upd_ne _ _ hit]
    exact hI.prunedHist i (by omega)

/-- A node's dropped set grows: every good dropped set stays good. -/
theorem sinv_nodeD {S : SState} (hI : SInv N S) {n : Nat} {D : OSet}
    (hgood : ∀ x, D x → S.nodeD n x ∨ (x ≠ root ∧ x < S.s.U.next ∧
      ∃ g, (S.s.node n).heads g ∧ Anc S.s.U.par x g) ∨ ∃ Δ, S.dmsgs n Δ ∧ Δ x)
    (hn : n < N) (hheads : ∀ h, (S.s.node n).heads h → ¬ D h) :
    SInv N { S with nodeD := upd S.nodeD n (fun x => S.nodeD n x ∨ D x) } := by
  have hD' : ∀ m x, S.nodeD m x → upd S.nodeD n (fun x => S.nodeD n x ∨ D x) m x := by
    intro m x hx
    by_cases hmn : m = n
    · subst hmn; rw [upd_same]; exact Or.inl hx
    · rw [upd_ne _ _ hmn]; exact hx
  have mono : ∀ {Δ}, DOK N S Δ →
      DOK N { S with nodeD := upd S.nodeD n (fun x => S.nodeD n x ∨ D x) } Δ :=
    fun h => h.mono (Nat.le_refl _) hD' (fun _ _ hc => hc)
  refine
    { base := hI.base
      hub := mono hI.hub
      hist := fun i hi => mono (hI.hist i hi)
      histCur := hI.histCur
      histHead := hI.histHead
      prunedCur := hI.prunedCur
      prunedHist := hI.prunedHist
      node := ?_
      sups := fun m T Δ h hm => mono (hI.sups m T Δ h hm)
      supsHead := hI.supsHead
      supsNode := fun m T Δ h hm x hx => hD' m x (hI.supsNode m T Δ h hm x hx)
      dmsgs := fun m Δ h => mono (hI.dmsgs m Δ h)
      headsOK := ?_ }
  · intro m x hx
    by_cases hmn : m = n
    · subst hmn
      have : S.nodeD m x ∨ D x := by
        have := hx; simp only [upd_same] at this; exact this
      rcases this with h | h
      · exact mono (hI.node m) x h
      · rcases hgood x h with h' | ⟨hr, hlt, g, hg, hA⟩ | ⟨Δ, hm, hΔ⟩
        · exact mono (hI.node m) x h'
        · refine ⟨hr, hlt, m, hn, ?_, g, hg, hA⟩
          show upd S.nodeD m _ m x; rw [upd_same]; exact Or.inr h
        · exact mono (hI.dmsgs m Δ hm) x hΔ
    · have : upd S.nodeD n (fun x => S.nodeD n x ∨ D x) m x := hx
      rw [upd_ne _ _ hmn] at this
      exact mono (hI.node m) x this
  · intro m x hx hd
    by_cases hmn : m = n
    · subst hmn
      have : S.nodeD m x ∨ D x := by
        have := hd; simp only [upd_same] at this; exact this
      rcases this with h | h
      · exact hI.headsOK m x hx h
      · exact hheads x hx h
    · have : upd S.nodeD n (fun x => S.nodeD n x ∨ D x) m x := hd
      rw [upd_ne _ _ hmn] at this
      exact hI.headsOK m x hx this

theorem sinv_step {S S' : SState} (hI : SInv N S) (h : SStep N S S') : SInv N S' := by
  cases h with
  | base t hs hh hn =>
    unfold SState.withBase
    rcases step_hub hs with ⟨hq, hhd, hhist⟩ | ⟨hq, -⟩
    · simp only [hq, ↓reduceIte]
      refine sinv_base hI hs hn hI.hub (fun i hi => ?_) (by rw [hq]; exact hI.histCur)
        (fun i hi => ?_) (by rw [hq]; exact hI.prunedCur)
      · rw [hq] at hi; rw [hhist]; exact ⟨hI.hist i hi, hI.histHead i hi⟩
      · rw [hq] at hi; exact hI.prunedHist i hi
    · have hq' : ¬ t.hub.seq = S.s.hub.seq := by omega
      simp only [hq', ↓reduceIte]
      refine sinv_base hI hs hn hI.hub (hist_upd_ok hI hs hq hI.hub ?_) (by simp)
        (phist_upd_ok hI hq (fun x hx => hI.pruned hx)) (by simp)
      rcases hI.head_step hh with e | e
      · rw [e]; exact hI.headOK
      · exact e
  | sup t n T Δ hs hseq hm hP hh hp hn =>
    have hD' : DOK N S (fun x => S.hubD x ∨ Δ x) := by
      intro x hx
      rcases hx with hx | hx
      · exact hI.hub x hx
      · exact hI.sups n T Δ _ hm x hx
    have hnd : ¬ S.hubD t.hub.head := hI.not_dropped ⟨n, T, Δ, hm, hP⟩ hh
    have hD'h : ¬ (S.hubD t.hub.head ∨ Δ t.hub.head) := by
      rintro (h | h)
      · exact hnd h
      · exact hI.supsHead n T Δ _ hm (Classical.byContradiction fun hT => hp ⟨h, hT⟩)
    exact sinv_base hI hs hn hD' (hist_upd_ok hI hs hseq hD' hD'h) (by simp)
      (phist_upd_ok hI hseq (fun x hx => Or.inl (hI.pruned hx))) (by simp)
  | abandon n D hn hD hheads hroot =>
    refine sinv_nodeD hI (fun x hx => Or.inr (Or.inl ?_)) hn hheads
    obtain ⟨g, hg, hA⟩ := hD x hx
    exact ⟨fun e => hroot (e ▸ hx),
      Nat.lt_of_le_of_lt (hA.le hI.base.parLt) (hI.base.headsLt hg), g, hg, hA⟩
  | sendSup n h T hn hT hh =>
    exact
      { hI with
        sups := by
          rintro m T' Δ g (hm | ⟨-, -, rfl, -⟩)
          · exact hI.sups m T' Δ g hm
          · exact hI.node n
        supsHead := by
          rintro m T' Δ g (hm | ⟨-, rfl, -, rfl⟩)
          · exact hI.supsHead m T' Δ g hm
          · exact hh
        supsNode := by
          rintro m T' Δ g (hm | ⟨rfl, rfl, -, -⟩)
          · exact hI.supsNode m T' Δ g hm
          · exact hT }
  | sendD n Δ hlo hhi =>
    exact
      { hI with
        dmsgs := by
          rintro m Δ' (h | ⟨-, rfl⟩)
          · exact hI.dmsgs m Δ' h
          · exact hI.hub.sub hhi }
  | adopt n Δ hn hm hheads =>
    exact sinv_nodeD hI (fun x hx => Or.inr (Or.inr ⟨Δ, hm, hx⟩)) hn hheads
  | prune F hF =>
    refine
      { hI with
        hist := fun i hi => ?_
        histCur := fun x => by simp only [upd_same]
        histHead := fun i hi => ?_
        prunedCur := fun x => by simp only [upd_same]
        prunedHist := fun i hi x hx => ?_ }
    · by_cases hit : i = S.s.hub.seq
      · subst hit; simp only [upd_same]; exact hI.hub
      · simp only [upd_ne _ _ hit]; exact hI.hist i hi
    · by_cases hit : i = S.s.hub.seq
      · subst hit; simp only [upd_same]; rw [hI.base.histHead]; exact hI.headOK
      · simp only [upd_ne _ _ hit]; exact hI.histHead i hi
    · by_cases hit : i = S.s.hub.seq
      · subst hit; simp only [upd_same] at hx ⊢
        exact hx.elim (fun h => hI.pruned h) (hF x)
      · simp only [upd_ne _ _ hit] at hx ⊢; exact hI.prunedHist i hi x hx

theorem sinv_regress {S : SState} (hI : SInv N S) {i : Nat} (hi : i ≤ S.s.hub.seq) :
    SInv N (S.regress i) := by
  have mono : ∀ {Δ}, DOK N S Δ → DOK N (S.regress i) Δ :=
    fun h => h.mono (Nat.le_refl _) (fun _ _ h => h) (fun _ _ hc => hc)
  exact
    { base := invR_regress hI.base hi
      hub := mono (hI.hist i hi)
      hist := fun j hj => mono (hI.hist j (Nat.le_trans hj hi))
      histCur := fun _ => Iff.rfl
      histHead := fun j hj => hI.histHead j (Nat.le_trans hj hi)
      prunedCur := fun _ => Iff.rfl
      prunedHist := fun j hj => hI.prunedHist j (Nat.le_trans hj hi)
      node := fun n => mono (hI.node n)
      sups := fun n T Δ h hm => mono (hI.sups n T Δ h hm)
      supsHead := hI.supsHead
      supsNode := hI.supsNode
      dmsgs := fun n Δ h => mono (hI.dmsgs n Δ h)
      headsOK := hI.headsOK }

theorem sinv_rstep {S S' : SState} (hI : SInv N S) (h : SRStep N S S') : SInv N S' := by
  rcases h with h | ⟨i, hi, rfl⟩
  · exact sinv_step hI h
  · exact sinv_regress hI hi

theorem sinv_reachable {S : SState} (h : SRReachable N S) : SInv N S := by
  induction h with
  | init => exact sinv_init N
  | step _ hs ih => exact sinv_rstep ih hs

/-! ## Dropped sets only grow -/

/-- What a node has dropped, it keeps dropped, whatever happens, the hub going back included. -/
theorem nodeD_grows {S S' : SState} (h : SRStep N S S') {n x : Nat} (hx : S.nodeD n x) :
    S'.nodeD n x := by
  rcases h with h | ⟨i, -, rfl⟩
  · cases h with
    | abandon m D =>
      show upd S.nodeD m _ n x
      by_cases hnm : n = m
      · subst hnm; rw [upd_same]; exact Or.inl hx
      · rw [upd_ne _ _ hnm]; exact hx
    | adopt m Δ =>
      show upd S.nodeD m _ n x
      by_cases hnm : n = m
      · subst hnm; rw [upd_same]; exact Or.inl hx
      · rw [upd_ne _ _ hnm]; exact hx
    | _ => exact hx
  · exact hx

/-- What the hub has dropped, it keeps dropped while it doesn't go back. -/
theorem hubD_grows {S S' : SState} (h : SStep N S S') {x : Nat} (hx : S.hubD x) :
    S'.hubD x := by
  cases h with
  | sup => exact Or.inl hx
  | _ => exact hx

/-- Runs of the system. -/
inductive SRSteps (N : Nat) : SState → SState → Prop
  | refl (S : SState) : SRSteps N S S
  | tail {S T U : SState} : SRSteps N S T → SRStep N T U → SRSteps N S U

/-- Runs of the system in which the hub doesn't go back. -/
inductive SSteps (N : Nat) : SState → SState → Prop
  | refl (S : SState) : SSteps N S S
  | tail {S T U : SState} : SSteps N S T → SStep N T U → SSteps N S U

theorem SSteps.sr {S T : SState} (h : SSteps N S T) : SRSteps N S T := by
  induction h with
  | refl => exact SRSteps.refl _
  | tail _ hs ih => exact ih.tail (Or.inl hs)

theorem SRSteps.reachable {S T : SState} (hS : SRReachable N S) (h : SRSteps N S T) :
    SRReachable N T := by
  induction h with
  | refl => exact hS
  | tail _ hs ih => exact ih.step hs

theorem SRSteps.nodeD {S T : SState} (h : SRSteps N S T) {n x : Nat} (hx : S.nodeD n x) :
    T.nodeD n x := by
  induction h with
  | refl => exact hx
  | tail _ hs ih => exact nodeD_grows hs ih

theorem SSteps.hubD {S T : SState} (h : SSteps N S T) {x : Nat} (hx : S.hubD x) :
    T.hubD x := by
  induction h with
  | refl => exact hx
  | tail _ hs ih => exact hubD_grows hs ih

/-- A run keeps the operations created so far as they were. -/
theorem SRSteps.par {S T : SState} (h : SRSteps N S T) :
    S.s.U.next ≤ T.s.U.next ∧ ∀ y, y < S.s.U.next → T.s.U.par y = S.s.U.par y := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | tail _ hs ih =>
    obtain ⟨hn, hp⟩ := ih
    have hstep : ∀ {A B : SState}, SRStep N A B →
        A.s.U.next ≤ B.s.U.next ∧ ∀ y, y < A.s.U.next → B.s.U.par y = A.s.U.par y := by
      intro A B h
      rcases h with h | ⟨i, -, rfl⟩
      · rcases SStep.base_step h with e | e
        · rw [e]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
        · exact step_par e
      · exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    obtain ⟨hn', hp'⟩ := hstep hs
    exact ⟨Nat.le_trans hn hn', fun y hy => (hp' y (Nat.lt_of_lt_of_le hy hn)).trans (hp y hy)⟩

/-- **A hub that prunes never takes a head it dropped**: once the hub has dropped `x`, it is
never its head again while the hub doesn't go back, though it may prune `x` and so no longer
know its id. A push to `x` carries records, which the hub checks are its own and so drop all
it pruned, and its node never names an operation they drop. -/
theorem dropped_never_head {S T : SState} (hS : SReachable N S) (hST : SSteps N S T) {x : Nat}
    (hx : S.hubD x) : T.s.hub.head ≠ x := by
  intro e
  exact (sinv_reachable (hST.sr.reachable hS.sr)).headOK (e ▸ hST.hubD hx)

/-! ## Superseded ids never come back -/

open Classical in
/-- The id of `x` in state `S` under the dropped set `D` (`Contract.cid`). -/
noncomputable def SState.cidOf (S : SState) (D : OSet) (x : Nat) : Contract.CId :=
  Contract.cid id S.s.U.par (fun y => decide (D y)) x

/-- Ids of operations that exist stay as they were, as later operations are created. -/
theorem cid_stable {S T : SState} (hS : SRReachable N S) (hST : SRSteps N S T) (D : OSet)
    {x : Nat} (hx : x < S.s.U.next) : T.cidOf D x = S.cidOf D x := by
  have hIS := (sinv_reachable hS).base
  have hIT := (sinv_reachable (hST.reachable hS)).base
  obtain ⟨-, hpar⟩ := hST.par
  exact Contract.cid_congr hIT.parLt hIS.parLt (fun y hy => hpar y (Nat.lt_of_le_of_lt hy hx))

/-- **Superseded ids never come back on a node**: once node `n` has dropped `x`, or an ancestor
of `x` it hadn't dropped at `S`, the id `x` had there is no id of an operation the node keeps,
then or ever after, the hub going back included. -/
theorem superseded_never_returns {S T T' : SState} (hS : SRReachable N S)
    (hST : SRSteps N S T) (hTT : SRSteps N T T') {n x : Nat} (hx : x < S.s.U.next)
    (hsup : T.nodeD n x ∨ ∃ a, Anc S.s.U.par a x ∧ a ≠ x ∧ T.nodeD n a ∧ ¬ S.nodeD n a)
    {y : Nat} (hy : ¬ T'.nodeD n y) : S.cidOf (S.nodeD n) x ≠ T'.cidOf (T'.nodeD n) y := by
  have hST' : SRSteps N S T' := by
    clear hy hsup
    induction hTT with
    | refl => exact hST
    | tail _ hs ih => exact ih.tail hs
  have hIT' := (sinv_reachable (hST'.reachable hS)).base
  rw [← cid_stable hS hST' (S.nodeD n) hx]
  obtain ⟨-, hpar⟩ := hST'.par
  apply Contract.superseded_ne hIT'.parLt (fun _ _ h => h)
  · rcases hsup with h | ⟨a, hA, hne, hTa, hSa⟩
    · exact Or.inl (by simpa using hTT.nodeD h)
    · refine Or.inr ⟨a, ?_, hne, by simpa using hTT.nodeD hTa, by simpa using hSa⟩
      exact Contract.anc_congr hIT'.parLt
        (fun z hz => hpar z (Nat.lt_of_le_of_lt hz hx)) |>.2 hA
  · simpa using hy

/-- **Superseded ids never come back on the hub**, while it doesn't go back. -/
theorem superseded_never_returns_hub {S T T' : SState} (hS : SReachable N S)
    (hST : SSteps N S T) (hTT : SSteps N T T') {x : Nat} (hx : x < S.s.U.next)
    (hsup : T.hubD x ∨ ∃ a, Anc S.s.U.par a x ∧ a ≠ x ∧ T.hubD a ∧ ¬ S.hubD a)
    {y : Nat} (hy : ¬ T'.hubD y) : S.cidOf S.hubD x ≠ T'.cidOf T'.hubD y := by
  have hST' : SSteps N S T' := by
    clear hy hsup
    induction hTT with
    | refl => exact hST
    | tail _ hs ih => exact ih.tail hs
  have hSR := hS.sr
  have hIT' := (sinv_reachable (hST'.sr.reachable hSR)).base
  rw [← cid_stable hSR hST'.sr S.hubD hx]
  obtain ⟨-, hpar⟩ := hST'.sr.par
  apply Contract.superseded_ne hIT'.parLt (fun _ _ h => h)
  · rcases hsup with h | ⟨a, hA, hne, hTa, hSa⟩
    · exact Or.inl (by simpa using hTT.hubD h)
    · refine Or.inr ⟨a, ?_, hne, by simpa using hTT.hubD hTa, by simpa using hSa⟩
      exact Contract.anc_congr hIT'.parLt
        (fun z hz => hpar z (Nat.lt_of_le_of_lt hz hx)) |>.2 hA
  · simpa using hy


/-! ## Liveness once the hub stops going back -/

/-- Every node has dropped what the hub has pruned: as when the hub waits for every node. -/
def AllPruned (N : Nat) (S : SState) : Prop := ∀ n, n < N → ∀ x, S.hubP x → S.nodeD n x

theorem allPruned_init (N : Nat) : AllPruned N SState.init := fun _ _ _ h => h.elim

/-- **A step keeps every node with what the hub pruned**, as long as what it prunes, every node
had dropped. -/
theorem allPruned_step {S S' : SState} (hA : AllPruned N S) (h : SStep N S S')
    (hp : ∀ x, S'.hubP x → ¬ S.hubP x → ∀ n, n < N → S.nodeD n x) : AllPruned N S' := by
  intro n hn x hx
  by_cases hs : S.hubP x
  · exact nodeD_grows (Or.inl h) (hA n hn x hs)
  · exact nodeD_grows (Or.inl h) (hp x hx hs n hn)

/-- **A node that hasn't dropped an operation the hub pruned has no supersede the hub takes**:
none it has sent carries records dropping all the hub pruned. The implementation checks the
records themselves, so it refuses too a node that dropped the operation but never took the
record. -/
theorem behind_not_carried {S : SState} (hI : SInv N S) {n x : Nat} (hx : S.hubP x)
    (hnx : ¬ S.nodeD n x) {T Δ : OSet} {h : Nat} (hm : S.sups n T Δ h) :
    ¬ ∀ y, S.hubP y → T y :=
  fun hT => hnx (hI.supsNode n T Δ h hm x (hT x hx))

namespace SState

/-- Node `n` takes what the hub remembers dropping, which the hub announces to it: what it has
pruned, the node dropped already, where every node has (`AllPruned`). -/
def adoptHub (S : SState) (n : Nat) : SState :=
  { S with dmsgs := fun m Δ => S.dmsgs m Δ ∨ (m = n ∧ Δ = Remembered S),
           nodeD := upd S.nodeD n (fun x => S.nodeD n x ∨ Remembered S x) }

/-- Node `n` sends its dropped set with a push to `h` the hub accepts, reaching `t`. -/
def supWith (S : SState) (n h : Nat) (t : State) : SState :=
  { S with s := t,
           sups := fun m T Δ g =>
             S.sups m T Δ g ∨ (m = n ∧ T = S.nodeD n ∧ Δ = S.nodeD n ∧ g = h),
           hubD := fun x => S.hubD x ∨ S.nodeD n x,
           hubDHist := upd S.hubDHist (S.s.hub.seq + 1) (fun x => S.hubD x ∨ S.nodeD n x),
           hubPHist := upd S.hubPHist (S.s.hub.seq + 1) S.hubP }

end SState

/-- The policy with supersedes. The steps of `PStepR`, where a node advances only to a head it
hasn't dropped, and pushes, to be accepted, only with the hub's dropped set, which it sends
with the push; and three more. A node takes what the hub remembers dropping once none of its
heads is in it (`adopt`). A node that has dropped operations the hub hasn't sends its dropped
set with its push (`supPush`), or first writes the fix-up operation on its head and pushes that
(`supFix`), as musubi does. -/
inductive SPStepR (N : Nat) : SState → SState → Prop
  | learn (S : SState) (n : Nat) (hn : n < N)
      (hs : (S.s.node n).known ≠ (S.s.hub.seq, S.s.hub.head)) :
      SPStepR N S (S.withBase (S.s.pLearn n))
  | realize (S : SState) (n x : Nat) (hn : n < N) (hc : Consistent S.s n)
      (hx : Anc S.s.U.par x (S.s.node n).known.2) (hnl : ¬ (S.s.node n).lops x)
      (hp : ∀ p ∈ S.s.U.par x, (S.s.node n).lops p) :
      SPStepR N S (S.withBase (S.s.pRealize n x))
  | advance (S : SState) (n : Nat) (hn : n < N) (hk : (S.s.node n).lops (S.s.node n).known.2)
      (hna : ¬ ∃ h, (S.s.node n).heads h ∧ Anc S.s.U.par (S.s.node n).known.2 h)
      (hd : ¬ S.nodeD n (S.s.node n).known.2) :
      SPStepR N S (S.withBase (S.s.advance n))
  | merge (S : SState) (n : Nat) (L O : List Nat) (hn : n < N)
      (hL : ∀ x, x ∈ L ↔ (S.s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
      SPStepR N S (S.withBase (S.s.mergeOp n L O))
  | pushAccept (S : SState) (n h : Nat) (hn : n < N)
      (hh : ∀ y, (S.s.node n).heads y ↔ y = h) (hne : h ≠ (S.s.node n).known.2)
      (hk : Anc S.s.U.par (S.s.node n).known.2 h) (hacc : S.s.hub.head = (S.s.node n).known.2)
      (hD : ∀ x, S.nodeD n x ↔ S.hubD x) :
      SPStepR N S ((S.sendSupS n h (S.nodeD n)).withBase (S.s.pPushAccept n h))
  | pushIdem (S : SState) (n h : Nat) (hn : n < N)
      (hh : ∀ y, (S.s.node n).heads y ↔ y = h) (hne : h ≠ (S.s.node n).known.2)
      (hk : Anc S.s.U.par (S.s.node n).known.2 h) (hidem : S.s.hub.head = h) :
      SPStepR N S (S.withBase (S.s.pPushIdem n h))
  | pushReject (S : SState) (n h : Nat) (hn : n < N)
      (hh : ∀ y, (S.s.node n).heads y ↔ y = h) (hne : h ≠ (S.s.node n).known.2)
      (hk : Anc S.s.U.par (S.s.node n).known.2 h) (hrej : S.s.hub.head ≠ (S.s.node n).known.2)
      (hrej' : S.s.hub.head ≠ h) :
      SPStepR N S (S.withBase (S.s.pPushReject n h))
  | adopt (S : SState) (n : Nat) (hn : n < N) (hlag : ∃ x, S.hubD x ∧ ¬ S.nodeD n x)
      (hheads : ∀ h, (S.s.node n).heads h → ¬ S.hubD h) :
      SPStepR N S (S.adoptHub n)
  | supPush (S : SState) (n h : Nat) (hn : n < N)
      (hh : ∀ y, (S.s.node n).heads y ↔ y = h) (hne : h ≠ (S.s.node n).known.2)
      (hk : Anc S.s.U.par (S.s.node n).known.2 h) (hacc : S.s.hub.head = (S.s.node n).known.2)
      (hsub : ∀ x, S.hubD x → S.nodeD n x) (hpend : ∃ x, S.nodeD n x ∧ ¬ S.hubD x) :
      SPStepR N S (S.supWith n h (S.s.pPushAccept n h))
  | supFix (S : SState) (n g : Nat) (hn : n < N)
      (hh : ∀ y, (S.s.node n).heads y ↔ y = g)
      (hk : (S.s.node n).known = (S.s.hub.seq, S.s.hub.head))
      (hkg : Anc S.s.U.par S.s.hub.head g)
      (hsub : ∀ x, S.hubD x → S.nodeD n x) (hpend : ∃ x, S.nodeD n x ∧ ¬ S.hubD x) :
      SPStepR N S (S.supWith n S.s.U.next ((S.s.userOp n g []).pPushAccept n S.s.U.next))

inductive SPStepsR (N : Nat) : SState → SState → Prop
  | refl (S : SState) : SPStepsR N S S
  | tail {S T U : SState} : SPStepsR N S T → SPStepR N T U → SPStepsR N S U

/-- Converged: the protocol has converged, and every node has the hub's dropped set. -/
def SConverged (N : Nat) (S : SState) : Prop :=
  Converged N S.s ∧ ∀ n, n < N → ∀ x, S.nodeD n x ↔ S.hubD x

/-! ### Policy steps are runs of the system -/

theorem SRSteps.single {S T : SState} (h : SRStep N S T) : SRSteps N S T :=
  (SRSteps.refl S).tail h

theorem SRSteps.trans {S T U : SState} (h₁ : SRSteps N S T) (h₂ : SRSteps N T U) :
    SRSteps N S U := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact ih.tail hs

/-- A sync step that keeps the hub's head and sequence number, and every node's heads. -/
theorem frame_tail {S T : SState} (h : SRSteps N S T) {t : State} (hs : SyncStep N T.s t)
    (hh : t.hub.head = T.s.hub.head) (hq : t.hub.seq = T.s.hub.seq)
    (hn : ∀ n, (t.node n).heads = (T.s.node n).heads) : SRSteps N S { T with s := t } := by
  have := SStep.base T t (Or.inr hs) (Or.inl hh) (fun n x hx => Or.inl (by rw [← hn n]; exact hx))
  simp only [SState.withBase, hq, ↓reduceIte] at this
  exact h.tail (Or.inl this)

theorem setNode_heads {s : State} {n : Nat} {nd : Node} (h : nd.heads = (s.node n).heads)
    (i : Nat) : ((s.setNode n nd).node i).heads = (s.node i).heads := by
  by_cases hi : i = n
  · subst hi; simp [h]
  · rw [setNode_ne hi]

theorem pRealize_srun {S : SState} {n x : Nat} (hn : n < N)
    (hx : Anc S.s.U.par x (S.s.node n).known.2) (hc : HubHas S.s x)
    (hp : ∀ p ∈ S.s.U.par x, (S.s.node n).lops p) :
    SRSteps N S { S with s := S.s.pRealize n x } := by
  have r1 := frame_tail (SRSteps.refl S) (SyncStep.fetchOps S.s n (· = x) hn (fun y hy => hy ▸ hx))
    rfl rfl (fun _ => rfl)
  have r2 := frame_tail r1 (SyncStep.hubGetOps _ n (· = x) (Or.inr rfl)) rfl rfl (fun _ => rfl)
  have r3 := frame_tail r2 (SyncStep.recvOps _ n (fun y => y = x ∧ S.s.hub.ops y) hn (Or.inr rfl))
    rfl rfl (setNode_heads rfl)
  have r4 := frame_tail r3 (SyncStep.fetchObjs _ n (· ∈ S.s.U.objs x) hn) rfl rfl (fun _ => rfl)
  have r5 := frame_tail r4 (SyncStep.hubGetObjs _ n (· ∈ S.s.U.objs x) (Or.inr rfl)) rfl rfl
    (fun _ => rfl)
  have r6 := frame_tail r5 (SyncStep.recvObjs _ n
    (fun o => o ∈ S.s.U.objs x ∧ S.s.hub.objs o) hn (Or.inr rfl)) rfl rfl (setNode_heads rfl)
  refine frame_tail r6 (SyncStep.realize _ n x hn ?_ ?_ ?_) rfl rfl (setNode_heads rfl)
  · simp [State.recvObjs, State.recvOps, State.setNode, State.send, hc.1]
  · simpa [State.recvObjs, State.recvOps, State.setNode, State.send] using hp
  · intro o ho
    have ho' : o ∈ S.s.U.objs x := ho
    simp [State.recvObjs, State.recvOps, State.setNode, State.send, ho', hc.2 o ho']

theorem pUpload_srun {S : SState} {n hd : Nat} (hn : n < N) (hI : InvR N S.s)
    (hl : (S.s.node n).lops hd) : SRSteps N S { S with s := S.s.pUpload n hd } := by
  have lopsAnc : ∀ {a}, Anc S.s.U.par a hd → (S.s.node n).lops a := fun ha =>
    Anc.closed (S := (S.s.node n).lops) (fun y p hy hp => hI.lParents n y p hy hp) ha hl
  have r1 := frame_tail (SRSteps.refl S) (SyncStep.uploadOps S.s n (S.s.upOps n hd) hn
    (fun x hx => lopsAnc hx.1)) rfl rfl (fun _ => rfl)
  have r2 := frame_tail r1 (SyncStep.hubPutOps _ n (S.s.upOps n hd) (Or.inr rfl)) rfl rfl
    (fun _ => rfl)
  have r3 := frame_tail r2 (SyncStep.uploadObjs _ n (S.s.upObjs n hd) hn
    (fun o ho => by
      obtain ⟨⟨y, hy, hoy⟩, -⟩ := ho
      exact hI.lObjs n y o (lopsAnc hy) hoy)) rfl rfl (fun _ => rfl)
  have r4 := frame_tail r3 (SyncStep.hubPutObjs _ n (S.s.upObjs n hd) (Or.inr rfl)) rfl rfl
    (fun _ => rfl)
  exact frame_tail r4 (SyncStep.push _ n (S.s.node n).known.2 hd hn hl) rfl rfl (fun _ => rfl)

/-- Learning the head in a reply, at any sequence number. -/
theorem learn_srun {S T : SState} (h : SRSteps N S T) {n : Nat} {k : HeadKind} {sq hd : Nat}
    (hn : n < N) (hm : T.s.net (.head n k sq hd)) :
    SRSteps N S { T with s := T.s.learn n sq hd } :=
  frame_tail h (SyncStep.learnUnfiltered _ n k sq hd hn hm) rfl rfl (setNode_heads rfl)

/-- The hub's dropped set as of its current head is the one it has, as a set. -/
theorem hist_cur_eq {S : SState} (hI : SInv N S) : S.hubDHist S.s.hub.seq = S.hubD :=
  funext fun x => propext (hI.histCur x)

/-- An upload, a push the hub accepts, carrying records that drop what it pruned, and learning
the head. -/
theorem pushAccept_srun {S : SState} (hS : SRReachable N S) {n hd : Nat} (hn : n < N)
    (hh : ∀ y, (S.s.node n).heads y ↔ y = hd) (hne : hd ≠ (S.s.node n).known.2)
    (hk : Anc S.s.U.par (S.s.node n).known.2 hd) (hacc : S.s.hub.head = (S.s.node n).known.2)
    (hc : Carried S hd) (hdh : ¬ Remembered S hd) :
    SRSteps N S (S.withBase (S.s.pPushAccept n hd)) := by
  have hI := sinv_reachable hS
  have hIb := hI.base
  have r := pUpload_srun (S := S) hn hIb (hIb.headsLocal n hd ((hh hd).2 rfl))
  have hcas := SyncStep.casAccept (N := N) (S.s.pUpload n hd) n (S.s.node n).known.2 hd
    (Or.inr rfl) (fun e => hne ((show S.s.hub.head = hd from e).symm.trans hacc)) hacc hk
    (pUpload_closed_of hIb.hubClosed (by rw [hacc]; exact Anc.refl))
  have st := SStep.base { S with s := S.s.pUpload n hd } _ (Or.inr hcas)
    (Or.inr ⟨hdh, Or.inl hc⟩) (fun _ _ hx => Or.inl hx)
  simp only [SState.withBase, State.hubAccept, State.notifyAll, State.send, pUpload_seq,
    Nat.succ_ne_self, ↓reduceIte] at st
  have r' := r.tail (Or.inl st)
  have r'' := learn_srun r' (k := .accepted) (sq := S.s.hub.seq + 1) (hd := hd) hn
    (Or.inl (Or.inr rfl))
  have hq : (S.s.pPushAccept n hd).hub.seq ≠ S.s.hub.seq := by
    simp [State.pPushAccept, State.learn, State.notifyAll, State.send, State.hubAccept]
  have e : S.withBase (S.s.pPushAccept n hd) =
      { S with s := S.s.pPushAccept n hd,
               hubDHist := upd S.hubDHist (S.s.hub.seq + 1) S.hubD,
               hubPHist := upd S.hubPHist (S.s.hub.seq + 1) S.hubP } := by
    simp only [SState.withBase, hq, ↓reduceIte]; rfl
  rw [e]; exact r''

/-- Every policy step is a run of the system, from a state where every node has what the hub
pruned. -/
theorem spstepR_reachable {S S' : SState} (hS : SRReachable N S) (hA : AllPruned N S)
    (hp : SPStepR N S S') : SRReachable N S' := by
  have hI := sinv_reachable hS
  have hIb := hI.base
  -- a step that keeps the hub's sequence number leaves the dropped-set history as it was
  have keep : ∀ {t : State}, t.hub.seq = S.s.hub.seq →
      S.withBase t = { S with s := t } := by
    intro t ht; simp only [SState.withBase, ht, ↓reduceIte]
  cases hp with
  | learn n hn hs =>
    rw [keep (t := S.s.pLearn n) rfl]
    have r1 := frame_tail (SRSteps.refl S) (SyncStep.getHead S.s n hn) rfl rfl (fun _ => rfl)
    have r2 := frame_tail r1 (SyncStep.hubGetHead _ n (Or.inr rfl)) rfl rfl (fun _ => rfl)
    exact (learn_srun r2 (k := .head) hn (Or.inr rfl)).reachable hS
  | realize n x hn hc hx hnl hp =>
    rw [keep (t := S.s.pRealize n x) rfl]
    exact (pRealize_srun hn hx (hIb.hubClosed x (hx.trans (hIb.consistentAnc hc))) hp).reachable hS
  | advance n hn hk hna hd =>
    refine hS.step (Or.inl (SStep.base S _ (Or.inr (SyncStep.advance S.s n hn hk hna))
      (Or.inl rfl) ?_))
    intro m y hy
    by_cases hmn : m = n
    · subst hmn
      have hy' := hy
      simp only [State.advance, setNode_self] at hy'
      rcases hy'.1 with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ hd)
    · exact Or.inl (by rwa [State.advance, setNode_ne hmn] at hy)
  | merge n L O hn hL h2 =>
    refine hS.step (Or.inl (SStep.base S _ (Or.inl (EnvStep.merge S.s n L O hn hL h2))
      (Or.inl rfl) ?_))
    intro m y hy
    by_cases hmn : m = n
    · subst hmn
      have hy' : y = S.s.U.next := by simpa [State.mergeOp, State.createOp] using hy
      exact Or.inr (fun hD => Nat.lt_irrefl _ (hy' ▸ (hI.node m y hD).2.1))
    · exact Or.inl (by simpa [State.mergeOp, State.createOp, hmn] using hy)
  | pushAccept n hd hn hh hne hk hacc hD =>
    have hdn : ¬ S.nodeD n hd := hI.headsOK n hd ((hh hd).2 rfl)
    have S1 := hS.step (Or.inl (SStep.sendSup S n hd (S.nodeD n) hn (fun _ h => h) hdn))
    exact (pushAccept_srun S1 hn hh hne hk hacc
      ⟨n, S.nodeD n, S.nodeD n, Or.inr ⟨rfl, rfl, rfl, rfl⟩, hA n hn⟩
      (fun h => hdn ((hD hd).2 h.1))).reachable S1
  | pushIdem n hd hn hh hne hk hidem =>
    rw [keep (t := S.s.pPushIdem n hd) rfl]
    have r := pUpload_srun (S := S) hn hIb (hIb.headsLocal n hd ((hh hd).2 rfl))
    have r' := frame_tail r (SyncStep.casIdem _ n (S.s.node n).known.2 hd (Or.inr rfl) hidem)
      rfl rfl (fun _ => rfl)
    exact (learn_srun r' (k := .accepted) hn (Or.inr rfl)).reachable hS
  | pushReject n hd hn hh hne hk hrej hrej' =>
    rw [keep (t := S.s.pPushReject n hd) rfl]
    have r := pUpload_srun (S := S) hn hIb (hIb.headsLocal n hd ((hh hd).2 rfl))
    have r' := frame_tail r (SyncStep.casReject _ n (S.s.node n).known.2 hd (Or.inr rfl)
      hrej' (fun ⟨e, _, _⟩ => hrej e)) rfl rfl (fun _ => rfl)
    exact (learn_srun r' (k := .rejected) hn (Or.inr rfl)).reachable hS
  | adopt n hn hlag hheads =>
    have r1 := hS.step (Or.inl (SStep.sendD S n (Remembered S) (fun _ h => h) (fun _ h => h.1)))
    exact r1.step (Or.inl (SStep.adopt _ n (Remembered S) hn (Or.inr ⟨rfl, rfl⟩)
      (fun g hg hr => hheads g hg hr.1)))
  | supPush n hd hn hh hne hk hacc hsub hpend =>
    have hdn : ¬ S.nodeD n hd := hI.headsOK n hd ((hh hd).2 rfl)
    have S1 := hS.step (Or.inl (SStep.sendSup S n hd (S.nodeD n) hn (fun _ h => h) hdn))
    have r := pUpload_srun (S := S.sendSupS n hd (S.nodeD n)) hn hIb
      (hIb.headsLocal n hd ((hh hd).2 rfl))
    have hcas := SyncStep.casAccept (N := N) (S.s.pUpload n hd) n (S.s.node n).known.2 hd
      (Or.inr rfl) (fun e => hne ((show S.s.hub.head = hd from e).symm.trans hacc)) hacc hk
      (pUpload_closed_of hIb.hubClosed (by rw [hacc]; exact Anc.refl))
    have st := SStep.sup { S.sendSupS n hd (S.nodeD n) with s := S.s.pUpload n hd } _ n
      (S.nodeD n) (S.nodeD n) (Or.inr hcas) rfl (Or.inr ⟨rfl, rfl, rfl, rfl⟩) (hA n hn)
      (fun h => hdn (hsub hd h.1)) (fun h => h.2 h.1) (fun _ _ hx => Or.inl hx)
    have r' := r.tail (Or.inl st)
    have r'' := learn_srun r' (k := .accepted) (sq := S.s.hub.seq + 1) (hd := hd) hn
      (Or.inl (Or.inr rfl))
    exact r''.reachable S1
  | supFix n g hn hh hk hkg hsub hpend =>
    have hg : (S.s.node n).heads g := (hh g).2 rfl
    have hhl : (S.s.node n).lops g := hIb.headsLocal n _ hg
    -- the fix-up operation, on the node's head
    have hu := EnvStep.userOp (N := N) S.s n g [] hn hhl
    have huheads : ∀ y, ((S.s.userOp n g []).node n).heads y ↔ y = S.s.U.next := by
      intro y
      simp only [State.userOp, createOp_heads]
      constructor
      · rintro ⟨⟨hy1, hne⟩ | h, -⟩
        · exact absurd ((hh y).1 hy1) hne
        · exact h
      · rintro rfl
        refine ⟨Or.inr rfl, fun z hz hA => ?_⟩
        rcases hz with ⟨hz1, hzne⟩ | hz
        · exact absurd ((hh z).1 hz1) hzne
        · exact hz.symm
    have hfD : ∀ D : OSet, DOK N S D → ¬ D S.s.U.next := fun D hD h =>
      Nat.lt_irrefl _ (hD _ h).2.1
    have st0 := SStep.base S _ (Or.inl hu) (Or.inl rfl) (by
        intro m y hy
        by_cases hmn : m = n
        · subst hmn
          right
          have hy' : y = S.s.U.next := (huheads y).1 hy
          exact fun hD => Nat.lt_irrefl _ (hy' ▸ (hI.node m y hD).2.1)
        · left; simpa [State.userOp, State.createOp, hmn] using hy)
    simp only [SState.withBase, show (S.s.userOp n g []).hub.seq = S.s.hub.seq from rfl,
      ↓reduceIte] at st0
    -- then the supersede, with the push to it
    have S1 := hS.step (Or.inl st0)
    have S2 := S1.step (Or.inl (SStep.sendSup { S with s := S.s.userOp n g [] } n S.s.U.next
      (S.nodeD n) hn (fun _ h => h) (hfD _ (hI.node n))))
    have hIu : InvR N (S.s.userOp n g []) := invR_rstep hIb (Or.inl (Or.inl hu))
    have huknown : ((S.s.userOp n g []).node n).known =
        (S.s.hub.seq, S.s.hub.head) := by
      simp only [State.userOp, createOp_known]; exact hk
    have hul : ((S.s.userOp n g []).node n).lops S.s.U.next := by
      simp [State.userOp, State.createOp]
    have r := pUpload_srun
      (S := ({ S with s := S.s.userOp n g [] }).sendSupS n S.s.U.next (S.nodeD n)) hn hIu hul
    have hfk : Anc (S.s.userOp n g []).U.par
        ((S.s.userOp n g []).node n).known.2 S.s.U.next := by
      rw [huknown]
      have hLlt : ∀ q ∈ [g], q < S.s.U.next := by
        intro q hq; simp at hq; rw [hq]; exact hIb.headsLt hg
      exact ((anc_upd_iff hIb.parLt hLlt (hIb.headsLt hg)).2 hkg).trans
        (Anc.parent (by simp))
    have hfne : S.s.U.next ≠ ((S.s.userOp n g []).node n).known.2 := by
      rw [huknown]; exact Nat.ne_of_gt (hIb.headLt)
    have huhead : (S.s.userOp n g []).hub.head =
        ((S.s.userOp n g []).node n).known.2 := by rw [huknown]; rfl
    have hcas := SyncStep.casAccept (N := N) ((S.s.userOp n g []).pUpload n S.s.U.next)
      n ((S.s.userOp n g []).node n).known.2 S.s.U.next (Or.inr rfl)
      (fun e => hfne ((show (S.s.userOp n g []).hub.head = S.s.U.next from e).symm.trans
        huhead)) huhead hfk
      (pUpload_closed_of hIu.hubClosed (by rw [huhead]; exact Anc.refl))
    let S2' := ({ S with s := S.s.userOp n g [] }).sendSupS n S.s.U.next (S.nodeD n)
    have hm : S2'.sups n (S.nodeD n) (S.nodeD n) S.s.U.next := Or.inr ⟨rfl, rfl, rfl, rfl⟩
    have hr : ¬ Remembered S2' S.s.U.next := fun h => hfD _ hI.hub h.1
    have st := SStep.sup { S2' with s := (S.s.userOp n g []).pUpload n S.s.U.next } _ n
      (S.nodeD n) (S.nodeD n) (Or.inr hcas) rfl hm (hA n hn) hr (fun h => h.2 h.1)
      (fun _ _ hx => Or.inl hx)
    have r' := r.tail (Or.inl st)
    have r'' := learn_srun r' (k := .accepted) (sq := S.s.hub.seq + 1) (hd := S.s.U.next) hn
      (Or.inl (Or.inr rfl))
    exact r''.reachable S2

/-- Policy steps prune nothing, and a node's dropped set only grows: they keep every node with
what the hub pruned. -/
theorem allPruned_spstep {S S' : SState} (hA : AllPruned N S) (hp : SPStepR N S S') :
    AllPruned N S' := by
  cases hp with
  | adopt n hn hlag hheads =>
    intro m hm x hx
    show upd S.nodeD n (fun x => S.nodeD n x ∨ Remembered S x) m x
    by_cases hmn : m = n
    · subst hmn; rw [upd_same]; exact Or.inl (hA m hm x hx)
    · rw [upd_ne _ _ hmn]; exact hA m hm x hx
  | _ => exact hA

theorem spstepsR_reachable {S S' : SState} (hS : SRReachable N S) (hA : AllPruned N S)
    (hp : SPStepsR N S S') : SRReachable N S' ∧ AllPruned N S' := by
  induction hp with
  | refl => exact ⟨hS, hA⟩
  | tail _ hst ih => exact ⟨spstepR_reachable ih.1 ih.2 hst, allPruned_spstep ih.2 hst⟩


/-! ### The measure -/

open Classical in
/-- Operations some node has dropped that the hub hasn't. -/
noncomputable def mPend (N : Nat) (S : SState) : Nat :=
  cnt S.s.U.next (fun x => (∃ n, n < N ∧ S.nodeD n x) ∧ ¬ S.hubD x)

open Classical in
/-- Operations the hub has dropped that a node hasn't, summed over nodes. -/
noncomputable def mLag (N : Nat) (S : SState) : Nat :=
  sumN N (fun n => cnt S.s.U.next (fun x => S.hubD x ∧ ¬ S.nodeD n x))

/-- Dropped operations not yet published come first, then those not yet taken, then
`rmeasure`. -/
noncomputable def smeasure (N : Nat) (S : SState) :
    Nat × Nat × (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (mPend N S, mLag N S, rmeasure N S.s)

def Lex8 : Nat × Nat × (Nat × Nat × Nat × Nat × Nat × Nat) →
    Nat × Nat × (Nat × Nat × Nat × Nat × Nat × Nat) → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) Lex6)

theorem lex8_wf : WellFounded Lex8 :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel ⟨Lex6, lex6_wf⟩)).wf

/-- Counting up to a larger bound counts nothing more where nothing beyond the smaller one
counts. -/
theorem cnt_grow {B B' : Nat} {P : Nat → Prop} (hB : B ≤ B') (hP : ∀ x, B ≤ x → ¬ P x) :
    cnt B' P = cnt B P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show B + (k + 1) = (B + k) + 1 by omega]
    simp only [cnt]
    rw [ih (Nat.le_add_right _ _)]
    simp [hP _ (Nat.le_add_right _ _)]

/-- What the dropped sets count is below the operations created so far. -/
theorem pend_lag_grow {S S' : SState} (hI : SInv N S) (hn : S.s.U.next ≤ S'.s.U.next)
    (hD : S'.nodeD = S.nodeD) (hH : S'.hubD = S.hubD) :
    mPend N S' = mPend N S ∧ mLag N S' = mLag N S := by
  constructor
  · unfold mPend; rw [hD, hH]
    refine cnt_grow hn (fun x hx h => ?_)
    obtain ⟨⟨m, -, hm⟩, -⟩ := h
    exact Nat.not_lt.2 hx (hI.node m x hm).2.1
  · unfold mLag; rw [hD, hH]
    exact sumN_congr (fun m _ => cnt_grow hn (fun x hx h => Nat.not_lt.2 hx (hI.hub x h.1).2.1))

theorem lex8_base {S S' : SState} (hI : SInv N S) (hn : S.s.U.next ≤ S'.s.U.next)
    (hD : S'.nodeD = S.nodeD) (hH : S'.hubD = S.hubD)
    (hr : Lex6 (rmeasure N S'.s) (rmeasure N S.s)) : Lex8 (smeasure N S') (smeasure N S) := by
  obtain ⟨e1, e2⟩ := pend_lag_grow hI hn hD hH
  unfold smeasure; rw [e1, e2]
  exact Prod.Lex.right _ (Prod.Lex.right _ hr)

theorem withBase_nodeD (S : SState) (t : State) : (S.withBase t).nodeD = S.nodeD := rfl
theorem withBase_hubD (S : SState) (t : State) : (S.withBase t).hubD = S.hubD := rfl

/-- Publishing a dropped set the hub lacks part of lowers the count of unpublished drops. -/
theorem pend_sup {S : SState} (hI : SInv N S) {n h : Nat} (hn : n < N) {t : State}
    (hnext : S.s.U.next ≤ t.U.next) (hpend : ∃ x, S.nodeD n x ∧ ¬ S.hubD x) :
    mPend N (S.supWith n h t) < mPend N S := by
  obtain ⟨x, hxn, hxh⟩ := hpend
  unfold mPend
  have e : cnt t.U.next (fun x => (∃ m, m < N ∧ S.nodeD m x) ∧ ¬ S.hubD x) =
      cnt S.s.U.next (fun x => (∃ m, m < N ∧ S.nodeD m x) ∧ ¬ S.hubD x) :=
    cnt_grow hnext (fun y hy h => by
      obtain ⟨⟨m, -, hm⟩, -⟩ := h
      exact Nat.not_lt.2 hy (hI.node m y hm).2.1)
  show cnt t.U.next (fun y => (∃ m, m < N ∧ S.nodeD m y) ∧ ¬ (S.hubD y ∨ S.nodeD n y)) < _
  rw [← e]
  refine cnt_lt (fun y _ ⟨h1, h2⟩ => ⟨h1, fun h => h2 (Or.inl h)⟩)
    ⟨x, Nat.lt_of_lt_of_le (hI.node n x hxn).2.1 hnext, ⟨⟨n, hn, hxn⟩, hxh⟩, ?_⟩
  rintro ⟨-, h⟩; exact h (Or.inr hxn)

theorem smeasure_decreases {S S' : SState} (hS : SRReachable N S) (hA : AllPruned N S)
    (hp : SPStepR N S S') : Lex8 (smeasure N S') (smeasure N S) := by
  have hI := sinv_reachable hS
  have hb := hS.base
  cases hp with
  | learn n hn hs =>
    exact lex8_base hI (Nat.le_refl _) rfl rfl
      (measureR_decreases hb (PStepR.learn S.s n hn hs))
  | realize n x hn hc hx hnl hp =>
    exact lex8_base hI (Nat.le_refl _) rfl rfl
      (measureR_decreases hb (PStepR.realize S.s n x hn hc hx hnl hp))
  | advance n hn hk hna hd =>
    exact lex8_base hI (Nat.le_refl _) rfl rfl
      (measureR_decreases hb (PStepR.advance S.s n hn hk hna))
  | merge n L O hn hL h2 =>
    exact lex8_base hI (Nat.le_succ _) rfl rfl
      (measureR_decreases hb (PStepR.merge S.s n L O hn hL h2))
  | pushAccept n h hn hh hne hk hacc hD =>
    exact lex8_base hI (Nat.le_refl _) rfl rfl
      (measureR_decreases hb (PStepR.pushAccept S.s n h hn hh hne hk hacc))
  | pushIdem n h hn hh hne hk hidem =>
    exact lex8_base hI (Nat.le_refl _) rfl rfl
      (measureR_decreases hb (PStepR.pushIdem S.s n h hn hh hne hk hidem))
  | pushReject n h hn hh hne hk hrej hrej' =>
    exact lex8_base hI (Nat.le_refl _) rfl rfl
      (measureR_decreases hb (PStepR.pushReject S.s n h hn hh hne hk hrej hrej'))
  | adopt n hn hlag hheads =>
    have e1 : mPend N (S.adoptHub n) = mPend N S := by
      unfold mPend
      refine cnt_congr (fun x _ => ?_)
      show ((∃ m, m < N ∧ upd S.nodeD n (fun x => S.nodeD n x ∨ Remembered S x) m x) ∧
        ¬ S.hubD x) ↔ _
      constructor
      · rintro ⟨⟨m, hm, hx⟩, hh⟩
        refine ⟨⟨m, hm, ?_⟩, hh⟩
        by_cases hmn : m = n
        · subst hmn; rw [upd_same] at hx
          exact hx.elim id (fun h => absurd h.1 hh)
        · rwa [upd_ne _ _ hmn] at hx
      · rintro ⟨⟨m, hm, hx⟩, hh⟩
        refine ⟨⟨m, hm, ?_⟩, hh⟩
        by_cases hmn : m = n
        · subst hmn; rw [upd_same]; exact Or.inl hx
        · rw [upd_ne _ _ hmn]; exact hx
    have e2 : mLag N (S.adoptHub n) < mLag N S := by
      unfold mLag
      obtain ⟨x, hxh, hxn⟩ := hlag
      -- what it lacks, the hub hasn't pruned: it remembers, and announces, all of it
      have hxr : Remembered S x := ⟨hxh, fun hf => hxn (hA n hn x hf)⟩
      refine sumN_lt hn ?_ (fun m _ hmn => ?_)
      · show cnt S.s.U.next (fun y => S.hubD y ∧
            ¬ upd S.nodeD n (fun x => S.nodeD n x ∨ Remembered S x) n y) < _
        refine cnt_lt (fun y _ ⟨h1, h2⟩ => ⟨h1, fun h => h2 (by rw [upd_same]; exact Or.inl h)⟩)
          ⟨x, (hI.hub x hxh).2.1, ⟨hxh, hxn⟩, ?_⟩
        rintro ⟨-, h⟩; exact h (by rw [upd_same]; exact Or.inr hxr)
      · show cnt S.s.U.next (fun y => S.hubD y ∧
            ¬ upd S.nodeD n (fun x => S.nodeD n x ∨ Remembered S x) m y) = _
        simp only [upd_ne _ _ hmn]
    unfold smeasure
    rw [e1]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ e2)
  | supPush n h hn hh hne hk hacc hsub hpend =>
    exact Prod.Lex.left _ _ (pend_sup hI hn (Nat.le_refl _) hpend)
  | supFix n g hn hh hk hkg hsub hpend =>
    exact Prod.Lex.left _ _ (pend_sup hI hn (Nat.le_succ _) hpend)

/-! ### Termination -/

theorem no_infinite_run_auxS {r : SState → SState → Prop} {a : SState} (ha : Acc r a) :
    ∀ f : Nat → SState, f 0 = a → ¬ ∀ i, r (f (i + 1)) (f i) := by
  induction ha with
  | intro a _ ih =>
    intro f hf hall
    exact ih (f 1) (hf ▸ hall 0) (fun i => f (i + 1)) rfl (fun i => hall (i + 1))

theorem spstepR_wf :
    WellFounded (fun S' S => (SRReachable N S ∧ AllPruned N S) ∧ SPStepR N S S') :=
  Subrelation.wf (fun ⟨⟨h, hA⟩, hp⟩ => smeasure_decreases h hA hp)
    (InvImage.wf (smeasure N) lex8_wf)

/-- **Termination** with supersedes, once the hub stops going back, from a state where every
node has what the hub pruned: no infinite sequence of policy steps, whatever the scheduling. -/
theorem no_infinite_policy_runS {S : SState} (h : SRReachable N S) (hA : AllPruned N S) :
    ¬ ∃ f : Nat → SState, f 0 = S ∧ ∀ i, SPStepR N (f i) (f (i + 1)) := by
  rintro ⟨f, hf0, hf⟩
  have hreach : ∀ i, SRReachable N (f i) ∧ AllPruned N (f i) := by
    intro i
    induction i with
    | zero => exact hf0 ▸ ⟨h, hA⟩
    | succ i ih => exact ⟨spstepR_reachable ih.1 ih.2 (hf i), allPruned_spstep ih.2 (hf i)⟩
  exact no_infinite_run_auxS (spstepR_wf.apply S) f hf0 (fun i => ⟨hreach i, hf i⟩)

/-! ### Progress -/

/-- Node `n` has nothing left to do: it is at the hub's head, knows it, and has the hub's
dropped set. -/
def NodeDone (S : SState) (n : Nat) : Prop :=
  (∀ y, (S.s.node n).heads y ↔ y = S.s.hub.head) ∧
    (S.s.node n).known = (S.s.hub.seq, S.s.hub.head) ∧ ∀ x, S.nodeD n x ↔ S.hubD x

/-- What node `n` can do: take a policy step; or nothing, being done; or it waits, on a hub
head it has dropped and isn't past, or with its only head one the hub has dropped. -/
theorem node_step_or {S : SState} (h : SRReachable N S) {n : Nat} (hn : n < N) :
    (∃ S', SPStepR N S S') ∨ NodeDone S n ∨
      (S.nodeD n S.s.hub.head ∧ ¬ ∃ g, (S.s.node n).heads g ∧ Anc S.s.U.par S.s.hub.head g) ∨
      (∃ g, (∀ y, (S.s.node n).heads y ↔ y = g) ∧ Anc S.s.U.par S.s.hub.head g ∧
        g ≠ S.s.hub.head ∧ S.hubD g) := by
  have hI := sinv_reachable h
  have hIb := hI.base
  -- 1. merge
  by_cases hmulti : ∃ a b, (S.s.node n).heads a ∧ (S.s.node n).heads b ∧ a ≠ b
  · obtain ⟨a, b, ha, hb, hab⟩ := hmulti
    have hmem := fun x => mem_headsList_of (s := S.s) (n := n) (x := x) (fun _ h => hIb.headsLt h)
    exact Or.inl ⟨_, SPStepR.merge S n (headsList S.s n) [] hn hmem
      ⟨a, b, (hmem a).2 ha, (hmem b).2 hb, hab⟩⟩
  -- 2. learn
  by_cases hk : (S.s.node n).known ≠ (S.s.hub.seq, S.s.hub.head)
  · exact Or.inl ⟨_, SPStepR.learn S n hn hk⟩
  have hk := Classical.not_not.1 hk
  have hk2 : (S.s.node n).known.2 = S.s.hub.head := by rw [hk]
  have hcons : Consistent S.s n := by
    unfold Consistent; rw [hk]; exact ⟨Nat.le_refl _, hIb.histHead⟩
  -- 3. fetch and realize
  by_cases hnloc : ¬ (S.s.node n).lops (S.s.node n).known.2
  · obtain ⟨x, ⟨hxa, hxl⟩, hmin⟩ := exists_min
      (fun x => Anc S.s.U.par x (S.s.node n).known.2 ∧ ¬ (S.s.node n).lops x)
      (a := (S.s.node n).known.2) ⟨Anc.refl, hnloc⟩
    refine Or.inl ⟨_, SPStepR.realize S n x hn hcons hxa hxl (fun p hp => ?_)⟩
    refine Classical.byContradiction fun hpl => ?_
    exact hmin p (hIb.parLt x p hp) ⟨(Anc.parent hp).trans hxa, hpl⟩
  have hloc := Classical.not_not.1 hnloc
  -- 4. advance, unless the head is one this node dropped
  by_cases hnadv : ¬ ∃ g, (S.s.node n).heads g ∧ Anc S.s.U.par (S.s.node n).known.2 g
  · by_cases hd : S.nodeD n (S.s.node n).known.2
    · rw [hk2] at hd hnadv
      exact Or.inr (Or.inr (Or.inl ⟨hd, hnadv⟩))
    · exact Or.inl ⟨_, SPStepR.advance S n hn hloc hnadv hd⟩
  have hadv := Classical.not_not.1 hnadv
  obtain ⟨g, hg, hkg⟩ := hadv
  have hsingle : ∀ y, (S.s.node n).heads y ↔ y = g := by
    intro y
    constructor
    · intro hy
      refine Classical.byContradiction fun hne => ?_
      exact hmulti ⟨y, g, hy, hg, hne⟩
    · rintro rfl; exact hg
  rw [hk2] at hkg
  by_cases hgk : g = S.s.hub.head
  · -- 5. at the hub's head: take its dropped set, or publish this node's
    subst hgk
    have hh' : ∀ y, (S.s.node n).heads y ↔ y = S.s.hub.head := hsingle
    by_cases hlag : ∃ x, S.hubD x ∧ ¬ S.nodeD n x
    · refine Or.inl ⟨_, SPStepR.adopt S n hn hlag (fun y hy => ?_)⟩
      rw [(hsingle y).1 hy]; exact hI.headOK
    have hsub : ∀ x, S.hubD x → S.nodeD n x := fun x hx =>
      Classical.byContradiction fun h => hlag ⟨x, hx, h⟩
    by_cases hpend : ∃ x, S.nodeD n x ∧ ¬ S.hubD x
    · exact Or.inl ⟨_, SPStepR.supFix S n _ hn hh' hk Anc.refl hsub hpend⟩
    · refine Or.inr (Or.inl ⟨hh', hk, fun x => ⟨fun hx => ?_, hsub x⟩⟩)
      exact Classical.byContradiction fun h => hpend ⟨x, hx, h⟩
  · -- 6. push
    by_cases hgD : S.hubD g
    · exact Or.inr (Or.inr (Or.inr ⟨g, hsingle, hkg, hgk, hgD⟩))
    have hne : g ≠ (S.s.node n).known.2 := by rw [hk2]; exact hgk
    have hkg' : Anc S.s.U.par (S.s.node n).known.2 g := by rw [hk2]; exact hkg
    by_cases hD : ∀ x, S.nodeD n x ↔ S.hubD x
    · exact Or.inl ⟨_, SPStepR.pushAccept S n g hn hsingle hne hkg' hk2.symm hD⟩
    by_cases hlag : ∃ x, S.hubD x ∧ ¬ S.nodeD n x
    · refine Or.inl ⟨_, SPStepR.adopt S n hn hlag (fun y hy => ?_)⟩
      rw [(hsingle y).1 hy]; exact hgD
    have hsub : ∀ x, S.hubD x → S.nodeD n x := fun x hx =>
      Classical.byContradiction fun h => hlag ⟨x, hx, h⟩
    have hpend : ∃ x, S.nodeD n x ∧ ¬ S.hubD x := by
      refine Classical.byContradiction fun hp => hD fun x => ⟨fun hx => ?_, hsub x⟩
      exact Classical.byContradiction fun h => hp ⟨x, hx, h⟩
    exact Or.inl ⟨_, SPStepR.supPush S n g hn hsingle hne hkg' hk2.symm hsub hpend⟩

/-- **Progress** with supersedes: in every state that is not converged, some policy step is
enabled. A node can wait on another, holding a head the hub dropped, or the hub's head dropped
and not past it; then the node with the newest head above the hub's head can always act: no
head it has is dropped, since each dropped operation is below a newer head of the node that
dropped it. -/
theorem progressS {S : SState} (h : SRReachable N S) (hc : ¬ SConverged N S) :
    ∃ S', SPStepR N S S' := by
  have hI := sinv_reachable h
  have hIb := hI.base
  -- some node isn't done
  have hnd : ∃ n, n < N ∧ ¬ NodeDone S n := by
    refine Classical.byContradiction fun hall => hc ⟨fun n hn => ?_, fun n hn => ?_⟩
    · have hd : NodeDone S n :=
        Classical.byContradiction fun h => hall ⟨n, hn, h⟩
      exact ⟨hd.1, hd.2.1⟩
    · have hd : NodeDone S n :=
        Classical.byContradiction fun h => hall ⟨n, hn, h⟩
      exact hd.2.2
  obtain ⟨n0, hn0, hnd0⟩ := hnd
  let x0 := S.s.hub.head
  let Q : Nat → Prop := fun g => ∃ m, m < N ∧ (S.s.node m).heads g ∧ Anc S.s.U.par x0 g
  -- some head is at or above the hub's head
  have hQ : ∃ g, Q g := by
    by_cases hx0 : x0 = root
    · obtain ⟨g, hg⟩ := hIb.headsNonempty n0
      refine ⟨g, n0, hn0, hg, ?_⟩
      rw [hx0]; exact hIb.rootAnc g (hIb.headsLt hg)
    · obtain ⟨c, hc, hcr⟩ := hIb.creatorSome x0 (Nat.pos_of_ne_zero hx0) hIb.headLt
      obtain ⟨g, hg, hA⟩ := hIb.ownInHeads c x0 hIb.headLt hcr
      exact ⟨g, c, hc, hg, hA⟩
  obtain ⟨a, ha⟩ := hQ
  obtain ⟨gs, ⟨M, hM, hgs, hxg⟩, hmax⟩ := Musubi.Presence.exists_max_le (Q := Q)
    (x := S.s.U.next) ha (fun g ⟨m, _, hg, _⟩ => Nat.le_of_lt (hIb.headsLt hg))
  -- an operation some node dropped above the hub's head is below a newer head
  have kept : ∀ y, Kept N S y → Anc S.s.U.par x0 y → ∃ g, Q g ∧ y < g := by
    rintro y ⟨m, hm, hDm, g, hg, hA⟩ hxy
    have hyg : y ≠ g := fun e => hI.headsOK m g hg (e ▸ hDm)
    exact ⟨g, ⟨m, hm, hg, hxy.trans hA⟩, Anc.lt_of_ne hIb.parLt hA hyg⟩
  rcases node_step_or h hM with hst | hdone | ⟨-, hno⟩ | ⟨g, hsg, -, -, hgD⟩
  · exact hst
  · -- the newest head is the hub's head: nothing waits
    have hgs0 : gs = x0 := (hdone.1 gs).1 hgs
    rcases node_step_or h hn0 with hst | hdone0 | ⟨hd, -⟩ | ⟨g, hsg, hxg', hne, -⟩
    · exact hst
    · exact absurd hdone0 hnd0
    · obtain ⟨g, hQg, hlt⟩ := kept x0 ((hI.node n0) x0 hd).2.2 Anc.refl
      have := hmax g hQg; omega
    · have hQg : Q g := ⟨n0, hn0, (hsg g).2 rfl, hxg'⟩
      have hlt : x0 < g := Anc.lt_of_ne hIb.parLt hxg' (Ne.symm hne)
      have := hmax g hQg; omega
  · exact absurd ⟨gs, hgs, hxg⟩ hno
  · have hgg : g = gs := ((hsg gs).1 hgs).symm
    subst hgg
    obtain ⟨g', hQg', hlt⟩ := kept g (hI.hub g hgD).2.2 hxg
    have := hmax g' hQg'; omega

/-! ### Convergence -/

/-- Converged states enable no policy step. -/
theorem converged_quiescentS {S : SState} (h : SRReachable N S) (hc : SConverged N S)
    {S' : SState} : ¬ SPStepR N S S' := by
  have hIb := (sinv_reachable h).base
  obtain ⟨hcb, hcD⟩ := hc
  intro hp
  cases hp with
  | learn n hn hs => exact hs (hcb n hn).2
  | realize n x hn _ hx hnl hp =>
    exact hnl (hcb.lops_below hn (hIb.lParents n) (hIb.headsLocal n) hx)
  | advance n hn hk hna => exact hna (hcb.known_in_heads hn)
  | merge n L O hn hL h2 =>
    obtain ⟨a, b, ha, hb, hab⟩ := h2
    exact hab (hcb.heads_eq hn ((hL a).1 ha) ((hL b).1 hb))
  | pushAccept n hd hn hh hne => exact hne (hcb.head_known hn hh)
  | pushIdem n hd hn hh hne => exact hne (hcb.head_known hn hh)
  | pushReject n hd hn hh hne => exact hne (hcb.head_known hn hh)
  | adopt n hn hlag =>
    obtain ⟨x, hx, hnx⟩ := hlag
    exact hnx ((hcD n hn x).2 hx)
  | supPush n hd hn hh hne => exact hne (hcb.head_known hn hh)
  | supFix n g hn hh hk hkg hsub hpend =>
    obtain ⟨x, hx, hnx⟩ := hpend
    exact hnx ((hcD n hn x).1 hx)

/-- A state with no enabled policy step is converged, and conversely. -/
theorem terminal_iff_convergedS {S : SState} (h : SRReachable N S) :
    (∀ S', ¬ SPStepR N S S') ↔ SConverged N S := by
  constructor
  · intro ht
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨S', hS'⟩ := progressS h hc
    exact ht S' hS'
  · intro hc S'
    exact converged_quiescentS h hc

theorem SPStepsR.head {S T U : SState} (h1 : SPStepR N S T) (h2 : SPStepsR N T U) :
    SPStepsR N S U := by
  induction h2 with
  | refl => exact SPStepsR.tail (SPStepsR.refl _) h1
  | tail _ hst ih => exact SPStepsR.tail ih hst

/-- **Liveness** with supersedes, once the hub stops going back: from every state where every
node has dropped what the hub pruned, policy steps reach a converged state. -/
theorem eventually_convergesS {S : SState} (h : SRReachable N S) (hA : AllPruned N S) :
    ∃ S', SPStepsR N S S' ∧ SConverged N S' := by
  refine WellFounded.induction (C := fun S => SRReachable N S ∧ AllPruned N S →
    ∃ S', SPStepsR N S S' ∧ SConverged N S') (spstepR_wf (N := N)) S
    (fun S ih h => ?_) ⟨h, hA⟩
  by_cases hc : SConverged N S
  · exact ⟨S, SPStepsR.refl S, hc⟩
  · obtain ⟨S', hS'⟩ := progressS h.1 hc
    obtain ⟨U, hU, hUc⟩ := ih S' ⟨h, hS'⟩
      ⟨spstepR_reachable h.1 h.2 hS', allPruned_spstep h.2 hS'⟩
    exact ⟨U, SPStepsR.head hS' hU, hUc⟩

/-- Every policy run that cannot be extended ends converged. -/
theorem maximal_run_convergesS {S S' : SState} (h : SRReachable N S) (hA : AllPruned N S)
    (hr : SPStepsR N S S') (hmax : ∀ S'', ¬ SPStepR N S' S'') : SConverged N S' :=
  (terminal_iff_convergedS (spstepsR_reachable h hA hr).1).1 hmax

/-- **Once converged, every abandon has reached every machine**: the hub has dropped every
operation any node dropped, every node has dropped exactly what the hub has, and every
operation any node created is below the hub's head. -/
theorem converged_all_droppedS {S : SState} (hc : SConverged N S)
    {n x : Nat} (hn : n < N) (hx : S.nodeD n x) :
    S.hubD x ∧ ∀ m, m < N → S.nodeD m x :=
  ⟨(hc.2 n hn x).1 hx, fun m hm => (hc.2 m hm x).2 ((hc.2 n hn x).1 hx)⟩

theorem converged_all_acceptedS {S : SState} (h : SRReachable N S) (hc : SConverged N S)
    {x : Nat} (hx : x < S.s.U.next) : Anc S.s.U.par x S.s.hub.head :=
  converged_all_acceptedR h.base hc.1 hx

end Musubi
