/-
Which repository is the copy of a key on one machine, and which is a duplicate made of its
files (docs/internals/copies.md).

A repository holds a key, a record (its hive, the config-id it had when it joined, and
whether it is joined, left, or its hive removed) and a jj config-id. The daemon keeps one
entry per key: its hive, config-id and path. jj keeps, for each config-id, the path it last
saw it at (`seen`), and when it finds a repository whose config-id it last saw elsewhere,
decides as `handle_metadata_path` in jj-lib's `secure_config.rs` does: if nothing is at the
old path, the repository moved and keeps its config-id; otherwise it is a duplicate and gets
a new one. Bind mounts and other aliases are not modeled.

`standing`, `refine` and `check` mirror `copy::standing`, `copy::refine` and `copy::check` in
`crates/musubi/src/copy.rs` exactly, and the oracle checks them against the Rust
(docs/internals/conformance.md, "Copies"). What a repository is to musubi, its `verdict`, is
its `standing`, `refine`d against what is at its entry's path, as `copy::standing_of` does.
Ids are numbers.

The system: the user moves, copies, deletes and replaces repositories (`put`, of a repository
whose key and config-id are new here, or that has none); jj runs in one (`jjRun`); musubi joins
one (`join`, which goes by the verdict), and the daemon syncs an entry's copy (`sync`) or follows it to where jj last saw
its config-id (`relocate`). Proved:

- every push is of a repository joined to the hive pushed to, under its own key
  (`right_hive`);
- while an entry's path holds its copy, no other repository with its key is the copy to
  musubi, whatever jj decides when it runs there (`duplicates_refused`);
- a duplicate of a copy that left, or whose hive was removed, can't join
  (`join_refuses_duplicate`);
- no step but `join` makes a key, except that the user may put a repository that has one
  (`only_join_makes_keys`);
- once jj has seen the copy at its entry's path, the daemon follows a move of it once jj has
  run in it (`moves_followed`);
- the daemon writes nothing to disk (`daemon_writes_nothing`).

When jj ran in the copy at another path, and the copy came back before jj ran in it again, jj
can take a duplicate for the copy moved: `standing` alone says it is the copy, and `refine`
is what makes it a duplicate (`duplicate_taken_for_moved`). jj can also take the copy moved
for a duplicate, if the other path is reused, and then the daemon can't follow it
(`move_taken_for_duplicate`), which copies.md leaves out of scope: `moves_followed` needs jj
to have seen the copy where it is.
-/
import Musubi.Basic

namespace Musubi.Copies

/-! ## The decisions (`copy.rs`) -/

/-- `config::Membership`. -/
inductive Membership where
  | joined
  | left
  | removed
deriving DecidableEq, Repr

/-- A repository's record (`config::HiveConfig`): its hive, its config-id when it joined, and
whether it is still part of the hive. -/
structure Record where
  hive : Nat
  cid : Nat
  state : Membership
deriving DecidableEq, Repr

/-- What a repository holds of its identity (`copy::Found`). -/
structure Repo where
  key : Option Nat
  record : Option Record
  cid : Option Nat
deriving DecidableEq, Repr

/-- The daemon's entry for a key (`config::Entry`). -/
structure Entry where
  key : Nat
  hive : Nat
  cid : Nat
  path : Nat
deriving DecidableEq, Repr

/-- `copy::Standing`. -/
inductive Standing where
  | outside
  | removed
  | copy
  | broken
  | duplicate
  | unknown
deriving DecidableEq, Repr

/-- `copy::standing`: what a repository is, given this machine's entry for its key. -/
def standing (r : Repo) (entry : Option Entry) : Standing :=
  match r.record with
  | none => .outside
  | some record =>
    -- A duplicate of a copy that left, which joining would join under the copy's key.
    match record.state, r.cid.any (· != record.cid) with
    | .left, true | .removed, true => .duplicate
    | .left, false => .outside
    | .removed, false => .removed
    | .joined, _ =>
      match r.key, r.cid with
      | some key, some cid =>
        if cid ≠ record.cid then .duplicate
        else
          match entry with
          | none => .unknown
          | some e =>
            if e.key = key ∧ e.hive = record.hive ∧ e.cid = record.cid then .copy
            else .duplicate
      | _, _ => .broken

/-- `copy::check`: whether `r` is the copy `e` names, as the daemon checks before each sync. -/
def check (e : Entry) (r : Repo) : Bool :=
  match r.record with
  | none => false
  | some record =>
    record.hive == e.hive && record.state == .joined && r.key == some e.key &&
      r.cid == some e.cid && record.cid == e.cid

/-- `copy::holds`: whether the repository at a path, if any, is the copy `e` names. -/
def holds (e : Entry) : Option Repo → Bool
  | none => false
  | some r => check e r

theorem check_iff {e : Entry} {r : Repo} :
    check e r = true ↔ ∃ record, r.record = some record ∧ record.hive = e.hive ∧
      record.state = .joined ∧ r.key = some e.key ∧ r.cid = some e.cid ∧ record.cid = e.cid := by
  unfold check
  split
  · simp_all
  · simp_all [and_assoc]

/-- `copy::refine`: the copy of a key is a duplicate after all if the entry's path holds the
copy the entry names (`elsewhereHolds`), in another directory than this repository's
(`sameDirectory` false). -/
def refine (st : Standing) (elsewhereHolds sameDirectory : Bool) : Standing :=
  match st with
  | .copy => if elsewhereHolds && !sameDirectory then .duplicate else .copy
  | st => st

theorem refine_ne_copy (st : Standing) : refine st true false ≠ .copy := by
  cases st <;> simp [refine]

/-! ## A machine -/

/-- One machine's repositories, jj's record of where it last saw each config-id, and the
daemon's entries, with every `(hive, key, repository)` whose work it pushed, and the next
fresh key and config-id. -/
structure State where
  disk : Nat → Option Repo
  /-- Where jj last saw each config-id, in the user's jj config directory. -/
  seen : Nat → Option Nat
  entry : Nat → Option Entry
  pushed : List (Nat × Nat × Repo)
  nextKey : Nat
  nextCid : Nat

def init : State := ⟨fun _ => none, fun _ => none, fun _ => none, [], 0, 0⟩

/-- What the repository at `p` is by `standing` alone, given this machine's entry for its
key. -/
def State.standingAt (s : State) (p : Nat) : Option Standing :=
  (s.disk p).map fun r => standing r (r.key.bind s.entry)

/-- What `r`, at `p`, is to musubi (`copy::standing_of`): its `standing`, `refine`d against
what is at its entry's path. With no aliases, another directory is another path. -/
def State.verdict (s : State) (p : Nat) (r : Repo) : Standing :=
  let entry := r.key.bind s.entry
  refine (standing r entry) (entry.any fun e => holds e (s.disk e.path))
    (entry.any fun e => e.path == p)

/-- What the repository at `p` is to musubi. -/
def State.verdictAt (s : State) (p : Nat) : Option Standing :=
  (s.disk p).map (s.verdict p)

/-- jj opens the repository at `p` (`handle_metadata_path`). -/
def jjRun (s : State) (p : Nat) : State :=
  match s.disk p with
  | none => s
  | some r =>
    match r.cid with
    | none => s
    | some c =>
      match s.seen c with
      | none => { s with seen := upd s.seen c (some p) }
      | some p' =>
        if p' = p then s
        else
          match s.disk p' with
          -- Moved.
          | none => { s with seen := upd s.seen c (some p) }
          -- Duplicated: a new config-id, seen here.
          | some _ =>
            { s with
              disk := upd s.disk p (some { r with cid := some s.nextCid })
              seen := upd s.seen s.nextCid (some p)
              nextCid := s.nextCid + 1 }

/-- `UserState::put_entry`: `e` becomes the entry for key `k`, and no other entry keeps its
path. -/
def putEntry (entry : Nat → Option Entry) (k : Nat) (e : Entry) : Nat → Option Entry :=
  fun k' => if k' = k then some e else (entry k').filter fun o => o.path != e.path

/-- Whether `musubi join` goes ahead in a repository `r` whose verdict is `v`, to join hive
`h`: one outside a hive, or whose hive was removed, joins any; the copy joins its own hive
again. (`join --original` is not modeled.) -/
def joinable (r : Repo) (v : Standing) (h : Nat) : Bool :=
  match v with
  | .outside | .removed => true
  | .copy => r.record.any (·.hive == h)
  | _ => false

/-- `musubi join`, after jj has resolved the repository's config-id: it gives the repository
a key and a config-id if it has none, records hive `h`, and puts its entry. -/
def joinAt (s : State) (p h : Nat) : Option State :=
  match s.disk p with
  | none => none
  | some r =>
    if joinable r (s.verdict p r) h then
      let key := r.key.getD s.nextKey
      let cid := r.cid.getD s.nextCid
      some { s with
        disk := upd s.disk p (some ⟨some key, some ⟨h, cid, .joined⟩, some cid⟩)
        seen := if r.cid.isNone then upd s.seen cid (some p) else s.seen
        entry := putEntry s.entry key ⟨key, h, cid, p⟩
        nextKey := if r.key.isNone then s.nextKey + 1 else s.nextKey
        nextCid := if r.cid.isNone then s.nextCid + 1 else s.nextCid }
    else none

inductive Act where
  /-- The user moves the repository at `p` to the empty path `q`. -/
  | move (p q : Nat)
  /-- The user copies the repository at `p` to the empty path `q`. -/
  | copy (p q : Nat)
  | delete (p : Nat)
  /-- The user puts another repository at `p`, made elsewhere: its key and config-id, if it
  has them, are new here. -/
  | put (p : Nat) (r : Repo)
  | jj (p : Nat)
  | join (p h : Nat)
  /-- The daemon syncs the copy of key `k`. -/
  | sync (k : Nat)
  /-- The daemon finds that key `k`'s entry no longer holds its copy, and follows it to where
  jj last saw its config-id (`copy::moved_to`). -/
  | relocate (k : Nat)
deriving Repr

/-- A step, or `none` if it can't be taken. -/
def step (s : State) : Act → Option State
  | .move p q =>
    match s.disk p, s.disk q with
    | some r, none => some { s with disk := upd (upd s.disk p none) q (some r) }
    | _, _ => none
  | .copy p q =>
    match s.disk p, s.disk q with
    | some r, none => some { s with disk := upd s.disk q (some r) }
    | _, _ => none
  | .delete p => some { s with disk := upd s.disk p none }
  | .put p r =>
    if (r.key = none ∨ r.key = some s.nextKey) ∧ (r.cid = none ∨ r.cid = some s.nextCid) then
      some { s with
        disk := upd s.disk p (some r)
        nextKey := if r.key.isNone then s.nextKey else s.nextKey + 1
        nextCid := if r.cid.isNone then s.nextCid else s.nextCid + 1 }
    else none
  | .jj p => some (jjRun s p)
  | .join p h => joinAt (jjRun s p) p h
  | .sync k =>
    match s.entry k with
    | none => none
    | some e =>
      match s.disk e.path with
      | none => none
      | some r =>
        if check e r then some { s with pushed := s.pushed ++ [(e.hive, k, r)] } else none
  | .relocate k =>
    match s.entry k with
    | none => none
    | some e =>
      match s.seen e.cid with
      | none => none
      | some q =>
        if !holds e (s.disk e.path) && holds e (s.disk q) then
          some { s with entry := putEntry s.entry k { e with path := q } }
        else none

inductive Reachable : State → Prop where
  | init : Reachable init
  | step {s s' : State} (a : Act) : Reachable s → step s a = some s' → Reachable s'

/-- Runs `as` from `s`. -/
def run : State → List Act → Option State
  | s, [] => some s
  | s, a :: as => (step s a).bind (run · as)

theorem run_reachable {as : List Act} {s s' : State} (hs : Reachable s)
    (h : run s as = some s') : Reachable s' := by
  induction as generalizing s with
  | nil => cases h; exact hs
  | cons a as ih =>
    simp only [run] at h
    cases hst : step s a with
    | none => simp [hst] at h
    | some s₁ =>
      simp only [hst, Option.bind_some] at h
      exact ih (Reachable.step a hs hst) h

/-! ## The invariant -/

/-- `r` is work of key `k` in hive `h`. -/
def Pushable (h k : Nat) (r : Repo) : Prop :=
  ∃ record, r.record = some record ∧ record.state = .joined ∧ record.hive = h ∧ r.key = some k

structure Inv (s : State) : Prop where
  disk_cid : ∀ p r c, s.disk p = some r → r.cid = some c → c < s.nextCid
  entry_key : ∀ k e, s.entry k = some e → e.key = k
  entry_cid : ∀ k e, s.entry k = some e → e.cid < s.nextCid
  pushed : ∀ h k r, (h, k, r) ∈ s.pushed → Pushable h k r

theorem inv_init : Inv init :=
  ⟨by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem jjRun_entry (s : State) (p : Nat) : (jjRun s p).entry = s.entry := by
  unfold jjRun
  repeat' split
  all_goals rfl

theorem jjRun_pushed (s : State) (p : Nat) : (jjRun s p).pushed = s.pushed := by
  unfold jjRun
  repeat' split
  all_goals rfl

/-- jj changes nothing, records where it saw a config-id, or makes the repository at `p` a
duplicate. -/
theorem jjRun_cases (s : State) (p : Nat) :
    jjRun s p = s ∨ (∃ c, jjRun s p = { s with seen := upd s.seen c (some p) }) ∨
      ∃ r, s.disk p = some r ∧ jjRun s p =
        { s with
          disk := upd s.disk p (some { r with cid := some s.nextCid })
          seen := upd s.seen s.nextCid (some p)
          nextCid := s.nextCid + 1 } := by
  unfold jjRun
  split
  · exact Or.inl rfl
  · rename_i r hr
    split
    · exact Or.inl rfl
    · rename_i c _
      split
      · exact Or.inr (Or.inl ⟨c, rfl⟩)
      · split
        · exact Or.inl rfl
        · split
          · exact Or.inr (Or.inl ⟨c, rfl⟩)
          · exact Or.inr (Or.inr ⟨r, hr, rfl⟩)

/-- jj changes only the repository at `p`. -/
theorem jjRun_disk_ne (s : State) {p p' : Nat} (hp : p' ≠ p) :
    (jjRun s p).disk p' = s.disk p' := by
  rcases jjRun_cases s p with he | ⟨c, he⟩ | ⟨r, hr, he⟩ <;> rw [he]
  simp only [upd_ne _ _ hp]

/-- A repository jj runs in stays, with its key. -/
theorem jjRun_keeps (s : State) {p : Nat} {r : Repo} (hr : s.disk p = some r) :
    ∃ r', (jjRun s p).disk p = some r' ∧ r'.key = r.key := by
  rcases jjRun_cases s p with he | ⟨c, he⟩ | ⟨r₀, hr₀, he⟩ <;> rw [he]
  · exact ⟨r, hr, rfl⟩
  · exact ⟨r, hr, rfl⟩
  · rw [hr] at hr₀
    cases hr₀
    exact ⟨_, upd_same _ _ _, rfl⟩

/-- jj changes a repository's config-id only. -/
theorem jjRun_disk (s : State) (p p' : Nat) (r' : Repo) (h : (jjRun s p).disk p' = some r') :
    ∃ r, s.disk p' = some r ∧ r.key = r'.key ∧ r.record = r'.record := by
  rcases jjRun_cases s p with he | ⟨c, he⟩ | ⟨r, hr, he⟩ <;> rw [he] at h
  · exact ⟨r', h, rfl, rfl⟩
  · exact ⟨r', h, rfl, rfl⟩
  · simp only at h
    by_cases hp : p' = p
    · subst hp
      simp only [upd_same, Option.some.injEq] at h
      subst h
      exact ⟨r, hr, rfl, rfl⟩
    · simp only [upd_ne _ _ hp] at h
      exact ⟨r', h, rfl, rfl⟩

theorem inv_jjRun {s : State} (hi : Inv s) (p : Nat) : Inv (jjRun s p) := by
  rcases jjRun_cases s p with he | ⟨c, he⟩ | ⟨r, hr, he⟩ <;> rw [he]
  · exact hi
  · exact ⟨hi.1, hi.2, hi.3, hi.4⟩
  refine ⟨?_, hi.entry_key, ?_, hi.pushed⟩
  · intro p' r' c' h1 h2
    simp only at h1 ⊢
    by_cases hp : p' = p
    · subst hp
      simp only [upd_same, Option.some.injEq] at h1
      subst h1
      simp only [Option.some.injEq] at h2
      omega
    · simp only [upd_ne _ _ hp] at h1
      exact Nat.lt_succ_of_lt (hi.disk_cid p' r' c' h1 h2)
  · intro k e he
    exact Nat.lt_succ_of_lt (hi.entry_cid k e he)

theorem inv_joinAt {s s' : State} (hi : Inv s) {p h : Nat} (hj : joinAt s p h = some s') :
    Inv s' := by
  unfold joinAt at hj
  split at hj
  · cases hj
  · rename_i r hr
    split at hj
    · cases hj
      have hcid : ∀ c, r.cid = some c → c < s.nextCid := fun c hc => hi.disk_cid p r c hr hc
      have hlt : r.cid.getD s.nextCid < if r.cid.isNone then s.nextCid + 1 else s.nextCid := by
        cases hc : r.cid with
        | none => simp
        | some c => simpa using hcid c hc
      have hle : s.nextCid ≤ if r.cid.isNone then s.nextCid + 1 else s.nextCid := by
        split <;> omega
      refine ⟨?_, ?_, ?_, hi.pushed⟩
      · intro p' r' c' h1 h2
        simp only at h1 ⊢
        by_cases hp : p' = p
        · subst hp
          simp only [upd_same, Option.some.injEq] at h1
          subst h1
          simp only [Option.some.injEq] at h2
          omega
        · simp only [upd_ne _ _ hp] at h1
          exact Nat.lt_of_lt_of_le (hi.disk_cid p' r' c' h1 h2) hle
      · intro k e he
        simp only [putEntry] at he
        split at he
        · rename_i hk
          simp only [Option.some.injEq] at he
          subst he hk
          rfl
        · cases he' : s.entry k with
          | none => simp [he'] at he
          | some o =>
            simp only [he', Option.filter_some] at he
            split at he
            · simp only [Option.some.injEq] at he
              subst he
              exact hi.entry_key k o he'
            · cases he
      · intro k e he
        simp only [putEntry] at he ⊢
        split at he
        · simp only [Option.some.injEq] at he
          subst he
          exact hlt
        · cases he' : s.entry k with
          | none => simp [he'] at he
          | some o =>
            simp only [he', Option.filter_some] at he
            split at he
            · simp only [Option.some.injEq] at he
              subst he
              exact Nat.lt_of_lt_of_le (hi.entry_cid k o he') hle
            · cases he
    · cases hj

theorem inv_step {s s' : State} (hi : Inv s) {a : Act} (hst : step s a = some s') : Inv s' := by
  cases a with
  | move p q =>
    cases hp : s.disk p with
    | none => simp [step, hp] at hst
    | some r =>
      cases hq : s.disk q with
      | some _ => simp [step, hp, hq] at hst
      | none =>
        simp only [step, hp, hq, Option.some.injEq] at hst
        subst hst
        refine ⟨?_, hi.entry_key, hi.entry_cid, hi.pushed⟩
        intro p' r' c h1 h2
        simp only [upd] at h1
        split at h1
        · cases h1; exact hi.disk_cid p _ c hp h2
        · split at h1
          · cases h1
          · exact hi.disk_cid p' r' c h1 h2
  | copy p q =>
    cases hp : s.disk p with
    | none => simp [step, hp] at hst
    | some r =>
      cases hq : s.disk q with
      | some _ => simp [step, hp, hq] at hst
      | none =>
        simp only [step, hp, hq, Option.some.injEq] at hst
        subst hst
        refine ⟨?_, hi.entry_key, hi.entry_cid, hi.pushed⟩
        intro p' r' c h1 h2
        simp only [upd] at h1
        split at h1
        · cases h1; exact hi.disk_cid p _ c hp h2
        · exact hi.disk_cid p' r' c h1 h2
  | delete p =>
    simp only [step, Option.some.injEq] at hst
    subst hst
    refine ⟨?_, hi.entry_key, hi.entry_cid, hi.pushed⟩
    intro p' r' c h1 h2
    simp only [upd] at h1
    split at h1
    · cases h1
    · exact hi.disk_cid p' r' c h1 h2
  | put p r =>
    simp only [step] at hst
    split at hst
    · rename_i hf
      cases hst
      have hle : s.nextCid ≤ if r.cid.isNone then s.nextCid else s.nextCid + 1 := by
        split <;> omega
      refine ⟨?_, hi.entry_key, ?_, hi.pushed⟩
      · intro p' r' c h1 h2
        simp only [upd] at h1
        split at h1
        · cases h1
          rcases hf.2 with hn | hn <;> simp_all
        · exact Nat.lt_of_lt_of_le (hi.disk_cid p' r' c h1 h2) hle
      · intro k e he
        exact Nat.lt_of_lt_of_le (hi.entry_cid k e he) hle
    · cases hst
  | jj p =>
    simp only [step, Option.some.injEq] at hst
    subst hst
    exact inv_jjRun hi p
  | join p h =>
    exact inv_joinAt (inv_jjRun hi p) hst
  | sync k =>
    simp only [step] at hst
    split at hst
    · cases hst
    · rename_i e he
      split at hst
      · cases hst
      · rename_i r hr
        split at hst
        · rename_i hc
          cases hst
          refine ⟨hi.disk_cid, hi.entry_key, hi.entry_cid, ?_⟩
          intro h' k' r' hm
          simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
          rcases hm with hm | ⟨rfl, rfl, rfl⟩
          · exact hi.pushed h' k' r' hm
          · obtain ⟨record, h1, h2, h3, h4, -, -⟩ := check_iff.1 hc
            exact ⟨record, h1, h3, h2, by rw [h4, hi.entry_key _ e he]⟩
        · cases hst
  | relocate k =>
    simp only [step] at hst
    split at hst
    · cases hst
    · rename_i e he
      split at hst
      · cases hst
      · split at hst
        · cases hst
          refine ⟨hi.disk_cid, ?_, ?_, hi.pushed⟩
          · intro k' o ho
            simp only [putEntry] at ho
            split at ho
            · rename_i hk
              simp only [Option.some.injEq] at ho
              subst ho hk
              exact hi.entry_key _ e he
            · cases ho' : s.entry k' with
              | none => simp [ho'] at ho
              | some o' =>
                simp only [ho', Option.filter_some] at ho
                split at ho
                · simp only [Option.some.injEq] at ho
                  subst ho
                  exact hi.entry_key k' o' ho'
                · cases ho
          · intro k' o ho
            simp only [putEntry] at ho
            split at ho
            · simp only [Option.some.injEq] at ho
              subst ho
              exact hi.entry_cid _ e he
            · cases ho' : s.entry k' with
              | none => simp [ho'] at ho
              | some o' =>
                simp only [ho', Option.filter_some] at ho
                split at ho
                · simp only [Option.some.injEq] at ho
                  subst ho
                  exact hi.entry_cid k' o' ho'
                · cases ho
        · cases hst

theorem inv_reachable {s : State} (hs : Reachable s) : Inv s := by
  induction hs with
  | init => exact inv_init
  | step a _ hst ih => exact inv_step ih hst

/-! ## The theorems -/

/-- (a) The daemon pushes only work of a repository joined to the hive it pushes to, under
the repository's own key. -/
theorem right_hive {s : State} (hs : Reachable s) {h k : Nat} {r : Repo}
    (hp : (h, k, r) ∈ s.pushed) :
    ∃ record, r.record = some record ∧ record.state = .joined ∧ record.hive = h ∧
      r.key = some k :=
  (inv_reachable hs).pushed h k r hp

/-- What jj records when it runs in a repository: that it saw the repository's config-id,
new or not, there. -/
theorem jj_records_path (s : State) (p : Nat) {r : Repo} {c : Nat}
    (hr : (jjRun s p).disk p = some r) (hc : r.cid = some c) : (jjRun s p).seen c = some p := by
  revert hr
  unfold jjRun
  repeat' split
  all_goals
    intro h
    try simp only [upd_same, Option.some.injEq] at h
    try subst h
    simp_all [upd]

/-- (b) Duplicates are refused. If key `k`'s entry holds its copy, no other repository with
key `k` is the copy to musubi, whatever jj decides when it runs there. -/
theorem duplicates_refused {s : State} {k q : Nat} {e : Entry} {r : Repo}
    (he : s.entry k = some e) (hc : holds e (s.disk e.path) = true) (hq : q ≠ e.path)
    (hr : s.disk q = some r) (hk : r.key = some k) :
    (jjRun s q).verdictAt q ≠ some .copy := by
  obtain ⟨r', hr', hk'⟩ := jjRun_keeps s hr
  have hd : (jjRun s q).disk e.path = s.disk e.path := jjRun_disk_ne s (Ne.symm hq)
  have hne : (e.path == q) = false := by simp [Ne.symm hq]
  simp only [State.verdictAt, State.verdict, hr', hk', hk, Option.map_some, Option.bind_some,
    jjRun_entry, he, Option.any_some, hd, hc, hne, ne_eq, Option.some.injEq]
  exact refine_ne_copy _

/-- A duplicate of a copy that left, or whose hive was removed, can't join: its record names
another config-id than the one jj resolves for it. -/
theorem join_refuses_duplicate {s : State} {p h c : Nat} {r : Repo} {record : Record}
    (hr : (jjRun s p).disk p = some r) (hrec : r.record = some record)
    (hst : record.state ≠ .joined) (hc : r.cid = some c) (hne : c ≠ record.cid) :
    step s (.join p h) = none := by
  have hv : standing r (r.key.bind (jjRun s p).entry) = .duplicate := by
    have hb : (c != record.cid) = true := bne_iff_ne.mpr hne
    obtain ⟨hv, rc, st⟩ := record
    cases st
    · exact absurd rfl hst
    all_goals simp only [standing, hrec, hc, Option.any_some, hb]
  simp only [step, joinAt, hr, State.verdict, hv, refine, joinable]
  rfl

/-- Keys present on the machine: in a repository, as an entry, or pushed. -/
def Keyed (s : State) (k : Nat) : Prop :=
  (∃ p r, s.disk p = some r ∧ r.key = some k) ∨ s.entry k ≠ none ∨
    ∃ h r, (h, k, r) ∈ s.pushed

/-- (c) Only `join` makes a key. A repository the user puts in place brings its own. -/
theorem only_join_makes_keys {s s' : State} {a : Act} {k : Nat} (hst : step s a = some s')
    (hk : Keyed s' k) :
    Keyed s k ∨ (∃ p h, a = .join p h) ∨ ∃ p r, a = .put p r ∧ r.key = some k := by
  cases a with
  | move p q =>
    left
    cases hp : s.disk p with
    | none => simp [step, hp] at hst
    | some r =>
      cases hq : s.disk q with
      | some _ => simp [step, hp, hq] at hst
      | none =>
        simp only [step, hp, hq, Option.some.injEq] at hst
        subst hst
        rcases hk with ⟨p', r', h1, h2⟩ | hk | hk
        · simp only [upd] at h1
          split at h1
          · cases h1; exact Or.inl ⟨p, _, hp, h2⟩
          · split at h1
            · cases h1
            · exact Or.inl ⟨p', r', h1, h2⟩
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr hk)
  | copy p q =>
    left
    cases hp : s.disk p with
    | none => simp [step, hp] at hst
    | some r =>
      cases hq : s.disk q with
      | some _ => simp [step, hp, hq] at hst
      | none =>
        simp only [step, hp, hq, Option.some.injEq] at hst
        subst hst
        rcases hk with ⟨p', r', h1, h2⟩ | hk | hk
        · simp only [upd] at h1
          split at h1
          · cases h1; exact Or.inl ⟨p, _, hp, h2⟩
          · exact Or.inl ⟨p', r', h1, h2⟩
        · exact Or.inr (Or.inl hk)
        · exact Or.inr (Or.inr hk)
  | delete p =>
    left
    simp only [step, Option.some.injEq] at hst
    subst hst
    rcases hk with ⟨p', r', h1, h2⟩ | hk | hk
    · simp only [upd] at h1
      split at h1
      · cases h1
      · exact Or.inl ⟨p', r', h1, h2⟩
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr hk)
  | put p r =>
    simp only [step] at hst
    split at hst
    · cases hst
      rcases hk with ⟨p', r', h1, h2⟩ | hk | hk
      · simp only [upd] at h1
        split at h1
        · cases h1; exact Or.inr (Or.inr ⟨p, _, rfl, h2⟩)
        · exact Or.inl (Or.inl ⟨p', r', h1, h2⟩)
      · exact Or.inl (Or.inr (Or.inl hk))
      · exact Or.inl (Or.inr (Or.inr hk))
    · cases hst
  | jj p =>
    left
    simp only [step, Option.some.injEq] at hst
    subst hst
    rcases hk with ⟨p', r', h1, h2⟩ | hk | hk
    · obtain ⟨r, hr, hkey, -⟩ := jjRun_disk s p p' r' h1
      exact Or.inl ⟨p', r, hr, hkey ▸ h2⟩
    · rw [jjRun_entry] at hk; exact Or.inr (Or.inl hk)
    · rw [jjRun_pushed] at hk; exact Or.inr (Or.inr hk)
  | join p h => exact Or.inr (Or.inl ⟨p, h, rfl⟩)
  | sync k' =>
    left
    simp only [step] at hst
    split at hst
    · cases hst
    · rename_i e he
      split at hst
      · cases hst
      · split at hst
        · cases hst
          rcases hk with hk | hk | ⟨h', r', hm⟩
          · exact Or.inl hk
          · exact Or.inr (Or.inl hk)
          · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
            rcases hm with hm | ⟨-, rfl, -⟩
            · exact Or.inr (Or.inr ⟨h', r', hm⟩)
            · exact Or.inr (Or.inl (by simp [he]))
        · cases hst
  | relocate k' =>
    left
    simp only [step] at hst
    split at hst
    · cases hst
    · rename_i e he
      split at hst
      · cases hst
      · split at hst
        · cases hst
          rcases hk with hk | hk | hk
          · exact Or.inl hk
          · right; left
            simp only [putEntry] at hk
            split at hk
            · rename_i hkk; subst hkk; simp [he]
            · intro hn; simp [hn] at hk
          · exact Or.inr (Or.inr hk)
        · cases hst

/-- (d) Moves are followed. If key `k`'s entry holds its copy, and jj last saw the copy's
config-id there, then once the copy is moved and jj has run in it, the daemon follows it. -/
theorem moves_followed {s : State} {k q : Nat} {e : Entry} (he : s.entry k = some e)
    (hc : holds e (s.disk e.path) = true) (hseen : s.seen e.cid = some e.path)
    (hq : s.disk q = none) :
    ∃ s₁ s₂, step s (.move e.path q) = some s₁ ∧ step (jjRun s₁ q) (.relocate k) = some s₂ ∧
      s₂.entry k = some { e with path := q } ∧ holds { e with path := q } (s₂.disk q) = true := by
  cases hd : s.disk e.path with
  | none => simp [hd, holds] at hc
  | some r =>
    have hcr : check e r = true := by simpa [hd, holds] using hc
    have hrc : r.cid = some e.cid := by
      obtain ⟨-, -, -, -, -, h, -⟩ := check_iff.1 hcr; exact h
    have hne : q ≠ e.path := by intro h; rw [h, hd] at hq; cases hq
    let s₁ : State := { s with disk := upd (upd s.disk e.path none) q (some r) }
    have hq₁ : s₁.disk q = some r := upd_same _ _ _
    have hp₁ : s₁.disk e.path = none := by
      simp only [s₁, upd_ne _ _ hne.symm, upd_same]
    -- jj finds nothing where it last saw the copy, and takes it for moved.
    have hj : jjRun s₁ q = { s₁ with seen := upd s.seen e.cid (some q) } := by
      unfold jjRun
      rw [hq₁]
      simp only [hrc]
      rw [show s₁.seen = s.seen from rfl, hseen]
      simp only [hne.symm, ↓reduceIte, hp₁]
    let s₂ : State :=
      { s₁ with
        seen := upd s.seen e.cid (some q)
        entry := putEntry s.entry k { e with path := q } }
    have he₁ : s₁.entry k = some e := he
    refine ⟨s₁, s₂, by simp only [step, hd, hq]; rfl, ?_, ?_, ?_⟩
    · rw [hj]
      simp only [step, he₁, hp₁, hq₁, holds, hcr, upd_same, Bool.not_false, Bool.true_and,
        ↓reduceIte]
      rfl
    · simp [s₂, putEntry]
    · show holds _ (s₁.disk q) = true
      rw [hq₁]
      exact hcr

/-- (e) The daemon writes nothing to disk: syncing and following a move change neither the
repositories nor jj's record. -/
theorem daemon_writes_nothing {s s' : State} {k : Nat}
    (hst : step s (.sync k) = some s' ∨ step s (.relocate k) = some s') :
    s'.disk = s.disk ∧ s'.seen = s.seen := by
  rcases hst with hst | hst
  · simp only [step] at hst
    repeat' split at hst
    all_goals first | cases hst | skip
    exact ⟨rfl, rfl⟩
  · simp only [step] at hst
    repeat' split at hst
    all_goals first | cases hst | skip
    exact ⟨rfl, rfl⟩

/-! ## What jj's rule doesn't cover

Both runs make a copy at path 0 (key 0, config-id 0, hive 0), move it to 1, run jj there,
and move it back before jj runs in it again, so that jj last saw its config-id at 1. -/

/-- A repository with nothing in it. -/
def blank : Repo := ⟨none, none, none⟩

def movedBack : List Act := [.put 0 blank, .join 0 0, .move 0 1, .jj 1, .move 1 0]

def dupRun : List Act := movedBack ++ [.copy 0 2]
def moveRun : List Act := movedBack ++ [.put 1 blank]

def dupState : State := (run init dupRun).getD init
def moveState : State := (run init moveRun).getD init

/-- jj takes a duplicate for the copy moved, and `refine` is needed. Copied to 2, the copy's
duplicate is the first that jj runs in, and finding nothing at 1, jj takes it for the copy
moved there. By `standing` alone it is the copy, though the entry's path holds the copy too;
its verdict is that it is a duplicate. -/
theorem duplicate_taken_for_moved :
    ∃ s k e q r, Reachable s ∧ s.entry k = some e ∧ holds e (s.disk e.path) = true ∧
      s.seen e.cid ≠ some e.path ∧ q ≠ e.path ∧ s.disk q = some r ∧ r.key = some k ∧
      (jjRun s q).standingAt q = some .copy ∧ (jjRun s q).verdictAt q = some .duplicate :=
  ⟨dupState, 0, ⟨0, 0, 0, 0⟩, 2, ⟨some 0, some ⟨0, 0, .joined⟩, some 0⟩,
    run_reachable Reachable.init (as := dupRun) rfl,
    by decide, by decide, by decide, by decide, by decide, rfl, by decide, by decide⟩

/-- jj takes the copy moved for a duplicate. With another repository put at 1, the copy
moved to 2 gets a new config-id when jj runs in it, so the daemon can't follow it. (copies.md,
"Out of scope": "A copy moved, and a new repository made at its old path before jj runs in
the copy".) -/
theorem move_taken_for_duplicate :
    ∃ s k e q s₁, Reachable s ∧ s.entry k = some e ∧ holds e (s.disk e.path) = true ∧
      s.seen e.cid ≠ some e.path ∧ s.disk q = none ∧ step s (.move e.path q) = some s₁ ∧
      step (jjRun s₁ q) (.relocate k) = none :=
  ⟨moveState, 0, ⟨0, 0, 0, 0⟩, 2, (step moveState (.move 0 2)).getD init,
    run_reachable Reachable.init (as := moveRun) rfl,
    by decide, by decide, by decide, by decide, rfl, by decide⟩

end Musubi.Copies
