/-
Which workspaces in a local operation are this machine's own, as translating the operation into
the hive's canonical form decides it (design.md, "Which workspaces are this machine's own").

A local view names this machine's workspaces plainly and another machine's as
`<prefix>/<workspace>` (`Names.lean`), but jj allows `/` in a name, so the name alone doesn't
say whose a workspace is. Two functions answer from different evidence:

- `canonical_view` (`crates/musubi-jj/src/node/view.rs`) decides from the operation's canonical
  parents, as this machine named their workspaces, the names it keeps privately, the
  operation's namespace context and the views it started from (`owned`);
- `own_of_view` (`crates/musubi-jj/src/node/presence.rs`) decides from the canonical operation
  the first wrote: its view, its presence and the context it carries (`ownOfView`). What it
  decides is recorded as private names, which both trust from then on.

Ownership is defined once, as a proposition (`Owns`), and both are executable forms of it:

- `mem_owned_iff`: `owned` computes `Owns`;
- `agreement`: where this machine is present, `own_of_view` of the canonical operation
  `canonical_view` wrote owns exactly what `canonical_view` put under this machine's key;
- `trims_keep_ownership`, `safety`: over every history of commands and merges on any earlier
  operations and realizations of other machines' operations, with trims of the whole history
  between, an operation's canonical form owns what
  the untrimmed history's would, so a name gets this machine's key only if the complete evidence
  makes it this machine's, and only realizations of the hive's operations keep a nonempty private
  record: translating a command records none.

jj's effects (the views, which workspaces a merge keeps) and presence are inputs: neither is
modeled here. Machine keys are `Names.Key`s, and names lists of characters, as in `Names.lean`.
-/
import Musubi.Names

namespace Musubi.Ownership

open Names (Str Key)

abbrev Name := Str

/-- A machine-qualified workspace key, `<machine key>/<workspace>`. -/
structure WKey where
  owner : Key
  ws : Name
deriving DecidableEq, Repr

/-- A namespace context (`musubi.workspace-context`): the local names its source machine gave
each workspace key, and the machines it knew. Its names are a map: no name twice. -/
structure Context where
  source : Key
  names : List (Name × WKey)
  known : List Key
deriving Repr

/-- A canonical operation, as translation reads it: its view's workspace keys, the machines its
history has known (`Presence::known`), whether this machine is present at it, the names of this
machine's workspaces as of its latest work (`Presence::worked`, read where it is absent), and
the context it carries. -/
structure Canon where
  keys : List WKey
  known : List Key
  present : Bool
  worked : Option (List Name) := none
  context : Option Context := none
deriving Repr

/-- A canonical parent of an operation: the root, or an operation, with the names that
realizations standing for it showed other machines' workspaces clear of (`reserved_at`). -/
inductive Parent where
  | root
  | op (c : Canon) (reserved : List Name)
deriving Repr

/-- Where an operation started from: its parents, or the view an undo, redo or restore brings
back, or for a revert its target's parents' views (`names`), with this machine's own names as
of that target and its parents (`own`, `restored_own_names`), or a target jj has collected. -/
inductive Source where
  | parents
  | restore (names own : List Name)
  | revert (names own : List Name)
  | collected
deriving Repr

/-- What translating one local operation reads: this machine's key, the names in the local
view, those this machine keeps privately (`private_workspace_names`), the canonical parents,
the names in the views of the local parents, where it started from, whether a `jj` command
made it (one that records a workspace name), whether it is a fix-up, and its context. -/
structure Ev where
  me : Key
  view : List Name
  priv : List Name
  parents : List Parent
  start : List Name
  source : Source := .parents
  command : Bool
  fixup : Bool := false
  context : Option Context := none
deriving Repr

/-- What the canonical operation gets besides the names of this machine's own workspaces:
whether this machine is present at it, the machines its history knows, this machine's names as
of its latest work, and the other machines' workspace keys jj's merge of its parents leaves. -/
structure Facts where
  present : Bool
  known : List Key
  worked : Option (List Name) := none
  others : List WKey
deriving Repr

/-! ## Names in a canonical view -/

/-- A key as text, `name#suffix`, by which musubi orders machines (a `BTreeSet<String>`). -/
def keyText (k : Key) : String := String.ofList (k.name ++ '#' :: k.suffix)

def insertKey (k : Key) : List Key → List Key
  | [] => [k]
  | x :: xs =>
    if k = x then x :: xs
    else if decide (keyText k ≤ keyText x) then k :: x :: xs
    else x :: insertKey k xs

/-- Machines in musubi's order, each once. -/
def sortKeys (l : List Key) : List Key := l.foldr insertKey []

theorem mem_insertKey {k k' : Key} : ∀ {l : List Key}, k' ∈ insertKey k l ↔ k' = k ∨ k' ∈ l
  | [] => by simp [insertKey]
  | x :: xs => by
    unfold insertKey
    by_cases h : k = x
    · subst h; simp
    · simp only [h, ↓reduceIte]
      split
      · simp
      · simp only [List.mem_cons, mem_insertKey]
        constructor
        · rintro (h | h | h) <;> simp [h]
        · rintro (h | h | h) <;> simp [h]

theorem mem_sortKeys {k : Key} : ∀ {l : List Key}, k ∈ sortKeys l ↔ k ∈ l
  | [] => by simp [sortKeys]
  | x :: xs => by
    show k ∈ insertKey x (sortKeys xs) ↔ _
    rw [mem_insertKey, mem_sortKeys]
    simp

/-- The machines a canonical view's history has known (`machines_of`): those its presence
knows, and those with workspaces in the view. -/
def machinesOf (c : Canon) : List Key := c.known ++ c.keys.map (·.owner)

/-- The names of `me`'s workspaces in a canonical view (`own_keys`). -/
def ownKeys (me : Key) (c : Canon) : List Name :=
  c.keys.filterMap fun k => if k.owner = me then some k.ws else none

/-- `own_names_in`: `me`'s names as of its latest work where it is absent and has worked, and
otherwise those in the view. -/
def ownNamesIn (me : Key) (c : Canon) : List Name :=
  match c.present, c.worked with
  | false, some w => w
  | _, _ => ownKeys me c

/-- `own_names`: those in the view, if any, else `ownNamesIn`. -/
def ownNames (me : Key) (c : Canon) : List Name :=
  if (ownKeys me c).isEmpty then ownNamesIn me c else ownKeys me c

/-- Each machine's prefix in a canonical view, clear of `me`'s names there and of `clear`
(`prefixes_with_own`). -/
def prefixes (me : Key) (c : Canon) (clear : List Name) : List (Key × Str) :=
  Names.assign (sortKeys (me :: machinesOf c)) (ownNamesIn me c ++ clear)

/-- The local name of a key of `c`'s view (`local_name`). -/
def nameOf (me : Key) (c : Canon) (clear : List Name) (k : WKey) : Name :=
  Names.localName me (prefixes me c clear) k.owner k.ws

/-- The local names of the other machines' workspaces in `c`'s view (`names_of`). -/
def othersOf (me : Key) (c : Canon) (clear : List Name) : List Name :=
  (c.keys.filter (·.owner ≠ me)).map (nameOf me c clear)

/-- Whether machine `k`'s workspaces could be shown under `p`, among any machines: whether `p`
is one of its candidates (`workspaces::could_be_shown_as`). -/
def couldBeShownAs (k : Key) (p : Str) : Bool :=
  p == k.name || p == k.name ++ '-' :: k.suffix.take 4 ||
    ((Names.full k).isPrefixOf p && (p.drop (Names.full k).length).all (· == '-'))

/-- Whether `n` is shown, or was once, as a workspace of one of `ms` other than `me`:
`<prefix>/<workspace>` with a prefix it could be shown under (`names_other_machine`). -/
def namesOther (me : Key) (n : Name) (ms : List Key) : Bool :=
  n.contains '/' && ms.any fun m => m != me && couldBeShownAs m (n.takeWhile (· != '/'))

/-! ## `canonical_view` -/

/-- What a context is taken against (`ContextBasis`): on the root alone, as after a full
trim, and at a fix-up, it stands for the views the operation started from; otherwise it gives
another machine only names in the views of the local parents. -/
inductive Basis where
  | initial
  | fixup
  | parents
deriving DecidableEq, Repr

/-- A context, if `me` recorded it: names in it apply only on the machine that recorded it. -/
def ctxFor (me : Key) (o : Option Context) : Option Context := o.filter (·.source == me)

def ownOf (me : Key) : Option Context → List Name
  | some x => (x.names.filter (·.2.owner == me)).map (·.1)
  | none => []

def foreignOf (me : Key) : Option Context → List Name
  | some x => (x.names.filter (·.2.owner != me)).map (·.1)
  | none => []

def knownOf : Option Context → List Key
  | some x => x.known
  | none => []

namespace Ev

variable (ev : Ev)

/-- The context, if this machine recorded it. -/
def ctx : Option Context := ctxFor ev.me ev.context

def basis : Basis :=
  match ev.parents with
  | [.root] => .initial
  | _ => if ev.fixup then .fixup else .parents

def admits (n : Name) : Bool :=
  match ev.basis with
  | .parents => ev.start.contains n
  | _ => true

def ctxKnown : List Key := knownOf ev.ctx

/-- The names the context gives this machine and the other machines. -/
def ctxOwn : List Name := ownOf ev.me ev.ctx
def ctxForeign : List Name := foreignOf ev.me ev.ctx

/-- This machine's names as of the canonical parents. -/
def parentOwn : List Name := ev.parents.flatMap fun
  | .root => []
  | .op c _ => ownNamesIn ev.me c

/-- This machine's own names, in the parents and private to it here, and on the root alone
those the context gives it (`Inherited::own_names`). -/
def inheritedOwn : List Name :=
  ev.priv ++ ev.parentOwn ++ (if ev.basis = .initial then ev.ctxOwn else [])

/-- Every machine the parents' histories and the context have known. -/
def inheritedMachines : List Key :=
  ev.parents.flatMap (fun | .root => [] | .op c _ => machinesOf c) ++ ev.ctxKnown

/-- The names under which this machine showed the parents' other workspaces. -/
def parentOthers : List Name := ev.parents.flatMap fun
  | .root => []
  | .op c r => othersOf ev.me c (ev.priv ++ r)

/-- The names the context gives another machine, as its basis admits them. -/
def ctxOthers : List Name :=
  ev.ctxForeign.filter fun n => !ev.inheritedOwn.contains n && ev.admits n

/-- Those the context stands for the start views in (`Inherited::captured`). -/
def captured : List Name := if ev.basis = .parents then [] else ev.ctxOthers

def others : List Name := ev.parentOthers ++ ev.ctxOthers

/-- The names in the views the operation started from (`names_started_from`). -/
def startedFrom : List Name :=
  match ev.source with
  | .parents | .collected => ev.start
  | .restore names own => names.filter (!own.contains ·)
  | .revert names own => ev.start ++ names.filter (!own.contains ·)

/-- Whether a name the operation made, there in none of the views it started from, can be its
own though another machine's workspace shows under it (`move_others_here`). -/
def mayMake : Bool := ev.command && ev.others.any (ev.view.contains ·)

/-- Another machine's workspace that this operation shows here: not this machine's. -/
def removed (n : Name) : Bool :=
  ev.others.contains n && !(ev.mayMake && !ev.startedFrom.contains n && !ev.captured.contains n)

/-- A name shown, or once shown, as a known other machine's, that nothing makes this machine's
(`drop_stale_names`). -/
def stale (n : Name) : Bool :=
  !ev.inheritedOwn.contains n && namesOther ev.me n ev.inheritedMachines

/-- A stale name this operation made after all: one in none of its parents' views, or, for an
operation that goes back to an older one, one that was this machine's there. -/
def keepStale (n : Name) : Bool :=
  match ev.source with
  | .parents => !ev.start.contains n
  | .collected => false
  | .restore _ own | .revert _ own => own.contains n

end Ev

/-- What `canonical_view` puts under this machine's key, where it is present. -/
def owned (ev : Ev) : List Name :=
  ev.view.filter fun n => !ev.removed n && (!ev.stale n || ev.keepStale n)

/-- The canonical operation `canonical_view` writes. -/
def canonView (ev : Ev) (f : Facts) : Canon where
  keys := f.others ++ (if f.present then (owned ev).map (WKey.mk ev.me) else [])
  known := f.known
  present := f.present
  worked := f.worked
  context := ev.context

/-! ## Ownership, defined once -/

namespace Ev

variable (ev : Ev)

/-- The evidence makes `n` this machine's: it keeps `n` privately, `n` is its own as of a
canonical parent, or, on the root alone, the context gives `n` to it. -/
def OwnClaim (n : Name) : Prop :=
  n ∈ ev.priv ∨ (∃ c r, Parent.op c r ∈ ev.parents ∧ n ∈ ownNamesIn ev.me c) ∨
    (ev.basis = .initial ∧ ∃ x ∈ ev.ctx, ∃ k, (n, k) ∈ x.names ∧ k.owner = ev.me)

/-- The context gives `n` to another machine where its basis admits that, and nothing makes it
this machine's. -/
def CtxGives (n : Name) : Prop :=
  (∃ x ∈ ev.ctx, ∃ k, (n, k) ∈ x.names ∧ k.owner ≠ ev.me) ∧ ¬ ev.OwnClaim n ∧
    (ev.basis = .parents → n ∈ ev.start)

/-- The evidence shows another machine's workspace under `n`: a canonical parent, as this
machine named its workspaces, or the context. -/
def ShownOther (n : Name) : Prop :=
  (∃ c r, Parent.op c r ∈ ev.parents ∧
    ∃ k ∈ c.keys, k.owner ≠ ev.me ∧ nameOf ev.me c (ev.priv ++ r) k = n) ∨ ev.CtxGives n

/-- A `jj` command that made `n`, there in none of the views it started from, which the context
doesn't stand for. It makes a workspace of this machine's, whatever another machine shows
under the same name (design.md: "as after `jj workspace forget laptop/default` here"). -/
def Made (n : Name) : Prop :=
  ev.command = true ∧ (∃ m ∈ ev.view, ev.ShownOther m) ∧ n ∉ ev.startedFrom ∧
    ¬ (ev.basis ≠ .parents ∧ ev.CtxGives n)

/-- A machine the parents' histories or the context know. -/
def Knows (m : Key) : Prop :=
  (∃ c r, Parent.op c r ∈ ev.parents ∧ m ∈ machinesOf c) ∨ m ∈ ev.ctxKnown

/-- `n` is shown as a known other machine's (`names_other_machine`). -/
def LooksOther (n : Name) : Prop :=
  n.contains '/' = true ∧
    ∃ m, ev.Knows m ∧ m ≠ ev.me ∧ couldBeShownAs m (n.takeWhile (· != '/')) = true

/-- A name shown as another machine's that this operation made all the same: one in none of
its parents' views, or, going back to an older operation, one this machine owned there. -/
def MadeStale (n : Name) : Prop :=
  match ev.source with
  | .parents => n ∉ ev.start
  | .collected => False
  | .restore _ own | .revert _ own => n ∈ own

end Ev

/-- **Ownership.** A name in an operation's local view is this machine's unless either:

- the evidence shows another machine's workspace under it, and the operation didn't make it;
- it is shown as a known other machine's, nothing in the evidence makes it this machine's, and
  the operation didn't make it. -/
def Owns (ev : Ev) (n : Name) : Prop :=
  n ∈ ev.view ∧ (ev.ShownOther n → ev.Made n) ∧
    (¬ ev.OwnClaim n → ev.LooksOther n → ev.MadeStale n)

/-! ## `own_of_view` -/

/-- `own_of_view`: of the names `view` of a local view whose canonical form is `c`, and the
names `priv` it keeps privately, every one but those `c`'s view gives other machines, and
those shown as a known other machine's or that the context gives another machine, unless
private or already this machine's own. -/
def ownOfView (me : Key) (view priv : List Name) (c : Canon) : List Name :=
  view.filter fun n => !(othersOf me c priv).contains n &&
    (priv.contains n || (ownNames me c).contains n ||
      (!(foreignOf me (ctxFor me c.context)).contains n &&
        !namesOther me n (machinesOf c ++ knownOf (ctxFor me c.context))))

/-- `own_of_view` before #167's fix, which read no context. -/
def ownOfViewUnfixed (me : Key) (view priv : List Name) (c : Canon) : List Name :=
  view.filter fun n => !(othersOf me c priv).contains n &&
    (priv.contains n || (ownNames me c).contains n || !namesOther me n (machinesOf c))

/-! ## What naming guarantees -/

/-- A machine key as musubi makes them: no `/` in its name or suffix. -/
def NoSlash (k : Key) : Prop := '/' ∉ k.name ∧ '/' ∉ k.suffix

theorem takeWhile_slash {w : Str} : ∀ {p : Str}, '/' ∉ p →
    (p ++ '/' :: w).takeWhile (· != '/') = p
  | [], _ => by simp
  | c :: p, h => by
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    have hp : '/' ∉ p := fun m => h (List.mem_cons_of_mem _ m)
    simp [hc, takeWhile_slash hp]

theorem full_isPrefixOf (k : Key) (x : Str) :
    (Names.full k).isPrefixOf (Names.full k ++ x) = true :=
  List.isPrefixOf_iff_prefix.mpr ⟨x, rfl⟩

theorem couldBeShownAs_dashes (k : Key) (j : Nat) :
    couldBeShownAs k (Names.full k ++ List.replicate j '-') = true := by
  simp only [couldBeShownAs, Bool.or_eq_true, full_isPrefixOf, List.drop_left, Bool.true_and]
  right
  simp

/-- Every candidate prefix of a machine is one it could be shown under. -/
theorem couldBeShownAs_candidate {plain : Bool} {k : Key} {b : Nat} {p : Str}
    (h : p ∈ Names.candidates plain k b) : couldBeShownAs k p = true := by
  simp only [Names.candidates, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.mem_nil_iff, or_false] at h
  rcases h with (h | rfl | rfl) | ⟨i, -, rfl⟩
  · split at h
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      subst h; simp [couldBeShownAs]
    · simp at h
  · simp [couldBeShownAs]
  · simpa using couldBeShownAs_dashes k 0
  · exact couldBeShownAs_dashes k (i + 1)

theorem couldBeShownAs_choose (own used : List Str) (plain : Bool) (k : Key) :
    couldBeShownAs k (Names.choose own used plain k) = true := by
  unfold Names.choose
  cases h : (Names.candidates plain k (Names.maxLen (used ++ own))).find? (Names.free own used) with
  | none => simpa using couldBeShownAs_dashes k 0
  | some p => exact couldBeShownAs_candidate (List.mem_of_find?_eq_some h)

theorem assignFrom_fst (machines : List Key) (own : List Str) :
    ∀ (ks : List Key) (acc : List (Key × Str)),
      (Names.assignFrom machines own acc ks).map (·.1) = acc.map (·.1) ++ ks
  | [], acc => by simp [Names.assignFrom]
  | k :: ks, acc => by
    rw [show Names.assignFrom machines own acc (k :: ks) =
      Names.assignFrom machines own
        (acc ++ [(k, Names.choose own (acc.map (·.2)) (Names.plainOk machines k) k)]) ks
      from rfl, assignFrom_fst machines own ks]
    simp

theorem assignFrom_choose (machines : List Key) (own : List Str) :
    ∀ (ks : List Key) (acc : List (Key × Str)), ∀ e ∈ Names.assignFrom machines own acc ks,
      e ∈ acc ∨ ∃ used plain, e.2 = Names.choose own used plain e.1
  | [], acc, e, he => Or.inl he
  | k :: ks, acc, e, he => by
    rcases assignFrom_choose machines own ks _ e he with h | h
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨_, _, rfl⟩
    · exact Or.inr h

/-- The prefix `assign` gives a machine is one it could be shown under. -/
theorem couldBeShownAs_prefixOf {machines : List Key} {own : List Str} {k : Key}
    (hk : k ∈ machines) :
    couldBeShownAs k (Names.prefixOf (Names.assign machines own) k) = true := by
  have hm : k ∈ (Names.assign machines own).map (·.1) := by
    simpa [Names.assign, assignFrom_fst] using hk
  rcases assignFrom_choose machines own machines [] _ (Names.prefixOf_mem hm) with h | ⟨_, _, h⟩
  · simp at h
  · simp only at h
    show couldBeShownAs k (Names.prefixOf (Names.assignFrom machines own [] machines) k) = true
    rw [h]; exact couldBeShownAs_choose _ _ _ _

/-- The name of another machine's workspace is shown as that machine's. -/
theorem namesOther_localName {me k : Key} {machines ms : List Key} {own : List Str} {w : Str}
    (hslash : ∀ m ∈ machines, NoSlash m) (hk : k ∈ machines) (hne : k ≠ me) (hms : k ∈ ms) :
    namesOther me (Names.localName me (Names.assign machines own) k w) ms = true := by
  obtain ⟨-, -, hsl⟩ := Names.assignFrom_spec machines own hslash machines []
    (fun _ h => h) ⟨List.nodup_nil, by simp⟩ (by simp)
  have hm : k ∈ (Names.assign machines own).map (·.1) := by
    simpa [Names.assign, assignFrom_fst] using hk
  have hp : '/' ∉ Names.prefixOf (Names.assign machines own) k := hsl _ (Names.prefixOf_mem hm)
  simp only [Names.localName, hne, ↓reduceIte, namesOther, Bool.and_eq_true, List.any_eq_true,
    bne_iff_ne, ne_eq]
  refine ⟨by simp, k, hms, ?_⟩
  rw [takeWhile_slash hp]
  exact ⟨by simpa using hne, couldBeShownAs_prefixOf hk⟩

theorem namesOther_mono {me : Key} {n : Name} {ms ms' : List Key}
    (h : namesOther me n ms = true) (hsub : ∀ m ∈ ms, m ≠ me → m ∈ ms') :
    namesOther me n ms' = true := by
  simp only [namesOther, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq] at h ⊢
  obtain ⟨hc, m, hm, hne, hs⟩ := h
  exact ⟨hc, m, hsub m hm hne, hne, hs⟩

/-- A name of `me`'s own, among those prefixes were chosen clear of, is no other machine's. -/
theorem localName_ne_own {me k : Key} {machines : List Key} {own : List Str} {v w : Str}
    (hslash : ∀ m ∈ machines, NoSlash m) (hk : k ∈ machines) (hne : k ≠ me) (hw : w ∈ own) :
    Names.localName me (Names.assign machines own) k v ≠ w := by
  intro h
  have := Names.localName_injective (me := me) (own := own) hslash (k₁ := k) (k₂ := me)
    (Or.inr ⟨hne, hk⟩) (Or.inl ⟨rfl, hw⟩) (by rw [h]; simp [Names.localName])
  exact hne this.1

/-! ## Agreement -/

/-- What translation reads of keys, as musubi makes it: no `/` in any machine key's name or
suffix, every machine a parent knows known at the operation too (presence only learns
machines), and the other machines' keys jj's merge leaves being other machines'. -/
structure WF (ev : Ev) (f : Facts) : Prop where
  me : NoSlash ev.me
  parents : ∀ c r, Parent.op c r ∈ ev.parents → ∀ m ∈ machinesOf c, NoSlash m
  known : ∀ c r, Parent.op c r ∈ ev.parents → ∀ m ∈ machinesOf c, m ≠ ev.me → m ∈ f.known
  factsKnown : ∀ m ∈ f.known, NoSlash m
  others : ∀ k ∈ f.others, k.owner ≠ ev.me ∧ NoSlash k.owner

theorem contains_true {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    l.contains a = true ↔ a ∈ l := List.contains_iff_mem

theorem contains_false {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    l.contains a = false ↔ a ∉ l := by
  rw [Bool.eq_false_iff, Ne, List.contains_iff_mem]

theorem owner_mem_machinesOf {c : Canon} {k : WKey} (hk : k ∈ c.keys) : k.owner ∈ machinesOf c :=
  List.mem_append_right _ (List.mem_map_of_mem hk)

theorem noSlash_sort {me : Key} {c : Canon} (hme : NoSlash me) (h : ∀ m ∈ machinesOf c, NoSlash m) :
    ∀ m ∈ sortKeys (me :: machinesOf c), NoSlash m := by
  intro m hm
  rcases List.mem_cons.mp (mem_sortKeys.mp hm) with rfl | hm
  · exact hme
  · exact h m hm

theorem mem_sort_owner {me : Key} {c : Canon} {k : WKey} (hk : k ∈ c.keys) :
    k.owner ∈ sortKeys (me :: machinesOf c) :=
  mem_sortKeys.mpr (List.mem_cons_of_mem _ (owner_mem_machinesOf hk))

theorem mem_othersOf {me : Key} {c : Canon} {clear : List Name} {n : Name} :
    n ∈ othersOf me c clear ↔ ∃ k ∈ c.keys, k.owner ≠ me ∧ nameOf me c clear k = n := by
  simp [othersOf, List.mem_map, List.mem_filter, and_assoc]

/-- A name `me` owns in a canonical view, or keeps privately, is no other machine's there. -/
theorem not_mem_othersOf {me : Key} {c : Canon} {clear : List Name} {n : Name}
    (hme : NoSlash me) (hs : ∀ m ∈ machinesOf c, NoSlash m) (hn : n ∈ ownNamesIn me c ++ clear) :
    n ∉ othersOf me c clear := by
  intro h
  obtain ⟨k, hk, hne, rfl⟩ := mem_othersOf.mp h
  exact localName_ne_own (noSlash_sort hme hs) (mem_sort_owner hk) hne hn rfl

/-- Another machine's workspace in a canonical view is shown as a known other machine's. -/
theorem namesOther_of_mem_othersOf {me : Key} {c : Canon} {clear : List Name} {n : Name}
    {ms : List Key} (hme : NoSlash me) (hs : ∀ m ∈ machinesOf c, NoSlash m)
    (hms : ∀ m ∈ machinesOf c, m ≠ me → m ∈ ms) (h : n ∈ othersOf me c clear) :
    namesOther me n ms = true := by
  obtain ⟨k, hk, hne, rfl⟩ := mem_othersOf.mp h
  exact namesOther_localName (noSlash_sort hme hs) (mem_sort_owner hk) hne
    (hms _ (owner_mem_machinesOf hk) hne)

theorem mem_parentOthers {ev : Ev} {n : Name} :
    n ∈ ev.parentOthers ↔
      ∃ c r, Parent.op c r ∈ ev.parents ∧ n ∈ othersOf ev.me c (ev.priv ++ r) := by
  simp only [Ev.parentOthers, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hn⟩
    cases p with
    | root => simp at hn
    | op c r => exact ⟨c, r, hp, hn⟩
  · rintro ⟨c, r, hp, hn⟩
    exact ⟨_, hp, hn⟩

theorem mem_parentOwn {ev : Ev} {n : Name} :
    n ∈ ev.parentOwn ↔ ∃ c r, Parent.op c r ∈ ev.parents ∧ n ∈ ownNamesIn ev.me c := by
  simp only [Ev.parentOwn, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hn⟩
    cases p with
    | root => simp at hn
    | op c r => exact ⟨c, r, hp, hn⟩
  · rintro ⟨c, r, hp, hn⟩
    exact ⟨_, hp, hn⟩

theorem mem_inheritedMachines {ev : Ev} {m : Key} :
    m ∈ ev.inheritedMachines ↔ (∃ c r, Parent.op c r ∈ ev.parents ∧ m ∈ machinesOf c) ∨
      m ∈ ev.ctxKnown := by
  simp only [Ev.inheritedMachines, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (⟨p, hp, hm⟩ | hm)
    · cases p with
      | root => simp at hm
      | op c r => exact Or.inl ⟨c, r, hp, hm⟩
    · exact Or.inr hm
  · rintro (⟨c, r, hp, hm⟩ | hm)
    · exact Or.inl ⟨_, hp, hm⟩
    · exact Or.inr hm

theorem priv_mem_inheritedOwn {ev : Ev} {n : Name} (h : n ∈ ev.priv) : n ∈ ev.inheritedOwn := by
  simp [Ev.inheritedOwn, h]

theorem mem_owned {ev : Ev} {n : Name} :
    n ∈ owned ev ↔ n ∈ ev.view ∧ ev.removed n = false ∧
      (ev.stale n = false ∨ ev.keepStale n = true) := by
  simp [owned, List.mem_filter]

theorem ownKeys_canonView {ev : Ev} {f : Facts} (hp : f.present = true)
    (ho : ∀ k ∈ f.others, k.owner ≠ ev.me) {n : Name} :
    n ∈ ownKeys ev.me (canonView ev f) ↔ n ∈ owned ev := by
  simp only [ownKeys, canonView, hp, ↓reduceIte, List.mem_filterMap, List.mem_append,
    List.mem_map]
  constructor
  · rintro ⟨k, hk | ⟨n', hn', rfl⟩, h⟩
    · simp [ho k hk] at h
    · simp only [↓reduceIte, Option.some.injEq] at h
      exact h ▸ hn'
  · intro h
    exact ⟨⟨ev.me, n⟩, Or.inr ⟨n, h, rfl⟩, by simp⟩

theorem ownNamesIn_present {me : Key} {c : Canon} (h : c.present = true) :
    ownNamesIn me c = ownKeys me c := by
  unfold ownNamesIn
  split
  · simp_all
  · rfl

theorem mem_ownNames_present {me : Key} {c : Canon} {n : Name} (h : c.present = true) :
    n ∈ ownNames me c ↔ n ∈ ownKeys me c := by
  unfold ownNames
  split <;> simp [ownNamesIn_present h]

/-- **Agreement.** Where this machine is present, `own_of_view`, reading only the canonical
operation `canonical_view` wrote, its context and the private names, owns exactly the names
`canonical_view` put under this machine's key. -/
theorem agreement (ev : Ev) (f : Facts) (hp : f.present = true) (hw : WF ev f) (n : Name) :
    n ∈ ownOfView ev.me ev.view ev.priv (canonView ev f) ↔ n ∈ owned ev := by
  have hC : (canonView ev f).present = true := hp
  have hown : n ∈ ownNames ev.me (canonView ev f) ↔ n ∈ owned ev :=
    (mem_ownNames_present hC).trans (ownKeys_canonView hp (fun k hk => (hw.others k hk).1))
  have hmC : ∀ m ∈ machinesOf (canonView ev f), NoSlash m := by
    intro m hm
    simp only [machinesOf, canonView, hp, ↓reduceIte, List.mem_append, List.map_append,
      List.mem_map] at hm
    rcases hm with hm | ⟨k, hk, rfl⟩ | ⟨k, ⟨_, _, rfl⟩, rfl⟩
    · exact hw.factsKnown m hm
    · exact (hw.others k hk).2
    · exact hw.me
  -- Every machine the parents and the context know, the canonical operation and its
  -- context know.
  have hsub : ∀ m ∈ ev.inheritedMachines, m ≠ ev.me →
      m ∈ machinesOf (canonView ev f) ++ knownOf (ctxFor ev.me (canonView ev f).context) := by
    intro m hm hne
    rcases mem_inheritedMachines.mp hm with ⟨c, r, hc, hm⟩ | hm
    · exact List.mem_append_left _ (List.mem_append_left _ (hw.known c r hc m hm hne))
    · exact List.mem_append_right _ hm
  have hmC' : ∀ c r, Parent.op c r ∈ ev.parents → ∀ m ∈ machinesOf c, m ≠ ev.me →
      m ∈ machinesOf (canonView ev f) ++ knownOf (ctxFor ev.me (canonView ev f).context) :=
    fun c r hc m hm hne =>
      List.mem_append_left _ (List.mem_append_left _ (hw.known c r hc m hm hne))
  constructor
  · intro h
    simp only [ownOfView, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_true, contains_true, contains_false] at h
    obtain ⟨hv, -, hcase⟩ := h
    rcases hcase with (hpriv | hownC) | ⟨hctx, hnames⟩
    · -- A private name: no canonical parent shows another machine's workspace under it,
      -- and the context and the alias rule yield to it.
      have hin := priv_mem_inheritedOwn hpriv
      refine mem_owned.mpr ⟨hv, ?_, Or.inl ?_⟩
      · simp only [Ev.removed, Bool.and_eq_false_iff]
        left
        simp only [contains_false, Ev.others, List.mem_append, not_or]
        constructor
        · intro hpo
          obtain ⟨c, r, hc, ho⟩ := mem_parentOthers.mp hpo
          exact not_mem_othersOf hw.me (hw.parents c r hc)
            (List.mem_append_right _ (List.mem_append_left _ hpriv)) ho
        · intro hco
          simp only [Ev.ctxOthers, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
            contains_false] at hco
          exact hco.2.1 hin
      · simp [Ev.stale, hin]
    · exact hown.mp hownC
    · -- Neither the context nor the alias rule gives it another machine.
      have hnot : namesOther ev.me n
          (machinesOf (canonView ev f) ++ knownOf (ctxFor ev.me (canonView ev f).context)) ≠
          true := by simp [hnames]
      refine mem_owned.mpr ⟨hv, ?_, Or.inl ?_⟩
      · simp only [Ev.removed, Bool.and_eq_false_iff]
        left
        simp only [contains_false, Ev.others, List.mem_append, not_or]
        constructor
        · intro hpo
          obtain ⟨c, r, hc, ho⟩ := mem_parentOthers.mp hpo
          exact hnot (namesOther_of_mem_othersOf hw.me (hw.parents c r hc) (hmC' c r hc) ho)
        · intro hco
          simp only [Ev.ctxOthers, List.mem_filter] at hco
          exact hctx hco.1
      · simp only [Ev.stale, Bool.and_eq_false_iff]
        right
        rw [Bool.eq_false_iff]
        exact fun h => hnot (namesOther_mono h hsub)
  · intro h
    have hv := (mem_owned.mp h).1
    have hk : n ∈ ownKeys ev.me (canonView ev f) :=
      (ownKeys_canonView hp (fun k hk => (hw.others k hk).1)).mpr h
    simp only [ownOfView, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_true, contains_true, contains_false]
    refine ⟨hv, ?_, Or.inl (Or.inr (hown.mpr h))⟩
    exact not_mem_othersOf hw.me hmC
      (List.mem_append_left _ (by rw [ownNamesIn_present hC]; exact hk))

/-! ## `owned` computes `Owns` -/

theorem mem_inheritedOwn {ev : Ev} {n : Name} : n ∈ ev.inheritedOwn ↔ ev.OwnClaim n := by
  simp only [Ev.inheritedOwn, Ev.OwnClaim, List.mem_append, mem_parentOwn, Ev.ctxOwn, ownOf]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · split at h
      · next hb =>
        right; right
        refine ⟨hb, ?_⟩
        cases hx : ev.ctx with
        | none => simp [hx] at h
        | some x =>
          simp only [hx, List.mem_map, List.mem_filter, beq_iff_eq] at h
          obtain ⟨⟨n', k⟩, ⟨hk, hown⟩, rfl⟩ := h
          exact ⟨x, rfl, k, hk, hown⟩
      · simp at h
  · rintro (h | h | ⟨hb, x, hx, k, hk, hown⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · right
      simp only [hb, ↓reduceIte]
      have hx : ev.ctx = some x := hx
      simp only [hx, List.mem_map, List.mem_filter, beq_iff_eq]
      exact ⟨(n, k), ⟨hk, hown⟩, rfl⟩

theorem mem_ctxForeign {ev : Ev} {n : Name} :
    n ∈ ev.ctxForeign ↔ ∃ x ∈ ev.ctx, ∃ k, (n, k) ∈ x.names ∧ k.owner ≠ ev.me := by
  simp only [Ev.ctxForeign, foreignOf]
  cases hx : ev.ctx with
  | none => simp
  | some x =>
    simp only [List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, Option.mem_def,
      Option.some.injEq]
    constructor
    · rintro ⟨⟨n', k⟩, ⟨hk, hown⟩, rfl⟩
      exact ⟨x, rfl, k, hk, hown⟩
    · rintro ⟨_, rfl, k, hk, hown⟩
      exact ⟨(n, k), ⟨hk, hown⟩, rfl⟩

theorem admits_iff {ev : Ev} {n : Name} :
    ev.admits n = true ↔ (ev.basis = .parents → n ∈ ev.start) := by
  unfold Ev.admits
  split <;> simp_all

theorem mem_ctxOthers {ev : Ev} {n : Name} : n ∈ ev.ctxOthers ↔ ev.CtxGives n := by
  simp only [Ev.ctxOthers, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', contains_false,
    mem_inheritedOwn, admits_iff, mem_ctxForeign, Ev.CtxGives]

theorem mem_others {ev : Ev} {n : Name} : n ∈ ev.others ↔ ev.ShownOther n := by
  simp only [Ev.others, List.mem_append, mem_parentOthers, mem_othersOf, mem_ctxOthers,
    Ev.ShownOther]

theorem mem_captured {ev : Ev} {n : Name} :
    n ∈ ev.captured ↔ ev.basis ≠ .parents ∧ ev.CtxGives n := by
  unfold Ev.captured
  split <;> simp_all [mem_ctxOthers]

theorem removed_iff {ev : Ev} {n : Name} : ev.removed n = true ↔ ev.ShownOther n ∧ ¬ ev.Made n := by
  have ho : ev.others.contains n = true ↔ ev.ShownOther n := contains_true.trans mem_others
  have hm : ev.mayMake = true ↔ ev.command = true ∧ ∃ m ∈ ev.view, ev.ShownOther m := by
    simp only [Ev.mayMake, Bool.and_eq_true, List.any_eq_true, contains_true, mem_others]
    constructor
    · rintro ⟨h, m, h1, h2⟩; exact ⟨h, m, h2, h1⟩
    · rintro ⟨h, m, h1, h2⟩; exact ⟨h, m, h2, h1⟩
  have hs : ev.startedFrom.contains n = true ↔ n ∈ ev.startedFrom := contains_true
  have hc : ev.captured.contains n = true ↔ ev.basis ≠ .parents ∧ ev.CtxGives n :=
    contains_true.trans mem_captured
  have hMade : ev.Made n ↔ ev.mayMake = true ∧ ev.startedFrom.contains n = false ∧
      ev.captured.contains n = false := by
    simp only [Ev.Made, hm, Bool.eq_false_iff, ne_eq, hs, hc, and_assoc]
  rw [hMade, ← ho]
  unfold Ev.removed
  cases ev.others.contains n <;> cases ev.mayMake <;> cases ev.startedFrom.contains n <;>
    cases ev.captured.contains n <;> simp

theorem namesOther_iff {ev : Ev} {n : Name} :
    namesOther ev.me n ev.inheritedMachines = true ↔ ev.LooksOther n := by
  simp only [namesOther, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    mem_inheritedMachines,
    Ev.LooksOther, Ev.Knows]

theorem stale_iff {ev : Ev} {n : Name} : ev.stale n = true ↔ ¬ ev.OwnClaim n ∧ ev.LooksOther n := by
  simp only [Ev.stale, Bool.and_eq_true, Bool.not_eq_true', contains_false, mem_inheritedOwn,
    namesOther_iff]

theorem keepStale_iff {ev : Ev} {n : Name} : ev.keepStale n = true ↔ ev.MadeStale n := by
  unfold Ev.keepStale Ev.MadeStale
  split <;> simp

/-- `owned` computes `Owns`. -/
theorem mem_owned_iff {ev : Ev} {n : Name} : n ∈ owned ev ↔ Owns ev n := by
  rw [mem_owned, Owns]
  have h1 : ev.removed n = false ↔ (ev.ShownOther n → ev.Made n) := by
    rw [Bool.eq_false_iff, Ne, removed_iff]
    constructor
    · intro h hs; exact Classical.byContradiction fun hm => h ⟨hs, hm⟩
    · rintro h ⟨hs, hm⟩; exact hm (h hs)
  have h2 : (ev.stale n = false ∨ ev.keepStale n = true) ↔
      (¬ ev.OwnClaim n → ev.LooksOther n → ev.MadeStale n) := by
    rw [Bool.eq_false_iff, Ne, stale_iff, keepStale_iff]
    constructor
    · rintro (h | h) ho hl
      · exact absurd ⟨ho, hl⟩ h
      · exact h
    · intro h
      by_cases ho : ev.OwnClaim n
      · exact Or.inl fun h' => h'.1 ho
      · by_cases hl : ev.LooksOther n
        · exact Or.inr (h ho hl)
        · exact Or.inl fun h' => hl h'.2
  rw [h1, h2]

/-- **Agreement**, against ownership as defined: where this machine is present, the names
`canonical_view` puts under its key, and those `own_of_view` owns reading that operation, are
exactly those it owns. -/
theorem canonical_owns (ev : Ev) (f : Facts) (hp : f.present = true)
    (ho : ∀ k ∈ f.others, k.owner ≠ ev.me) (n : Name) :
    n ∈ ownKeys ev.me (canonView ev f) ↔ Owns ev n :=
  (ownKeys_canonView hp ho).trans mem_owned_iff

theorem ownOfView_owns (ev : Ev) (f : Facts) (hp : f.present = true) (hw : WF ev f) (n : Name) :
    n ∈ ownOfView ev.me ev.view ev.priv (canonView ev f) ↔ Owns ev n :=
  (agreement ev f hp hw n).trans mem_owned_iff

/-! ## Ownership of a command, in two plain forms -/

/-- A command whose own context gives no name to another machine where a canonical parent
already did, judged against its parents (`Basis.parents`): it owns a name in its view that the
evidence makes its own, that isn't shown as a known other machine's, or that it made. -/
theorem owns_simple {ev : Ev} (hc : ev.command = true) (hs : ev.source = .parents)
    (hb : ev.basis = .parents)
    (hshown : ∀ n ∈ ev.view, ev.ShownOther n → ¬ ev.OwnClaim n ∧ ev.LooksOther n) (n : Name) :
    Owns ev n ↔ n ∈ ev.view ∧ (ev.OwnClaim n ∨ ¬ ev.LooksOther n ∨ n ∉ ev.start) := by
  have hsf : ev.startedFrom = ev.start := by simp [Ev.startedFrom, hs]
  have hms : ev.MadeStale n ↔ n ∉ ev.start := by simp [Ev.MadeStale, hs]
  have hmade : ev.Made n ↔ (∃ m ∈ ev.view, ev.ShownOther m) ∧ n ∉ ev.start := by
    simp [Ev.Made, hc, hsf, hb]
  rw [Owns, hms, hmade]
  constructor
  · rintro ⟨hv, -, h⟩
    refine ⟨hv, ?_⟩
    rcases Classical.em (ev.OwnClaim n) with ho | ho
    · exact Or.inl ho
    · rcases Classical.em (ev.LooksOther n) with hl | hl
      · exact Or.inr (Or.inr (h ho hl))
      · exact Or.inr (Or.inl hl)
  · rintro ⟨hv, h⟩
    have hstart : ¬ ev.OwnClaim n → ev.LooksOther n → n ∉ ev.start := fun ho hl =>
      (h.resolve_left ho).resolve_left (fun h' => h' hl)
    refine ⟨hv, fun hsh => ⟨⟨n, hv, hsh⟩, ?_⟩, hstart⟩
    exact hstart (hshown n hv hsh).1 (hshown n hv hsh).2

theorem basis_root {ev : Ev} (h : ev.parents = [.root]) : ev.basis = .initial := by
  simp [Ev.basis, h]

theorem not_parentOthers_root {ev : Ev} (h : ev.parents = [.root]) (n : Name) :
    ¬ ∃ c r, Parent.op c r ∈ ev.parents ∧
      ∃ k ∈ c.keys, k.owner ≠ ev.me ∧ nameOf ev.me c (ev.priv ++ r) k = n := by
  rintro ⟨c, r, hc, -⟩
  simp [h] at hc

/-- A command on the root alone, judged by its context (`Basis.initial`): it owns a name in its
view that the context doesn't give another machine, and that the evidence makes its own, that
isn't shown as a known other machine's, or that it made. -/
theorem owns_initial {ev : Ev} (hs : ev.source = .parents)
    (hp : ev.parents = [.root]) (n : Name) :
    Owns ev n ↔ n ∈ ev.view ∧ ¬ ev.CtxGives n ∧
      (ev.OwnClaim n ∨ ¬ ev.LooksOther n ∨ n ∉ ev.start) := by
  have hb := basis_root hp
  have hms : ev.MadeStale n ↔ n ∉ ev.start := by simp [Ev.MadeStale, hs]
  have hshown : ev.ShownOther n ↔ ev.CtxGives n := by
    simp only [Ev.ShownOther]
    constructor
    · rintro (h | h)
      · exact absurd h (not_parentOthers_root hp n)
      · exact h
    · exact Or.inr
  have hmade : ev.ShownOther n → ev.Made n ↔ ¬ ev.CtxGives n := by
    rw [hshown]
    simp only [Ev.Made, hb, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    constructor
    · intro h hg; exact (h hg).2.2.2 hg
    · intro h hg; exact absurd hg h
  rw [Owns, hms, hmade]
  constructor
  · rintro ⟨hv, hg, h⟩
    refine ⟨hv, hg, ?_⟩
    rcases Classical.em (ev.OwnClaim n) with ho | ho
    · exact Or.inl ho
    · rcases Classical.em (ev.LooksOther n) with hl | hl
      · exact Or.inr (Or.inr (h ho hl))
      · exact Or.inr (Or.inl hl)
  · rintro ⟨hv, hg, h⟩
    exact ⟨hv, hg, fun ho hl => (h.resolve_left ho).resolve_left (fun h' => h' hl)⟩

/-- `LooksOther` reads only the other machines known. -/
theorem looksOther_congr {a b : Ev} (hme : a.me = b.me)
    (hn : ∀ m, m ≠ a.me → (a.Knows m ↔ b.Knows m))
    (n : Name) : a.LooksOther n ↔ b.LooksOther n := by
  simp only [Ev.LooksOther]
  constructor
  · rintro ⟨hc, m, hk, hne, hs⟩
    exact ⟨hc, m, (hn m hne).mp hk, hme ▸ hne, hs⟩
  · rintro ⟨hc, m, hk, hne, hs⟩
    exact ⟨hc, m, (hn m (hme ▸ hne)).mpr hk, hme ▸ hne, hs⟩

theorem looksOther_of_namesOther {ev : Ev} {n : Name} {ms : List Key}
    (h : namesOther ev.me n ms = true) (hsub : ∀ m ∈ ms, m ≠ ev.me → ev.Knows m) :
    ev.LooksOther n := by
  simp only [namesOther, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hc, m, hm, hne, hs⟩ := h
  exact ⟨hc, m, hsub m hm hne, hne, hs⟩


/-! ## Histories: commands, merges, trims to the root, and commands from before a trim

A history is this machine's local operations, as translated. It starts from realizations of
canonical operations from the hive (`bases`), which may know different machines, and each step
is a `jj` command on earlier operations, its parents: any of them, as `jj --at-op` writes, or a
merge of several, as jj reconciles divergent operations. A trim (`jj op abandon` of the whole
history) takes every canonical form so far away. A command whose parents all come from before a
trim is translated on the root alone, with a context recomputed from its translation on its
parents' canonical forms (`canonical_form`'s source translation), which reads the contexts they
carry and keeps their other machines' names and the machines they know. A command on operations
since carries their contexts, folded together at a merge (`carried_context`).

Each operation also has the canonical form it would have had with no trim (`Node.ref`), read
from the same views and private names: the untrimmed history's evidence.
`trims_keep_ownership` proves the two own the same names.

Not modeled: a merge of an operation from before a trim with one since, and a merge where a
parent shows another machine's workspace under a name this machine owns at another parent,
as a `jj` command racing a sync can make (docs/internals/races.md, "Copies that go away");
`stepNodes` leaves the history as it is for those. A merge's canonical operation has every
parent's other workspaces, as jj's merge of them would keep them all. -/

/-- A local operation, translated: its view, the private names it reads, those it records if
it is marked (a realization, or a late operation's rewrite), its canonical form, the one the
untrimmed history gives it, and whether a trim has since taken its canonical form away. -/
structure Node where
  view : List Name
  priv : List Name
  record : Option (List Name)
  canon : Canon
  ref : Canon
  trimmed : Bool
  /-- Whether it realizes a canonical operation from the hive, rather than a command here. -/
  realized : Bool := false

/-- The private names a child of `x` reads, before its own view (`private_workspace_names`):
those `x` records where it is marked, those it reads otherwise, each still in `x`'s view. -/
def Node.privAt (x : Node) : List Name :=
  match x.record with
  | some r => r.filter (x.view.contains ·)
  | none => x.priv

inductive Step where
  /-- A `jj` command on the nodes `parents`, leaving the local view `view` (jj's effect). -/
  | command (parents : List Nat) (view : List Name)
  /-- A trim: every canonical form so far is taken away. -/
  | trim
  /-- A realization of `c`, a canonical operation from the hive, with local view `view` and the
  private names it records: another machine's work arriving, before a trim or after one, as a
  workspace renamed. -/
  | realize (c : Canon) (view : List Name) (record : Option (List Name))

/-- A command on `ps` with view `view`, translated on canonical `parents` with `context`. -/
def commandEv (me : Key) (ps : List Node) (view : List Name) (parents : List Parent)
    (context : Option Context) : Ev where
  me := me
  view := view
  priv := (ps.flatMap Node.privAt).filter (view.contains ·)
  parents := parents
  start := ps.flatMap (·.view)
  command := true
  context := context

def onParents (cs : List Canon) : List Parent := cs.map fun c => .op c []

/-- What a command's canonical operation on parents `cs` gets: it is this machine's work, which
is known from then on, with every machine the parents know, and the parents' other machines'
workspaces. -/
def mergeFacts (me : Key) (cs : List Canon) : Facts where
  present := true
  known := cs.flatMap (·.known) ++ [me]
  others := cs.flatMap fun c => c.keys.filter (·.owner != me)

/-- The same, on the root alone. -/
def rootFacts (me : Key) : Facts := { present := true, known := [me], others := [] }

/-- The presence before a command's own effect, as naming its recomputed context reads it:
exactly its parent's for one parent. For several, which only a merge after a trim reads, it
approximates `Presence::merge`, which can find this machine absent where one parent forgot it;
the presence only chooses the prefixes the context names other machines' workspaces under, and
no theorem here depends on which. -/
def mergedPresence (cs : List Canon) : Canon where
  keys := []
  known := cs.flatMap (·.known)
  present := cs.any (·.present)
  worked := cs.findSome? (·.worked)

/-- The context `workspace_context_of_view` records for canonical view `s`, judged by the
presence `src` gives before the operation's own effect: each key's local name, and every
machine known. -/
def contextView (s src : Canon) : Canon :=
  { s with known := src.known, present := src.present, worked := src.worked }

def contextOf (me : Key) (s src : Canon) : Context where
  source := me
  names := (contextView s src).keys.map fun k => (nameOf me (contextView s src) (ownKeys me s) k, k)
  known := sortKeys (me :: machinesOf (contextView s src))

/-- `Namespace::keep_others_of`: what `carried` says of other machines, the machines it knows
and the names it gives them, unless `x` has the name already or gives the workspace another. -/
def keepOthers (x carried : Context) : Context :=
  { x with
    known := x.known ++ carried.known
    names := x.names ++ carried.names.filter fun e =>
      e.2.owner != x.source && !(x.names.any (·.1 == e.1)) && !(x.names.any (·.2 == e.2)) }

/-- `carried_context`: the first parent's context, with what each other parent's says of other
machines folded in. -/
def carriedOf (me : Key) (cs : List Canon) : Option Context :=
  match cs.filterMap (fun c => ctxFor me c.context) with
  | [] => none
  | c :: rest => some (rest.foldl keepOthers c)

/-- `Namespace::take_others_of`: what `recorded`, the context an operation itself records, gives
other machines, as `keepOthers` adds it, but over a name `x` gives this machine. -/
def takeOthers (x recorded : Context) : Context :=
  let added := recorded.names.filter fun e =>
    e.2.owner != x.source && !(x.names.any fun f => f.1 == e.1 && f.2.owner != x.source) &&
      !(x.names.any (·.2 == e.2))
  { x with
    known := x.known ++ recorded.known
    names := x.names.filter (fun f => !(added.any (·.1 == f.1))) ++ added }

/-- `canonical_form`'s recomputed context for an operation on canonical parents `cs` whose
parents changed, from its translation `src` on them, as fixed for one that records a context of
its own (`recorded`), as a trim leaves on the operation it keeps: that context's other machines'
names are taken over the names `src` gives this machine, then the carried contexts' kept. -/
def recompute (me : Key) (cs : List Canon) (src : Ev) (recorded : Option Context) : Context :=
  let x := contextOf me (canonView src (mergeFacts me cs)) (mergedPresence cs)
  let x := match ctxFor me recorded with
    | some r => takeOthers x r
    | none => x
  match carriedOf me cs with
  | some c => keepOthers x c
  | none => x

/-- The context of a command on parents `cs` after a trim, recomputed from its translation `src`
on them, which reads the contexts they carry. -/
def capture (me : Key) (cs : List Canon) (src : Ev) : Context :=
  let x := contextOf me (canonView src (mergeFacts me cs)) (mergedPresence cs)
  match carriedOf me cs with
  | some c => keepOthers x c
  | none => x

/-- The context a command on canonical parents `cs` carries, until their histories know every
machine it does. -/
def carriedKept (me : Key) (cs : List Canon) : Option Context :=
  match carriedOf me cs with
  | some x => if x.known.all ((cs.flatMap (·.known)).contains ·) then none else some x
  | none => none

/-- What `record_private_workspaces` records of `own_of_view`'s verdict: nothing, if the
canonical operation's own names have all of it. -/
def recordOf (me : Key) (view priv : List Name) (c : Canon) : List Name :=
  let own := ownOfView me view priv c
  if own.all ((ownNames me c).contains ·) then [] else own

/-- No name in the view is shown as another machine's at one parent and owned at another. -/
def clashFree (me : Key) (priv view : List Name) (cs : List Canon) : Bool :=
  view.all fun n => !(cs.any fun q => (othersOf me q (priv ++ [])).contains n) ||
    !(cs.any fun c => (ownNamesIn me c).contains n)

def noSlashB (k : Key) : Bool := !k.name.contains '/' && !k.suffix.contains '/'

theorem noSlash_of {k : Key} (h : noSlashB k = true) : NoSlash k := by
  simp only [noSlashB, Bool.and_eq_true, Bool.not_eq_true', contains_false] at h
  exact h

/-- A canonical operation a realization can stand for: one from the hive, carrying no context of
this machine's, with machine keys as musubi makes them. -/
def hiveB (c : Canon) : Bool := c.context.isNone && (machinesOf c).all noSlashB

def stepNodes (me : Key) (nodes : List Node) : Step → List Node
  | .trim => nodes.map fun x => { x with trimmed := true }
  | .realize c view record =>
    if hiveB c then
      nodes ++ [{ view, priv := [], record, canon := c, ref := c, trimmed := false,
                  realized := true }]
    else nodes
  | .command is view =>
    match is.mapM (nodes[·]?) with
    | none => nodes
    | some ps =>
      let cs := ps.map (·.canon)
      let rs := ps.map (·.ref)
      let priv := (ps.flatMap Node.privAt).filter (view.contains ·)
      if ps.isEmpty || !clashFree me priv view cs || !clashFree me priv view rs then nodes
      else
        let ref := canonView (commandEv me ps view (onParents rs) none) (mergeFacts me rs)
        if ps.all (·.trimmed) then
          let ctx := capture me cs (commandEv me ps view (onParents cs) (carriedOf me cs))
          let a := commandEv me ps view [.root] (some ctx)
          let canon := canonView a (rootFacts me)
          nodes ++ [{ view, priv := a.priv, record := some (recordOf me view a.priv canon),
                      canon, ref, trimmed := false }]
        else if ps.any (·.trimmed) then nodes
        else
          let a := commandEv me ps view (onParents cs) (carriedKept me cs)
          nodes ++ [{ view, priv := a.priv, record := none,
                      canon := canonView a (mergeFacts me cs), ref, trimmed := false }]

/-- The histories that start from `bases`, realizations of canonical operations from the hive. -/
inductive Reach (me : Key) (bases : List Node) : List Node → Prop
  | init : Reach me bases bases
  | step {nodes : List Node} (s : Step) :
      Reach me bases nodes → Reach me bases (stepNodes me nodes s)

/-! ### What every step keeps -/

def ctxNames : Option Context → List (Name × WKey)
  | some c => c.names
  | none => []

/-- A node's canonical form owns what its untrimmed one owns; it and the context it carries
know the same other machines; the context gives other machines only names shown as theirs;
machine keys are as musubi makes them; and the private record it writes, if any, is empty,
unless it realizes a canonical operation from the hive, as a base or a realization does. -/
structure NodeOK (me : Key) (bases : List Node) (x : Node) : Prop where
  own : ∀ n, n ∈ ownNamesIn me x.canon ↔ n ∈ ownNamesIn me x.ref
  knows : ∀ m, m ≠ me →
    (m ∈ machinesOf x.canon ∨ m ∈ knownOf (ctxFor me x.canon.context) ↔ m ∈ machinesOf x.ref)
  aliases : ∀ e ∈ ctxNames (ctxFor me x.canon.context), e.2.owner ≠ me →
    namesOther me e.1 (knownOf (ctxFor me x.canon.context)) = true
  slashCanon : ∀ m ∈ machinesOf x.canon, NoSlash m
  slashRef : ∀ m ∈ machinesOf x.ref, NoSlash m
  same : x.canon = x.ref ∨ (x.canon.present = true ∧ x.ref.present = true)
  record : x.record = none ∨ x.record = some [] ∨ x.realized = true

/-- A history's start: a realization of a canonical operation from the hive, which carries no
context of this machine's, with machine keys as musubi makes them. -/
structure BaseOK (x : Node) : Prop where
  realized : x.realized = true
  ref : x.canon = x.ref
  context : x.canon.context = none
  slash : ∀ m ∈ machinesOf x.canon, NoSlash m

theorem exists_mem_map' {α β : Type} {f : α → β} {l : List α} {P : β → Prop} :
    (∃ b ∈ l.map f, P b) ↔ ∃ a ∈ l, P (f a) := by
  constructor
  · rintro ⟨b, hb, h⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨f a, List.mem_map_of_mem ha, h⟩

section Steps

variable {me : Key} {ps : List Node} {view : List Name}

theorem mem_onParents {c : Canon} {r : List Name} {cs : List Canon} :
    Parent.op c r ∈ onParents cs ↔ c ∈ cs ∧ r = [] := by
  simp only [onParents, List.mem_map, Parent.op.injEq]
  constructor
  · rintro ⟨c', hc', rfl, rfl⟩; exact ⟨hc', rfl⟩
  · rintro ⟨hc, rfl⟩; exact ⟨c, hc, rfl, rfl⟩

theorem basis_onParents {cs : List Canon} {o : Option Context} :
    (commandEv me ps view (onParents cs) o).basis = .parents := by
  unfold Ev.basis
  split
  · next h =>
    cases cs with
    | nil => simp [commandEv, onParents] at h
    | cons c cs => simp [commandEv, onParents] at h
  · rfl

theorem knows_iff {cs : List Canon} {o : Option Context} {m : Key} :
    (commandEv me ps view (onParents cs) o).Knows m ↔
      (∃ c ∈ cs, m ∈ machinesOf c) ∨ m ∈ knownOf (ctxFor me o) := by
  simp only [Ev.Knows, Ev.ctxKnown, Ev.ctx, commandEv]
  constructor
  · rintro (⟨c, r, hc, hm⟩ | hm)
    · exact Or.inl ⟨c, (mem_onParents.mp hc).1, hm⟩
    · exact Or.inr hm
  · rintro (⟨c, hc, hm⟩ | hm)
    · exact Or.inl ⟨c, [], mem_onParents.mpr ⟨hc, rfl⟩, hm⟩
    · exact Or.inr hm

theorem claim_iff {cs : List Canon} {o : Option Context} {n : Name} :
    (commandEv me ps view (onParents cs) o).OwnClaim n ↔
      n ∈ (commandEv me ps view (onParents cs) o).priv ∨ ∃ c ∈ cs, n ∈ ownNamesIn me c := by
  simp only [Ev.OwnClaim, basis_onParents, reduceCtorEq, false_and, or_false]
  constructor
  · rintro (h | ⟨c, r, hc, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, (mem_onParents.mp hc).1, h⟩
  · rintro (h | ⟨c, hc, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, [], mem_onParents.mpr ⟨hc, rfl⟩, h⟩

/-- A command's evidence never contradicts itself: a name shown as another machine's, by a
parent or the context, is no name the evidence makes this machine's, and is shown as a known
other machine's. -/
theorem shown_ok {cs : List Canon} {o : Option Context} (hme : NoSlash me)
    (hs : ∀ c ∈ cs, ∀ m ∈ machinesOf c, NoSlash m)
    (hcf : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view cs = true)
    (hal : ∀ e ∈ ctxNames (ctxFor me o), e.2.owner ≠ me →
      namesOther me e.1 (knownOf (ctxFor me o)) = true) :
    ∀ n ∈ view, (commandEv me ps view (onParents cs) o).ShownOther n →
      ¬ (commandEv me ps view (onParents cs) o).OwnClaim n ∧
        (commandEv me ps view (onParents cs) o).LooksOther n := by
  intro n hv hsh
  rcases hsh with ⟨c, r, hc, k, hk, hne, rfl⟩ | ⟨⟨x, hx, k, hk, hne⟩, hno, -⟩
  · obtain ⟨hcs, rfl⟩ := mem_onParents.mp hc
    have hmem : nameOf me c ((commandEv me ps view (onParents cs) o).priv ++ []) k ∈
        othersOf me c ((commandEv me ps view (onParents cs) o).priv ++ []) :=
      mem_othersOf.mpr ⟨k, hk, hne, rfl⟩
    refine ⟨fun hown => ?_, ?_⟩
    · rcases claim_iff.mp hown with hp | ⟨c', hc', ho⟩
      · exact not_mem_othersOf hme (hs c hcs)
          (List.mem_append_right _ (List.mem_append_left _ hp)) hmem
      · have := List.all_eq_true.mp hcf _ hv
        simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false] at this
        rcases this with h | h
        · exact h c hcs (contains_true.mpr hmem)
        · exact h c' hc' (contains_true.mpr ho)
    · exact looksOther_of_namesOther
        (namesOther_of_mem_othersOf (ms := machinesOf c) hme (hs c hcs) (fun m hm _ => hm) hmem)
        (fun m hm _ => knows_iff.mpr (Or.inl ⟨c, hcs, hm⟩))
  · refine ⟨hno, ?_⟩
    have hx' : x ∈ ctxFor me o := hx
    cases hco : ctxFor me o with
    | none => rw [hco] at hx'; simp at hx'
    | some c =>
      rw [hco] at hx'
      simp only [Option.mem_def, Option.some.injEq] at hx'
      subst hx'
      have hn := hal (n, k) (by simp [ctxNames, hco, hk]) hne
      rw [hco] at hn
      exact looksOther_of_namesOther hn
        (fun m hm _ => knows_iff.mpr (Or.inr (by rw [hco]; exact hm)))

theorem priv_owns_ref (hme : NoSlash me) (hs : ∀ p ∈ ps, ∀ m ∈ machinesOf p.ref, NoSlash m)
    (hcf : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.ref)) = true) {n : Name}
    (h : n ∈ (commandEv me ps view (onParents (ps.map (·.ref))) none).priv) :
    Owns (commandEv me ps view (onParents (ps.map (·.ref))) none) n := by
  have hs' : ∀ c ∈ ps.map (·.ref), ∀ m ∈ machinesOf c, NoSlash m := by
    intro c hc m hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact hs p hp m hm
  have hv : n ∈ view := by
    simp only [commandEv, List.mem_filter, contains_true] at h
    exact h.2
  refine (owns_simple rfl rfl basis_onParents (shown_ok hme hs' hcf (by simp [ctxNames, ctxFor]))
    n).mpr ⟨hv, Or.inl (claim_iff.mpr (Or.inl h))⟩

/-- **A command below a trim**, on parents whose canonical forms own what their untrimmed ones
own and, with the context the command reads, know the same other machines: it owns what the
same command on the untrimmed parents owns. -/
theorem merge_owns {bases : List Node} {o : Option Context} (hme : NoSlash me)
    (hok : ∀ p ∈ ps, NodeOK me bases p)
    (hcfc : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.canon)) = true)
    (hcfr : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.ref)) = true)
    (hko : ∀ m, m ≠ me → ((∃ p ∈ ps, m ∈ machinesOf p.canon) ∨ m ∈ knownOf (ctxFor me o) ↔
      ∃ p ∈ ps, m ∈ machinesOf p.ref))
    (hal : ∀ e ∈ ctxNames (ctxFor me o), e.2.owner ≠ me →
      namesOther me e.1 (knownOf (ctxFor me o)) = true) (n : Name) :
    Owns (commandEv me ps view (onParents (ps.map (·.canon))) o) n ↔
      Owns (commandEv me ps view (onParents (ps.map (·.ref))) none) n := by
  have hsc : ∀ c ∈ ps.map (·.canon), ∀ m ∈ machinesOf c, NoSlash m := by
    intro c hc m hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact (hok p hp).slashCanon m hm
  have hsr : ∀ c ∈ ps.map (·.ref), ∀ m ∈ machinesOf c, NoSlash m := by
    intro c hc m hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact (hok p hp).slashRef m hm
  rw [owns_simple rfl rfl basis_onParents (shown_ok hme hsc hcfc hal) n,
    owns_simple rfl rfl basis_onParents
      (shown_ok hme hsr hcfr (by simp [ctxNames, ctxFor])) n]
  have hclaim : (commandEv me ps view (onParents (ps.map (·.canon))) o).OwnClaim n ↔
      (commandEv me ps view (onParents (ps.map (·.ref))) none).OwnClaim n := by
    rw [claim_iff, claim_iff]
    simp only [commandEv, exists_mem_map']
    constructor
    · rintro (h | ⟨p, hp, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, hp, ((hok p hp).own n).mp h⟩
    · rintro (h | ⟨p, hp, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, hp, ((hok p hp).own n).mpr h⟩
  have hknows : ∀ m, m ≠ (commandEv me ps view (onParents (ps.map (·.canon))) o).me →
      ((commandEv me ps view (onParents (ps.map (·.canon))) o).Knows m ↔
        (commandEv me ps view (onParents (ps.map (·.ref))) none).Knows m) := by
    intro m hne
    rw [knows_iff, knows_iff]
    simp only [exists_mem_map']
    rw [hko m hne]
    simp [ctxFor, knownOf]
  have hl := looksOther_congr
    (a := commandEv me ps view (onParents (ps.map (·.canon))) o)
    (b := commandEv me ps view (onParents (ps.map (·.ref))) none) rfl hknows n
  rw [hclaim, hl]
  rfl

/-! ### Folding contexts -/

theorem foldl_keepOthers_source :
    ∀ (rest : List Context) (c : Context), (rest.foldl keepOthers c).source = c.source
  | [], _ => rfl
  | d :: rest, c => by
    rw [List.foldl_cons, foldl_keepOthers_source rest]
    rfl

theorem mem_foldl_keepOthers_known :
    ∀ (rest : List Context) (c : Context) (m : Key),
      m ∈ (rest.foldl keepOthers c).known ↔ m ∈ c.known ∨ ∃ d ∈ rest, m ∈ d.known
  | [], _, _ => by simp
  | d :: rest, c, m => by
    rw [List.foldl_cons, mem_foldl_keepOthers_known rest]
    simp only [keepOthers, List.mem_append, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem mem_foldl_keepOthers_names :
    ∀ (rest : List Context) (c : Context) (e : Name × WKey),
      e ∈ (rest.foldl keepOthers c).names → e ∈ c.names ∨ ∃ d ∈ rest, e ∈ d.names
  | [], _, _, h => Or.inl h
  | d :: rest, c, e, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_keepOthers_names rest _ e h with h | ⟨d', hd', h⟩
    · simp only [keepOthers, List.mem_append, List.mem_filter] at h
      rcases h with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨d, List.mem_cons_self, h⟩
    · exact Or.inr ⟨d', List.mem_cons_of_mem _ hd', h⟩

theorem mem_ctxs {cs : List Canon} {x : Context} :
    x ∈ cs.filterMap (fun c => ctxFor me c.context) ↔ ∃ c ∈ cs, ctxFor me c.context = some x := by
  simp [List.mem_filterMap]

theorem ctxFor_source {o : Option Context} {x : Context} (h : ctxFor me o = some x) :
    x.source = me := by
  cases o with
  | none => simp [ctxFor] at h
  | some c =>
    simp only [ctxFor, Option.filter] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      simpa using hc
    · simp at h

theorem carriedOf_source {cs : List Canon} {x : Context} (h : carriedOf me cs = some x) :
    x.source = me := by
  unfold carriedOf at h
  split at h
  · simp at h
  · next c rest hcs =>
    simp only [Option.some.injEq] at h
    subst h
    rw [foldl_keepOthers_source]
    obtain ⟨c', -, hc'⟩ := mem_ctxs.mp (hcs ▸ List.mem_cons_self : c ∈ _)
    exact ctxFor_source hc'

theorem ctxFor_carried {cs : List Canon} : ctxFor me (carriedOf me cs) = carriedOf me cs := by
  cases h : carriedOf me cs with
  | none => rfl
  | some x => simp [ctxFor, Option.filter, carriedOf_source h]

theorem mem_known_carriedOf {cs : List Canon} {m : Key} :
    m ∈ knownOf (carriedOf me cs) ↔ ∃ c ∈ cs, m ∈ knownOf (ctxFor me c.context) := by
  unfold carriedOf
  split
  · next hcs =>
    simp only [knownOf, List.not_mem_nil, false_iff, not_exists, not_and]
    intro c hc hm
    cases hx : ctxFor me c.context with
    | none => rw [hx] at hm; simp at hm
    | some x =>
      have : x ∈ cs.filterMap (fun c => ctxFor me c.context) := mem_ctxs.mpr ⟨c, hc, hx⟩
      rw [hcs] at this
      simp at this
  · next c rest hcs =>
    simp only [knownOf, mem_foldl_keepOthers_known]
    have hmem : ∀ x, x ∈ c :: rest ↔ ∃ c' ∈ cs, ctxFor me c'.context = some x := by
      intro x; rw [← hcs]; exact mem_ctxs
    constructor
    · rintro (h | ⟨d, hd, h⟩)
      · obtain ⟨c', hc', hx⟩ := (hmem c).mp List.mem_cons_self
        exact ⟨c', hc', by rw [hx]; exact h⟩
      · obtain ⟨c', hc', hx⟩ := (hmem d).mp (List.mem_cons_of_mem _ hd)
        exact ⟨c', hc', by rw [hx]; exact h⟩
    · rintro ⟨c', hc', h⟩
      cases hx : ctxFor me c'.context with
      | none => rw [hx] at h; simp at h
      | some x =>
        rw [hx] at h
        rcases List.mem_cons.mp ((hmem x).mpr ⟨c', hc', hx⟩) with rfl | hx'
        · exact Or.inl h
        · exact Or.inr ⟨x, hx', h⟩

theorem mem_names_carriedOf {cs : List Canon} {e : Name × WKey}
    (h : e ∈ ctxNames (carriedOf me cs)) :
    ∃ c ∈ cs, e ∈ ctxNames (ctxFor me c.context) := by
  unfold carriedOf at h
  split at h
  · simp [ctxNames] at h
  · next c rest hcs =>
    have hmem : ∀ x, x ∈ c :: rest → ∃ c' ∈ cs, ctxFor me c'.context = some x := by
      intro x hx; rw [← hcs] at hx; exact mem_ctxs.mp hx
    rcases mem_foldl_keepOthers_names rest c e h with h | ⟨d, hd, h⟩
    · obtain ⟨c', hc', hx⟩ := hmem c List.mem_cons_self
      exact ⟨c', hc', by rw [hx]; exact h⟩
    · obtain ⟨c', hc', hx⟩ := hmem d (List.mem_cons_of_mem _ hd)
      exact ⟨c', hc', by rw [hx]; exact h⟩

end Steps

/-! ### The contexts a command reads fit its parents -/

section Fits

variable {me : Key} {ps : List Node} {view : List Name} {bases : List Node}

/-- With the contexts its parents carry folded together, a command knows exactly the other
machines its untrimmed parents know. -/
theorem carried_knows (hok : ∀ p ∈ ps, NodeOK me bases p) (m : Key) (hne : m ≠ me) :
    (∃ p ∈ ps, m ∈ machinesOf p.canon) ∨
        m ∈ knownOf (ctxFor me (carriedOf me (ps.map (·.canon)))) ↔
      ∃ p ∈ ps, m ∈ machinesOf p.ref := by
  rw [ctxFor_carried, mem_known_carriedOf, exists_mem_map']
  constructor
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, hp, ((hok p hp).knows m hne).mp (Or.inl h)⟩
    · exact ⟨p, hp, ((hok p hp).knows m hne).mp (Or.inr h)⟩
  · rintro ⟨p, hp, h⟩
    rcases ((hok p hp).knows m hne).mpr h with h | h
    · exact Or.inl ⟨p, hp, h⟩
    · exact Or.inr ⟨p, hp, h⟩

theorem carried_aliases (hok : ∀ p ∈ ps, NodeOK me bases p) :
    ∀ e ∈ ctxNames (ctxFor me (carriedOf me (ps.map (·.canon)))), e.2.owner ≠ me →
      namesOther me e.1 (knownOf (ctxFor me (carriedOf me (ps.map (·.canon))))) = true := by
  intro e he hne
  rw [ctxFor_carried] at he ⊢
  obtain ⟨c, hc, he⟩ := mem_names_carriedOf he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact namesOther_mono ((hok p hp).aliases e he hne)
    (fun m hm _ => mem_known_carriedOf.mpr ⟨p.canon, hc, hm⟩)

theorem kept_cases (cs : List Canon) :
    carriedKept me cs = carriedOf me cs ∨
      (carriedKept me cs = none ∧ ∀ m ∈ knownOf (carriedOf me cs), ∃ c ∈ cs, m ∈ c.known) := by
  unfold carriedKept
  cases h : carriedOf me cs with
  | none => exact Or.inl rfl
  | some x =>
    simp only
    split
    · next hall =>
      refine Or.inr ⟨rfl, fun m hm => ?_⟩
      have := List.all_eq_true.mp hall m hm
      simpa [List.mem_flatMap] using this
    · exact Or.inl rfl

theorem kept_knows (hok : ∀ p ∈ ps, NodeOK me bases p) (m : Key) (hne : m ≠ me) :
    (∃ p ∈ ps, m ∈ machinesOf p.canon) ∨
        m ∈ knownOf (ctxFor me (carriedKept me (ps.map (·.canon)))) ↔
      ∃ p ∈ ps, m ∈ machinesOf p.ref := by
  rcases kept_cases (me := me) (ps.map (·.canon)) with h | ⟨h, hsub⟩
  · rw [h]; exact carried_knows hok m hne
  · rw [h, ← carried_knows hok m hne, ctxFor_carried]
    rw [show knownOf (ctxFor me none) = [] from rfl]
    simp only [List.not_mem_nil, or_false]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · obtain ⟨c, hc, hm⟩ := hsub m h
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
        exact ⟨p, hp, List.mem_append_left _ hm⟩

theorem kept_aliases (hok : ∀ p ∈ ps, NodeOK me bases p) :
    ∀ e ∈ ctxNames (ctxFor me (carriedKept me (ps.map (·.canon)))), e.2.owner ≠ me →
      namesOther me e.1 (knownOf (ctxFor me (carriedKept me (ps.map (·.canon))))) = true := by
  rcases kept_cases (me := me) (ps.map (·.canon)) with h | ⟨h, -⟩
  · rw [h]; exact carried_aliases hok
  · rw [h]; simp [ctxNames, ctxFor, Option.filter]

end Fits

/-! ### A command after a trim -/

section Late

variable {me : Key} {ps : List Node} {view : List Name} {bases : List Node}

theorem capture_source {cs : List Canon} {src : Ev} : (capture me cs src).source = me := by
  unfold capture
  split <;> rfl

theorem ctxFor_capture {cs : List Canon} {src : Ev} :
    ctxFor me (some (capture me cs src)) = some (capture me cs src) := by
  simp [ctxFor, Option.filter, capture_source]

/-- A recomputed context gives this machine exactly the names its source translation owns. -/
theorem ownOf_capture {cs : List Canon} {src : Ev} {n : Name} :
    n ∈ ownOf me (some (capture me cs src)) ↔
      n ∈ ownKeys me (canonView src (mergeFacts me cs)) := by
  have hname : ∀ k : WKey, k.owner = me → nameOf me (contextView (canonView src (mergeFacts me cs))
      (mergedPresence cs)) (ownKeys me (canonView src (mergeFacts me cs))) k = k.ws := by
    intro k hk
    simp [nameOf, Names.localName, hk]
  have hx : ∀ e, e ∈ (contextOf me (canonView src (mergeFacts me cs)) (mergedPresence cs)).names ∧
      e.2.owner = me ↔
      ∃ k ∈ (canonView src (mergeFacts me cs)).keys, k.owner = me ∧ e = (k.ws, k) := by
    intro e
    simp only [contextOf, List.mem_map]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hown⟩
      exact ⟨k, hk, hown, by rw [hname k hown]⟩
    · rintro ⟨k, hk, hown, rfl⟩
      exact ⟨⟨k, hk, by rw [hname k hown]⟩, hown⟩
  have hnames : ∀ e, e ∈ (capture me cs src).names ∧ e.2.owner = me ↔
      ∃ k ∈ (canonView src (mergeFacts me cs)).keys, k.owner = me ∧ e = (k.ws, k) := by
    intro e
    rw [← hx]
    unfold capture
    split
    · simp only [keepOthers, List.mem_append, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
      constructor
      · rintro ⟨h | ⟨-, ⟨hne, -⟩, -⟩, hown⟩
        · exact ⟨h, hown⟩
        · exact absurd hown (by simpa [contextOf] using hne)
      · rintro ⟨h, hown⟩
        exact ⟨Or.inl h, hown⟩
    · exact Iff.rfl
  simp only [ownOf, List.mem_map, List.mem_filter, beq_iff_eq, ownKeys, List.mem_filterMap]
  constructor
  · rintro ⟨e, ⟨he, hown⟩, rfl⟩
    obtain ⟨k, hk, hk', rfl⟩ := (hnames e).mp ⟨he, hown⟩
    exact ⟨k, hk, by simp [hk']⟩
  · rintro ⟨k, hk, hkn⟩
    split at hkn
    · next hown =>
      simp only [Option.some.injEq] at hkn
      subst hkn
      obtain ⟨he, hown'⟩ := (hnames (k.ws, k)).mpr ⟨k, hk, hown, rfl⟩
      exact ⟨(k.ws, k), ⟨he, hown'⟩, rfl⟩
    · simp at hkn

theorem claim_root {o : Option Context} {n : Name} :
    (commandEv me ps view [.root] o).OwnClaim n ↔
      n ∈ (commandEv me ps view [.root] o).priv ∨ n ∈ ownOf me (ctxFor me o) := by
  simp only [Ev.OwnClaim, basis_root (show (commandEv me ps view [.root] o).parents = [.root]
    from rfl), true_and]
  have hp : ¬ ∃ c r, Parent.op c r ∈ (commandEv me ps view [.root] o).parents ∧
      n ∈ ownNamesIn me c := by
    rintro ⟨c, r, hc, -⟩
    simp [commandEv] at hc
  have hc : (∃ x ∈ (commandEv me ps view [.root] o).ctx, ∃ k, (n, k) ∈ x.names ∧ k.owner = me) ↔
      n ∈ ownOf me (ctxFor me o) := by
    simp only [Ev.ctx, commandEv]
    cases ctxFor me o with
    | none => simp [ownOf]
    | some x =>
      simp only [Option.mem_def, Option.some.injEq, exists_eq_left', ownOf, List.mem_map,
        List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨k, hk, hown⟩; exact ⟨(n, k), ⟨hk, hown⟩, rfl⟩
      · rintro ⟨⟨n', k⟩, ⟨hk, hown⟩, rfl⟩; exact ⟨k, hk, hown⟩
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact absurd h hp
    · exact Or.inr (hc.mp h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (hc.mpr h))

theorem machinesOf_contextView {src : Ev} {cs : List Canon} {m : Key} (hsrc : src.me = me)
    (hm : m ∈ machinesOf (contextView (canonView src (mergeFacts me cs)) (mergedPresence cs))) :
    m = me ∨ ∃ c ∈ cs, m ∈ machinesOf c := by
  · simp only [machinesOf, contextView, canonView, mergeFacts, mergedPresence, ↓reduceIte,
      List.mem_append, List.mem_map] at hm
    rcases hm with hm | ⟨k, hk | hk, rfl⟩
    · obtain ⟨c, hc, hm⟩ := List.mem_flatMap.mp hm
      exact Or.inr ⟨c, hc, List.mem_append_left _ hm⟩
    · obtain ⟨c, hc, hk⟩ := List.mem_flatMap.mp hk
      exact Or.inr ⟨c, hc, owner_mem_machinesOf (List.mem_filter.mp hk).1⟩
    · obtain ⟨_, -, rfl⟩ := hk
      exact Or.inl hsrc

/-- The machines a recomputed context knows before the carried context's are folded in: this
one, and those its parents' canonical forms know. -/
theorem contextOf_known {src : Ev} {cs : List Canon} {m : Key} (hsrc : src.me = me)
    (hm : m ∈ (contextOf me (canonView src (mergeFacts me cs)) (mergedPresence cs)).known) :
    m = me ∨ ∃ c ∈ cs, m ∈ machinesOf c := by
  simp only [contextOf] at hm
  rcases List.mem_cons.mp (mem_sortKeys.mp hm) with rfl | hm
  · exact Or.inl rfl
  · exact machinesOf_contextView hsrc hm

theorem capture_known {src : Ev} {cs : List Canon} {m : Key} (hsrc : src.me = me)
    (hm : m ∈ (capture me cs src).known) :
    m = me ∨ (∃ c ∈ cs, m ∈ machinesOf c) ∨ m ∈ knownOf (carriedOf me cs) := by
  unfold capture at hm
  split at hm
  · next c hc =>
    simp only [keepOthers, List.mem_append] at hm
    rcases hm with hm | hm
    · rcases contextOf_known hsrc hm with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by rw [hc]; exact hm))
  · next hc =>
    rcases contextOf_known hsrc hm with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem mergeFacts_others_ne {cs : List Canon} : ∀ k ∈ (mergeFacts me cs).others, k.owner ≠ me := by
  intro k hk
  simp only [mergeFacts, List.mem_flatMap, List.mem_filter, bne_iff_ne] at hk
  obtain ⟨_, -, -, h⟩ := hk
  exact h

theorem known_sub_capture {cs : List Canon} {src : Ev} {m : Key}
    (hm : m ∈ (contextOf me (canonView src (mergeFacts me cs)) (mergedPresence cs)).known) :
    m ∈ (capture me cs src).known := by
  unfold capture
  split
  · simp only [keepOthers, List.mem_append]
    exact Or.inl hm
  · exact hm

theorem carried_sub_capture {cs : List Canon} {src : Ev} {m : Key}
    (hm : m ∈ knownOf (carriedOf me cs)) : m ∈ (capture me cs src).known := by
  unfold capture
  split
  · next c hc =>
    simp only [keepOthers, List.mem_append]
    rw [hc] at hm
    exact Or.inr hm
  · next hc =>
    rw [hc] at hm
    simp [knownOf] at hm

/-- A recomputed context knows every other machine the untrimmed parents know. -/
theorem capture_knows (hok : ∀ p ∈ ps, NodeOK me bases p) {src : Ev} (m : Key) (hne : m ≠ me)
    (h : ∃ p ∈ ps, m ∈ machinesOf p.ref) : m ∈ (capture me (ps.map (·.canon)) src).known := by
  obtain ⟨p, hp, hm⟩ := h
  rcases ((hok p hp).knows m hne).mpr hm with h | h
  · apply known_sub_capture
    simp only [contextOf]
    refine mem_sortKeys.mpr (List.mem_cons_of_mem _ ?_)
    simp only [machinesOf, contextView, canonView, mergeFacts, mergedPresence, ↓reduceIte,
      List.mem_append, List.mem_map] at h ⊢
    rcases h with h | ⟨k, hk, rfl⟩
    · exact Or.inl (List.mem_flatMap.mpr ⟨p.canon, List.mem_map_of_mem hp, h⟩)
    · exact Or.inr ⟨k, Or.inl (List.mem_flatMap.mpr ⟨p.canon, List.mem_map_of_mem hp,
        List.mem_filter.mpr ⟨hk, by simpa using hne⟩⟩), rfl⟩
  · exact carried_sub_capture
      (mem_known_carriedOf.mpr ⟨p.canon, List.mem_map_of_mem hp, h⟩)

/-- A recomputed context knows no other machine the untrimmed parents don't. -/
theorem capture_known_sub (hok : ∀ p ∈ ps, NodeOK me bases p) {src : Ev} (hsrc : src.me = me)
    (m : Key) (hne : m ≠ me) (hm : m ∈ (capture me (ps.map (·.canon)) src).known) :
    ∃ p ∈ ps, m ∈ machinesOf p.ref := by
  rcases capture_known hsrc hm with h | ⟨c, hc, h⟩ | h
  · exact absurd h hne
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact ⟨p, hp, ((hok p hp).knows m hne).mp (Or.inl h)⟩
  · obtain ⟨c, hc, h⟩ := mem_known_carriedOf.mp h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact ⟨p, hp, ((hok p hp).knows m hne).mp (Or.inr h)⟩

/-- A recomputed context gives other machines only names shown as theirs. -/
theorem capture_aliases (hme : NoSlash me) (hok : ∀ p ∈ ps, NodeOK me bases p) {src : Ev}
    (hsrc : src.me = me) :
    ∀ e ∈ (capture me (ps.map (·.canon)) src).names, e.2.owner ≠ me →
      namesOther me e.1 (capture me (ps.map (·.canon)) src).known = true := by
  intro e he hne
  have hx : e ∈ (contextOf me (canonView src (mergeFacts me (ps.map (·.canon))))
      (mergedPresence (ps.map (·.canon)))).names → namesOther me e.1
        (capture me (ps.map (·.canon)) src).known = true := by
    intro he
    simp only [contextOf, List.mem_map] at he
    obtain ⟨k, hk, rfl⟩ := he
    have hslash : ∀ m ∈ sortKeys (me :: machinesOf (contextView
        (canonView src (mergeFacts me (ps.map (·.canon)))) (mergedPresence (ps.map (·.canon))))),
        NoSlash m := by
      intro m hm
      rcases List.mem_cons.mp (mem_sortKeys.mp hm) with rfl | hm
      · exact hme
      · rcases machinesOf_contextView hsrc hm with rfl | ⟨c, hc, h⟩
        · exact hme
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
          exact (hok p hp).slashCanon m h
    exact namesOther_localName hslash
      (mem_sortKeys.mpr (List.mem_cons_of_mem _ (owner_mem_machinesOf hk))) hne
      (known_sub_capture (by
        simp only [contextOf]
        exact mem_sortKeys.mpr (List.mem_cons_of_mem _ (owner_mem_machinesOf hk))))
  unfold capture at he
  split at he
  · next c hc =>
    simp only [keepOthers, List.mem_append, List.mem_filter] at he
    rcases he with he | ⟨he, -⟩
    · exact hx he
    · have he' : e ∈ ctxNames (carriedOf me (ps.map (·.canon))) := by rw [hc]; exact he
      obtain ⟨c', hc', he'⟩ := mem_names_carriedOf he'
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
      exact namesOther_mono ((hok p hp).aliases e he' hne) (fun m hm _ => carried_sub_capture
        (mem_known_carriedOf.mpr ⟨p.canon, hc', hm⟩))
  · exact hx he

/-- **A command after a trim.** A command whose parents a trim took away, translated on the root
alone with the context recomputed from its translation on their canonical forms, owns what
the same command on the untrimmed parents owns. -/
theorem late_owns (hme : NoSlash me) (hok : ∀ p ∈ ps, NodeOK me bases p)
    (hcfc : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.canon)) = true)
    (hcfr : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.ref)) = true) (n : Name) :
    Owns (commandEv me ps view [.root] (some (capture me (ps.map (·.canon))
        (commandEv me ps view (onParents (ps.map (·.canon)))
          (carriedOf me (ps.map (·.canon))))))) n ↔
      Owns (commandEv me ps view (onParents (ps.map (·.ref))) none) n := by
  have hsr : ∀ c ∈ ps.map (·.ref), ∀ m ∈ machinesOf c, NoSlash m := by
    intro c hc m hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact (hok p hp).slashRef m hm
  have hsrc := merge_owns (o := carriedOf me (ps.map (·.canon))) hme hok hcfc hcfr
    (carried_knows hok) (carried_aliases hok)
  have hown : ∀ n, n ∈ ownOf me (ctxFor me (some (capture me (ps.map (·.canon))
      (commandEv me ps view (onParents (ps.map (·.canon))) (carriedOf me (ps.map (·.canon))))))) ↔
      Owns (commandEv me ps view (onParents (ps.map (·.ref))) none) n := by
    intro n
    rw [ctxFor_capture, ownOf_capture]
    exact (ownKeys_canonView
      (ev := commandEv me ps view (onParents (ps.map (·.canon))) (carriedOf me (ps.map (·.canon))))
      (f := mergeFacts me (ps.map (·.canon))) rfl mergeFacts_others_ne).trans
        (mem_owned_iff.trans (hsrc n))
  have hshr : ∀ n ∈ view, (commandEv me ps view (onParents (ps.map (·.ref))) none).ShownOther n →
      ¬ (commandEv me ps view (onParents (ps.map (·.ref))) none).OwnClaim n ∧
        (commandEv me ps view (onParents (ps.map (·.ref))) none).LooksOther n :=
    shown_ok hme hsr hcfr (by simp [ctxNames, ctxFor])
  have hsimple := owns_simple rfl rfl basis_onParents hshr n
  constructor
  · intro ha
    rw [owns_initial rfl rfl n] at ha
    obtain ⟨hv, -, h⟩ := ha
    rcases h with ho | hl | hs
    · rcases claim_root.mp ho with hp | ho
      · exact priv_owns_ref hme (fun p hp => (hok p hp).slashRef) hcfr hp
      · exact (hown n).mp ho
    · refine hsimple.mpr ⟨hv, Or.inr (Or.inl fun hlr => hl ?_)⟩
      obtain ⟨hc, m, hk, hne, hs⟩ := hlr
      refine ⟨hc, m, Or.inr ?_, hne, hs⟩
      rw [knows_iff] at hk
      simp only [exists_mem_map'] at hk
      have hk' : ∃ p ∈ ps, m ∈ machinesOf p.ref := by
        rcases hk with hk | hk
        · exact hk
        · simp [ctxFor, knownOf] at hk
      simpa [Ev.ctxKnown, Ev.ctx, commandEv, ctxFor_capture, knownOf] using
        capture_knows hok m hne hk'
    · exact hsimple.mpr ⟨hv, Or.inr (Or.inr hs)⟩
  · intro hr
    have ho := (hown n).mpr hr
    rw [owns_initial rfl rfl n]
    exact ⟨hr.1, fun hg => hg.2.1 (claim_root.mpr (Or.inr ho)), Or.inl (claim_root.mpr (Or.inr ho))⟩

end Late

/-! ### Every history keeps the invariant -/

section Reach

variable {me : Key} {bases : List Node}

theorem mapM_mem {nodes : List Node} :
    ∀ {is : List Nat} {ps : List Node}, is.mapM (nodes[·]?) = some ps → ∀ p ∈ ps, p ∈ nodes
  | [], ps, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | i :: is, ps, h => by
    rw [List.mapM_cons] at h
    cases hi : nodes[i]? with
    | none => simp [hi] at h
    | some p =>
      cases hr : is.mapM (nodes[·]?) with
      | none => simp [hi, hr] at h
      | some qs =>
        simp only [hi, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_iff_getElem?.mpr ⟨i, hi⟩
        · exact mapM_mem hr x hx

theorem machines_merge {ev : Ev} {cs : List Canon} (hme : ev.me = me) {m : Key} (hne : m ≠ me) :
    m ∈ machinesOf (canonView ev (mergeFacts me cs)) ↔ ∃ c ∈ cs, m ∈ machinesOf c := by
  simp only [machinesOf, canonView, mergeFacts, ↓reduceIte, List.mem_append, List.mem_flatMap,
    List.mem_singleton, List.map_append, List.mem_map, List.mem_filter, bne_iff_ne]
  constructor
  · rintro ((⟨c, hc, h⟩ | h) | ⟨k, ⟨c, hc, hk, -⟩, rfl⟩ | ⟨k, ⟨_, -, rfl⟩, rfl⟩)
    · exact ⟨c, hc, Or.inl h⟩
    · exact absurd h hne
    · exact ⟨c, hc, Or.inr ⟨k, hk, rfl⟩⟩
    · exact absurd hme hne
  · rintro ⟨c, hc, h | ⟨k, hk, rfl⟩⟩
    · exact Or.inl (Or.inl ⟨c, hc, h⟩)
    · exact Or.inr (Or.inl ⟨k, ⟨c, hc, hk, hne⟩, rfl⟩)

theorem machines_root {ev : Ev} (hme : ev.me = me) {m : Key}
    (h : m ∈ machinesOf (canonView ev (rootFacts me))) : m = me := by
  simp only [machinesOf, canonView, rootFacts, ↓reduceIte, List.mem_append, List.mem_singleton,
    List.nil_append, List.mem_map] at h
  rcases h with h | ⟨k, ⟨_, -, rfl⟩, rfl⟩
  · exact h
  · exact hme

theorem ownNamesIn_canonView {ev : Ev} {f : Facts} (hp : f.present = true)
    (ho : ∀ k ∈ f.others, k.owner ≠ ev.me) {n : Name} :
    n ∈ ownNamesIn ev.me (canonView ev f) ↔ Owns ev n := by
  rw [ownNamesIn_present hp]
  exact (ownKeys_canonView hp ho).trans mem_owned_iff

theorem machines_merge_cmd {ps : List Node} {view : List Name} {pars : List Parent}
    {o : Option Context} {cs : List Canon} {m : Key} (hne : m ≠ me) :
    m ∈ machinesOf (canonView (commandEv me ps view pars o) (mergeFacts me cs)) ↔
      ∃ c ∈ cs, m ∈ machinesOf c :=
  machines_merge rfl hne

theorem machines_root_cmd {ps : List Node} {view : List Name} {pars : List Parent}
    {o : Option Context} {m : Key}
    (h : m ∈ machinesOf (canonView (commandEv me ps view pars o) (rootFacts me))) : m = me :=
  machines_root rfl h

theorem own_merge_cmd {ps : List Node} {view : List Name} {pars : List Parent}
    {o : Option Context} {cs : List Canon} {n : Name} :
    n ∈ ownNamesIn me (canonView (commandEv me ps view pars o) (mergeFacts me cs)) ↔
      Owns (commandEv me ps view pars o) n :=
  ownNamesIn_canonView (ev := commandEv me ps view pars o) (f := mergeFacts me cs) rfl
    mergeFacts_others_ne

theorem own_root_cmd {ps : List Node} {view : List Name} {pars : List Parent}
    {o : Option Context} {n : Name} :
    n ∈ ownNamesIn me (canonView (commandEv me ps view pars o) (rootFacts me)) ↔
      Owns (commandEv me ps view pars o) n :=
  ownNamesIn_canonView (ev := commandEv me ps view pars o) (f := rootFacts me) rfl
    (by simp [rootFacts])

/-- The untrimmed form a command gets keeps the invariant's facts about machines. -/
theorem ref_machines {ps : List Node} {view : List Name} (hok : ∀ p ∈ ps, NodeOK me bases p)
    (hme : NoSlash me) :
    (∀ m, m ≠ me → (m ∈ machinesOf (canonView (commandEv me ps view (onParents (ps.map (·.ref)))
        none) (mergeFacts me (ps.map (·.ref)))) ↔ ∃ p ∈ ps, m ∈ machinesOf p.ref)) ∧
      ∀ m ∈ machinesOf (canonView (commandEv me ps view (onParents (ps.map (·.ref))) none)
        (mergeFacts me (ps.map (·.ref)))), NoSlash m := by
  have h : ∀ m, m ≠ me → (m ∈ machinesOf (canonView (commandEv me ps view
      (onParents (ps.map (·.ref))) none) (mergeFacts me (ps.map (·.ref)))) ↔
        ∃ p ∈ ps, m ∈ machinesOf p.ref) := by
    intro m hne
    rw [machines_merge_cmd hne, exists_mem_map']
  refine ⟨h, fun m hm => ?_⟩
  rcases Classical.em (m = me) with rfl | hne
  · exact hme
  · obtain ⟨p, hp, h⟩ := (h m hne).mp hm
    exact (hok p hp).slashRef m h

/-- A command on parents whose canonical forms survive keeps the invariant. -/
theorem command_ok {ps : List Node} {view : List Name} (hme : NoSlash me)
    (hok : ∀ p ∈ ps, NodeOK me bases p)
    (hcfc : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.canon)) = true)
    (hcfr : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.ref)) = true) :
    NodeOK me bases
      { view, priv := (commandEv me ps view (onParents (ps.map (·.canon)))
          (carriedKept me (ps.map (·.canon)))).priv, record := none,
        canon := canonView (commandEv me ps view (onParents (ps.map (·.canon)))
          (carriedKept me (ps.map (·.canon)))) (mergeFacts me (ps.map (·.canon))),
        ref := canonView (commandEv me ps view (onParents (ps.map (·.ref))) none)
          (mergeFacts me (ps.map (·.ref))),
        trimmed := false } := by
  obtain ⟨hrk, hrs⟩ := ref_machines (view := view) hok hme
  refine ⟨fun n => ?_, fun m hne => ?_, kept_aliases hok, fun m hm => ?_, hrs,
    Or.inr ⟨rfl, rfl⟩, Or.inl rfl⟩
  · dsimp only
    rw [own_merge_cmd, own_merge_cmd]
    exact merge_owns hme hok hcfc hcfr (kept_knows hok) (kept_aliases hok) n
  · dsimp only
    rw [hrk m hne, machines_merge_cmd hne, exists_mem_map']
    exact kept_knows hok m hne
  · dsimp only at hm
    rcases Classical.em (m = me) with rfl | hne
    · exact hme
    · obtain ⟨c, hc, h⟩ := (machines_merge_cmd hne).mp hm
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact (hok p hp).slashCanon m h

/-- A command on parents a trim took away keeps the invariant, and records nothing private. -/
theorem late_ok {ps : List Node} {view : List Name} (hme : NoSlash me)
    (hok : ∀ p ∈ ps, NodeOK me bases p)
    (hcfc : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.canon)) = true)
    (hcfr : clashFree me ((ps.flatMap Node.privAt).filter (view.contains ·)) view
      (ps.map (·.ref)) = true) :
    let ctx := capture me (ps.map (·.canon))
      (commandEv me ps view (onParents (ps.map (·.canon))) (carriedOf me (ps.map (·.canon))))
    let a := commandEv me ps view [.root] (some ctx)
    NodeOK me bases
      { view, priv := a.priv,
        record := some (recordOf me view a.priv (canonView a (rootFacts me))),
        canon := canonView a (rootFacts me),
        ref := canonView (commandEv me ps view (onParents (ps.map (·.ref))) none)
          (mergeFacts me (ps.map (·.ref))),
        trimmed := false } := by
  intro ctx a
  obtain ⟨hrk, hrs⟩ := ref_machines (view := view) hok hme
  have hown : ∀ n, Owns a n ↔ Owns (commandEv me ps view (onParents (ps.map (·.ref))) none) n :=
    late_owns hme hok hcfc hcfr
  have hctx : ctxFor me (canonView a (rootFacts me)).context = some ctx := ctxFor_capture
  refine ⟨fun n => ?_, fun m hne => ?_, fun e he hne => ?_, fun m hm => ?_, hrs,
    Or.inr ⟨rfl, rfl⟩, Or.inr (Or.inl ?_)⟩
  · dsimp only
    rw [own_root_cmd, own_merge_cmd]
    exact hown n
  · dsimp only
    rw [hctx, hrk m hne]
    simp only [knownOf]
    constructor
    · rintro (h | h)
      · exact absurd (machines_root_cmd h) hne
      · exact capture_known_sub hok rfl m hne h
    · intro h
      exact Or.inr (capture_knows hok m hne h)
  · dsimp only at he ⊢
    rw [hctx] at he ⊢
    exact capture_aliases hme hok rfl e he hne
  · dsimp only at hm
    rw [machines_root_cmd hm]
    exact hme
  · -- `own_of_view` agrees, so the record is empty.
    have hw : WF a (rootFacts me) :=
      ⟨hme, by simp [a, commandEv], by simp [a, commandEv], by simp [rootFacts, hme],
        by simp [rootFacts]⟩
    have hcond : (ownOfView me view a.priv (canonView a (rootFacts me))).all
        ((ownNames me (canonView a (rootFacts me))).contains ·) = true := by
      apply List.all_eq_true.mpr
      intro n hn
      have h1 := (agreement a (rootFacts me) rfl hw n).mp hn
      rw [contains_true, mem_ownNames_present rfl]
      exact (ownKeys_canonView rfl (by simp [rootFacts])).mpr h1
    simp only [recordOf, hcond, ↓reduceIte]

theorem stepNodes_ok (hme : NoSlash me) {nodes : List Node} (hok : ∀ x ∈ nodes, NodeOK me bases x)
    (s : Step) : ∀ x ∈ stepNodes me nodes s, NodeOK me bases x := by
  cases s with
  | trim =>
    intro x hx
    simp only [stepNodes, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h := hok y hy
    refine ⟨h.own, h.knows, h.aliases, h.slashCanon, h.slashRef, h.same, ?_⟩
    exact h.record
  | realize c view record =>
    simp only [stepNodes]
    split
    · next hc =>
      simp only [hiveB, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true] at hc
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hok x hx
      · rw [List.mem_singleton.mp hx]
        refine ⟨fun n => Iff.rfl, fun m _ => ?_, fun e he => ?_,
          fun m hm => noSlash_of (hc.2 m hm), fun m hm => noSlash_of (hc.2 m hm), Or.inl rfl,
          Or.inr (Or.inr rfl)⟩
        · simp [hc.1, ctxFor, Option.filter, knownOf]
        · simp [hc.1, ctxFor, Option.filter, ctxNames] at he
    · exact hok
  | command is view =>
    simp only [stepNodes]
    split
    · exact hok
    · next ps hps =>
      have hpok : ∀ p ∈ ps, NodeOK me bases p := fun p hp => hok p (mapM_mem hps p hp)
      split
      · exact hok
      · next hguard =>
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hguard
        obtain ⟨⟨-, hcfc⟩, hcfr⟩ := hguard
        split
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hok x hx
          · rw [List.mem_singleton.mp hx]
            exact late_ok hme hpok hcfc hcfr
        · split
          · exact hok
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hok x hx
            · rw [List.mem_singleton.mp hx]
              exact command_ok hme hpok hcfc hcfr

theorem reach_ok (hme : NoSlash me) (hb : ∀ x ∈ bases, BaseOK x) {nodes : List Node}
    (h : Reach me bases nodes) : ∀ x ∈ nodes, NodeOK me bases x := by
  induction h with
  | init =>
    intro x hx
    have hbx := hb x hx
    refine ⟨fun n => by rw [hbx.ref], fun m _ => ?_, fun e he => ?_, hbx.slash,
      hbx.ref ▸ hbx.slash, Or.inl hbx.ref, Or.inr (Or.inr hbx.realized)⟩
    · rw [hbx.context, ← hbx.ref]
      simp [ctxFor, Option.filter, knownOf]
    · rw [hbx.context] at he
      simp [ctxFor, Option.filter, ctxNames] at he
  | step s _ ih => exact stepNodes_ok hme ih s

/-- **Trims keep ownership.** Over every history of `jj` commands and merges, on any earlier
operations, with trims of the whole history between: whatever canonical form an operation gets,
on the root alone after a trim with its recomputed context, or below one carrying the folded
contexts of its parents, it owns exactly what the untrimmed history's canonical form owns. -/
theorem trims_keep_ownership (hme : NoSlash me) (hb : ∀ x ∈ bases, BaseOK x)
    {nodes : List Node} (h : Reach me bases nodes) :
    ∀ x ∈ nodes, ∀ n, n ∈ ownKeys me x.canon ↔ n ∈ ownKeys me x.ref := by
  intro x hx n
  have hok := reach_ok hme hb h x hx
  rcases hok.same with heq | ⟨hc, hr⟩
  · rw [heq]
  · rw [← ownNamesIn_present hc, ← ownNamesIn_present hr]
    exact hok.own n

/-- **Safety.** A name gets this machine's key in an operation's canonical form only if the
untrimmed history's translation of it makes the name this machine's (`Owns`): no evidence a trim
leaves behind, no context recomputed or carried, gives this machine a name the complete
evidence gives another machine. And only an operation that realizes one from the hive, a base or
a realization, keeps a nonempty private record (`realized`): translating a command records none, and a late
operation's rewrite an empty one, so nothing launders a name into the private names both
functions trust from then on. -/
theorem safety (hme : NoSlash me) (hb : ∀ x ∈ bases, BaseOK x) {nodes : List Node}
    (h : Reach me bases nodes) :
    ∀ x ∈ nodes, (∀ n, n ∈ ownKeys me x.canon → n ∈ ownKeys me x.ref) ∧
      (x.record = none ∨ x.record = some [] ∨ x.realized = true) :=
  fun x hx => ⟨fun n hc => (trims_keep_ownership hme hb h x hx n).mp hc,
    (reach_ok hme hb h x hx).record⟩

end Reach

theorem recompute_none {me : Key} {cs : List Canon} {src : Ev} :
    recompute me cs src none = capture me cs src := rfl

/-! ## What the oracle checks of a request -/

/-- `WF`, decided: the oracle answers only requests that meet it, so that `agreement` covers
every one it answers. -/
def wfB (ev : Ev) (f : Facts) : Bool :=
  noSlashB ev.me &&
    ev.parents.all (fun
      | .root => true
      | .op c _ => (machinesOf c).all fun m => noSlashB m && (m == ev.me || f.known.contains m)) &&
    f.known.all noSlashB && f.others.all fun k => k.owner != ev.me && noSlashB k.owner

theorem wf_of_wfB {ev : Ev} {f : Facts} (h : wfB ev f = true) : WF ev f := by
  simp only [wfB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hme, hpar⟩, hknown⟩, hothers⟩ := h
  have hp : ∀ c r, Parent.op c r ∈ ev.parents → ∀ m ∈ machinesOf c,
      noSlashB m = true ∧ (m = ev.me ∨ m ∈ f.known) := by
    intro c r hc m hm
    have := List.all_eq_true.mp (hpar _ hc) m hm
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, contains_true] at this
    exact this
  refine ⟨noSlash_of hme, fun c r hc m hm => noSlash_of (hp c r hc m hm).1,
    fun c r hc m hm hne => ((hp c r hc m hm).2.resolve_left hne),
    fun m hm => noSlash_of (hknown m hm), fun k hk => ?_⟩
  have := hothers k hk
  simp only [bne_iff_ne, ne_eq] at this
  exact ⟨this.1, noSlash_of this.2⟩

/-! ## Examples, checked at build time

alpha and beta share a hive, and alpha shows beta's workspace as `beta/beta`. A full trim
leaves a late command of alpha's on the root alone (#167): only the context it carries says
`beta/beta` is beta's. -/

private def alpha : Key := ⟨"alpha".toList, "aaaa1111".toList⟩
private def beta : Key := ⟨"beta".toList, "bbbb2222".toList⟩

private def lateCtx : Context :=
  ⟨alpha, [("alpha".toList, ⟨alpha, "alpha".toList⟩), ("beta/beta".toList, ⟨beta, "beta".toList⟩)],
    [alpha, beta]⟩

private def late : Ev where
  me := alpha
  view := ["alpha".toList, "beta/beta".toList]
  priv := []
  parents := [.root]
  start := ["alpha".toList, "beta/beta".toList]
  command := true
  context := some lateCtx

private def lateFacts : Facts := ⟨true, [alpha], none, []⟩

#guard wfB late lateFacts
#guard owned late == ["alpha".toList]
#guard ownOfView alpha late.view late.priv (canonView late lateFacts) == ["alpha".toList]
-- Before #167's fix, `own_of_view` took beta's workspace for alpha's.
#guard ownOfViewUnfixed alpha late.view late.priv (canonView late lateFacts) ==
  ["alpha".toList, "beta/beta".toList]

/-- A command on that late one, after a second full trim: translated on the late one's canonical
form, which has only alpha's workspaces and knows only alpha, it owns `beta/beta` unless it
reads the context that form carries. -/
private def onLate (context : Option Context) : Ev :=
  { late with parents := [.op (canonView late lateFacts) []], context }

#guard owned (onLate none) == ["alpha".toList, "beta/beta".toList]
#guard owned (onLate (canonView late lateFacts).context) == ["alpha".toList]

/-- A merge of two operations after trims, each knowing only this machine and carrying the
context of a different trim: one knows beta, the other gamma, which joined between them
(`a_merge_of_late_commands_after_two_trims_keeps_others_workspaces_theirs`). Read with the first
context alone, `gamma/g` is taken for this machine's; with both folded in (`carriedOf`), it
stays gamma's. -/
private def gamma : Key := ⟨"gamma".toList, "cccc3333".toList⟩

private def rebased (context : Context) : Canon :=
  { keys := [⟨alpha, "alpha".toList⟩], known := [alpha], present := true, context := some context }

private def beforeGamma : Canon :=
  rebased ⟨alpha, [("beta/beta".toList, ⟨beta, "beta".toList⟩)], [alpha, beta]⟩

private def afterGamma : Canon :=
  rebased ⟨alpha, [("gamma/g".toList, ⟨gamma, "g".toList⟩)], [alpha, gamma]⟩

private def merge (context : Option Context) : Ev where
  me := alpha
  view := ["alpha".toList, "beta/beta".toList, "gamma/g".toList]
  priv := []
  parents := onParents [beforeGamma, afterGamma]
  start := ["alpha".toList, "beta/beta".toList, "gamma/g".toList]
  command := true
  context := context

#guard owned (merge (ctxFor alpha beforeGamma.context)) == ["alpha".toList, "gamma/g".toList]
#guard owned (merge (carriedOf alpha [beforeGamma, afterGamma])) == ["alpha".toList]

/-- Finding A. A trim leaves alpha's operation `d3` on the root, recording the context it was
translated with, which gives `beta/third`, beta's workspace renamed, to beta. `jj op abandon`
of an operation below it then gives `d3` a local parent `d1` whose view lacks `beta/third`, and
whose canonical form, written after an earlier trim, knows only alpha and carries a context of
that trim's, from before the rename. -/
private def d1 : Canon :=
  rebased ⟨alpha, [("alpha".toList, ⟨alpha, "alpha".toList⟩),
    ("beta/beta".toList, ⟨beta, "beta".toList⟩)], [alpha, beta]⟩

private def recordedA : Context :=
  ⟨alpha, [("alpha".toList, ⟨alpha, "alpha".toList⟩), ("beta/beta".toList, ⟨beta, "beta".toList⟩),
    ("beta/third".toList, ⟨beta, "third".toList⟩)], [alpha, beta]⟩

private def viewA : List Name := ["alpha".toList, "beta/beta".toList, "beta/third".toList]

/-- `d3` judged on `d1`, as `canonical_form`'s source translation judges it: `beta/third` is in
no view it now starts from, so it looks made by `d3`. -/
private def sourceA : Ev where
  me := alpha
  view := viewA
  priv := []
  parents := onParents [d1]
  start := ["alpha".toList, "beta/beta".toList]
  command := true
  context := some recordedA

/-- `d3` on the root, with the context the recomputation leaves it. -/
private def onRootA (context : Context) : Ev :=
  { sourceA with parents := [.root], context := some context }

#guard owned sourceA == ["alpha".toList, "beta/third".toList]
-- Before the fix, the recomputed context gives `beta/third` to alpha, and so does `d3`.
#guard owned (onRootA (recompute alpha [d1] sourceA none)) ==
  ["alpha".toList, "beta/third".toList]
-- With the context `d3` records taken over it, `beta/third` stays beta's.
#guard owned (onRootA (recompute alpha [d1] sourceA (some recordedA))) == ["alpha".toList]

/-- An old alias, as `jj undo` brings back: two machines named beta now show as `beta-bbbb` and
`beta-bbbb9999`, but `d3`'s view still names the first one's workspace `beta/x`, as when it was
the only one. Translated on its parents, which had that name, `d3` left it beta's, and the
context it recorded names beta's workspace as `beta-bbbb/x`, so it says nothing of `beta/x`. -/
private def beta9 : Key := ⟨"beta".toList, "bbbb9999".toList⟩

private def recordedB : Context :=
  ⟨alpha, [("alpha".toList, ⟨alpha, "alpha".toList⟩),
    ("beta-bbbb/x".toList, ⟨beta, "x".toList⟩)], [alpha, beta, beta9]⟩

private def d1B : Canon := rebased recordedB

private def sourceB : Ev where
  me := alpha
  view := ["alpha".toList, "beta/x".toList]
  priv := []
  parents := onParents [d1B]
  start := ["alpha".toList]
  command := true
  context := some recordedB

/-- `d3` as it was translated before the abandon, on a parent that showed beta's workspace, and
whose view had the old alias: being in a view it started from, the alias wasn't its own. -/
private def p0B : Canon where
  keys := [⟨alpha, "alpha".toList⟩, ⟨beta, "x".toList⟩]
  known := [alpha, beta, beta9]
  present := true

private def beforeB : Ev where
  me := alpha
  view := ["alpha".toList, "beta/x".toList]
  priv := []
  parents := onParents [p0B]
  start := ["alpha".toList, "beta/x".toList]
  command := true

private def onRootB (context : Context) : Ev :=
  { sourceB with parents := [.root], context := some context }

#guard owned beforeB == ["alpha".toList]
-- After the abandon, even with the fix, the recomputed context gives the old alias to alpha:
-- the context `d3` records doesn't mention it.
#guard owned (onRootB (recompute alpha [d1B] sourceB (some recordedB))) ==
  ["alpha".toList, "beta/x".toList]

end Musubi.Ownership
