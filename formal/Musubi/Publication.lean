/-
Publication budgets concern the file versions retained by automatic snapshots, beyond the
content explicit history edits require. The native binding supplies each commit's full file
closure, including its parents, and jj's snapshot flag, creation/rewrite records and explicit
revision selections. Those are
checked against actual jj commands. The binding recognizes automatic reconciliation and musubi
transactions separately from explicit jj change commands.

Cleanup removes selected whole operations. A fresh checkpoint retains the current view and
the intentional commit versions of the removed operations. Contraction of operation parents
is supplied by Contract.lean; file contents and commit identities are never rewritten here.
-/
import Musubi.Contract

namespace Musubi.Publication

structure File where
  path : Nat
  object : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

structure Write where
  commit : Nat
  workspaceTip : Bool
  rewritten : Bool
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

structure Operation where
  id : Nat
  parents : List Nat := []
  snapshot : Bool
  /-- Immutable source intent, recorded before any parent contraction. -/
  frozen : Option (List Nat) := none
  writes : List Write
  /-- Existing versions selected explicitly, including parents chosen for fresh WC tips. -/
  selections : List Nat
  required : List Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- Newly created working-copy tips can contain the unselected remainder of a partial commit.
Rewriting a change explicitly, including a working-copy change, is intentional. -/
def intentional (op : Operation) : List Nat :=
  op.frozen.getD (if op.snapshot then [] else
    (op.writes.filter (fun w => !w.workspaceTip || w.rewritten)).map Write.commit ++ op.selections)

def protectedRoots (ops : List Operation) : List Nat := (ops.flatMap intentional).eraseDups

def references (ops : List Operation) : List Nat := (ops.flatMap Operation.required).eraseDups

/-- The caller supplies the complete file closure of each named commit. -/
def files (closure : Nat → List File) (commits : List Nat) : List File :=
  (commits.flatMap closure).eraseDups

def charged (closure : Nat → List File) (known : List Nat) (ops : List Operation) : List File :=
  let exempt := (files closure known ++ files closure (protectedRoots ops)).eraseDups
  (files closure (references ops)).filter (fun f => !exempt.contains f)

/-- A new path can cost a file entry while reusing content already required elsewhere. -/
def chargeSize (closure : Nat → List File) (known : List Nat) (ops : List Operation)
    (size : Nat → Nat) (object : Nat) : Nat :=
  let exempt := ((files closure known ++ files closure (protectedRoots ops)).map File.object)
  if exempt.contains object then 0 else size object

def fileCount (fs : List File) : Nat := (fs.map File.path).eraseDups.length

/-- File versions shared by several paths or snapshots occupy content bytes once. -/
def byteCount (size : Nat → Nat) (fs : List File) : Nat :=
  ((fs.map File.object).eraseDups.map size).sum

structure Limits where
  files : Nat
  bytes : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- Zero disables the corresponding limit. -/
def fits (size : Nat → Nat) (limits : Limits) (fs : List File) : Bool :=
  (limits.files == 0 || fileCount fs ≤ limits.files) &&
  (limits.bytes == 0 || byteCount size fs ≤ limits.bytes)

structure Plan where
  /-- Immutable operation identities, accepted basis and all applicable limits. -/
  identity : List Nat
  extra : List File
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def maySend (size : Nat → Nat) (limits : Limits) (plan : Plan)
    (approval : Option Plan) : Bool := fits size limits plan.extra || approval == some plan

/-- A changed plan cannot use approval for its predecessor. -/
theorem changed_plan_held (size : Nat → Nat) (limits : Limits) (old next : Plan)
    (hlarge : fits size limits next.extra = false) (hchanged : old ≠ next) :
    maySend size limits next (some old) = false := by
  simp [maySend, hlarge, hchanged]

theorem protected_not_charged (closure : Nat → List File) (known : List Nat)
    (ops : List Operation) (f : File) (h : f ∈ files closure (protectedRoots ops)) :
    f ∉ charged closure known ops := by
  simp only [charged, List.mem_filter]
  simp [h]

theorem known_not_charged (closure : Nat → List File) (known : List Nat)
    (ops : List Operation) (f : File) (h : f ∈ files closure known) :
    f ∉ charged closure known ops := by
  simp only [charged, List.mem_filter]
  simp [h]

theorem protected_content_free (closure : Nat → List File) (known : List Nat)
    (ops : List Operation) (size : Nat → Nat) (f : File)
    (h : f ∈ files closure (protectedRoots ops)) :
    chargeSize closure known ops size f.object = 0 := by
  have hm : f.object ∈ (files closure (protectedRoots ops)).map File.object :=
    List.mem_map.mpr ⟨f, h, rfl⟩
  simp [chargeSize, hm]

/-- Sealing changes hash-visible nonparent content. It precedes contraction and is not
identified with the source operation's immutable body or physical jj id. -/
def freezeIntent (op : Operation) : Operation := { op with frozen := some (intentional op) }

@[simp] theorem intentional_freezeIntent (op : Operation) :
    intentional (freezeIntent op) = intentional op := by
  simp [freezeIntent, intentional]

structure State where
  heads : List Nat
  /-- Current refs, including working-copy commits, without changing commit identities. -/
  view : List Nat
  operations : List Operation
  /-- Namespace, expected Git values and full foreign causal presence, not just live bits. -/
  context : List Nat := []
  /-- Native command facts must establish intent completely before history can be removed. -/
  intentKnown : Bool := true
  /-- Cleanup is genuine new local activity; it never forges another copy's activity. -/
  localWork : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def parents (s : State) (id : Nat) : List Nat :=
  ((s.operations.find? (fun op => op.id == id)).map Operation.parents).getD []

def dropped (selected : List Nat) (id : Nat) : Bool := selected.contains id

/-- Labels stay source labels. Physical identities hash the sealed body and contracted
parents; native preparation rejects coalescing physical identities. -/
def survivor (s : State) (selected : List Nat) (op : Operation) : Operation :=
  { freezeIntent op with parents := Contract.cpar (parents s) (dropped selected) op.id }

def checkpoint (id : Nat) (view roots frontier : List Nat) : Operation :=
  { id, parents := frontier, snapshot := false, frozen := some roots, writes := [],
    selections := [], required := (view ++ roots).eraseDups }

def cleanup (s : State) (selected : List Nat) (fresh : Nat) : State :=
  { heads := [fresh], view := s.view, context := s.context, intentKnown := s.intentKnown,
    localWork := s.localWork + 1,
    operations := (s.operations.filter (fun op => !selected.contains op.id)).map
      (survivor s selected) ++
      [checkpoint fresh s.view (protectedRoots s.operations)
        (Contract.dd (s.heads.flatMap (Contract.exp (parents s) (dropped selected))))] }

@[simp] theorem intentional_survivor (s : State) (selected : List Nat) (op : Operation) :
    intentional (survivor s selected op) = intentional op := by
  simp [survivor, freezeIntent, intentional]

theorem cleanup_keeps_current_view (s : State) (selected : List Nat) (fresh : Nat) :
    (cleanup s selected fresh).view = s.view := rfl

theorem cleanup_keeps_context (s : State) (selected : List Nat) (fresh : Nat) :
    (cleanup s selected fresh).context = s.context := rfl

/-- Contraction changes neither a surviving operation's required commits nor its intent. -/
theorem cleanup_keeps_unselected (s : State) (selected : List Nat) (fresh : Nat)
    (op : Operation) (hop : op ∈ s.operations) (h : selected.contains op.id = false) :
    ∃ kept ∈ (cleanup s selected fresh).operations,
      kept.required = op.required ∧ intentional kept = intentional op := by
  refine ⟨survivor s selected op, ?_, rfl, intentional_survivor s selected op⟩
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨op, List.mem_filter.mpr ⟨hop, by simp only [h, Bool.not_false]⟩, rfl⟩

/-- Every explicit commit version is an actual required reference after cleanup, even if
its source operation is removed. This is stronger than preserving an exemption label. -/
theorem cleanup_requires_intentional (s : State) (selected : List Nat) (fresh c : Nat)
    (h : c ∈ protectedRoots s.operations) :
    c ∈ references (cleanup s selected fresh).operations := by
  simp only [references, List.mem_eraseDups, List.mem_flatMap]
  refine ⟨checkpoint fresh s.view (protectedRoots s.operations)
    (Contract.dd (s.heads.flatMap (Contract.exp (parents s) (dropped selected)))), ?_, ?_⟩
  · simp [cleanup]
  · simp [checkpoint, h]

/-- Intent is fixed from the source, including when a removed parent would otherwise change
what an explicit survivor appears to have introduced. -/
theorem cleanup_keeps_intentional (s : State) (selected : List Nat) (fresh c : Nat) :
    c ∈ protectedRoots (cleanup s selected fresh).operations ↔
    c ∈ protectedRoots s.operations := by
  simp only [protectedRoots, List.mem_eraseDups, List.mem_flatMap]
  constructor
  · rintro ⟨op, hop, hc⟩
    simp only [cleanup, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_singleton] at hop
    rcases hop with ⟨source, ⟨hs, _⟩, rfl⟩ | rfl
    · exact ⟨source, hs, by simpa using hc⟩
    · simpa [checkpoint, intentional, protectedRoots] using hc
  · intro hc
    refine ⟨checkpoint fresh s.view (protectedRoots s.operations)
      (Contract.dd (s.heads.flatMap (Contract.exp (parents s) (dropped selected)))), ?_, ?_⟩
    · simp [cleanup]
    · simpa [checkpoint, intentional, protectedRoots] using hc

theorem cleanup_keeps_intentional_files (s : State) (selected : List Nat) (fresh : Nat)
    (closure : Nat → List File) (f : File)
    (h : f ∈ files closure (protectedRoots s.operations)) :
    f ∈ files closure (references (cleanup s selected fresh).operations) := by
  simp only [files, List.mem_eraseDups, List.mem_flatMap] at h ⊢
  obtain ⟨c, hc, hf⟩ := h
  exact ⟨c, cleanup_requires_intentional s selected fresh c hc, hf⟩

/-- The operation graph uses the existing contraction algebra, with its ordered parents
and surviving-ancestry theorem. The immutable annotation step above is separate. -/
theorem survivor_parent_survives (s : State) (selected : List Nat)
    (hlt : ParLt (parents s)) (op : Operation) (q : Nat)
    (h : q ∈ (survivor s selected op).parents) :
    dropped selected q = false ∧ Anc (parents s) q op.id ∧ q ≠ op.id :=
  Contract.mem_cpar hlt h

theorem survivor_ancestry (s : State) (selected : List Nat)
    (hlt : ParLt (parents s)) (a x : Nat) (ha : dropped selected a = false) :
    Anc (Contract.cpar (parents s) (dropped selected)) a x ↔
      Anc (parents s) a x := Contract.anc_cpar_iff hlt ha

/-- Native preparation is read back through canonicalization. This executable check runs
before op heads move, and compares content sets, not only their aggregate sizes. -/
def preparedMatches (closure : Nat → List File) (known : List Nat)
    (source preview actual : State) : Bool :=
  actual.view == source.view && actual.context == source.context &&
  (protectedRoots actual.operations).all (references actual.operations).contains &&
  ((protectedRoots actual.operations).all (protectedRoots source.operations).contains &&
    (protectedRoots source.operations).all (protectedRoots actual.operations).contains) &&
  ((charged closure known actual.operations).all
      (charged closure known preview.operations).contains &&
    (charged closure known preview.operations).all
      (charged closure known actual.operations).contains)

/-- The source-head check and prepared-effect check both precede installation. The caller
also verifies unselected native bodies' saved views and frozen intent. -/
def applyCleanup (closure : Nat → List File) (known expected : List Nat) (s : State)
    (selected : List Nat) (fresh : Nat) (actual : State) : Option State :=
  if expected == s.heads && s.intentKnown && preparedMatches closure known s (cleanup s selected fresh) actual
    then some actual else none

theorem stale_cleanup_refused (closure : Nat → List File) (known : List Nat)
    (s actual : State) (expected selected : List Nat) (fresh : Nat)
    (h : expected ≠ s.heads) :
    applyCleanup closure known expected s selected fresh actual = none := by
  simp [applyCleanup, h]

theorem uncertain_cleanup_refused (closure : Nat → List File) (known expected : List Nat)
    (s actual : State) (selected : List Nat) (fresh : Nat) (h : s.intentKnown = false) :
    applyCleanup closure known expected s selected fresh actual = none := by
  simp [applyCleanup, h]

theorem installed_keeps_view_context (closure : Nat → List File) (known expected : List Nat)
    (s actual installed : State) (selected : List Nat) (fresh : Nat)
    (h : applyCleanup closure known expected s selected fresh actual = some installed) :
    installed.view = s.view ∧ installed.context = s.context := by
  unfold applyCleanup at h
  split at h
  · rename_i condition
    simp only [Bool.and_eq_true, preparedMatches] at condition
    have checks := condition.2
    simp only [beq_iff_eq] at checks
    cases h
    exact ⟨checks.1.1.1.1, checks.1.1.1.2⟩
  · contradiction

/-- The installed result, not just the planner, still references every intentional file. -/
theorem installed_keeps_intentional_files (closure : Nat → List File)
    (known expected : List Nat) (s actual installed : State) (selected : List Nat)
    (fresh : Nat) (f : File)
    (happly : applyCleanup closure known expected s selected fresh actual = some installed)
    (hf : f ∈ files closure (protectedRoots s.operations)) :
    f ∈ files closure (references installed.operations) := by
  unfold applyCleanup at happly
  split at happly
  · rename_i condition
    simp only [Bool.and_eq_true, preparedMatches] at condition
    have checks := condition.2
    cases happly
    simp only [files, List.mem_eraseDups, List.mem_flatMap] at hf ⊢
    obtain ⟨c, hc, hfile⟩ := hf
    have hactual : c ∈ protectedRoots actual.operations := by
      simpa using List.all_eq_true.mp checks.1.2.2 c hc
    have hrequired : c ∈ references actual.operations := by
      simpa using List.all_eq_true.mp checks.1.1.2 c hactual
    exact ⟨c, hrequired, hfile⟩
  · contradiction

end Musubi.Publication
