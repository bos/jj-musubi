/-
Source selection from raw graph, namespace and record observations. No final owned map,
overlap bit, current-Git bit or preferred cache alias is an input to these decisions.
An evidence gap is not a claim that shipping Rust returns a refusal for the same trace.
-/
import Musubi.NativeLifecycle.Graph

namespace Musubi.NativeLifecycle

def copyText (copy : Copy) : String :=
  String.ofList copy.name ++ "#" ++ String.ofList copy.suffix

def orderedCopies (copies : List Copy) : List Copy :=
  (unique copies).mergeSort (fun a b => decide (copyText a ≤ copyText b))

def ownedKeys (me : Copy) (view : SharedBindings) : List Name :=
  view.filterMap fun (key, _) => if key.owner = me then some key.name else none

def ownNames (e : Evidence) (fuel : Nat) (me : Copy) (id : Canonical) : Query (List Name) := do
  if id = e.root then return []
  let b ← e.canonicalBody id
  let own := ownedKeys me b.workspaces
  if !own.isEmpty then return own
  let p ← presence e fuel id
  if present p me then return []
  let mut names := []
  for work in (lookup p.worked me).getD [] do
    if let some standing := work.standing then
      names := names ++ ownedKeys me (← e.canonicalBody standing).workspaces
  return unique names

def machinesOf (view : SharedBindings) (known : List Copy) : List Copy :=
  orderedCopies (known ++ view.map (·.1.owner))

def renderedNames (e : Evidence) (fuel : Nat) (me : Copy) (id : Canonical)
    (privateNames : List Name) : Query (List (WorkspaceKey × Name)) := do
  let b ← e.canonicalBody id
  let p ← presence e fuel id
  let machines := orderedCopies (me :: machinesOf b.workspaces p.known)
  let own := unique ((← ownNames e fuel me id) ++ privateNames)
  let prefixes := Names.assign machines own
  return b.workspaces.map fun (key, _) =>
    (key, Names.localName me prefixes key.owner key.name)

def namesOtherMachine (me : Copy) (name : Name) (machines : List Copy) : Bool :=
  if !name.contains '/' then false
  else
    let leading := name.takeWhile (· != '/')
    machines.any fun copy => decide (copy ≠ me) &&
      (Names.candidates true copy leading.length).contains leading

/-- Native commands follow their actual parents; restore/revert follow their native source.
A collected optional restore target certifies no names, matching the native boundary. -/
def privateNames (e : Evidence) (me : Copy) : Nat → Physical → Query (List Name)
  | 0, _ => .error .exhausted
  | fuel + 1, id => do
    let b ← e.nativeBody id
    let inherited ←
      if b.marker.isSome || e.joinInputs.contains id || b.parents.isEmpty then do
        match b.context with
        | none => pure []
        | some ns =>
          if !ns.valid then throw (.malformed "namespace attribute")
          pure (if ns.source = me then
            ns.names.filterMap (fun (name, key) => if key.owner = me then some name else none)
            else [])
      else do
        let sources := match b.source with
          | .parents => b.parents
          | .restore target =>
            if e.native.any (fun op => decide (op.id = target)) then [target] else []
          | .revert target =>
            ((e.native.find? (fun (op : NativeBody) => decide (op.id = target))).map
              (fun (op : NativeBody) => op.parents)).getD []
        pure (← sources.mapM (privateNames e me fuel)).flatten
    return unique (inherited.filter (fun name => (lookup b.workspaces name).isSome))

def prejoinInput (e : Evidence) (fuel : Nat) (id : Physical) : Query Bool := do
  for input in e.joinInputs do
    if ← nativeAncestor e fuel id input then return true
  return false

/-- A prejoin view has this copy's namespace. This interpretation does not give each
prejoin operation the canonical root as an actual counterpart. -/
def namespaceCanonical (e : Evidence) (fuel : Nat) (id : Physical) : Query Canonical := do
  let counterpart ← e.counterpart id
  if let some canonical := counterpart then return canonical
  if ← prejoinInput e fuel id then return e.root
  throw (.identity id)

/-- Source queries exclude known prejoin operations without a canonical counterpart.
Other missing identities remain evidence gaps rather than shrinking a candidate set. -/
def sourceCounterpart (e : Evidence) (fuel : Nat) (id : Physical) : Query (Option Canonical) := do
  let counterpart ← e.counterpart id
  if counterpart.isSome then return counterpart
  if ← prejoinInput e fuel id then return none
  throw (.identity id)

/-- Qualify before merging. Same-spelled foreign slots are removed using the complete
namespace, while an authenticated private literal can remain owned. -/
def ownOfNative (e : Evidence) (fuel : Nat) (me : Copy) (id : Physical) : Query Bindings := do
  let raw ← e.nativeBody id
  if !uniqueKeys raw.workspaces then throw (.malformed "duplicate native workspace")
  let canonical ← namespaceCanonical e fuel id
  if canonical = e.root then return raw.workspaces
  let literals ← privateNames e me fuel id
  let names ← renderedNames e fuel me canonical literals
  let others := names.filterMap fun (key, name) => if key.owner ≠ me then some name else none
  let body ← e.canonicalBody canonical
  let machines := machinesOf body.workspaces (← presence e fuel canonical).known
  let own ← ownNames e fuel me canonical
  return raw.workspaces.filter fun (name, _) =>
    !others.contains name && (literals.contains name || own.contains name ||
      !namesOtherMachine me name machines)

/-- The pinned jj workspace-slot rule, awaiting the independent native-law handoff. -/
def mergeBinding (ours base theirs : Option Commit) : Option Commit :=
  if ours = theirs then ours
  else if ours = base then theirs
  else if theirs = base then ours
  else if ours.isNone || theirs.isNone then none
  else ours

def mergeBindings (ours base theirs : Bindings) : Bindings :=
  (unique ((ours ++ base ++ theirs).map (·.1))).filterMap fun name =>
    (mergeBinding (lookup ours name) (lookup base name) (lookup theirs name)).map (name, ·)

def mergedOwned (e : Evidence) (me : Copy) : Nat → List Physical → Query Bindings
  | 0, _ => .error .exhausted
  | fuel + 1, heads => do
    match heads with
    | [] => return []
    | first :: rest =>
      let mut merged ← ownOfNative e (fuel + 1) me first
      let mut parents := [first]
      for other in rest do
        let bases ← orderedBases e (fuel + 1) parents other
        let base ← match bases with
          | [] => pure []
          | [one] => ownOfNative e (fuel + 1) me one
          | several => mergedOwned e me fuel several
        let theirs ← ownOfNative e (fuel + 1) me other
        merged := mergeBindings merged base theirs
        parents := parents ++ [other]
      return merged

def ownAtHeads (e : Evidence) (fuel : Nat) (me : Copy) (heads : List Physical) :
    Query Bindings := do
  let native ← heads.mapM e.nativeBody
  let ordered := native.mergeSort (fun a b =>
    if a.endTime = b.endTime then decide (a.id.value ≤ b.id.value)
    else decide (a.endTime ≤ b.endTime))
  mergedOwned e me fuel (ordered.map (·.id))

def receiptMatches (receipt : Receipt) (heads : List Physical) : Bool :=
  !receipt.switched && sameSet receipt.capturedHeads heads

def ownForRoot (e : Evidence) (fuel : Nat) (me : Copy) (heads : List Physical)
    (receipt : Option Receipt) : Query Bindings :=
  match receipt with
  | some r => if receiptMatches r heads then ownAtHeads r.input fuel me r.capturedHeads
      else ownAtHeads e fuel me heads
  | none => ownAtHeads e fuel me heads

def expandDropped (e : Evidence) (dropped : Drops) : Nat → Canonical → Query (List Canonical)
  | 0, _ => .error .exhausted
  | fuel + 1, id => do
    let body ← e.canonicalBody id
    if !dropped.contains body.original then return [id]
    return unique (← body.parents.mapM (expandDropped e dropped fuel)).flatten

/-- Derive the prepared base from actual record-leading comparison and dropped originals.
The first surviving expansion is selected in parent order; an absent base stays absent. -/
def preparedBase (e : Evidence) (fuel : Nat) (saved : Persistent) (r : Receipt) :
    Query (Option Canonical) := do
  let common := if saved.recordPrefix = r.recordPrefix ∧ saved.prunedCount = r.prunedCount then
    ((saved.applied.zip r.records).takeWhile (fun pair => decide (pair.1 = pair.2))).length
    else 0
  let base := if common < saved.applied.length then some e.root else saved.acceptedBase
  match base with
  | none => return none
  | some base =>
    let dropped := unique ((r.records.drop common).flatMap (·.drops))
    return (← expandDropped e dropped fuel base).head?

def rootBase (e : Evidence) (fuel : Nat) (saved : Persistent) (receipt : Option Receipt) :
    Query Bool := do
  match receipt with
  | none => return false
  | some r =>
    if r.switched then return false
    return (← preparedBase e fuel saved r) == some e.root

structure GitChoice where
  currentOwned : Bindings
  targetOwned : Bindings
  rootBase : Bool
  known : Bool
  present : Bool
  overlap : Bool
  useCurrent : Bool
deriving DecidableEq, Repr

/-- All inputs are complete observations. Output maps and booleans are compared answers. -/
def gitChoice (e : Evidence) (fuel : Nat) (me : Copy) (heads : List Physical)
    (target : Physical) (saved : Persistent) (receipt : Option Receipt) : Query GitChoice := do
  let currentOwned ← ownAtHeads e fuel me heads
  let targetOwned ← ownOfNative e fuel me target
  let canonical ← e.identity target
  let p ← presence e fuel canonical
  let root ← rootBase e fuel saved receipt
  let overlap := currentOwned.any (fun row => (lookup targetOwned row.1).isSome)
  let known := p.known.contains me
  let isPresent := present p me
  return {
    currentOwned, targetOwned, rootBase := root, known, present := isPresent, overlap,
    useCurrent := root || (known && !isPresent && overlap) }

inductive Role where
  | rendered
  | prepared
  | published
  | fallback
deriving DecidableEq, Repr

structure CandidateSet where
  values : List Physical := []
  unresolved : List (Physical × Gap) := []
deriving DecidableEq, Repr, Inhabited

structure Candidates where
  prepared : CandidateSet
  published : CandidateSet
  fallback : CandidateSet
deriving DecidableEq, Repr

def matchingCandidates (e : Evidence) (fuel : Nat) (ids : List Physical)
    (canonical : Canonical) : CandidateSet :=
  { values := (unique ids).filter (fun id => decide (sourceCounterpart e fuel id = .ok (some canonical))),
    unresolved := (unique ids).filterMap fun id => match sourceCounterpart e fuel id with
      | .error gap => some (id, gap)
      | .ok _ => none }

/-- Membership comes from the supplied raw domain and the executable identity query. This
does not assert that the native evidence rows have been authenticated. -/
theorem matchingCandidates_member {e : Evidence} {fuel : Nat} {ids : List Physical}
    {canonical : Canonical} {id : Physical}
    (h : id ∈ (matchingCandidates e fuel ids canonical).values) :
    id ∈ ids ∧ sourceCounterpart e fuel id = .ok (some canonical) := by
  have h' := List.mem_filter.1 h
  exact ⟨by simpa [unique] using h'.1, of_decide_eq_true h'.2⟩

/-- Candidate enumeration walks complete physical ancestry and full receipt locals. A
preferred translation-cache value is deliberately absent from this interface. -/
def candidates (e : Evidence) (fuel : Nat) (heads : List Physical)
    (receipt : Option Receipt) (canonical : Canonical) : Query Candidates := do
  let reachable ← nativeFrontierClosure e fuel heads
  let prepared := match receipt with
    | some r => if receiptMatches r heads then unique (r.locals.flatMap (·.2)) else []
    | none => []
  return {
    prepared := matchingCandidates e fuel prepared canonical,
    published := matchingCandidates e fuel reachable canonical,
    fallback := matchingCandidates e fuel (e.native.map (·.id)) canonical }

inductive SourceChoice where
  | missing
  | unavailable (role : Role) (gaps : List (Physical × Gap))
  | ambiguous (role : Role) (candidates : List Physical)
  | selected (role : Role) (physical : Physical)
deriving DecidableEq, Repr

def chooseSource (sources : Candidates) : SourceChoice :=
  let choose := fun (role : Role) (set : CandidateSet) =>
    if !set.unresolved.isEmpty then SourceChoice.unavailable role set.unresolved
    else match set.values with
      | [] => .missing
      | [id] => .selected role id
      | _ => .ambiguous role set.values
  if !sources.prepared.values.isEmpty || !sources.prepared.unresolved.isEmpty then
    choose .prepared sources.prepared
  else if !sources.published.values.isEmpty || !sources.published.unresolved.isEmpty then
    choose .published sources.published
  else choose .fallback sources.fallback

theorem chooseSource_prepared (sources : Candidates) (id : Physical)
    (values : sources.prepared.values = [id]) (complete : sources.prepared.unresolved = []) :
    chooseSource sources = .selected .prepared id := by
  simp [chooseSource, values, complete]

/-- U is a computed domain restriction, not a new runtime refusal or normalization guard. -/
def uniqueSource (sources : Candidates) : Bool :=
  match chooseSource sources with
  | .selected _ _ => true
  | _ => false

structure Suffix where
  order : List Canonical := []
  anchors : List (Canonical × SourceChoice) := []
  references : List (Canonical × SourceChoice) := []
deriving DecidableEq, Repr, Inhabited

/-- Compute the finite parents-first suffix, stopping only at actual published or exact
receipt counterparts. A disposable fallback alias does not shorten this walk. Reference
queries remain separate, so a restore target is never silently made an operation parent. -/
def suffix (e : Evidence) (heads : List Physical) (receipt : Option Receipt) :
    Nat → Canonical → Query Suffix
  | 0, _ => .error .exhausted
  | fuel + 1, id => do
    let sources ← candidates e (fuel + 1) heads receipt id
    let stopping := !sources.prepared.values.isEmpty || !sources.prepared.unresolved.isEmpty ||
      !sources.published.values.isEmpty || !sources.published.unresolved.isEmpty
    if stopping then return { anchors := [(id, chooseSource sources)] }
    let body ← e.canonicalBody id
    let parents ← body.parents.mapM (suffix e heads receipt fuel)
    let references ← body.references.mapM fun reference => do
      return (reference, chooseSource (← candidates e (fuel + 1) heads receipt reference))
    return {
      order := unique (parents.flatMap (·.order) ++ [id]),
      anchors := unique (parents.flatMap (·.anchors)),
      references := unique (parents.flatMap (·.references) ++ references) }

structure ParentSelection where
  /-- Original canonical parent order is retained even when a source is unavailable. -/
  choices : List (Canonical × SourceChoice)
deriving DecidableEq, Repr

def ParentSelection.parents (selection : ParentSelection) : Option (List Physical) :=
  selection.choices.mapM fun (_, choice) => match choice with
    | .selected _ id => some id
    | _ => none

def selectParents (e : Evidence) (fuel : Nat) (heads : List Physical)
    (receipt : Option Receipt) (canonical : Canonical) : Query ParentSelection := do
  let body ← e.canonicalBody canonical
  let choices ← body.parents.mapM fun parent => do
    return (parent, chooseSource (← candidates e fuel heads receipt parent))
  return { choices }

def followCommit (rewrites : List (Commit × List Commit)) : Nat → List Commit → Commit → Commit
  | 0, _, commit => commit
  | fuel + 1, seen, commit =>
    let next := rewrites.find? (fun row => row.2.contains commit)
    match next with
    | none => commit
    | some (next, _) => if seen.contains next then commit
        else followCommit rewrites fuel (next :: seen) next

def followBindings (rewrites : List (Commit × List Commit)) (bindings : Bindings) : Bindings :=
  bindings.map fun (name, commit) =>
    (name, followCommit rewrites (rewrites.length + 1) [] commit)

inductive OwnSource where
  | canonicalSlots
  | parent (index : Nat) (physical : Physical)
  | receipt (identity : Nat)
  | currentHeads
  | absent
deriving DecidableEq, Repr

structure OwnSelection where
  source : OwnSource
  bindings : Bindings
deriving DecidableEq, Repr

/-- The private-binding selector used while rendering. It derives the latest-work parent,
respects owner deletion, and uses receipt capture only for that exact unswitched frontier.
Physical parents must have been selected in canonical parent order by the caller. -/
def selectOwn (e : Evidence) (fuel : Nat) (me : Copy) (canonical : Canonical)
    (parents heads : List Physical) (receipt : Option Receipt) : Query OwnSelection := do
  let body ← e.canonicalBody canonical
  let sharedOwn := body.workspaces.filterMap fun (key, commit) =>
    if key.owner = me then some (key.name, commit) else none
  if !sharedOwn.isEmpty then return ⟨.canonicalSlots, sharedOwn⟩
  if parents.length ≠ body.parents.length then throw (.malformed "parent vector length")
  for (physical, canonicalParent) in parents.zip body.parents do
    if (← e.identity physical) ≠ canonicalParent then
      throw (.malformed "parent vector identity")
  let index ← latestWorkParent e fuel me body.parents
  let some parent := parents[index]? | return ⟨.absent, []⟩
  let mut own ← ownOfNative e fuel me parent
  let mut source := OwnSource.parent index parent
  if own.isEmpty && parent = e.physicalRoot then
    own ← ownForRoot e fuel me heads receipt
    source := match receipt with
      | some r => if receiptMatches r heads then .receipt r.identity else .currentHeads
      | none => .currentHeads
  let p ← presence e fuel canonical
  if own.isEmpty || (body.work ≠ some me && !body.fixup && present p me) then
    return ⟨.absent, []⟩
  return ⟨source, followBindings body.rewrites own⟩

end Musubi.NativeLifecycle
