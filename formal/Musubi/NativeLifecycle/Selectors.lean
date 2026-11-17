/-
Source selection from raw graph, namespace and record observations: which physical operation
stands for each canonical parent, which workspace names this copy owns, and the prepared base.
No final owned map, overlap bit, current-Git bit or cached alias is an input. A gap in the
evidence is reported as a gap; it is not a claim that shipping Rust refuses the same trace.
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

/-- Missing identity material is a typed result, not absence. Every recursive query uses
the current positive rows and raw retained material, so new evidence rechecks dependencies. -/
def classifyIdentity (e : Evidence) : Nat → Physical → Query IdentityClass
  | 0, _ => .ok (.unresolved .exhausted)
  | fuel + 1, id => do
    let raw ← e.nativeBody id
    let rows := e.identities.filter (fun row => decide (row.physical = id))
    for row in rows do e.checkIdentity row
    if let some row := rows.head? then return .known row
    if id = e.physicalRoot then
      return .known ⟨id, e.root, (← e.canonicalBody e.root).original, .original⟩
    if let some marker := raw.marker then
      return .known ⟨id, marker, (← e.canonicalBody marker).original, .markedBody⟩
    let fingerprint := lookup e.nativeFingerprints id
    if let some fingerprint := fingerprint then
      let joins := unique ((e.joinFingerprints.filter (fun row => row.2 == fingerprint)).map (·.1))
      match joins with
      | [canonical] =>
        return .known ⟨id, canonical, (← e.canonicalBody canonical).original, .original⟩
      | _ :: _ => return .unresolved .ambiguous
      | [] => pure ()
    for input in e.joinInputs do
      if ← nativeAncestor e (fuel + 1) id input then return .prejoin input
    let some fingerprint := fingerprint | return .unresolved .missingFingerprint
    let mut parents := []
    for parent in raw.parents do
      match ← classifyIdentity e fuel parent with
      | .known row => parents := unique (parents ++ [row.canonical])
      | .prejoin _ => pure ()
      | .unresolved _ => return .unresolved (.dependency parent)
    let canonicalParents := if parents.isEmpty then [e.root] else parents
    let originals := (e.originalFingerprints.filter (fun row => row.2 == fingerprint)).map (·.1)
    let candidates := unique ((e.canonical.filter (fun body =>
      originals.contains body.original && decide (body.parents = canonicalParents))).map (·.id))
    match candidates with
    | [canonical] =>
      return .known ⟨id, canonical, (← e.canonicalBody canonical).original, .original⟩
    | [] => return .unresolved .noMatch
    | _ => return .unresolved .ambiguous

/-- New positive evidence must agree with all existing positive classification, including
raw marker/fingerprint results. No retained material is erased; dependencies are recomputed. -/
def Evidence.installIdentities (e : Evidence) (rows : List IdentityRow) : Query Evidence := do
  let mut result := e
  for row in rows do
    result.checkIdentity row
    match ← classifyIdentity result (result.native.length + result.canonical.length + 1) row.physical with
    | .known prior =>
      if prior.canonical ≠ row.canonical || prior.original ≠ row.original then
        throw (.malformed "new identity conflicts with established identity")
    | .prejoin _ => throw (.malformed "new identity conflicts with established prejoin")
    | .unresolved _ => pure ()
    result := { result with identities := unique (result.identities ++ [row]) }
  return result

def Evidence.identity (e : Evidence) (id : Physical) : Query Canonical := do
  match ← classifyIdentity e (e.native.length + e.canonical.length + 1) id with
  | .known row => return row.canonical
  | .prejoin _ => throw (.identity id)
  | .unresolved issue => throw (.unresolvedIdentity id issue)

/-- Only independently established prejoin ancestry supplies a negative counterpart.
An unresolved member remains a gap in every role domain that consults it. -/
def sourceCounterpart (e : Evidence) (fuel : Nat) (id : Physical) : Query (Option Canonical) := do
  match ← classifyIdentity e fuel id with
  | .known row => return some row.canonical
  | .prejoin _ => return none
  | .unresolved issue => throw (.unresolvedIdentity id issue)

def Evidence.counterpart (e : Evidence) (id : Physical) : Query (Option Canonical) :=
  sourceCounterpart e (e.native.length + e.canonical.length + 1) id

theorem sourceCounterpart_none {e : Evidence} {fuel : Nat} {id : Physical}
    (success : sourceCounterpart e fuel id = .ok none) :
    ∃ input, classifyIdentity e fuel id = .ok (.prejoin input) := by
  cases classified : classifyIdentity e fuel id with
  | error gap => simp [sourceCounterpart, classified, bind, Except.bind] at success
  | ok result =>
    cases result with
    | known row => simp [sourceCounterpart, classified, bind, Except.bind,
        pure, Except.pure] at success
    | unresolved issue => simp [sourceCounterpart, classified, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw] at success
    | prejoin input => exact ⟨input, rfl⟩

/-- A prejoin view has this copy's namespace. This interpretation does not give each
prejoin operation the canonical root as an actual counterpart. -/
def namespaceCanonical (e : Evidence) (fuel : Nat) (id : Physical) : Query Canonical := do
  let counterpart ← e.counterpart id
  if let some canonical := counterpart then return canonical
  if ← prejoinInput e fuel id then return e.root
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

/-- jj's three-way merge of one workspace slot, as pinned. -/
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

/-- Whether the records being taken drop one of `heads`, the current op heads, by immutable
original: the readable records after the common prefix, and records in custody that they lack.
What moving the heads leaves in a dropped head's place is below it, without its changes to this
copy's Git record, such as the HEAD its commit recorded. A head with no canonical identity, as
a native command's not yet translated, is never dropped. Rust's `taking_drops_a_head` tests the
head's canonical id against a dropped set holding every local version of each dropped original,
which is this test by original. -/
def dropsHead (e : Evidence) (saved : Persistent) (heads : List Physical)
    (receipt : Option Receipt) : Bool :=
  match receipt with
  | none => false
  | some r =>
    let common := if saved.recordPrefix = r.recordPrefix ∧ saved.prunedCount = r.prunedCount then
      ((saved.applied.zip r.records).takeWhile (fun pair => decide (pair.1 = pair.2))).length
      else 0
    let held := r.recordPrefix :: r.records.map (·.identity)
    let dropped := (r.records.drop common).flatMap (·.drops) ++
      (saved.custody.filter (fun record => !held.contains record.identity)).flatMap (·.drops)
    !r.switched && heads.any fun head =>
      e.identities.any fun row => decide (row.physical = head) && dropped.contains row.original

structure GitChoice where
  currentOwned : Bindings
  targetOwned : Bindings
  rootBase : Bool
  dropsHead : Bool
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
  let drops := dropsHead e saved heads receipt
  let overlap := currentOwned.any (fun row => (lookup targetOwned row.1).isSome)
  let known := p.known.contains me
  let isPresent := present p me
  return {
    currentOwned, targetOwned, rootBase := root, dropsHead := drops, known,
    present := isPresent, overlap, useCurrent := root || drops || (known && !isPresent && overlap) }

inductive Role where
  | rendered
  | prepared
  | published
  | fallback
deriving DecidableEq, Repr

structure CandidateSet where
  values : List Physical := []
  unresolved : List (Physical × Gap) := []
  excluded : List DescriptionExclusion := []
deriving DecidableEq, Repr, Inhabited

structure Candidates where
  prepared : CandidateSet
  published : CandidateSet
  fallback : CandidateSet
deriving DecidableEq, Repr

/-- The finite ordinary route is closed only by independently parsed durable state AND
the supplied memory relations. A missing observation or any alternate route remains a gap.
The target is this exact canonical version/original, never its drop expansion. -/
def descriptionExclusion (e : Evidence) (id : Physical) (target : Canonical) :
    Query (Option { w : DescriptionExclusion // w.necessary }) := do
  let raw ← e.nativeBody id
  let body ← e.canonicalBody target
  if raw.description = body.description then return none
  if raw.marker.isSome || raw.source ≠ .parents ||
      restoreDescription raw.description || restoreDescription body.description then return none
  -- An explicit join can replace the description and maps its old head. Its canonical
  -- constructor has no author workspace; this slice also requires an ordinary target.
  if body.authorWorkspace.isNone then return none
  let some routes := e.sourceRoutes | throw (.nativeFact "complete source-route snapshot missing")
  if !routes.closed || !e.joinInputs.isEmpty || !e.joinFingerprints.isEmpty then
    throw (.nativeFact "nonempty source/join/accepted route needs identity authentication")
  if different : raw.description ≠ body.description then
    return some ⟨{
      physical := id, target, targetOriginal := body.original,
      nativeDescription := raw.description, originalDescription := body.description }, different⟩
  else return none

theorem descriptionExclusion_necessary {e : Evidence} {id : Physical} {target : Canonical}
    {w : { w : DescriptionExclusion // w.necessary }}
    (_computed : descriptionExclusion e id target = .ok (some w)) :
    ordinaryOriginalDescription w.val.nativeDescription ≠ w.val.originalDescription := w.property

theorem descriptionExclusion_pinned {e : Evidence} {id : Physical} {target : Canonical}
    {w : { w : DescriptionExclusion // w.necessary }}
    (computed : descriptionExclusion e id target = .ok (some w)) :
    w.val.physical = id ∧ w.val.target = target := by
  cases native : e.nativeBody id with
  | error gap => simp [descriptionExclusion, native, bind, Except.bind] at computed
  | ok raw =>
    cases canonical : e.canonicalBody target with
    | error gap => simp [descriptionExclusion, native, canonical, bind, Except.bind] at computed
    | ok body =>
      simp only [descriptionExclusion, native, canonical, bind, Except.bind] at computed
      split at computed <;> try simp_all [pure, Except.pure]
      split at computed <;> try simp_all
      split at computed <;> try simp_all
      cases routes : e.sourceRoutes with
      | none => simp [routes, throw, throwThe, MonadExceptOf.throw] at computed
      | some value =>
        simp only [routes] at computed
        split at computed <;> try simp_all [throw, throwThe,
          MonadExceptOf.throw]
        rw [← computed]
        exact ⟨rfl, rfl⟩

inductive CandidateComparison where
  | unrelated
  | excluded (w : { w : DescriptionExclusion // w.necessary })
  | unresolved (gap : Gap)

def compareCandidate (e : Evidence) (fuel : Nat) (id : Physical) (target : Canonical) :
    CandidateComparison :=
  match sourceCounterpart e fuel id with
  | .ok _ => .unrelated
  | .error gap =>
    match gap with
    | .unresolvedIdentity _ _ =>
      match descriptionExclusion e id target with
      | .ok (some w) => .excluded w
      | .ok none => .unresolved gap
      | .error missing => .unresolved missing
    | _ => .unresolved gap

def matchingCandidates (e : Evidence) (fuel : Nat) (ids : List Physical)
    (canonical : Canonical) : CandidateSet :=
  { values := (unique ids).filter (fun id => decide (sourceCounterpart e fuel id = .ok (some canonical))),
    unresolved := (unique ids).filterMap fun id => match compareCandidate e fuel id canonical with
      | .unresolved gap => some (id, gap)
      | _ => none,
    excluded := (unique ids).filterMap fun id => match compareCandidate e fuel id canonical with
      | .excluded w => some w.val
      | _ => none }

/-- Membership comes from the supplied raw domain and the executable identity query. This
does not assert that the native evidence rows have been authenticated. -/
theorem matchingCandidates_member {e : Evidence} {fuel : Nat} {ids : List Physical}
    {canonical : Canonical} {id : Physical}
    (h : id ∈ (matchingCandidates e fuel ids canonical).values) :
    id ∈ ids ∧ sourceCounterpart e fuel id = .ok (some canonical) := by
  have h' := List.mem_filter.1 h
  exact ⟨by simpa [unique] using h'.1, of_decide_eq_true h'.2⟩

theorem matchingCandidates_gap {e : Evidence} {fuel : Nat} {ids : List Physical}
    {canonical : Canonical} {id : Physical} {gap : Gap} (member : id ∈ ids)
    (unresolved : compareCandidate e fuel id canonical = .unresolved gap) :
    (id, gap) ∈ (matchingCandidates e fuel ids canonical).unresolved := by
  apply List.mem_filterMap.mpr
  exact ⟨id, by simpa [unique] using member, by simp [unresolved]⟩

theorem matchingCandidates_excluded_necessary {e : Evidence} {fuel : Nat}
    {ids : List Physical} {canonical : Canonical} {w : DescriptionExclusion}
    (member : w ∈ (matchingCandidates e fuel ids canonical).excluded) : w.necessary := by
  obtain ⟨id, _, result⟩ := List.mem_filterMap.mp member
  cases compared : compareCandidate e fuel id canonical with
  | unrelated => simp [compared] at result
  | unresolved gap => simp [compared] at result
  | excluded checked =>
    simp only [compared, Option.some.injEq] at result
    subst w
    exact checked.property

theorem matchingCandidates_accounted {e : Evidence} {fuel : Nat} {ids : List Physical}
    {canonical : Canonical} {id : Physical} (member : id ∈ ids) :
    match compareCandidate e fuel id canonical with
    | .unrelated => True
    | .unresolved gap => (id, gap) ∈ (matchingCandidates e fuel ids canonical).unresolved
    | .excluded checked => checked.val ∈ (matchingCandidates e fuel ids canonical).excluded ∧
        checked.val.necessary := by
  cases compared : compareCandidate e fuel id canonical with
  | unrelated => trivial
  | unresolved gap => exact matchingCandidates_gap member compared
  | excluded checked =>
    constructor
    · apply List.mem_filterMap.mpr
      exact ⟨id, by simpa [unique] using member, by simp [compared]⟩
    · exact checked.property

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

theorem candidates_complete {e : Evidence} {fuel : Nat} {heads : List Physical}
    {receipt : Option Receipt} {canonical : Canonical} {sources : Candidates}
    (computed : candidates e fuel heads receipt canonical = .ok sources) :
    ∃ reachable, nativeFrontierClosure e fuel heads = .ok reachable ∧
      sources.prepared = matchingCandidates e fuel (match receipt with
        | some r => if receiptMatches r heads then unique (r.locals.flatMap (·.2)) else []
        | none => []) canonical ∧
      sources.published = matchingCandidates e fuel reachable canonical ∧
      sources.fallback = matchingCandidates e fuel (e.native.map (·.id)) canonical := by
  unfold candidates at computed
  cases walk : nativeFrontierClosure e fuel heads with
  | error gap => simp [walk, bind, Except.bind] at computed
  | ok reachable =>
    simp only [walk, bind, Except.bind, pure, Except.pure] at computed
    have same := Except.ok.inj computed
    subst sources
    refine ⟨reachable, rfl, ?_, rfl, rfl⟩
    cases receipt <;> rfl

inductive SourceChoice where
  | missing
  | unavailable (role : Role) (gaps : List (Physical × Gap))
  | ambiguous (role : Role) (candidates : List Physical)
  | selected (role : Role) (physical : Physical)
deriving DecidableEq, Repr

def chooseTier (role : Role) (set : CandidateSet) : SourceChoice :=
  if set.unresolved ≠ [] then .unavailable role set.unresolved
  else match set.values with
    | [] => .missing
    | [id] => .selected role id
    | _ => .ambiguous role set.values

def chooseSource (sources : Candidates) : SourceChoice :=
  if sources.prepared.values ≠ [] ∨ sources.prepared.unresolved ≠ [] then
    chooseTier .prepared sources.prepared
  else if sources.published.values ≠ [] ∨ sources.published.unresolved ≠ [] then
    chooseTier .published sources.published
  else chooseTier .fallback sources.fallback

def Candidates.domain (sources : Candidates) : Role → CandidateSet
  | .prepared => sources.prepared
  | .published => sources.published
  | .fallback => sources.fallback
  | .rendered => {}

def Candidates.higherClear (sources : Candidates) : Role → Prop
  | .prepared => True
  | .published => sources.prepared.values = [] ∧ sources.prepared.unresolved = []
  | .fallback => sources.prepared.values = [] ∧ sources.prepared.unresolved = [] ∧
      sources.published.values = [] ∧ sources.published.unresolved = []
  | .rendered => False

theorem chooseTier_selected {tier role : Role} {set : CandidateSet} {id : Physical}
    (success : chooseTier tier set = .selected role id) :
    role = tier ∧ set.values = [id] ∧ set.unresolved = [] := by
  cases gaps : set.unresolved with
  | cons gap rest => simp [chooseTier, gaps] at success
  | nil =>
    cases values : set.values with
    | nil => simp [chooseTier, gaps, values] at success
    | cons first rest =>
      cases rest with
      | cons other more => simp [chooseTier, gaps, values] at success
      | nil =>
        simp only [chooseTier, gaps, ne_eq, not_true_eq_false, ↓reduceIte, values,
          SourceChoice.selected.injEq] at success
        obtain ⟨rfl, rfl⟩ := success
        exact ⟨rfl, rfl, rfl⟩

/-- Priority and completeness follow from the computed choice. Lower tiers remain in
the corpus, but cannot block a positive higher tier that the model independently selects. -/
theorem chooseSource_selected {sources : Candidates} {role : Role} {id : Physical}
    (success : chooseSource sources = .selected role id) :
    (sources.domain role).values = [id] ∧
      (sources.domain role).unresolved = [] ∧ sources.higherClear role := by
  unfold chooseSource at success
  split at success
  · obtain ⟨rfl, values, gaps⟩ := chooseTier_selected success
    exact ⟨values, gaps, True.intro⟩
  · rename_i inactivePrepared
    have prepared : sources.prepared.values = [] ∧ sources.prepared.unresolved = [] := by
      exact ⟨Classical.byContradiction (fun h => inactivePrepared (.inl h)),
        Classical.byContradiction (fun h => inactivePrepared (.inr h))⟩
    split at success
    · obtain ⟨rfl, values, gaps⟩ := chooseTier_selected success
      exact ⟨values, gaps, prepared⟩
    · rename_i inactivePublished
      have published : sources.published.values = [] ∧ sources.published.unresolved = [] := by
        exact ⟨Classical.byContradiction (fun h => inactivePublished (.inl h)),
          Classical.byContradiction (fun h => inactivePublished (.inr h))⟩
      obtain ⟨rfl, values, gaps⟩ := chooseTier_selected success
      exact ⟨values, gaps, prepared.1, prepared.2, published.1, published.2⟩

theorem computedSource_selected {e : Evidence} {fuel : Nat} {heads : List Physical}
    {receipt : Option Receipt} {canonical : Canonical} {sources : Candidates}
    {role : Role} {id : Physical}
    (computed : candidates e fuel heads receipt canonical = .ok sources)
    (chosen : chooseSource sources = .selected role id) :
    sourceCounterpart e fuel id = .ok (some canonical) ∧
      (sources.domain role).unresolved = [] ∧ sources.higherClear role := by
  obtain ⟨values, gaps, higher⟩ := chooseSource_selected chosen
  have member : id ∈ (sources.domain role).values := by rw [values]; simp
  obtain ⟨reachable, _, prepared, published, fallback⟩ := candidates_complete computed
  have qualified : sourceCounterpart e fuel id = .ok (some canonical) := by
    cases role with
    | rendered => exact False.elim higher
    | prepared =>
      have included := member
      simp only [Candidates.domain, prepared] at included
      exact (matchingCandidates_member included).2
    | published =>
      have included := member
      simp only [Candidates.domain, published] at included
      exact (matchingCandidates_member included).2
    | fallback =>
      have included := member
      simp only [Candidates.domain, fallback] at included
      exact (matchingCandidates_member included).2
  exact ⟨qualified, gaps, higher⟩

theorem chooseSource_prepared (sources : Candidates) (id : Physical)
    (values : sources.prepared.values = [id]) (complete : sources.prepared.unresolved = []) :
    chooseSource sources = .selected .prepared id := by
  simp [chooseSource, chooseTier, values, complete]

/-- Holds when the source query selects exactly one physical operation. This is the model's
domain U: the inputs for which every source answer is unique. It is a restriction on the
model's inputs, computed here, not a runtime refusal or a normalization step; outside it the
model records the gap (`Outside.sources`). -/
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
