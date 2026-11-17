/-
Graph and presence queries over complete finite observations: ancestry, closest bases, latest
work and presence stamps. Fuel exhaustion and unreadable bodies are reported as evidence gaps.
A raw stamp names the originals a body presents, not who owns it. Correspondence with the native
parsers and with the stamping of `PresenceContract.lean` is not proved.
-/
import Musubi.NativeLifecycle.Types

namespace Musubi.NativeLifecycle

def canonicalClosure (e : Evidence) : Nat → Canonical → Query (List Canonical)
  | 0, _ => .error .exhausted
  | fuel + 1, id => do
    let b ← e.canonicalBody id
    let parents ← b.parents.mapM (canonicalClosure e fuel)
    return unique (parents.flatten ++ [id])

def nativeClosure (e : Evidence) : Nat → Physical → Query (List Physical)
  | 0, _ => .error .exhausted
  | fuel + 1, id => do
    let b ← e.nativeBody id
    let parents ← b.parents.mapM (nativeClosure e fuel)
    return unique (parents.flatten ++ [id])

def canonicalAncestor (e : Evidence) (fuel : Nat) (a b : Canonical) : Query Bool := do
  return (← canonicalClosure e fuel b).contains a

def nativeAncestor (e : Evidence) (fuel : Nat) (a b : Physical) : Query Bool := do
  return (← nativeClosure e fuel b).contains a

def nativeFrontierClosure (e : Evidence) (fuel : Nat) (heads : List Physical) :
    Query (List Physical) := do
  return unique (← heads.mapM (nativeClosure e fuel)).flatten

def closestBases (e : Evidence) (fuel : Nat) (left : List Physical) (right : Physical) :
    Query (List Physical) := do
  let ours ← nativeFrontierClosure e fuel left
  let theirs ← nativeClosure e fuel right
  let common := ours.filter (theirs.contains ·)
  let mut maximal := []
  for a in common do
    let mut below := false
    for b in common do
      if a ≠ b && (← nativeAncestor e fuel a b) then below := true
    if !below then maximal := maximal ++ [a]
  return maximal

/-- Native base enumeration order is needed only where several closest bases exist. Its
membership is checked against the complete graph, never against the adapter's chosen base. -/
def orderedBases (e : Evidence) (fuel : Nat) (left : List Physical) (right : Physical) :
    Query (List Physical) := do
  let computed ← closestBases e fuel left right
  match computed with
  | [] => return []
  | [base] => return [base]
  | _ =>
    let some observed := e.bases.find? (fun o => decide (o.left = left ∧ o.right = right))
      | throw (.nativeBases left right)
    if !sameSet observed.bases computed || !(decide observed.bases.Nodup) then
      throw (.malformed "native bases differ from complete graph")
    return observed.bases

def workContains (xs : List Work) (w : Work) : Bool := xs.any (workEq · w)

def uniqueWork (xs : List Work) : List Work :=
  xs.foldl (fun acc w => if workContains acc w then acc else acc ++ [w]) []

/-- Same relation as Work::below: erased work is below concrete work; two erased works
remain unordered. Original equality is handled by set membership before this relation. -/
def workBelow (e : Evidence) (fuel : Nat) (a b : Work) : Query Bool :=
  match a.standing, b.standing with
  | some a, some b => canonicalAncestor e fuel a b
  | none, some _ => .ok true
  | _, none => .ok false

def mergeWork (e : Evidence) (fuel : Nat) (prior theirs : List Work) : Query (List Work) := do
  let added := theirs.filter (fun w => !workContains prior w)
  let mut older : List Original := []
  for a in prior.filter (fun w => !workContains theirs w) do
    for b in added do
      if ← workBelow e fuel a b then older := a.original :: older
      else if ← workBelow e fuel b a then older := b.original :: older
  return (uniqueWork (prior ++ added)).filter (fun w => !older.contains w.original)

def mergePresence (e : Evidence) (fuel : Nat)
    (parents : List (Canonical × Presence)) : Query Presence := do
  match parents with
  | [] => return {}
  | [(_, p)] => return p
  | (_, first) :: rest =>
    let known := unique (parents.flatMap (·.2.known))
    let mut worked := first.worked
    let mut forgetAfter := first.forgetAfter
    for (_, p) in rest do
      for (copy, work) in p.worked do
        let prior := (lookup worked copy).getD []
        worked := put worked copy (← mergeWork e fuel prior work)
      for (copy, records) in p.forgetAfter do
        let prior := (lookup forgetAfter copy).getD []
        let selected ← mergeWork e fuel (prior.map (·.1)) (records.map (·.1))
        let kept := selected.filterMap fun work =>
          ((prior ++ records).find? (fun entry => workEq entry.1 work)).map
            (fun entry => (work, entry.2))
        forgetAfter := put forgetAfter copy kept
    let copies := unique (parents.flatMap (fun p => p.2.latest.map (·.1)))
    let mut latest := []
    for copy in copies do
      let candidates := uniqueWork (parents.flatMap (fun p => (lookup p.2.latest copy).getD []))
      let mut kept := []
      for candidate in candidates do
        let mut survives := true
        for (id, p) in parents do
          if !workContains ((lookup p.latest copy).getD []) candidate &&
              (← workBelow e fuel candidate ⟨⟨0⟩, some id⟩) then
            survives := false
        if survives then kept := kept ++ [candidate]
      if !kept.isEmpty then latest := latest ++ [(copy, kept)]
    return { known, latest, worked, forgetAfter }

def applyKind (b : CanonicalBody) (p : Presence) : Presence := Id.run do
  let known := unique (p.known ++ b.work.toList ++ b.forgets)
  let mut latest := p.latest
  let mut worked := p.worked
  let mut forgetAfter := p.forgetAfter
  if let some copy := b.work then
    let w := [({ original := b.original, standing := some b.id } : Work)]
    latest := put latest copy w
    worked := put worked copy w
    if let some duration := b.forgetAfter then
      forgetAfter := put forgetAfter copy [(⟨b.original, some b.id⟩, duration)]
  latest := latest.filter (fun e => !b.forgets.contains e.1)
  return { known, latest, worked, forgetAfter }

def readStamp (b : CanonicalBody) (merged : Presence) (stamp : Stamp) : Query Presence := do
  if !uniqueKeys stamp.latest || !uniqueKeys stamp.worked ||
      !uniqueKeys stamp.forgetAfter ||
      !(stamp.latest ++ stamp.worked).all (fun row => stamp.known.contains row.1) ||
      !stamp.forgetAfter.all (fun row => stamp.known.contains row.1) then
    throw (.malformed "presence stamp keys")
  let standing := (merged.latest ++ merged.worked).flatMap (·.2) ++
    merged.forgetAfter.flatMap (fun row => row.2.map (·.1))
  let resolve := fun original =>
    ({ original := original, standing := (if original = b.original then some b.id
      else (standing.find? (fun w => decide (w.original = original))).bind (·.standing)) } : Work)
  let latest := stamp.latest.map (fun row => (row.1, row.2.map resolve))
  let worked := stamp.worked.map (fun row => (row.1, row.2.map resolve))
  let forgetAfter := stamp.forgetAfter.map fun row =>
    (row.1, row.2.map (fun entry => (resolve entry.1, entry.2)))
  return { known := unique stamp.known, latest := latest, worked := worked, forgetAfter }

def presence (e : Evidence) : Nat → Canonical → Query Presence
  | 0, _ => .error .exhausted
  | fuel + 1, id => do
    let body ← e.canonicalBody id
    let parents ← body.parents.mapM fun parent => do
      return (parent, ← presence e fuel parent)
    let merged ← mergePresence e (fuel + 1) parents
    match body.stamp with
    | some stamp => readStamp body merged stamp
    | none => return applyKind body merged

def present (p : Presence) (copy : Copy) : Bool :=
  !((lookup p.latest copy).getD []).isEmpty

/-- Latest-work parent selection is executable and compares sets by original identity.
No supplied dominating-parent index is accepted. -/
def latestWorkParent (e : Evidence) (fuel : Nat) (copy : Copy)
    (parents : List Canonical) : Query Nat := do
  let worked ← parents.mapM fun id => do
    return (lookup (← presence e fuel id).worked copy).getD []
  if worked.isEmpty then return 0
  for index in List.range worked.length do
    let mine := worked[index]!
    let mut covers := true
    for theirs in worked do
      for work in theirs.filter (fun w => !workContains mine w) do
        let mut seen := false
        for later in mine do
          if ← workBelow e fuel work later then seen := true
        if !seen then covers := false
    if covers then return index
  return 0

end Musubi.NativeLifecycle
