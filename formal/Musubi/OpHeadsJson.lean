/-
The oracle's `opHeads` request (`docs/internals/conformance.md`, "Moving op heads"): the
decisions of `OpHeads.lean` on operations the request gives, an operation being its place in
`ops`, its parents, its fingerprint (a number) and whether musubi's translation cache knows it.
`call` says which: `look` (`lookPlan`), `entries`, `compose` or `same`. Lists keep the order the
Rust code makes them in, which the reply keeps too.
-/
import Lean.Data.Json
import Musubi.OpHeads
import Musubi.ParentsBefore

namespace Musubi.OpHeads.Json

open Lean (Json ToJson toJson)

structure OpIn where
  parents : List Nat
  fp : Nat
  known : Bool

instance : Inhabited OpIn := ⟨{ parents := [], fp := 0, known := true }⟩

def getNats (j : Json) (k : String) : Except String (List Nat) := do
  return (← j.getObjValAs? (Array Nat) k).toList

def decodeOp (j : Json) : Except String OpIn := do
  let parents ← getNats j "parents"
  let fp ← j.getObjValAs? Nat "fp"
  let known ← j.getObjValAs? Bool "known"
  return { parents, fp, known }

/-- The graph a request names, and its size. Every operation's parents come before it. -/
def decodeGraph (j : Json) : Except String (Graph × Nat) := do
  let ops ← (← j.getObjValAs? (Array Json) "ops").toList.mapM decodeOp
  if !parentsBefore (ops.map (·.parents)) then
    throw "an operation's parents must come before it"
  let at_ (x : Nat) : OpIn := ops.getD x default
  return (⟨fun x => (at_ x).parents, fun x => (at_ x).fp, fun x => (at_ x).known⟩, ops.length)

def decodeReplaced (j : Json) : Except String Replaced := do
  let head ← j.getObjValAs? Nat "head"
  let fp ← j.getObjValAs? Nat "fp"
  let images ← getNats j "images"
  let put ← getNats j "by"
  return { head, fp, images, put }

def getReplaced (j : Json) (k : String) : Except String (List Replaced) := do
  (← j.getObjValAs? (Array Json) k).toList.mapM decodeReplaced

def encodeReplaced (r : Replaced) : Json :=
  Json.mkObj [("head", toJson r.head), ("fp", toJson r.fp), ("images", toJson r.images.toArray),
    ("by", toJson r.put.toArray)]

def encodeList (rs : List Replaced) : Json := Json.arr (rs.map encodeReplaced).toArray

def encodeLook : Look → Json
  | .nothing kept => Json.mkObj [("ok", Json.bool true), ("look", "nothing"),
      ("kept", encodeList kept)]
  | .retire out back kept n => Json.mkObj [("ok", Json.bool true), ("look", "retire"),
      ("out", toJson out.toArray), ("back", toJson back.toArray), ("kept", encodeList kept),
      ("rewritten", toJson n)]

def decodeFrom (j : Json) : Except String (List (Nat × List Nat)) := do
  (← j.getObjValAs? (Array Json) "from").toList.mapM fun e =>
    return ((← e.getObjValAs? Nat "head"), (← getNats e "images"))

/-- Every operation a request names is one of its operations. -/
def inRange (n : Nat) (ids : List Nat) : Except String Unit :=
  if ids.all (· < n) then pure () else throw "an operation the request names is not in ops"

def reply (j : Json) : Except String Json := do
  match ← j.getObjValAs? String "call" with
  | "look" =>
    let (g, n) ← decodeGraph j
    let heads ← getNats j "heads"
    let W ← getReplaced j "watch"
    inRange n (heads ++ W.flatMap fun r => [r.head] ++ r.images ++ r.put)
    return encodeLook (lookPlan g heads W)
  | "entries" =>
    let (g, n) ← decodeGraph j
    let read ← getNats j "read"
    let new ← getNats j "new"
    let from_ ← decodeFrom j
    inRange n (read ++ new ++ from_.flatMap fun (h, imgs) => h :: imgs)
    return Json.mkObj [("ok", Json.bool true), ("entries", encodeList (entries g read new from_))]
  | "compose" =>
    let W ← getReplaced j "watch"
    let E ← getReplaced j "replaced"
    return Json.mkObj [("ok", Json.bool true), ("watch", encodeList (compose W E))]
  | "same" =>
    return Json.mkObj [("ok", Json.bool true),
      ("same", Json.bool (same (← getNats j "a") (← getNats j "b")))]
  | c => throw s!"unknown call {c}"

end Musubi.OpHeads.Json
