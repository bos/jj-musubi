/-
The oracle's `realization` request (`docs/internals/conformance.md`, "Realization"): what jj shows
once musubi has published a realization, and what stays in the op log, from `Realize.lean`.

The request names operations by numbers, each with its parents, every parent numbered before its
operation; an operation it doesn't list has no parents, as the root `0`. `heads` are the op heads
musubi read, and `realization` the realization it publishes. The reply's `merge` is `settledE`,
the operations whose merge jj shows, in the order of `heads` and then the realization; `kept` is
`keptE`, every operation below them, in increasing order.
-/
import Lean.Data.Json
import Musubi.Realize

namespace Musubi.Realize.Json

open Lean (Json toJson)

/-- The parents the request gives an operation. -/
def parOf (g : List (Nat × List Nat)) (x : Nat) : List Nat :=
  match g.find? (·.1 == x) with
  | some (_, ps) => ps
  | none => []

def reply (j : Json) : Except String Json := do
  let g := (← j.getObjValAs? (Array (Nat × Array Nat)) "parents").toList.map
    fun (x, ps) => (x, ps.toList)
  let heads := (← j.getObjValAs? (Array Nat) "heads").toList
  let r ← j.getObjValAs? Nat "realization"
  unless g.all fun (x, ps) => ps.all (· < x) do
    throw "every parent must be numbered before its operation"
  unless (g.map (·.1)).Nodup do
    throw "an operation is listed twice"
  let known (x : Nat) : Bool := x == 0 || g.any (·.1 == x)
  unless known r && heads.all known do
    throw "the op heads and the realization must be listed"
  if heads.isEmpty then throw "there must be an op head"
  let par := parOf g
  return Json.mkObj [("ok", Json.bool true), ("merge", toJson (settledE par heads r)),
    ("kept", toJson (keptE par (heads ++ [r])))]

end Musubi.Realize.Json
