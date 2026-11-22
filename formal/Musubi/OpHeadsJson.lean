/-
The oracle's `opHeads` request (`docs/internals/conformance.md`, "Moving op heads"): the
decisions of `OpHeads.lean`. `call` says which; there is one, `same`. Lists keep the order the
Rust code makes them in, which the reply keeps too.
-/
import Lean.Data.Json
import Musubi.OpHeads

namespace Musubi.OpHeads.Json

open Lean (Json)

def getNats (j : Json) (k : String) : Except String (List Nat) := do
  return (← j.getObjValAs? (Array Nat) k).toList

def reply (j : Json) : Except String Json := do
  match ← j.getObjValAs? String "call" with
  | "same" =>
    return Json.mkObj [("ok", Json.bool true),
      ("same", Json.bool (same (← getNats j "a") (← getNats j "b")))]
  | c => throw s!"unknown call {c}"

end Musubi.OpHeads.Json
