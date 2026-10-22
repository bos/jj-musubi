/-
JSON codec for the oracle (`docs/conformance.md`, "Wire format"). Decoding and encoding only;
no protocol logic.
-/
import Lean.Data.Json
import Musubi.Exec

namespace Musubi.Exec.Json

open Lean (Json ToJson toJson)

/-! ## Decoding -/

def getNat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k

def getNats (j : Json) (k : String) : Except String (List Nat) := do
  let a ← j.getObjValAs? (Array Nat) k
  pure a.toList

def decodeHeadKind : String → Except String HeadKind
  | "head" => pure .head
  | "accepted" => pure .accepted
  | "rejected" => pure .rejected
  | "incomplete" => pure .incomplete
  | "notify" => pure .notify
  | k => throw s!"unknown headKind {k}"

def decodeAction (j : Json) : Except String Action := do
  let kind ← j.getObjValAs? String "kind"
  let node := getNat j "node"
  match kind with
  | "userOp" => return .userOp (← node) (← getNat j "parent") (← getNats j "objs")
  | "merge" => return .merge (← node) (← getNats j "parents") (← getNats j "objs")
  | "getHead" => return .getHead (← node)
  | "learn" =>
    return .learn (← node) (← decodeHeadKind (← j.getObjValAs? String "headKind"))
      (← getNat j "seq") (← getNat j "head")
  | "fetchOps" => return .fetchOps (← node) (← getNats j "ops")
  | "fetchObjs" => return .fetchObjs (← node) (← getNats j "objs")
  | "recvOps" => return .recvOps (← node) (← getNats j "ops")
  | "recvObjs" => return .recvObjs (← node) (← getNats j "objs")
  | "realize" => return .realize (← node) (← getNat j "opId")
  | "advance" => return .advance (← node)
  | "uploadOps" => return .uploadOps (← node) (← getNats j "ops")
  | "uploadObjs" => return .uploadObjs (← node) (← getNats j "objs")
  | "push" => return .push (← node) (← getNat j "expected") (← getNat j "new")
  | "pushAll" =>
    return .pushAll (← node) (← getNats j "ops") (← getNats j "objs") (← getNat j "expected")
      (← getNat j "new")
  | "fetchAll" => return .fetchAll (← node) (← getNat j "base") (← getNats j "haves")
  | "crashNode" => return .crashNode (← node)
  | "loseKnown" => return .loseKnown (← node)
  | "loseVolatile" => return .loseVolatile (← node)
  | "hubGetHead" => return .hubGetHead (← node)
  | "hubPutOps" => return .hubPutOps (← node) (← getNats j "ops")
  | "hubPutObjs" => return .hubPutObjs (← node) (← getNats j "objs")
  | "hubGetOps" => return .hubGetOps (← node) (← getNats j "ops")
  | "hubGetObjs" => return .hubGetObjs (← node) (← getNats j "objs")
  | "casIdem" => return .casIdem (← node) (← getNat j "expected") (← getNat j "new")
  | "casAccept" => return .casAccept (← node) (← getNat j "expected") (← getNat j "new")
  | "casReject" => return .casReject (← node) (← getNat j "expected") (← getNat j "new")
  | "hubPushIdem" =>
    return .hubPushIdem (← node) (← getNats j "ops") (← getNats j "objs")
      (← getNat j "expected") (← getNat j "new")
  | "hubPushAccept" =>
    return .hubPushAccept (← node) (← getNats j "ops") (← getNats j "objs")
      (← getNat j "expected") (← getNat j "new")
  | "hubPushReject" =>
    return .hubPushReject (← node) (← getNats j "ops") (← getNats j "objs")
      (← getNat j "expected") (← getNat j "new")
  | "hubPushIncomplete" =>
    return .hubPushIncomplete (← node) (← getNats j "ops") (← getNats j "objs")
      (← getNat j "expected") (← getNat j "new")
  | "hubFetch" => return .hubFetch (← node) (← getNat j "base") (← getNats j "haves")
  | "crashHub" => return .crashHub
  | k => throw s!"unknown action kind {k}"

/-! ## Encoding -/

/-- Sorted, without duplicates. -/
def sortNats (l : List Nat) : List Nat := (l.mergeSort (· ≤ ·)).eraseDups

def nats (l : List Nat) : Json := toJson (sortNats l).toArray

def headKindStr : HeadKind → String
  | .head => "head"
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .incomplete => "incomplete"
  | .notify => "notify"

def msgObj (kind : String) (n : Nat) (rest : List (String × Json)) : Json :=
  Json.mkObj ([("msg", Json.str kind), ("node", toJson n)] ++ rest)

/-- The wire messages a finite message stands for (a broadcast expands to one per node). -/
def encodeMsg (N : Nat) : EMsg → List Json
  | .getHead n => [msgObj "getHead" n []]
  | .putOps n S => [msgObj "putOps" n [("ops", nats S)]]
  | .putObjs n S => [msgObj "putObjs" n [("objs", nats S)]]
  | .getOps n S => [msgObj "getOps" n [("ops", nats S)]]
  | .getObjs n S => [msgObj "getObjs" n [("objs", nats S)]]
  | .cas n e d => [msgObj "cas" n [("expected", toJson e), ("new", toJson d)]]
  | .head n k sq h =>
    [msgObj "head" n [("headKind", Json.str (headKindStr k)), ("seq", toJson sq),
      ("head", toJson h)]]
  | .ops n S => [msgObj "ops" n [("ops", nats S)]]
  | .objs n S => [msgObj "objs" n [("objs", nats S)]]
  | .stored n => [msgObj "stored" n []]
  | .push n S O e d =>
    [msgObj "push" n [("ops", nats S), ("objs", nats O), ("expected", toJson e),
      ("new", toJson d)]]
  | .fetch n b H => [msgObj "fetch" n [("base", toJson b), ("haves", nats H)]]
  | .notifyAll sq h =>
    (List.range N).map fun n =>
      msgObj "head" n [("headKind", Json.str "notify"), ("seq", toJson sq), ("head", toJson h)]

/-- Sort key `(msg, node, whole message)`. -/
def msgKey (j : Json) : String × Nat × String :=
  ((j.getObjValAs? String "msg").toOption.getD "", (j.getObjValAs? Nat "node").toOption.getD 0,
    j.compress)

def keyLe (a b : String × Nat × String) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2)))

def encodeNet (N : Nat) (net : List EMsg) : Json :=
  let js := (net.flatMap (encodeMsg N)).mergeSort (fun a b => keyLe (msgKey a) (msgKey b))
  let dedup := js.foldr (fun j acc =>
    match acc with
    | j' :: _ => if j.compress == j'.compress then acc else j :: acc
    | [] => [j]) []
  Json.arr dedup.toArray

def encodeNode (nd : ENode) : Json :=
  Json.mkObj [("lops", nats nd.lops), ("lobj", nats nd.lobj), ("heads", nats nd.heads),
    ("known", toJson #[nd.known.1, nd.known.2]), ("sops", nats nd.sops),
    ("sobj", nats nd.sobj)]

def encodeOp (o : EOp) : Json :=
  Json.mkObj [("id", toJson o.id), ("parents", nats o.parents), ("objs", nats o.objs)]

def encodeState (N : Nat) (es : EState) : Json :=
  Json.mkObj [
    ("next", toJson es.next),
    ("ops", Json.arr ((es.ops.mergeSort (fun a b => a.id ≤ b.id)).map encodeOp).toArray),
    ("hub", Json.mkObj [("ops", nats es.hub.ops), ("objs", nats es.hub.objs),
      ("head", toJson es.hub.head), ("seq", toJson es.hub.seq)]),
    ("nodes", Json.arr ((List.range N).map (fun i => encodeNode (es.nodeOf i))).toArray),
    ("net", encodeNet N es.net)]

def okReply (N : Nat) (es : EState) : Json :=
  Json.mkObj [("ok", Json.bool true), ("state", encodeState N es)]

def errReply (e : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("error", Json.str e)]

/-! ## Request handling -/

/-- The oracle's session: the node count and current state, once `reset`. -/
abbrev Session := Option (Nat × EState)

/-- Handle one request line. A rejected or malformed request leaves the session unchanged. -/
def handle (sess : Session) (line : String) : Json × Session :=
  match Json.parse line with
  | .error e => (errReply s!"bad request: {e}", sess)
  | .ok j =>
    match j.getObjValAs? String "op" with
    | .error e => (errReply s!"bad request: {e}", sess)
    | .ok "reset" =>
      match getNat j "nodes" with
      | .error e => (errReply s!"bad request: {e}", sess)
      | .ok N => (okReply N initE, some (N, initE))
    | .ok "step" =>
      match sess with
      | none => (errReply "bad request: step before reset", sess)
      | some (N, es) =>
        match j.getObjVal? "action" >>= decodeAction with
        | .error e => (errReply s!"bad request: {e}", sess)
        | .ok a =>
          match execStep N es a with
          | .error e => (errReply e, sess)
          | .ok es' => (okReply N es', some (N, es'))
    | .ok op => (errReply s!"bad request: unknown op {op}", sess)

end Musubi.Exec.Json
