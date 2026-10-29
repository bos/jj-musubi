/-
JSON codec for the oracle (`docs/internals/conformance.md`, "Wire format"). Decoding and encoding
only; no protocol logic.
-/
import Lean.Data.Json
import Musubi.Exec
import Musubi.PresenceExec
import Musubi.Copies
import Musubi.Chunks
import Musubi.Names
import Musubi.RefsExec

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
  | "hubForget" => return .hubForget (← getNats j "ops") (← getNats j "objs")
  | "hubRegress" => return .hubRegress (← getNat j "seq")
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

/-! ## Presence (`PresenceExec.lean`) -/

def decodeEOp (j : Json) : Except String Presence.EOp := do
  let parents ← getNats j "parents"
  let work ← j.getObjValAs? (Option Nat) "work"
  let forgets ← getNats j "forgets"
  pure { parents, work, forgets }

/-- For each operation, the copies present there, each with its latest work that no forget
saw, both in order. -/
def presenceReply (ops : List Presence.EOp) : Json :=
  let copies := sortNats (Presence.EHist.copies ops)
  let atOp (x : Nat) : Json :=
    Json.arr ((copies.filter (Presence.EHist.presentB ops x)).map fun k =>
      Json.mkObj [("copy", toJson k), ("latest", nats (Presence.EHist.latestB ops x k))]).toArray
  Json.mkObj [("ok", Json.bool true),
    ("presence", Json.arr ((List.range ops.length).map atOp).toArray)]

/-! ## Copies (`Copies.lean`) -/

/-- Field `k` of `j`, `none` if it is missing or null. -/
def getOpt {α : Type} (j : Json) (k : String) (f : Json → Except String α) :
    Except String (Option α) :=
  match j.getObjVal? k with
  | .error _ | .ok .null => pure none
  | .ok v => some <$> f v

def decodeMembership : String → Except String Copies.Membership
  | "joined" => pure .joined
  | "left" => pure .left
  | "removed" => pure .removed
  | m => throw s!"unknown state {m}"

def decodeRecord (j : Json) : Except String Copies.Record := do
  pure { hive := ← getNat j "hive", cid := ← getNat j "cid",
         state := ← decodeMembership (← j.getObjValAs? String "state") }

def decodeRepo (j : Json) : Except String Copies.Repo := do
  pure { key := ← getOpt j "key" (·.getNat?), record := ← getOpt j "record" decodeRecord,
         cid := ← getOpt j "cid" (·.getNat?) }

/-- An entry's path decides neither `standing` nor `check`: 0 if not given. -/
def decodeEntry (j : Json) : Except String Copies.Entry := do
  pure { key := ← getNat j "key", hive := ← getNat j "hive", cid := ← getNat j "cid",
         path := (← getOpt j "path" (·.getNat?)).getD 0 }

/-- A case: a repository, this machine's entry for its key, and, for `refine`, whether the
entry's path holds the copy the entry names and whether it is the repository's directory
(each false if not given). -/
structure CopiesCase where
  repo : Copies.Repo
  entry : Option Copies.Entry
  elsewhereHolds : Bool
  sameDirectory : Bool

def decodeCase (j : Json) : Except String CopiesCase := do
  pure { repo := ← decodeRepo (← j.getObjVal? "repo"), entry := ← getOpt j "entry" decodeEntry,
         elsewhereHolds := (← getOpt j "elsewhereHolds" (·.getBool?)).getD false,
         sameDirectory := (← getOpt j "sameDirectory" (·.getBool?)).getD false }

def standingStr : Copies.Standing → String
  | .outside => "outside"
  | .removed => "removed"
  | .copy => "copy"
  | .broken => "broken"
  | .duplicate => "duplicate"
  | .unknown => "unknown"

/-- For each case, the repository's standing given the entry, that standing `refine`d, and, if
there is an entry, whether the repository passes its check. -/
def copiesReply (cases : List CopiesCase) : Json :=
  let answer (c : CopiesCase) : Json :=
    let st := Copies.standing c.repo c.entry
    let standings := [("standing", Json.str (standingStr st)),
      ("refined", Json.str (standingStr (Copies.refine st c.elsewhereHolds c.sameDirectory)))]
    match c.entry with
    | none => Json.mkObj standings
    | some e => Json.mkObj (standings ++ [("check", Json.bool (Copies.check e c.repo))])
  Json.mkObj [("ok", Json.bool true), ("copies", Json.arr (cases.map answer).toArray)]

/-! ## Chunked blobs (`Chunks.lean`) -/

/-- A step of the prefix receiver: a chunk delivered with the length it claims (`recv`), or a
sweep of the partial blob, the stored one, or both (`sweepPartial`, `sweepStored`). -/
inductive ChunkStep where
  | chunk (c : Chunks.Chunk) (total : Nat)
  | sweep (pre stored : Bool)

def decodeChunkStep (j : Json) : Except String ChunkStep :=
  match j.getObjVal? "sweep" with
  | .ok s => return .sweep (← s.getObjValAs? Bool "partial") (← s.getObjValAs? Bool "stored")
  | .error _ => return .chunk ⟨← getNat j "off", ← getNats j "data"⟩ (← getNat j "total")

/-- The hash the oracle takes for blob `b`: `0` for `b` and `1` for anything else. The proofs
take the hash injective; this one tells the blob from every other byte string, which is all
`receive` asks of it. -/
def blobHash (b : List Nat) (p : List Nat) : Nat := if p = b then 0 else 1

/-- The prefix receiver's state after each step from `initP`: its reply to a chunk
(`Chunks.receive`; a number for `Received::Prefix`, null for `Received::Complete`), the
prefix it has, and whether it has stored the blob. -/
def chunksReply (b : List Nat) (steps : List ChunkStep) : Json :=
  let state (s : Chunks.PState) (fields : List (String × Json)) : Json :=
    Json.mkObj (fields ++ [("pre", toJson s.pre.toArray), ("stored", Json.bool s.store.isSome)])
  let rec go (s : Chunks.PState) : List ChunkStep → List Json
    | [] => []
    | .chunk c total :: rest =>
      let (s', reply) := Chunks.receive (blobHash b) b s c total
      state s' [("received", match reply with | some n => toJson n | none => Json.null)] ::
        go s' rest
    | .sweep pre stored :: rest =>
      let s' := { s with pre := if pre then [] else s.pre,
                         store := if stored then none else s.store }
      state s' [] :: go s' rest
  Json.mkObj [("ok", Json.bool true), ("steps", Json.arr (go Chunks.initP steps).toArray)]

/-! ## Workspace names (`Names.lean`) -/

def decodeKey (j : Json) : Except String Names.Key := do
  pure ⟨(← j.getObjValAs? String "name").toList, (← j.getObjValAs? String "suffix").toList⟩

/-- Each machine's prefix (`Names.assign`), in the order given, among the machines given and
the names of this machine's own, `me`; and the name here of each workspace given, the
`workspace` of the machine at index `machine` (`Names.localName`). -/
def namesReply (machines : List Names.Key) (own : List String) (me : Names.Key)
    (workspaces : List (Nat × String)) : Json :=
  let assigned := Names.assign machines (own.map String.toList)
  let name (w : Nat × String) : Json :=
    match machines[w.1]? with
    | some k => Json.str (String.ofList (Names.localName me assigned k w.2.toList))
    | none => Json.null
  Json.mkObj [("ok", Json.bool true),
    ("prefixes", Json.arr (assigned.map fun (_, p) => Json.str (String.ofList p)).toArray),
    ("names", Json.arr (workspaces.map name).toArray)]

def decodeWorkspace (j : Json) : Except String (Nat × String) := do
  pure (← getNat j "machine", ← j.getObjValAs? String "workspace")

/-! ## Per-machine refs (`RefsExec.lean`) -/

def decodeTable (j : Json) : Except String Refs.Exec.Table := do
  let terms ← (← j.getObjValAs? (Array Json) "terms").toList.mapM fun t => do
    pure ((← getNat t "conflict"), (← getNats t "terms"))
  let merges ← (← j.getObjValAs? (Array (Array Nat)) "merges").toList.mapM fun
    | #[a, b, c, m] => pure (a, b, c, m)
    | m => throw s!"a merge is [a, b, c, merged], not {m}"
  pure { resolved := ← getNats j "resolved", writable := ← getNats j "writable", terms, merges }

def decodeSlot (j : Json) : Except String (Refs.TSlot Nat) := do
  pure { L := ← getNat j "L", R := ← getNat j "R", K := ← getNat j "K",
         tr := ← j.getObjValAs? Bool "tr" }

def decodeCall (j : Json) : Except String Refs.Exec.Call := do
  let slot (k : String) := j.getObjVal? k >>= decodeSlot
  match ← j.getObjValAs? String "fn" with
  | "set" => return .set (← slot "s") (← getNat j "l")
  | "track" => return .track (← slot "s")
  | "import" => return .import (← slot "s") (← getNat j "g")
  | "merge" => return .merge (← slot "b") (← slot "v") (← slot "w")
  | "exportLocal" => return .exportLocal (← slot "s") (← getNat j "g")
  | "exportRemote" => return .exportRemote (← slot "s") (← getNat j "g")
  | "exportConflicted" => return .exportConflicted (← slot "s") (← getNat j "g") (← getNat j "e")
  | "linv" => return .linv (← slot "s") (← getNat j "g") (← j.getObjValAs? Bool "moved")
  | "cinv" =>
    return .cinv (← slot "s") (← getNat j "g") (← j.getObjValAs? Bool "moved") (← getNat j "e")
  | "restorable" => return .restorable (← slot "o") (← slot "s")
  | "restorableRemote" => return .restorableRemote (← slot "o") (← slot "s")
  | f => throw s!"unknown fn {f}"

def encodeSlot (s : Refs.TSlot Nat) : Json :=
  Json.mkObj [("L", toJson s.L), ("R", toJson s.R), ("K", toJson s.K), ("tr", Json.bool s.tr)]

def refsReply : Refs.Exec.Answer → Json
  | .slot s none => Json.mkObj [("ok", Json.bool true), ("slot", encodeSlot s)]
  | .slot s (some g) =>
    Json.mkObj [("ok", Json.bool true), ("slot", encodeSlot s), ("g", toJson g)]
  | .imported s sets =>
    Json.mkObj [("ok", Json.bool true), ("slot", encodeSlot s), ("sets", Json.bool sets)]
  | .holds b => Json.mkObj [("ok", Json.bool true), ("holds", Json.bool b)]

/-! ## Liveness (`Exec.lean`, "The liveness measure") -/

/-- The session state's measures, and whether it has converged. -/
def measureReply (N : Nat) (es : EState) : Json :=
  let (a, b, c, d, e) := es.measureE N
  let (a', b', c', d', e', f') := es.rmeasureE N
  Json.mkObj [("ok", Json.bool true), ("measure", toJson #[a, b, c, d, e]),
    ("rmeasure", toJson #[a', b', c', d', e', f']), ("converged", Json.bool (es.convergedE N))]

/-- What node `n` uploads with a policy `Push` of `new`: `upOps` and `upObjs`. -/
def uploadReply (es : EState) (n new : Nat) : Json :=
  Json.mkObj [("ok", Json.bool true), ("ops", nats (es.upOpsL n new)),
    ("objs", nats (es.upObjsL n new))]

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
    | .ok "measure" =>
      match sess with
      | none => (errReply "bad request: measure before reset", sess)
      | some (N, es) => (measureReply N es, sess)
    | .ok "upload" =>
      match sess, getNat j "node", getNat j "new" with
      | none, _, _ => (errReply "bad request: upload before reset", sess)
      | _, .error e, _ | _, _, .error e => (errReply s!"bad request: {e}", sess)
      | some (_, es), .ok n, .ok new => (uploadReply es n new, sess)
    | .ok "presence" =>
      match j.getObjValAs? (Array Json) "ops" >>= fun ops => ops.toList.mapM decodeEOp with
      | .error e => (errReply s!"bad request: {e}", sess)
      | .ok ops =>
        if Presence.EHist.orderedB ops then (presenceReply ops, sess)
        else (errReply "presence: an operation's parents must come before it", sess)
    | .ok "chunks" =>
      match getNats j "blob", j.getObjValAs? (Array Json) "steps" >>= fun ss =>
          ss.toList.mapM decodeChunkStep with
      | .error e, _ | _, .error e => (errReply s!"bad request: {e}", sess)
      | .ok b, .ok steps => (chunksReply b steps, sess)
    | .ok "names" =>
      let me := j.getObjVal? "me" >>= decodeKey
      let workspaces := j.getObjValAs? (Array Json) "workspaces" >>= fun ws =>
        ws.toList.mapM decodeWorkspace
      match j.getObjValAs? (Array Json) "machines" >>= fun ms => ms.toList.mapM decodeKey,
          j.getObjValAs? (Array String) "own", me, workspaces with
      | .error e, _, _, _ | _, .error e, _, _ | _, _, .error e, _ | _, _, _, .error e =>
        (errReply s!"bad request: {e}", sess)
      | .ok machines, .ok own, .ok me, .ok workspaces =>
        (namesReply machines own.toList me workspaces, sess)
    | .ok "copies" =>
      match j.getObjValAs? (Array Json) "cases" >>= fun cs => cs.toList.mapM decodeCase with
      | .error e => (errReply s!"bad request: {e}", sess)
      | .ok cases => (copiesReply cases, sess)
    | .ok "refs" =>
      match j.getObjVal? "table" >>= decodeTable, decodeCall j with
      | .error e, _ | _, .error e => (errReply s!"bad request: {e}", sess)
      | .ok tb, .ok call => (refsReply (Refs.Exec.run tb call), sess)
    | .ok op => (errReply s!"bad request: unknown op {op}", sess)

end Musubi.Exec.Json
