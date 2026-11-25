/-
JSON codec and request dispatch for the oracle (`docs/internals/conformance.md`, "Wire format").
Decoding turns a request into model inputs, encoding turns model results into replies, and the
`...Reply` functions run an executable model between the two. Protocol logic stays in the
modules this file imports; the replies here only check that a request is well formed (for
example that parents precede their children) and report a model's refusal as an error.
-/
import Lean.Data.Json
import Init.Data.List.Sort.Lemmas
import Musubi.Publication
import Musubi.ParentsBefore
import Musubi.Exec
import Musubi.PresenceExec
import Musubi.Copies
import Musubi.Chunks
import Musubi.Names
import Musubi.RefsExec
import Musubi.ExpectedExec
import Musubi.OpHeadsJson
import Musubi.RealizeJson

namespace Musubi.Exec.Json

open Lean (Json ToJson toJson)

/-! ## Decoding -/

def getNat (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k

def getNats (j : Json) (k : String) : Except String (List Nat) := do
  let a ← j.getObjValAs? (Array Nat) k
  pure a.toList

/-- The wire name of each `HeadKind`; the codec reads and writes names by this one table. -/
def headKindNames : List (String × HeadKind) :=
  [("head", .head), ("accepted", .accepted), ("rejected", .rejected),
    ("incomplete", .incomplete), ("notify", .notify)]

def decodeHeadKind (k : String) : Except String HeadKind :=
  match headKindNames.lookup k with
  | some h => pure h
  | none => throw s!"unknown headKind {k}"

/-- The fields of a push to the hub: the node, the operations and objects it sends, and the
head it expects and the one it sets. -/
def getPush (j : Json) : Except String (Nat × List Nat × List Nat × Nat × Nat) :=
  return (← getNat j "node", ← getNats j "ops", ← getNats j "objs", ← getNat j "expected",
    ← getNat j "new")

def decodeAction (j : Json) : Except String Action := do
  let kind ← j.getObjValAs? String "kind"
  let node := getNat j "node"
  let push (f : Nat → List Nat → List Nat → Nat → Nat → Action) := do
    let (n, S, O, e, d) ← getPush j
    return f n S O e d
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
  | "hubPushIdem" => push .hubPushIdem
  | "hubPushAccept" => push .hubPushAccept
  | "hubPushReject" => push .hubPushReject
  | "hubPushIncomplete" => push .hubPushIncomplete
  | "hubFetch" => return .hubFetch (← node) (← getNat j "base") (← getNats j "haves")
  | "crashHub" => return .crashHub
  | "hubForget" => return .hubForget (← getNats j "ops") (← getNats j "objs")
  | "hubRegress" => return .hubRegress (← getNat j "seq")
  | k => throw s!"unknown action kind {k}"

/-! ## Encoding -/

/-- Sorted, without duplicates. -/
def sortNats (l : List Nat) : List Nat := (l.mergeSort (· ≤ ·)).eraseDups

def nats (l : List Nat) : Json := toJson (sortNats l).toArray

def headKindStr (h : HeadKind) : String :=
  ((headKindNames.find? (·.2 == h)).map (·.1)).getD ""

/-- Every `HeadKind` is in the table, so `headKindStr` never falls back to the empty string. -/
theorem decodeHeadKind_headKindStr (h : HeadKind) :
    decodeHeadKind (headKindStr h) = pure h := by
  cases h <;> rfl

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
      msgObj "head" n [("headKind", Json.str (headKindStr .notify)), ("seq", toJson sq),
        ("head", toJson h)]

/-- Sort key `(msg, node, whole message)`. -/
def msgKey (j : Json) : String × Nat × String :=
  ((j.getObjValAs? String "msg").toOption.getD "", (j.getObjValAs? Nat "node").toOption.getD 0,
    j.compress)

def keyLe (a b : String × Nat × String) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2)))

/-- The original encoder, retained as the exact specification for key caching below. -/
def encodeNetReference (N : Nat) (net : List EMsg) (extra : List Json) : Json :=
  let js := (net.flatMap (encodeMsg N) ++ extra).mergeSort
    (fun a b => keyLe (msgKey a) (msgKey b))
  let dedup := js.foldr (fun j acc =>
    match acc with
    | j' :: _ => if j.compress == j'.compress then acc else j :: acc
    | [] => [j]) []
  Json.arr dedup.toArray

/-- The equality is a construction fact, erased at runtime. The key and original JSON are
stored together so sorting and deduplication never recompute a message's compressed text. -/
private structure CachedMessage where
  key : String × Nat × String
  value : Json
  key_eq : key = msgKey value

private def cacheMessage (j : Json) : CachedMessage := ⟨msgKey j, j, rfl⟩

private theorem cacheMessage_values (js : List Json) :
    (js.map cacheMessage).map CachedMessage.value = js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simpa only [List.map_cons, cacheMessage] using congrArg (List.cons j) ih

private def appendDistinctMessage (j : Json) (acc : List Json) : List Json :=
  match acc with
  | next :: _ => if j.compress == next.compress then acc else j :: acc
  | [] => [j]

private def appendDistinctCached (j : CachedMessage) (acc : List CachedMessage) :
    List CachedMessage :=
  match acc with
  | next :: _ => if j.key.2.2 == next.key.2.2 then acc else j :: acc
  | [] => [j]

private theorem cachedSort_values (js : List CachedMessage) :
    (js.mergeSort (fun a b => keyLe a.key b.key)).map CachedMessage.value =
      (js.map CachedMessage.value).mergeSort (fun a b => keyLe (msgKey a) (msgKey b)) := by
  apply List.map_mergeSort
  intro a _ b _
  rw [a.key_eq, b.key_eq]

private theorem appendDistinctCached_values (j : CachedMessage) (acc : List CachedMessage) :
    appendDistinctMessage j.value (acc.map CachedMessage.value) =
      (appendDistinctCached j acc).map CachedMessage.value := by
  cases acc with
  | nil => rfl
  | cons next rest =>
    simp only [appendDistinctMessage, appendDistinctCached, List.map_cons]
    rw [j.key_eq, next.key_eq]
    simp only [msgKey]
    split <;> simp_all

private theorem cachedDedup_values (js : List CachedMessage) :
    (js.foldr appendDistinctCached []).map CachedMessage.value =
      (js.map CachedMessage.value).foldr appendDistinctMessage [] := by
  simpa only [List.foldr_map, List.map_nil] using
    (List.foldr_hom (fun acc : List CachedMessage => acc.map CachedMessage.value)
      (g₁ := appendDistinctCached)
      (g₂ := fun j acc => appendDistinctMessage j.value acc)
      (l := js) (init := []) appendDistinctCached_values).symm

/-- Cache the unchanged sort key once, retain the stable sort and the original foldr
duplicate representative, and return the original JSON values. -/
def encodeNet (N : Nat) (net : List EMsg) (extra : List Json) : Json :=
  let js := ((net.flatMap (encodeMsg N) ++ extra).map cacheMessage).mergeSort
    (fun a b => keyLe a.key b.key)
  let dedup := js.foldr appendDistinctCached []
  Json.arr (dedup.map CachedMessage.value).toArray

/-- Exact JSON equality for every network and arbitrary extra JSON messages. No model-state
invariant, ordering hypothesis or native law is needed for this representation optimization. -/
theorem encodeNet_eq_reference (N : Nat) (net : List EMsg) (extra : List Json) :
    encodeNet N net extra = encodeNetReference N net extra := by
  unfold encodeNet encodeNetReference
  dsimp only
  rw [cachedDedup_values, cachedSort_values, cacheMessage_values]
  rfl

theorem encodeNet_compress_eq_reference (N : Nat) (net : List EMsg) (extra : List Json) :
    (encodeNet N net extra).compress = (encodeNetReference N net extra).compress :=
  congrArg Json.compress (encodeNet_eq_reference N net extra)

def encodeNode (nd : ENode) : Json :=
  Json.mkObj [("lops", nats nd.lops), ("lobj", nats nd.lobj), ("heads", nats nd.heads),
    ("known", toJson #[nd.known.seq, nd.known.head]), ("sops", nats nd.sops),
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
    ("net", encodeNet N es.net [])]

def okReply (N : Nat) (es : EState) : Json :=
  Json.mkObj [("ok", Json.bool true), ("state", encodeState N es)]

def errReply (e : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("error", Json.str e)]

/-- The message for a request that is not well formed. -/
def badRequest (e : String) : String := s!"bad request: {e}"

/-! ## Presence (`PresenceExec.lean`) -/

def decodeEOp (j : Json) : Except String Presence.EOp := do
  let parents ← getNats j "parents"
  let work ← j.getObjValAs? (Option Nat) "work"
  let forgets ← getNats j "forgets"
  pure { parents, work, forgets }

/-- For each operation, the copies present there, each with its latest work that no forget
saw, both in order. -/
def encodePresence (ops : List Presence.EOp) : Json :=
  let copies := sortNats (Presence.EHist.copies ops)
  let atOp (x : Nat) : Json :=
    Json.arr ((copies.filter (Presence.EHist.presentB ops x)).map fun k =>
      Json.mkObj [("copy", toJson k), ("latest", nats (Presence.EHist.latestB ops x k))]).toArray
  Json.mkObj [("ok", Json.bool true),
    ("presence", Json.arr ((List.range ops.length).map atOp).toArray)]

/-- Unlike other requests' replies, this one's errors are whole messages: a history that is out
of order is not a `bad request`. -/
def presenceReply (j : Json) : Except String Json :=
  match j.getObjValAs? (Array Json) "ops" >>= fun ops => ops.toList.mapM decodeEOp with
  | .error e => throw (badRequest e)
  | .ok ops =>
    if Presence.EHist.orderedB ops then pure (encodePresence ops)
    else throw "presence: an operation's parents must come before it"

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
def encodeCopies (cases : List CopiesCase) : Json :=
  let answer (c : CopiesCase) : Json :=
    let st := Copies.standing c.repo c.entry
    let standings := [("standing", Json.str (standingStr st)),
      ("refined", Json.str (standingStr (Copies.refine st c.elsewhereHolds c.sameDirectory)))]
    match c.entry with
    | none => Json.mkObj standings
    | some e => Json.mkObj (standings ++ [("check", Json.bool (Copies.check e c.repo))])
  Json.mkObj [("ok", Json.bool true), ("copies", Json.arr (cases.map answer).toArray)]

/-- Decode a `copies` request and answer it with `encodeCopies`. -/
def copiesReply (j : Json) : Except String Json := do
  let cases ← (← j.getObjValAs? (Array Json) "cases").toList.mapM decodeCase
  pure (encodeCopies cases)

/-- The durable prefixes of a leave and the next join, plain or fresh, with the files after
retrying each. -/
def copyDetachReply (j : Json) : Except String Json := do
  let old ← decodeEntry (← j.getObjVal? "old")
  let fresh ← decodeEntry (← j.getObjVal? "fresh")
  unless old.key != fresh.key && old.cid == fresh.cid do
    throw "copy-detach requires a fresh key and the original config-id"
  let entry (e : Copies.Entry) := Json.mkObj [
    ("key", toJson e.key), ("hive", toJson e.hive), ("cid", toJson e.cid)]
  let record (r : Copies.Record) := Json.mkObj [
    ("hive", toJson r.hive), ("cid", toJson r.cid),
    ("state", .str (match r.state with
      | .joined => "joined"
      | .left => "left"
      | .removed => "removed"))]
  let encode (s : Copies.Detach.Files) := Json.mkObj [
    ("repo", Json.mkObj [
      ("key", toJson s.repo.key), ("cid", toJson s.repo.cid),
      ("record", (s.repo.record.map record).getD .null)]),
    ("entry", (s.entry.map entry).getD .null),
    ("marker", .bool s.marker), ("retired", .bool s.retired),
    ("history", .str (match s.history with
      | .kept => "kept"
      | .part => "part"
      | .none => "none")),
    ("discarding", .bool s.discarding),
    ("oldCheck", .bool (Copies.check old s.repo)),
    ("freshCheck", .bool (Copies.check fresh s.repo))]
  let leave := Copies.Detach.leaveTrace (Copies.Detach.joined old)
  let join := Copies.Detach.joinTrace (Copies.Detach.detached old.cid) fresh
  let freshJoin := Copies.Detach.joinTrace (Copies.Detach.detached old.cid) fresh true
  let withRetry (states : List Copies.Detach.Files)
      (finish : Copies.Detach.Files → Copies.Detach.Files) :=
    Json.arr (states.map (fun s => Json.mkObj [
      ("prefix", encode s), ("retry", encode (finish s))])).toArray
  pure (Json.mkObj [
    ("ok", .bool true), ("leave", withRetry leave Copies.Detach.finishLeave),
    ("join", withRetry join (Copies.Detach.finishJoin · fresh)),
    -- A join stopped partway through a fresh one is retried as a plain join.
    ("fresh", withRetry freshJoin (Copies.Detach.finishJoin · fresh))])

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

/-- A reply as JSON: a number for `Received::Prefix`, null for `Received::Complete`. -/
def optJson : Option Nat → Json
  | some n => toJson n
  | none => Json.null

/-- The receiver's state after a step: `fields`, then the prefix it has and whether it has
stored the blob. -/
def receiverState (s : Chunks.PState) (fields : List (String × Json)) : Json :=
  Json.mkObj (fields ++ [("pre", toJson s.pre.toArray), ("stored", Json.bool s.store.isSome)])

/-- The receiver after a sweep of the partial blob, the stored one, or both. -/
def sweepReceiver (s : Chunks.PState) (pre stored : Bool) : Chunks.PState :=
  { s with pre := if pre then [] else s.pre, store := if stored then none else s.store }

/-- The prefix receiver's state after each step from `initP`: its reply to a chunk
(`Chunks.receive`; a number for `Received::Prefix`, null for `Received::Complete`), the
prefix it has, and whether it has stored the blob. -/
def encodeChunks (b : List Nat) (steps : List ChunkStep) : Json :=
  let rec go (s : Chunks.PState) : List ChunkStep → List Json
    | [] => []
    | .chunk c total :: rest =>
      let (s', reply) := Chunks.receive (blobHash b) b s c total
      receiverState s' [("received", optJson reply)] :: go s' rest
    | .sweep pre stored :: rest =>
      let s' := sweepReceiver s pre stored
      receiverState s' [] :: go s' rest
  Json.mkObj [("ok", Json.bool true), ("steps", Json.arr (go Chunks.initP steps).toArray)]

/-- Decode a `chunks` request and answer it with `encodeChunks`. -/
def chunksReply (j : Json) : Except String Json := do
  let blob ← getNats j "blob"
  let steps ← (← j.getObjValAs? (Array Json) "steps").toList.mapM decodeChunkStep
  pure (encodeChunks blob steps)

/-- Each age after a renewal of `renew` (`Chunks.refresh`). -/
def refreshReply (j : Json) : Except String Json := do
  let renew ← getNat j "renew"
  let ages ← getNats j "ages"
  pure (Json.mkObj [("ok", Json.bool true),
    ("ages", toJson (ages.map (Chunks.refresh renew)).toArray)])

/-- A step of a transfer by attempts (`Chunks.lean`, "Attempts under a deadline"): an attempt
whose window has `w` chunks, of which the receiver takes the first `m` and the sender hears of
the first `k`; a sweep, as in a chunks request; or the sender starting afresh, as a new process
does, which forgets how far the receiver had got. -/
inductive AttemptStep where
  | attempt (w m k : Nat)
  | sweep (pre stored : Bool)
  | restart

def decodeAttemptStep (j : Json) : Except String AttemptStep :=
  match j.getObjVal? "attempt", j.getObjVal? "sweep" with
  | .ok a, _ => do
    let w ← getNat a "window"
    let m ← getNat a "delivered"
    let k ← getNat a "heard"
    if k ≤ m ∧ m ≤ w then return .attempt w m k
    else throw "an attempt hears of no more chunks than arrive, nor more arrive than it sends"
  | _, .ok s => return .sweep (← s.getObjValAs? Bool "partial") (← s.getObjValAs? Bool "stored")
  | _, _ => do
    let _ ← j.getObjValAs? Bool "restart"
    return .restart

/-- A transfer by attempts from `initP`, the sender an uploader, which goes on from where the
receiver last said it was (`Chunks.next`), or a downloader, which goes on from the receiver's
prefix, being the receiver (`Chunks.ARun.reread`). After each attempt: the offsets of its
window, the receiver's replies to the chunks it took, the prefix it has, whether it has stored
the blob, and where the sender goes on from (null once it has heard that the receiver has the
blob). -/
def encodeAttempts (b : List Nat) (limit : Nat) (download : Bool) (steps : List AttemptStep) :
    Json :=
  let rec go (s : Chunks.PState) (o : Nat) : List AttemptStep → List Json
    | [] => []
    | .attempt w m k :: rest =>
      let o := if download then s.pre.length else o
      let replies := (Chunks.deliver (blobHash b) b s (Chunks.windowFrom b limit o m)).2
      let (s', next) := Chunks.attempt (blobHash b) b limit s o m k
      receiverState s' [("offsets", toJson ((Chunks.windowFrom b limit o w).map (·.off)).toArray),
          ("replies", Json.arr (replies.map optJson).toArray), ("next", optJson next)] ::
        go s' (next.getD o) rest
    | .sweep pre stored :: rest =>
      let s' := sweepReceiver s pre stored
      receiverState s' [] :: go s' o rest
    | .restart :: rest => receiverState s [] :: go s 0 rest
  Json.mkObj [("ok", Json.bool true), ("steps", Json.arr (go Chunks.initP 0 steps).toArray)]

/-- Decode an `attempts` request from an `upload` or `download` sender and answer it with
`encodeAttempts`. -/
def attemptsReply (j : Json) : Except String Json := do
  let blob ← getNats j "blob"
  let limit ← getNat j "limit"
  let sender ← j.getObjValAs? String "sender"
  let steps ← (← j.getObjValAs? (Array Json) "steps").toList.mapM decodeAttemptStep
  if limit = 0 then throw "chunks hold a byte at least"
  else if sender = "upload" then pure (encodeAttempts blob limit false steps)
  else if sender = "download" then pure (encodeAttempts blob limit true steps)
  else throw s!"no sender {sender}"

/-! ## Workspace names (`Names.lean`) -/

def decodeKey (j : Json) : Except String Names.Key := do
  pure ⟨(← j.getObjValAs? String "name").toList, (← j.getObjValAs? String "suffix").toList⟩

/-- Each machine's prefix (`Names.assign`), in the order given, among the machines given and
the names of this machine's own, `me`; and the name here of each workspace given, the
`workspace` of the machine at index `machine` (`Names.localName`). -/
def encodeNames (machines : List Names.Key) (own : List String) (me : Names.Key)
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

/-- Decode a `names` request and answer it with `encodeNames`. -/
def namesReply (j : Json) : Except String Json := do
  let machines ← (← j.getObjValAs? (Array Json) "machines").toList.mapM decodeKey
  let own ← j.getObjValAs? (Array String) "own"
  let me ← j.getObjVal? "me" >>= decodeKey
  let workspaces ← (← j.getObjValAs? (Array Json) "workspaces").toList.mapM decodeWorkspace
  pure (encodeNames machines own.toList me workspaces)

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
  | "exportConflictedBeside" =>
    return .exportConflictedBeside (← slot "s") (← getNat j "g") (← getNat j "e")
      (← getNat j "k")
  | "linv" => return .linv (← slot "s") (← getNat j "g") (← j.getObjValAs? Bool "moved")
  | "cinv" =>
    return .cinv (← slot "s") (← getNat j "g") (← j.getObjValAs? Bool "moved") (← getNat j "e")
  | "restorable" => return .restorable (← slot "o") (← slot "s")
  | "restorableRemote" => return .restorableRemote (← slot "o") (← slot "s")
  | f => throw s!"unknown fn {f}"

def encodeSlot (s : Refs.TSlot Nat) : Json :=
  Json.mkObj [("L", toJson s.L), ("R", toJson s.R), ("K", toJson s.K), ("tr", Json.bool s.tr)]

def encodeRefs : Refs.Exec.Answer → Json
  | .slot s none => Json.mkObj [("ok", Json.bool true), ("slot", encodeSlot s)]
  | .slot s (some g) =>
    Json.mkObj [("ok", Json.bool true), ("slot", encodeSlot s), ("g", toJson g)]
  | .imported s sets =>
    Json.mkObj [("ok", Json.bool true), ("slot", encodeSlot s), ("sets", Json.bool sets)]
  | .holds b => Json.mkObj [("ok", Json.bool true), ("holds", Json.bool b)]

/-- Decode a `refs` request, run it against its table and answer with `encodeRefs`. -/
def refsReply (j : Json) : Except String Json := do
  let table ← j.getObjVal? "table" >>= decodeTable
  pure (encodeRefs (Refs.Exec.run table (← decodeCall j)))

/-! ## Expected values from operation history (`Expected.lean`) -/

/-- `[]` means no checkpoint; `[null]` means a checkpoint with no expected value. -/
def decodeCheckpoint (j : Json) (key : String) : Except String (Option (Option Nat)) := do
  match (← j.getObjValAs? (Array Json) key).toList with
  | [] => pure none
  | [.null] => pure (some none)
  | [value] => pure (some (some (← Lean.fromJson? value)))
  | _ => throw s!"{key} must have at most one value"

/-- Decode an `expected` request, a history of nodes' checks, and reply with the value it
ends in, or an error if the history is invalid or unfinished. -/
def expectedReply (j : Json) : Except String Json := do
  let nodes ← (← j.getObjValAs? (Array Json) "nodes").toList.mapM fun n => do
    let target ← getNat n "target"
    let known ← decodeCheckpoint n "known"
    let recorded ← decodeCheckpoint n "recorded"
    let boundary ← n.getObjValAs? Bool "boundary"
    let parents ← getNats n "parents"
    pure ({ target, known, recorded, boundary, parents } : Refs.Expected.Exec.Node)
  let sides ← (← j.getObjValAs? (Array Json) "sides").toList.mapM fun s => do
    let candidates ← s.getObjValAs? (List (Int × Nat)) "candidates"
    pure ((← getNat s "target"), candidates)
  let tb : Refs.Expected.Exec.Table := { resolved := ← getNats j "resolved", sides }
  let head ← getNat j "head"
  match Refs.Expected.Exec.run tb nodes head with
  | none => throw "invalid or unfinished expected-value history"
  | some value => pure (Json.mkObj [("ok", Json.bool true), ("value", toJson value)])

/-! ## The liveness measure (`Exec.lean`, "The liveness measure") -/

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

/-! ## Publication reply and request dispatch -/

/-- Native publication fixtures supply file closures and jj's operation facts. The reply
computes the budget and selected cleanup using the same definitions as the proofs. -/
def publicationReply (j : Json) : Except String Json := do
  let decodeFile (v : Json) : Except String Publication.File := do
    return ⟨← getNat v "path", ← getNat v "object"⟩
  let decodeWrite (v : Json) : Except String Publication.Write := do
    return ⟨← getNat v "commit", ← v.getObjValAs? Bool "workspaceTip",
      ← v.getObjValAs? Bool "rewritten"⟩
  let decodeOperation (v : Json) : Except String Publication.Operation := do
    let writes ← v.getObjValAs? (Array Json) "writes"
    let frozen ← v.getObjValAs? (Option (List Nat)) "frozen"
    return {
      id := ← getNat v "id"
      parents := ← getNats v "parents"
      snapshot := ← v.getObjValAs? Bool "snapshot"
      frozen := frozen
      writes := ← writes.toList.mapM decodeWrite
      selections := ← getNats v "selections"
      required := ← getNats v "required" }
  let commits ← j.getObjValAs? (Array (Array Json)) "commits"
  let closures ← commits.toList.mapM (fun row => row.toList.mapM decodeFile)
  let sizes ← j.getObjValAs? (Array Nat) "sizes"
  let operations ← j.getObjValAs? (Array Json) "operations"
  let operations ← operations.toList.mapM decodeOperation
  let known ← getNats j "known"
  let selected ← getNats j "selected"
  let view ← getNats j "view"
  let limits : Publication.Limits := ⟨← getNat j "maxFiles", ← getNat j "maxBytes"⟩
  let closure := fun c => closures[c]?.getD []
  let size := fun o => sizes[o]?.getD 0
  let before := Publication.charged closure known operations
  let heads ← getNats j "heads"
  let expected ← getNats j "expectedHeads"
  let context ← getNats j "context"
  let identity ← getNats j "planIdentity"
  let approvalJson ← j.getObjVal? "approval"
  let approval ← if approvalJson == Json.null then pure none else do
    let extra ← approvalJson.getObjValAs? (Array Json) "extra"
    let identity ← getNats approvalJson "identity"
    let extra ← extra.toList.mapM decodeFile
    pure (some ({ identity, extra } : Publication.Plan))
  let intentKnown ← j.getObjValAs? Bool "intentKnown"
  let state : Publication.State := { heads, view, operations, context, intentKnown }
  let fresh := (operations.map Publication.Operation.id).foldl max 0 + 1
  let afterState := Publication.cleanup state selected fresh
  let actualJson ← j.getObjVal? "actual"
  let actual ← if actualJson == Json.null then pure afterState else do
    let actualOps ← actualJson.getObjValAs? (Array Json) "operations"
    let heads ← getNats actualJson "heads"
    let view ← getNats actualJson "view"
    let context ← getNats actualJson "context"
    let operations ← actualOps.toList.mapM decodeOperation
    pure ({ heads, view, context, operations } : Publication.State)
  let after := Publication.charged closure known afterState.operations
  let beforeSize := Publication.chargeSize closure known operations size
  let afterSize := Publication.chargeSize closure known afterState.operations size
  let encodeFile (f : Publication.File) := Json.mkObj [
    ("path", toJson f.path), ("object", toJson f.object)]
  return Json.mkObj [
    ("ok", toJson true),
    ("files", Json.arr (before.map encodeFile).toArray),
    ("fileCount", toJson (Publication.fileCount before)),
    ("bytes", toJson (Publication.byteCount beforeSize before)),
    ("fits", toJson (Publication.fits beforeSize limits before)),
    ("maySend", toJson (Publication.maySend beforeSize limits ⟨identity, before⟩ approval)),
    ("applies", toJson (Publication.applyCleanup closure known expected state selected fresh
      actual).isSome),
    ("parents", toJson (afterState.operations.map (fun op => (op.id, op.parents)))),
    ("intentional", nats (Publication.protectedRoots operations)),
    ("afterFiles", Json.arr (after.map encodeFile).toArray),
    ("afterFileCount", toJson (Publication.fileCount after)),
    ("afterBytes", toJson (Publication.byteCount afterSize after)),
    ("afterFits", toJson (Publication.fits afterSize limits after)),
    ("afterView", nats afterState.view),
    ("afterIntentional", nats (Publication.protectedRoots afterState.operations))]

/-- The oracle's session: the node count and current state, once `reset`. -/
abbrev Session := Option (Nat × EState)

/-- Requests that need no session, by `op`, whose errors are bad requests: the decoding failing,
or the model refusing what was decoded. -/
def badRequestOps : List (String × (Json → Except String Json)) :=
  [("publication", publicationReply), ("chunks", chunksReply), ("refresh", refreshReply),
    ("attempts", attemptsReply), ("names", namesReply), ("copies", copiesReply),
    ("copy-detach", copyDetachReply),
    ("expected", expectedReply), ("refs", refsReply), ("opHeads", OpHeads.Json.reply),
    ("realization", Realize.Json.reply)]

/-- Requests that need no session, by `op`, whose errors are whole messages, not bad requests. -/
def wholeMessageOps : List (String × (Json → Except String Json)) :=
  [("presence", presenceReply)]

/-- Every request that needs no session, by `op`. An error is the message of the reply. -/
def statelessOps : List (String × (Json → Except String Json)) :=
  badRequestOps.map (fun (op, f) => (op, fun j => (f j).mapError badRequest)) ++ wholeMessageOps

/-- A request that reads the session and leaves it as it is, by its `op`, given the node count
and state. Before `reset`, it fails as `bad request: OP before reset`. -/
def sessionOps : List (String × (Nat × EState → Json → Except String Json)) :=
  [("measure", fun (N, es) _ => pure (measureReply N es)),
    ("upload", fun (_, es) j => return uploadReply es (← getNat j "node") (← getNat j "new"))]

/-- A `step`: the action's refusal by the model is reported as it is, not as a bad request. -/
def handleStep (N : Nat) (es : EState) (j : Json) : Json × Session :=
  match j.getObjVal? "action" >>= decodeAction with
  | .error e => (errReply (badRequest e), some (N, es))
  | .ok a =>
    match execStep N es a with
    | .error e => (errReply e, some (N, es))
    | .ok es' => (okReply N es', some (N, es'))

/-- Handle the request `j` of kind `op`. A new op goes in `badRequestOps` or `wholeMessageOps` if
it needs no session, or in `sessionOps` if it reads one. `reset` and `step` are handled here
because they replace the session; every other op leaves it as it is. -/
def handleOp (sess : Session) (j : Json) (op : String) : Json × Session :=
  let reply (r : Except String Json) : Json × Session :=
    match r with
    | .error e => (errReply e, sess)
    | .ok v => (v, sess)
  if op == "reset" then
    match getNat j "nodes" with
    | .error e => (errReply (badRequest e), sess)
    | .ok N => (okReply N initE, some (N, initE))
  else if op == "step" then
    match sess with
    | none => (errReply (badRequest "step before reset"), sess)
    | some (N, es) => handleStep N es j
  else
    match statelessOps.lookup op with
    | some f => reply (f j)
    | none =>
      match sessionOps.lookup op with
      | none => (errReply (badRequest s!"unknown op {op}"), sess)
      | some f =>
        match sess with
        | none => (errReply (badRequest s!"{op} before reset"), sess)
        | some st => reply ((f st j).mapError badRequest)

/-- Handle one request line. A rejected or malformed request leaves the session unchanged. -/
def handle (sess : Session) (line : String) : Json × Session :=
  match Json.parse line with
  | .error e => (errReply (badRequest e), sess)
  | .ok j =>
    match j.getObjValAs? String "op" with
    | .error e => (errReply (badRequest e), sess)
    | .ok op => handleOp sess j op

end Musubi.Exec.Json
