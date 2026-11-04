import Musubi.EarlyEntry.Abstract
import Musubi.EarlyEntry.FreshFetch
import Musubi.RecordEpoch

namespace Musubi.EarlyEntry.Control

open Musubi NodeSettle

/-! ### A raw entry

From the common finite cut, a node's first fresh reply leaves it with the hub's records applied,
no record receipts, a known pair from after the cut, and nothing announced but the hub's records,
and it is no `Incomplete` answer, after which the driver would reopen the node
(`raw_entry_reached`). A fresh `Fetched` reply does so through the round after it
(`FetchLaws.current`). A fresh `Head` reply answers a push, which is refused unless it offers the
hub's records, and it offers those it has applied; a push is made with the core's record test
quiet (`choose_push_announced`), so, receipts having an announcement in an active round, with none
(`Retry.Records.no_receipts_when_quiet`), and the reply leaves them so; and an honest push from
the hub's head with the hub's records is closed once uploaded, so it is not answered `Incomplete`.
Nothing before the entry is read as NodeSettle's state. -/

/-- A node enters, raw: its first fresh reply leaves it with the hub's records `R` applied, no
record receipts, a known sequence from the cut's `w` on and nothing announced but `R`, and is no
`Incomplete` answer. Given what `fresh_head_reached` takes, and: a fresh reply comes only from a
`Fetch` or a push; the round after a fresh `Fetch`'s reply (`FetchLaws` of its sampled data
`round`, holding receipts if the node did right after the reply: its prelude may add some),
which is never `Incomplete`; a push offers the records the node has applied (`ap`); the core's
first test is `Retry.Records.needsRecords` of what it has applied, what is announced (`annc`) and
its receipts, and receipts have an announcement in an active round
(`Retry.Records.State.Guard`), so a push, made with that test quiet, is made with no receipts
(`Retry.Records.no_receipts_when_quiet`), and a `Head` reply leaves them so;
`Push::answer` answers `Incomplete` only from its head and to a push whose closure it lacks, and
an honest push with the hub's records from its head is closed once uploaded (the conditional
closure law); and a fresh reply names a head from after the cut and announces only the hub's
records. And, not as a law of the run, that no `GetObjects` fails in the round after a fresh
`Fetch` (`hroundServe`). -/
theorem raw_entry_reached {ρ α : Type} [DecidableEq ρ] (raw : List Nat) (nm : Naming α)
    (par : Nat → List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (hlt : ParLt par) (H : Nat) (hraw : ∀ x, Anc par x H → x ∈ raw)
    (run after : Nat → State) (prims : Nat → Prims) (reply : Nat → Reply)
    (core starts fetchCall : Nat → Prop) (pushDropped : Nat → Bool)
    (offered R : ρ) (heard : Nat → Option ρ)
    (hnaming : nm.Laws par H (Before reply))
    (hkind : ∀ i, Before reply i → core i ∨ starts i)
    (hrecord : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt ∧
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance →
        (prims i).dropHead = false))
    (hdiffer : ∀ i, Before reply i → core i → (prims i).differ = match heard i with
      | some h => !decide (h = offered)
      | none => (prims i).pending)
    (hheard : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .idle → reply i ≠ .fresh →
      heard (i + 1) = if reply i = .refused then some R else heard i)
    (hburst : ∀ i, Before reply i → core i → nm.Still i →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance) →
      ∃ k, callB raw (nm.images i) anc (.burst k) (run i) (after i) = true)
    (hobjects : ∀ i, Before reply i → core i → nm.Still i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects →
      (∃ j, i < j ∧ starts j) ∨
      ((∀ x, walkB par (run i).burst.loc (run i).stg H x = true →
        (run i).burst.loc x = false → (run i).stg x = true → (run i).obj x = false →
        (after i).obj x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true))
    (hframe : ∀ i, Before reply (i + 1) → core i → nm.Still i → Frame raw (after i) (run (i + 1)))
    (hpoll : ∀ i, Before reply i → core i →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .fetch ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .poll) → fetchCall i)
    (hstart : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .idle → ∃ j, i < j ∧ starts j)
    (hstartFetch : ∀ j, Before reply j → starts j → fetchCall j)
    (hfetchCall : ∀ j, Before reply j → fetchCall j → reply j = .fresh)
    (hnd : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .push → offered = R →
      pushDropped i = false)
    (hpush : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .push →
      (offered = R → pushDropped i = false → reply i = .fresh) ∧
      (offered ≠ R → reply i = .refused))
    (ap : Nat → ρ) (seqAfter : Nat → Nat) (anncAfter : Nat → Option ρ) (w : Nat)
    (receipts receiptsAfter : Nat → Bool) (incomplete expectedIsHead closed : Nat → Bool)
    (hsource : ∀ j, Before reply j → reply j = .fresh →
      fetchCall j ∨ (core j ∧ rawControl raw (nm.images j) par anc H (run j) (prims j) = .push))
    (round : Nat → FetchData α)
    (hround : ∀ j, Before reply j → fetchCall j → reply j = .fresh →
      FetchLaws (ap j) R (round j) ∧ (receiptsAfter j = true → (round j).receipts = true))
    (hroundServe : ∀ j, Before reply j → fetchCall j → reply j = .fresh → ∀ i,
      (round j).active i = true → ¬ (round j).failed i)
    (hfetchInc : ∀ j, Before reply j → fetchCall j → incomplete j = false)
    (hoffer : ∀ j, Before reply j → core j →
      rawControl raw (nm.images j) par anc H (run j) (prims j) = .push → ap j = offered)
    (annc : Nat → Option ρ)
    (hneeds : ∀ i, Before reply i → core i →
      (prims i).announced = Retry.Records.needsRecords (ap i) (annc i) (receipts i))
    (hguard : ∀ i, Before reply i → core i → receipts i = true → annc i ≠ none)
    (hheadReceipts : ∀ j, Before reply j → core j →
      rawControl raw (nm.images j) par anc H (run j) (prims j) = .push →
      receiptsAfter j = receipts j)
    (hinc : ∀ j, Before reply j → core j →
      rawControl raw (nm.images j) par anc H (run j) (prims j) = .push → incomplete j = true →
      expectedIsHead j = true ∧ closed j = false)
    (hclosure : ∀ j, Before reply j → core j →
      rawControl raw (nm.images j) par anc H (run j) (prims j) = .push → offered = R →
      expectedIsHead j = true → closed j = true)
    (hseq : ∀ j, reply j = .fresh → w ≤ seqAfter j)
    (hannc : ∀ j, reply j = .fresh → anncAfter j = none ∨ anncAfter j = some R) :
    ∃ j, reply j = .fresh ∧ ap j = R ∧ receiptsAfter j = false ∧ incomplete j = false ∧
      w ≤ seqAfter j ∧ (anncAfter j = none ∨ anncAfter j = some R) := by
  obtain ⟨j, hj, hmin⟩ := exists_first (fresh_head_reached raw nm par anc trans hlt H hraw
    run after prims reply core starts fetchCall pushDropped offered R heard hnaming hkind hrecord
    hdiffer hheard hburst hobjects hframe hpoll hstart hstartFetch hfetchCall hnd hpush)
  have hb : Before reply j := fun m hm h => hmin m hm h
  rcases hsource j hb hj with hf | ⟨hc, hp⟩
  · obtain ⟨F, hF⟩ := hround j hb hf hj
    obtain ⟨hap, hrec⟩ := F.current (hroundServe j hb hf hj)
    have hra : receiptsAfter j = false := by
      cases h : receiptsAfter j
      · rfl
      · rw [hF h] at hrec; cases hrec
    exact ⟨j, hj, hap, hra, hfetchInc j hb hf, hseq j hj, hannc j hj⟩
  · have hl := hpush j hb hc hp
    have hoR : offered = R := Classical.byContradiction fun hne => by
      have h := hl.2 hne
      rw [hj] at h
      cases h
    have hrec : receipts j = false := by
      have hn : (prims j).announced = false := choose_push_announced hp
      rw [hneeds j hb hc] at hn
      exact Retry.Records.no_receipts_when_quiet (ap j) (annc j) (receipts j)
        (hguard j hb hc) hn
    have hinc' : incomplete j = false := by
      cases h : incomplete j
      · rfl
      · obtain ⟨he, hcl⟩ := hinc j hb hc hp h
        rw [hclosure j hb hc hp hoR he] at hcl
        cases hcl
    refine ⟨j, hj, by rw [hoffer j hb hc hp, hoR], ?_, hinc', hseq j hj, hannc j hj⟩
    rw [hheadReceipts j hb hc hp, hrec]

/-- What a node's entry reads of it, raw: the records it has applied, its known sequence, the
records announced to it, and whether it holds record receipts. -/
structure RawNode (ρ : Type) where
  applied : ρ
  seq : Nat
  annc : Option ρ
  receipts : Bool

/-- A node has entered, raw: the hub's records applied, a known sequence from the cut's `w` on,
nothing announced but the hub's records, no receipts. -/
def RawEntry {ρ : Type} (R : ρ) (w : Nat) (e : RawNode ρ) : Prop :=
  e.applied = R ∧ w ≤ e.seq ∧ (e.annc = none ∨ e.annc = some R) ∧ e.receipts = false

/-- Entry, once reached, lasts: given that each step keeps it unless the driver reopens the node
(no adoption past the credit cut, the known sequence never going back without a reopen,
announcements only of the hub's records, no receipts without taking), that the driver reopens
the node only after an `Incomplete` answer in the successful suffix, after ordinary I/O and
transport failures and their reopens have ceased. `Incomplete` comes only from the hub's head
to a push whose closure it lacks; an entered node's push from that head is closed once uploaded
(the conditional closure law: it offers the hub's records). Protocol-caused failure is ruled
out by that law rather than treated as an ordinary failure assumed to stop. -/
theorem raw_entry_persists {ρ : Type} (R : ρ) (w : Nat) (state : Nat → RawNode ρ)
    (reopen incomplete : Nat → Prop) (expectedIsHead closed : Nat → Bool) (j : Nat)
    (hj : RawEntry R w (state j))
    (hreopen : ∀ i, j ≤ i → reopen i → incomplete i)
    (hinc : ∀ i, j ≤ i → incomplete i → expectedIsHead i = true ∧ closed i = false)
    (hclosure : ∀ i, j ≤ i → RawEntry R w (state i) → expectedIsHead i = true →
      closed i = true)
    (hkeep : ∀ i, j ≤ i → RawEntry R w (state i) → ¬ reopen i →
      RawEntry R w (state (i + 1))) :
    ∀ i, j ≤ i → RawEntry R w (state i) := by
  intro i hi
  obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
  induction d with
  | zero => exact hj
  | succ d ih =>
    have he := ih (by omega)
    have hnr : ¬ reopen (j + d) := fun hr => by
      obtain ⟨hh, hc⟩ := hinc (j + d) (by omega) (hreopen (j + d) (by omega) hr)
      rw [hclosure (j + d) (by omega) he hh] at hc
      cases hc
    exact hkeep (j + d) (by omega) he hnr

/-- What a node's pre-entry raw run reads, sampled from its actual events: the round's raw
closure, naming, raw graph and known head, and at each of its sampled steps its core state (and
right after the step's calls complete, `after`), reads, reply, kind of event, push packet bits,
records heard, applied and announced, receipts and `Push::answer` bits, and the data of the round
after each fresh `Fetched` reply. Data only: its laws are `EntryLaws`. -/
structure EntryData (ρ α : Type) where
  raw : List Nat
  naming : Naming α
  par : Nat → List Nat
  anc : Nat → Nat → Bool
  H : Nat
  run : Nat → State
  after : Nat → State
  prims : Nat → Prims
  reply : Nat → Reply
  core : Nat → Prop
  starts : Nat → Prop
  fetchCall : Nat → Prop
  pushDropped : Nat → Bool
  offered : ρ
  heard : Nat → Option ρ
  ap : Nat → ρ
  seqAfter : Nat → Nat
  anncAfter : Nat → Option ρ
  receipts : Nat → Bool
  receiptsAfter : Nat → Bool
  incomplete : Nat → Bool
  expectedIsHead : Nat → Bool
  closed : Nat → Bool
  round : Nat → FetchData α
  annc : Nat → Option ρ

/-- The native per-call laws of that run, as `raw_entry_reached` takes them, each asked before
its first fresh reply only. The objects laws rest on a valid base: a node advertises as haves
only objects it holds, so a reply brings what it lacks, or the round fails and another starts.
That no `GetObjects` fails in the round after a fresh `Fetch` is not one of them:
`EntryLaws.enters` takes it apart. -/
structure EntryLaws {ρ α : Type} [DecidableEq ρ] (R : ρ) (w : Nat) (d : EntryData ρ α) :
    Prop where
  trans : ∀ a b c, d.anc a b = true → d.anc b c = true → d.anc a c = true
  hlt : ParLt d.par
  hraw : ∀ x, Anc d.par x d.H → x ∈ d.raw
  hnaming : d.naming.Laws d.par d.H (Before d.reply)
  hkind : ∀ i, Before d.reply i → d.core i ∨ d.starts i
  hrecord : ∀ i, Before d.reply i → d.core i → rawControl d.raw (d.naming.images i) d.par d.anc d.H
    (d.run i) (d.prims i) ≠ .adopt ∧ (rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i)
    (d.prims i) = .advance → (d.prims i).dropHead = false)
  hdiffer : ∀ i, Before d.reply i → d.core i → (d.prims i).differ = match d.heard i with
      | some h => !decide (h = d.offered)
      | none => (d.prims i).pending
  hheard : ∀ i, Before d.reply i → d.core i → rawControl d.raw (d.naming.images i) d.par d.anc d.H
    (d.run i) (d.prims i) ≠ .idle → d.reply i ≠ .fresh → d.heard (i + 1) = if d.reply i = .refused
    then some R else d.heard i
  hburst : ∀ i, Before d.reply i → d.core i → d.naming.Still i → (rawControl d.raw (d.naming.images
    i) d.par d.anc d.H (d.run i) (d.prims i) = .merge ∨ rawControl d.raw (d.naming.images i) d.par
    d.anc d.H (d.run i) (d.prims i) = .realize ∨ rawControl d.raw (d.naming.images i) d.par d.anc
    d.H (d.run i) (d.prims i) = .advance) → ∃ k, callB d.raw (d.naming.images i) d.anc (.burst k)
    (d.run i) (d.after i) = true
  hobjects : ∀ i, Before d.reply i → d.core i → d.naming.Still i → rawControl d.raw (d.naming.images
    i) d.par d.anc d.H (d.run i) (d.prims i) = .objects → (∃ j, i < j ∧ d.starts j) ∨ ((∀ x, walkB
    d.par (d.run i).burst.loc (d.run i).stg d.H x = true → (d.run i).burst.loc x = false → (d.run
    i).stg x = true → (d.run i).obj x = false → (d.after i).obj x = true ∨ (d.after i).burst.loc x =
    true) ∧ (d.after i).burst.heads = (d.run i).burst.heads ∧ (d.after i).burst.plan = (d.run
    i).burst.plan ∧ growsB d.raw (d.run i) (d.after i) = true)
  hframe : ∀ i, Before d.reply (i + 1) → d.core i → d.naming.Still i → Frame d.raw (d.after i)
    (d.run (i + 1))
  hpoll : ∀ i, Before d.reply i → d.core i → (rawControl d.raw (d.naming.images i) d.par d.anc d.H
    (d.run i) (d.prims i) = .fetch ∨ rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i)
    (d.prims i) = .poll) → d.fetchCall i
  hstart : ∀ i, Before d.reply i → d.core i → rawControl d.raw (d.naming.images i) d.par d.anc d.H
    (d.run i) (d.prims i) = .idle → ∃ j, i < j ∧ d.starts j
  hstartFetch : ∀ j, Before d.reply j → d.starts j → d.fetchCall j
  hfetchCall : ∀ j, Before d.reply j → d.fetchCall j → d.reply j = .fresh
  hnd : ∀ i, Before d.reply i → d.core i → rawControl d.raw (d.naming.images i) d.par d.anc d.H
    (d.run i) (d.prims i) = .push → d.offered = R → d.pushDropped i = false
  hpush : ∀ i, Before d.reply i → d.core i → rawControl d.raw (d.naming.images i) d.par d.anc d.H
    (d.run i) (d.prims i) = .push → (d.offered = R → d.pushDropped i = false → d.reply i = .fresh) ∧
    (d.offered ≠ R → d.reply i = .refused)
  hsource : ∀ j, Before d.reply j → d.reply j = .fresh → d.fetchCall j ∨ (d.core j ∧ rawControl
    d.raw (d.naming.images j) d.par d.anc d.H (d.run j) (d.prims j) = .push)
  hround : ∀ j, Before d.reply j → d.fetchCall j → d.reply j = .fresh → FetchLaws (d.ap j) R
    (d.round j) ∧ (d.receiptsAfter j = true → (d.round j).receipts = true)
  hfetchInc : ∀ j, Before d.reply j → d.fetchCall j → d.incomplete j = false
  hoffer : ∀ j, Before d.reply j → d.core j → rawControl d.raw (d.naming.images j) d.par d.anc d.H
    (d.run j) (d.prims j) = .push → d.ap j = d.offered
  hneeds : ∀ i, Before d.reply i → d.core i → (d.prims i).announced = Retry.Records.needsRecords
    (d.ap i) (d.annc i) (d.receipts i)
  hguard : ∀ i, Before d.reply i → d.core i → d.receipts i = true → d.annc i ≠ none
  hheadReceipts : ∀ j, Before d.reply j → d.core j → rawControl d.raw (d.naming.images j) d.par
    d.anc d.H (d.run j) (d.prims j) = .push → d.receiptsAfter j = d.receipts j
  hinc : ∀ j, Before d.reply j → d.core j → rawControl d.raw (d.naming.images j) d.par d.anc d.H
    (d.run j) (d.prims j) = .push → d.incomplete j = true → d.expectedIsHead j = true ∧ d.closed j =
    false
  hclosure : ∀ j, Before d.reply j → d.core j → rawControl d.raw (d.naming.images j) d.par d.anc d.H
    (d.run j) (d.prims j) = .push → d.offered = R → d.expectedIsHead j = true → d.closed j = true
  hseq : ∀ j, d.reply j = .fresh → w ≤ d.seqAfter j
  hannc : ∀ j, d.reply j = .fresh → d.anncAfter j = none ∨ d.anncAfter j = some R

/-- Such a run reaches a fresh reply that leaves it entered. -/
theorem EntryLaws.enters {ρ α : Type} [DecidableEq ρ] {R : ρ} {w : Nat} {d : EntryData ρ α}
    (L : EntryLaws R w d)
    (hroundServe : ∀ j, Before d.reply j → d.fetchCall j → d.reply j = .fresh → ∀ i,
      (d.round j).active i = true → ¬ (d.round j).failed i) :
    ∃ j, d.reply j = .fresh ∧ d.ap j = R ∧ d.receiptsAfter j = false ∧
      d.incomplete j = false ∧ w ≤ d.seqAfter j ∧
      (d.anncAfter j = none ∨ d.anncAfter j = some R) :=
  raw_entry_reached
    d.raw d.naming d.par d.anc L.trans L.hlt d.H L.hraw d.run d.after d.prims d.reply d.core
    d.starts d.fetchCall d.pushDropped d.offered R d.heard L.hnaming L.hkind L.hrecord L.hdiffer
    L.hheard L.hburst L.hobjects L.hframe L.hpoll L.hstart L.hstartFetch L.hfetchCall L.hnd
    L.hpush d.ap d.seqAfter d.anncAfter w d.receipts d.receiptsAfter d.incomplete
    d.expectedIsHead d.closed L.hsource d.round L.hround hroundServe L.hfetchInc L.hoffer d.annc
    L.hneeds L.hguard L.hheadReceipts L.hinc L.hclosure L.hseq L.hannc

end Musubi.EarlyEntry.Control
