/-
Raw entry, its persistence and the native per-call contract assembly. The convergence proof uses
this file.
-/
import Musubi.EarlyEntry.Abstract
import Musubi.EarlyEntry.FreshFetch
import Musubi.RecordEpoch

namespace Musubi.EarlyEntry.Control

open Musubi NodeSettle

/-! ### A raw entry

From the common finite cut, a node's first fresh reply leaves it entered (`raw_entry_reached`):
the hub's records applied, no record receipts, a known pair from after the cut, and nothing
announced but the hub's records. The reply is not an `Incomplete` answer, after which the driver
would reopen the node.

* After a fresh `Fetched` reply this holds through the round after it (`fresh_fetch_current`).
* A fresh `Head` reply answers a push. The push is refused unless it offers the hub's records,
  and it offers those the node has applied. It is made with the core's record test quiet
  (`choose_push_announced`), and receipts have an announcement in an active round, so it is made
  with no receipts (`Retry.Records.no_receipts_when_quiet`), and the reply leaves them so.
* An honest push from the hub's head with the hub's records is closed once uploaded, so it is not
  answered `Incomplete`.

Nothing before the entry is read as NodeSettle's state. -/

/-- What a node's pre-entry raw run reads, sampled from its actual events: its run up to a first
fresh reply (`HeadData`), and the rest. Data only: its laws are `EntryLaws`. -/
structure EntryData (ρ α : Type) extends HeadData ρ α where
  /-- The records applied right after the step. -/
  ap : Nat → ρ
  /-- The known sequence right after the step. -/
  seqAfter : Nat → Nat
  /-- The records announced, right after the step. -/
  anncAfter : Nat → Option ρ
  /-- The records announced, at each step. -/
  annc : Nat → Option ρ
  /-- Whether the node holds record receipts at the step. -/
  receipts : Nat → Bool
  /-- Whether it holds record receipts right after the step. -/
  receiptsAfter : Nat → Bool
  /-- A `Push::answer` bit: the answer is `Incomplete`. -/
  incomplete : Nat → Bool
  /-- A `Push::answer` bit: the push's expected head is the hub's head. -/
  expectedIsHead : Nat → Bool
  /-- A `Push::answer` bit: the hub holds the push's closure. -/
  closed : Nat → Bool
  /-- The data of the round after a fresh `Fetched` reply. -/
  round : Nat → FetchData α

/-- The native per-call laws of that run, as `raw_entry_reached` takes them: those of its run up
to a fresh head (`HeadLaws`), and those that carry it from there to entry. Each law is asked of
the steps before the first fresh reply, except `fresh_seq` and `fresh_announces`, which are asked
of every fresh reply. The objects laws rest on a valid base: a node advertises as haves
only objects it holds, so a reply brings what it lacks, or the round fails and another starts.
`hroundServe` is not among them: `raw_entry_reached` takes it as a separate argument. -/
structure EntryLaws {ρ α : Type} [DecidableEq ρ] (R : ρ) (w : Nat) (d : EntryData ρ α) : Prop
    extends HeadLaws R d.toHeadData where
  /-- A fresh reply comes from a `Fetch` or a push. -/
  fresh_source : ∀ j, Before d.reply j → d.reply j = .fresh →
    d.fetchCall j ∨ (d.core j ∧ d.ctl j = .push)
  /-- The round after a fresh `Fetch` reply obeys `FetchCurrent` of its data, holding receipts if
  the node did right after the reply (its prelude may add some). -/
  round_laws : ∀ j, Before d.reply j → d.fetchCall j → d.reply j = .fresh →
    FetchCurrent (d.ap j) R (d.round j) ∧
      (d.receiptsAfter j = true → (d.round j).receiptsAtStart = true)
  /-- A fresh `Fetch` reply is not an `Incomplete` answer. -/
  fetch_complete : ∀ j, Before d.reply j → d.fetchCall j → d.incomplete j = false
  /-- A push offers the records the node has applied. -/
  push_offers_applied : ∀ j, Before d.reply j → d.core j → d.ctl j = .push → d.ap j = d.offered
  /-- The core's first test is `Retry.Records.needsRecords` of the records applied, those
  announced and the receipts. -/
  announced_needs : ∀ i, Before d.reply i → d.core i →
    (d.prims i).announced = Retry.Records.needsRecords (d.ap i) (d.annc i) (d.receipts i)
  /-- Receipts have an announcement (`Retry.Records.State.Guard`). -/
  receipts_announced : ∀ i, Before d.reply i → d.core i → d.receipts i = true → d.annc i ≠ none
  /-- A push leaves the receipts as they were. -/
  push_keeps_receipts : ∀ j, Before d.reply j → d.core j → d.ctl j = .push →
    d.receiptsAfter j = d.receipts j
  /-- `Push::answer` answers `Incomplete` only from its head, to a push whose closure it lacks. -/
  incomplete_from_head : ∀ j, Before d.reply j → d.core j → d.ctl j = .push →
    d.incomplete j = true → d.expectedIsHead j = true ∧ d.closed j = false
  /-- An honest push from the hub's head, with the hub's records, is closed once uploaded. -/
  head_push_closed : ∀ j, Before d.reply j → d.core j → d.ctl j = .push → d.offered = R →
    d.expectedIsHead j = true → d.closed j = true
  /-- A fresh reply names a known sequence from the cut's `w` on. -/
  fresh_seq : ∀ j, d.reply j = .fresh → w ≤ d.seqAfter j
  /-- A fresh reply announces only the hub's records. -/
  fresh_announces : ∀ j, d.reply j = .fresh → d.anncAfter j = none ∨ d.anncAfter j = some R

/-- A node enters, raw: its first fresh reply leaves it with the hub's records `R` applied, no
record receipts, a known sequence from the cut's `w` on and nothing announced but `R`, and is not
an `Incomplete` answer. `EntryLaws` gives what `fresh_head_reached` takes (`HeadLaws`), and:
* `fresh_source`: a fresh reply comes only from a `Fetch` or a push.
* `round_laws`: the round after a fresh `Fetch` reply obeys `FetchCurrent` of its sampled data
  `round`, holding receipts if the node did right after the reply (its prelude may add some).
  `fetch_complete`: such a reply is never `Incomplete`.
* `push_offers_applied`: a push offers the records the node has applied (`ap`).
* `announced_needs`, `receipts_announced`, `push_keeps_receipts`: the core's first test is
  `Retry.Records.needsRecords` of the records applied, those announced (`annc`) and the receipts.
  Receipts have an announcement in an active round (`Retry.Records.State.Guard`), so a push, made
  with that test quiet, is made with no receipts (`Retry.Records.no_receipts_when_quiet`), and a
  `Head` reply leaves them so.
* `incomplete_from_head`, `head_push_closed`: `Push::answer` answers `Incomplete` only from its
  head and to a push whose closure it lacks, and an honest push with the hub's records from its
  head is closed once uploaded (the conditional closure law).
* `fresh_seq`, `fresh_announces`: a fresh reply names a head from after the cut and announces only
  the hub's records.

`hroundServe` is a separate premise, not a law of the run: no `GetObjects` fails in the round
after a fresh `Fetch`. -/
theorem raw_entry_reached {ρ α : Type} [DecidableEq ρ] {R : ρ} {w : Nat} {d : EntryData ρ α}
    (L : EntryLaws R w d)
    (hroundServe : ∀ j, Before d.reply j → d.fetchCall j → d.reply j = .fresh → ∀ i,
      (d.round j).active i = true → ¬ (d.round j).failed i) :
    ∃ j, d.reply j = .fresh ∧ d.ap j = R ∧ d.receiptsAfter j = false ∧
      d.incomplete j = false ∧ w ≤ d.seqAfter j ∧
      (d.anncAfter j = none ∨ d.anncAfter j = some R) := by
  obtain ⟨j, hj, hmin⟩ := exists_first (fresh_head_reached L.toHeadLaws)
  have hb : Before d.reply j := fun m hm h => hmin m hm h
  rcases L.fresh_source j hb hj with hf | ⟨hc, hp⟩
  · obtain ⟨F, hF⟩ := L.round_laws j hb hf hj
    obtain ⟨hap, hrec⟩ := fresh_fetch_current F (hroundServe j hb hf hj)
    have hra : d.receiptsAfter j = false := by
      cases h : d.receiptsAfter j
      · rfl
      · rw [hF h] at hrec; cases hrec
    exact ⟨j, hj, hap, hra, L.fetch_complete j hb hf, L.fresh_seq j hj, L.fresh_announces j hj⟩
  · have hl := L.push_reply j hb hc hp
    have hoR : d.offered = R := Classical.byContradiction fun hne => by
      have h := hl.2 hne
      rw [hj] at h
      cases h
    have hrec : d.receipts j = false := by
      have hn : (d.prims j).announced = false := choose_push_announced hp
      rw [L.announced_needs j hb hc] at hn
      exact Retry.Records.no_receipts_when_quiet (d.ap j) (d.annc j) (d.receipts j)
        (L.receipts_announced j hb hc) hn
    have hinc' : d.incomplete j = false := by
      cases h : d.incomplete j
      · rfl
      · obtain ⟨he, hcl⟩ := L.incomplete_from_head j hb hc hp h
        rw [L.head_push_closed j hb hc hp hoR he] at hcl
        cases hcl
    refine ⟨j, hj, by rw [L.push_offers_applied j hb hc hp, hoR], ?_, hinc', L.fresh_seq j hj,
      L.fresh_announces j hj⟩
    rw [L.push_keeps_receipts j hb hc hp, hrec]

/-- What a node's entry reads of it, raw. -/
structure RawNode (ρ : Type) where
  /-- The records it has applied. -/
  applied : ρ
  /-- Its known sequence. -/
  seq : Nat
  /-- The records announced to it. -/
  annc : Option ρ
  /-- Whether it holds record receipts. -/
  receipts : Bool

/-- A node has entered, raw: the hub's records applied, a known sequence from the cut's `w` on,
nothing announced but the hub's records, no receipts. -/
def RawEntry {ρ : Type} (R : ρ) (w : Nat) (e : RawNode ρ) : Prop :=
  e.applied = R ∧ w ≤ e.seq ∧ (e.annc = none ∨ e.annc = some R) ∧ e.receipts = false

/-- Entry, once reached, lasts. Assumes:
* each step keeps entry unless the driver reopens the node (no adoption past the credit cut, the
  known sequence never going back without a reopen, announcements only of the hub's records, no
  receipts without taking);
* the driver reopens the node only after an `Incomplete` answer, in the successful suffix after
  ordinary I/O and transport failures and their reopens have ceased;
* `Incomplete` comes only from the hub's head to a push whose closure it lacks, and an entered
  node's push from that head is closed once uploaded (the conditional closure law: it offers the
  hub's records).

So an entered node is never reopened. -/
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

end Musubi.EarlyEntry.Control
