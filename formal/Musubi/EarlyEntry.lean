/-
An eligible node comes to have the hub's records applied and to know a pair from after the
cut, with no assumption that the hub's head has settled (`early_entry`). This is what HubSuffix
needs of eligible nodes on entry, besides maintenance writes stopping.

After the record cut the hub's records are `R` in every reply, but its head may still move.
The daemon takes notifications only between rounds, so within a round the node's known pair
changes only by a reply to its own request. Until the node has applied `R`, the hub refuses its
pushes, checking records before heads, so a push leaves the known pair alone too. With it
frozen, every NodeSettle step lowers NodeSettle's rank (`local_burst_finite`), so a running
round soon polls or idles. A poll's reply, or the next round's, announces `R`, and an eligible
node, whose op heads `R` does not drop, adopts it at its next step. A core `Idle` ends the round
only when housekeeping (`when_idle`) writes nothing; that it eventually writes nothing is
assumed, as HubSuffix does. A failed call reopens the node, which this model does not take:
root's RecordEpoch shows such failures stop.

Ids are raw hub-space ones throughout, as in NodeSettle.
-/
import Musubi.NodeSettle
import Musubi.PendingEpoch
import Musubi.ExecSound
import Musubi.RecordEpoch

namespace Musubi.EarlyEntry

open Musubi Musubi.NodeSettle

/-! ## Bursts with the known pair frozen -/

/-- What NodeSettle's steps need of a state, wherever the hub's head is. -/
structure LInv (σ : NS) : Prop where
  parLt : ParLt σ.par
  knownLt : σ.known.2 < σ.next
  headsNe : σ.heads ≠ []
  headsLt : ∀ y ∈ σ.heads, y < σ.next
  imgNe : σ.img ≠ []
  imgLt : ∀ i ∈ σ.img, i < σ.next

/-- NodeSettle's context for a burst with known pair `K`: the hub's records `R`, and a pair that
is not `K`, so that none of NodeSettle's replies, which teach the context's pair, is part of a
burst. -/
def bctx (R : Nat) (drops : Nat → Nat → Prop) (K : Nat × Nat) : Ctx :=
  ⟨K.1 + 1, K.2, R, drops⟩

theorem LInv.sinv {σ : NS} (I : LInv σ) (R : Nat) (drops : Nat → Nat → Prop) :
    NodeSettle.SInv (bctx R drops σ.known) σ where
  parLt := I.parLt
  knownLt := I.knownLt
  hLt := I.knownLt
  headsNe := I.headsNe
  headsLt := I.headsLt
  imgNe := I.imgNe
  imgLt := I.imgLt
  recs := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only [bctx] at h1
    omega

theorem linv_of_sinv {c : Ctx} {σ : NS} (I : NodeSettle.SInv c σ) : LInv σ :=
  ⟨I.parLt, I.knownLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt⟩

/-- A burst of steps that leave the known pair alone is finite: there is no endless one. -/
theorem local_burst_finite (R : Nat) (drops : Nat → Nat → Prop) (run : Nat → NS) (K : Nat × Nat)
    (h0 : LInv (run 0)) (hk0 : (run 0).known = K)
    (hs : ∀ i, Busy (bctx R drops K) (run i) (run (i + 1)) ∧ (run (i + 1)).known = K) :
    False := by
  have hk : ∀ i, (run i).known = K := by
    intro i
    induction i with
    | zero => exact hk0
    | succ i _ => exact (hs i).2
  have hinv : ∀ i, NodeSettle.SInv (bctx R drops K) (run i) := by
    intro i
    induction i with
    | zero => have := h0.sinv R drops; rwa [hk0] at this
    | succ i ih => exact inv_busy ih (hs i).1
  have hlt : ∀ i, LexLt (rank (bctx R drops K) (run (i + 1))) (rank (bctx R drops K) (run i)) :=
    fun i => rank_busy (hinv i) (hs i).1
  obtain ⟨k, hk⟩ := lex_stabilizes 11 (fun i => rank (bctx R drops K) (run i))
    (fun _ => rank_length _ _) (fun i => (hlt i).le)
  have h := hlt k
  rw [hk (k + 1) (Nat.le_succ k)] at h
  exact lexLt_irrefl _ h

/-! ## The early events -/

/-- A `Fetched` reply after the cut, from a hub whose records are `R`, wherever its head is: the
node knows a pair from after the cut, whose sequence is `w`, and announces `R` unless applied,
or announces nothing. What it has applied is unchanged, and its state stays well formed. -/
structure FetchAny (R w : Nat) (σ σ' : NS) : Prop where
  known : w ≤ σ'.known.1
  annc : σ'.annc = some R ∨ (σ'.annc = none ∧ R = σ.ap)
  ap : σ'.ap = σ.ap
  act : σ'.act = σ.act
  inv : LInv σ'

/-- A `Head` reply after the cut, to a push or as a notification: the node knows a pair from
after the cut, and what it announced and applied is unchanged. -/
structure HeadAny (w : Nat) (σ σ' : NS) : Prop where
  known : w ≤ σ'.known.1
  annc : σ'.annc = σ.annc
  ap : σ'.ap = σ.ap
  act : σ'.act = σ.act
  inv : LInv σ'

inductive ELab
  | step
  | idle
  | maint
  | poll
  | push
  | start
  | notify
  | frame

/-- What can happen to the node after the cut, before the hub settles. -/
inductive EEv (R w : Nat) (drops : Nat → Nat → Prop) : ELab → NS → NS → Prop
  /-- A core step whose replies, if any, teach no head: its known pair is as it was. A push
  before `R` is applied is one, refused before the hub reads its heads (NodeSettle's
  `pushStale` with a refusal). -/
  | step {σ σ' : NS} (ha : σ.act = true) (h : Busy (bctx R drops σ.known) σ σ')
      (hk : σ'.known = σ.known) : EEv R w drops .step σ σ'
  | idle {σ σ' : NS} (ha : σ.act = true) (h : Idle (bctx R drops σ.known) σ σ') :
      EEv R w drops .idle σ σ'
  /-- The core idled, but housekeeping (`when_idle`) wrote something, so the round goes on:
  fresh operations on top, nothing else changed. -/
  | maint {σ σ' σ1 : NS} (ha : σ.act = true) (h : Idle (bctx R drops σ.known) σ σ1)
      (hw : Ext { σ1 with act := true } σ') : EEv R w drops .maint σ σ'
  /-- A core step that polls, with the reply. -/
  | poll {σ σ' : NS} (ha : σ.act = true) (hg : Go (bctx R drops σ.known) σ)
      (h : FetchAny R w σ σ') : EEv R w drops .poll σ σ'
  /-- A core step that pushes once `R` is applied, with the hub's `Head` reply. -/
  | push {σ σ' : NS} (ha : σ.act = true) (hg : Go (bctx R drops σ.known) σ) (hap : σ.ap = R)
      (hn : (norm σ).annc = none) (h : HeadAny w (norm σ) σ') : EEv R w drops .push σ σ'
  | start {σ σ' σ1 : NS} (ha : σ.act = false) (h : FetchAny R w σ σ1)
      (he : σ' = { σ1 with act := true }) : EEv R w drops .start σ σ'
  /-- A notification, which the daemon takes only between rounds. -/
  | notify {σ σ' : NS} (ha : σ.act = false) (h : HeadAny w σ σ') : EEv R w drops .notify σ σ'
  | frame {σ : NS} : EEv R w drops .frame σ σ

/-- Entry: the hub's records applied, a pair from after the cut known, and no other
announcement. -/
def Entry (R w : Nat) (σ : NS) : Prop :=
  σ.ap = R ∧ w ≤ σ.known.1 ∧ (σ.annc = none ∨ σ.annc = some R)

/-! ## Steps that keep entry, and the one an announcement forces -/

theorem normA_fine {σ : NS} {R : Nat} (hap : σ.ap = R) (hann : σ.annc = none ∨ σ.annc = some R) :
    normA σ.annc σ.ap = none := by
  rcases hann with h | h <;> rw [h]
  · rfl
  · rw [hap]; simp [normA]

/-- Once the hub's records are applied, with no other announcement, no step changes that. -/
theorem busy_fine {c : Ctx} {σ σ' : NS} (hap : σ.ap = c.R)
    (hann : σ.annc = none ∨ σ.annc = some c.R) (h : Busy c σ σ') :
    σ'.ap = c.R ∧ (σ'.annc = none ∨ σ'.annc = some c.R) := by
  have hn := normA_fine hap hann
  have nota : ∀ A, σ.annc = some A → A ≠ σ.ap → False := by
    intro A hA hne
    rcases hann with h | h <;> rw [h] at hA <;> cases hA
    exact hne hap.symm
  have fetched : ∀ {τ τ' : NS}, FetchedRep c τ τ' → τ.ap = c.R →
      τ'.ap = c.R ∧ (τ'.annc = none ∨ τ'.annc = some c.R) := by
    intro τ τ' F ht
    refine ⟨F.ap.trans ht, ?_⟩
    rcases F.annc with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  have written : ∀ {σ1 : NS} {new : Nat}, WriteRes { norm σ with plan := [] } σ1 new →
      σ1.ap = c.R ∧ σ1.annc = none := by
    intro σ1 new W
    obtain ⟨y, -, (⟨-, F⟩ | ⟨-, he, -⟩)⟩ := W
    · obtain ⟨-, fa, fap, -, -, -, -, -, -⟩ := F.ext.fields
      exact ⟨fap.trans hap, fa.trans hn⟩
    · subst he; exact ⟨hap, hn⟩
  cases h with
  | adopt A ha hne _ _ => exact (nota A ha hne).elim
  | merge _ _ _ _ he => subst he; exact ⟨hap, Or.inl hn⟩
  | mergeExisting _ _ _ _ _ _ _ he => subst he; exact ⟨hap, Or.inl hn⟩
  | prune _ _ _ _ he => subst he; exact ⟨hap, Or.inl hn⟩
  | realizePlan _ _ _ _ _ _ he => subst he; exact ⟨hap, Or.inl hn⟩
  | realizeSurvey _ _ _ _ _ _ _ he => subst he; exact ⟨hap, Or.inl hn⟩
  | fetch σ1 _ _ _ _ _ _ hf ho =>
    have h1 : σ1.ap = c.R ∧ (σ1.annc = none ∨ σ1.annc = some c.R) := by
      rcases hf with ⟨-, F⟩ | ⟨-, he⟩
      · exact fetched F hap
      · subst he; exact ⟨hap, Or.inl hn⟩
    rcases ho with ⟨-, O⟩ | ⟨-, he⟩
    · rw [O.rest]; exact h1
    · subst he; exact h1
  | advanceTake A _ _ _ ha _ =>
    obtain ⟨h1, h2⟩ := normA_some ha
    exact (nota A h1 h2).elim
  | advance _ _ _ _ _ hv =>
    obtain ⟨-, fa, fap, -, -, -, -, -, -⟩ := hv.ext.fields
    exact ⟨fap.trans hap, Or.inl (fa.trans hn)⟩
  | differPoll _ _ _ _ _ _ hr => exact fetched hr hap
  | pushStale σ1 _ _ _ _ _ _ _ _ _ hw' _ hr =>
    have h1 := written hw'
    rcases hr with ⟨-, he⟩ | ⟨-, F⟩
    · subst he; exact ⟨h1.1, Or.inl h1.2⟩
    · exact ⟨F.ap.trans h1.1, Or.inl (F.annc.trans h1.2)⟩
  | writePoll σ1 _ _ _ _ _ _ _ _ hw' _ hr => exact fetched hr (written hw').1

theorem idle_fields {c : Ctx} {σ σ' : NS} (h : Idle c σ σ') :
    σ'.ap = σ.ap ∧ σ'.known = σ.known ∧ σ'.annc = normA σ.annc σ.ap ∧ σ'.act = false := by
  cases h with
  | fetchIdle _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl, rfl, rfl⟩
  | differIdle _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl, rfl, rfl⟩
  | goal _ _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl, rfl, rfl⟩

theorem idle_go {c : Ctx} {σ σ' : NS} (h : Idle c σ σ') : Go c σ := by
  cases h with
  | fetchIdle hg _ _ _ _ _ _ _ => exact hg
  | differIdle hg _ _ _ _ _ _ _ => exact hg
  | goal hg _ _ _ _ _ _ _ _ => exact hg

/-- With the hub's records announced, not applied, and dropping no op head, a step must adopt
them: every other step is past `Go`, which a blocked preparation alone allows. -/
theorem forced_adopt {c : Ctx} {σ σ' : NS} (ha : σ.annc = some c.R) (hne : c.R ≠ σ.ap)
    (hb : ¬ Blocked c σ c.R) (h : Busy c σ σ') : Take c σ σ' c.R := by
  have nogo : ¬ Go c σ := fun hg => hb (hg c.R ha hne)
  cases h with
  | adopt A ha' _ _ ht => rw [ha] at ha'; cases ha'; exact ht
  | merge _ hg _ _ _ => exact absurd hg nogo
  | mergeExisting _ _ hg _ _ _ _ _ => exact absurd hg nogo
  | prune _ hg _ _ _ => exact absurd hg nogo
  | realizePlan _ _ hg _ _ _ _ => exact absurd hg nogo
  | realizeSurvey _ _ hg _ _ _ _ _ => exact absurd hg nogo
  | fetch _ hg _ _ _ _ _ _ _ => exact absurd hg nogo
  | advanceTake _ hg _ _ _ _ => exact absurd hg nogo
  | advance hg _ _ _ _ _ => exact absurd hg nogo
  | differPoll hg _ _ _ _ _ _ => exact absurd hg nogo
  | pushStale _ _ hg _ _ _ _ _ _ _ _ _ _ => exact absurd hg nogo
  | writePoll _ _ hg _ _ _ _ _ _ _ _ _ => exact absurd hg nogo

theorem LInv.act {σ : NS} (I : LInv σ) (b : Bool) : LInv { σ with act := b } :=
  ⟨I.parLt, I.knownLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt⟩

theorem LInv.ext {σ σ' : NS} (I : LInv σ) (E : Ext σ σ') : LInv σ' := by
  obtain ⟨fk, -, -, -, fi, -, -, -, -⟩ := E.fields
  refine ⟨E.parLt, ?_, E.headsNe, E.headsLt, ?_, ?_⟩
  · rw [fk]; exact Nat.lt_of_lt_of_le I.knownLt E.grows
  · rw [fi]; exact I.imgNe
  · rw [fi]; exact fun i hi => Nat.lt_of_lt_of_le (I.imgLt i hi) E.grows

section Run

variable {R w : Nat} {drops : Nat → Nat → Prop}

theorem linv_ev {σ σ' : NS} {l : ELab} (I : LInv σ) (h : EEv R w drops l σ σ') : LInv σ' := by
  cases h with
  | step _ h _ => exact linv_of_sinv (inv_busy (I.sinv R drops) h)
  | idle _ h => exact linv_of_sinv (inv_idle (I.sinv R drops) h)
  | maint _ h hw => exact ((linv_of_sinv (inv_idle (I.sinv R drops) h)).act true).ext hw
  | poll _ _ F => exact F.inv
  | push _ _ _ _ F => exact F.inv
  | start _ F he => subst he; exact F.inv.act true
  | notify _ F => exact F.inv
  | frame => exact I

/-- Entry is kept. -/
theorem entry_ev {σ σ' : NS} {l : ELab} (he : Entry R w σ) (h : EEv R w drops l σ σ') :
    Entry R w σ' := by
  obtain ⟨hap, hw, hann⟩ := he
  cases h with
  | step _ h hk =>
    obtain ⟨a, b⟩ := busy_fine (c := bctx R drops σ.known) hap hann h
    exact ⟨a, by rw [hk]; exact hw, b⟩
  | idle _ h =>
    obtain ⟨a, k, n, -⟩ := idle_fields h
    exact ⟨a.trans hap, by rw [k]; exact hw, Or.inl (n.trans (normA_fine hap hann))⟩
  | poll _ _ F =>
    refine ⟨F.ap.trans hap, F.known, ?_⟩
    rcases F.annc with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  | push _ _ _ _ F =>
    exact ⟨F.ap.trans hap, F.known, Or.inl (F.annc.trans (normA_fine hap hann))⟩
  | maint _ h hx =>
    obtain ⟨a, k, n, -⟩ := idle_fields h
    obtain ⟨fk, fa, fap, -, -, -, -, -, -⟩ := hx.fields
    have hk' : σ'.known = σ.known := fk.trans k
    exact ⟨fap.trans (a.trans hap), by rw [hk']; exact hw,
      Or.inl (fa.trans (n.trans (normA_fine hap hann)))⟩
  | start _ F he =>
    subst he
    refine ⟨F.ap.trans hap, F.known, ?_⟩
    rcases F.annc with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  | notify _ F => exact ⟨F.ap.trans hap, F.known, by rw [F.annc]; exact hann⟩
  | frame => exact ⟨hap, hw, hann⟩

/-- A frame changes nothing. -/
theorem frame_eq {σ σ' : NS} (h : EEv R w drops .frame σ σ') : σ' = σ := by
  cases h; rfl

theorem step_facts {σ σ' : NS} (h : EEv R w drops .step σ σ') :
    Busy (bctx R drops σ.known) σ σ' ∧ σ'.known = σ.known := by
  cases h with
  | step _ h hk => exact ⟨h, hk⟩

theorem idle_act' {σ σ' : NS} (h : EEv R w drops .idle σ σ') : σ'.act = false := by
  cases h with
  | idle _ h => exact (idle_fields h).2.2.2

theorem notify_act {σ σ' : NS} (h : EEv R w drops .notify σ σ') : σ.act = false := by
  cases h with
  | notify ha _ => exact ha

/-- A push answered by a head comes only once the records are applied, so it reaches entry. -/
theorem push_entry {σ σ' : NS} (h : EEv R w drops .push σ σ') : Entry R w σ' := by
  cases h with
  | push _ _ hap hn F => exact ⟨F.ap.trans hap, F.known, Or.inl (F.annc.trans hn)⟩

/-- What a poll's reply, or a round's first, leaves. -/
theorem fetch_facts {σ σ' : NS} {l : ELab} (h : EEv R w drops l σ σ')
    (hl : l = .poll ∨ l = .start) :
    w ≤ σ'.known.1 ∧ (σ'.annc = some R ∨ (σ'.annc = none ∧ R = σ.ap)) ∧ σ'.ap = σ.ap ∧
      σ'.act = true := by
  cases h with
  | poll ha _ F => exact ⟨F.known, F.annc, F.ap, F.act.trans ha⟩
  | start _ F he => subst he; exact ⟨F.known, F.annc, F.ap, rfl⟩
  | step => rcases hl with h | h <;> cases h
  | idle => rcases hl with h | h <;> cases h
  | maint => rcases hl with h | h <;> cases h
  | push => rcases hl with h | h <;> cases h
  | notify => rcases hl with h | h <;> cases h
  | frame => rcases hl with h | h <;> cases h

/-- In a running round, with the hub's records announced, not applied, and dropping no op head,
the next event that is not a frame reaches entry: it is an adoption. -/
theorem forced_step {σ σ' : NS} {l : ELab} (h : EEv R w drops l σ σ') (hact : σ.act = true)
    (hann : σ.annc = some R) (hne : R ≠ σ.ap) (hb : ¬ ∃ y ∈ σ.heads, drops R y)
    (hw : w ≤ σ.known.1) (hl : l ≠ .frame) : Entry R w σ' := by
  have nogo : ¬ Go (bctx R drops σ.known) σ := fun hg => hb (hg R hann hne)
  cases h with
  | step _ h hk =>
    have T := forced_adopt (c := bctx R drops σ.known) hann hne hb h
    refine ⟨T.ap, by rw [hk]; exact hw, ?_⟩
    rcases T.annc with h | h
    · exact Or.inl h
    · rw [h]; exact Or.inr hann
  | idle _ h => exact absurd (idle_go h) nogo
  | maint _ h _ => exact absurd (idle_go h) nogo
  | poll _ hg _ => exact absurd hg nogo
  | push _ hg _ _ _ => exact absurd hg nogo
  | start ha _ _ => rw [hact] at ha; cases ha
  | notify ha _ => rw [hact] at ha; cases ha
  | frame => exact absurd rfl hl

end Run

theorem exists_first {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  apply Classical.byContradiction
  intro hno
  have key : ∀ n m, m < n → ¬ P m := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm hp
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with h | h
      · exact ih m h hp
      · subst h; exact hno ⟨m, hp, ih⟩
  obtain ⟨n, hn⟩ := h
  exact key (n + 1) n (Nat.lt_succ_self n) hn

/-! ## Entry -/

/-- The core of `early_entry`: from `k0` on there is no housekeeping. -/
theorem early_entry_from (R w : Nat) (drops : Nat → Nat → Prop) (run : Nat → NS)
    (lab : Nat → ELab) (k0 : Nat)
    (hev : ∀ i, k0 ≤ i → EEv R w drops (lab i) (run i) (run (i + 1)))
    (h0 : LInv (run k0))
    (nomaint : ∀ i, k0 ≤ i → lab i ≠ .maint)
    (hE : ∀ i, k0 ≤ i → ¬ ∃ y ∈ (run i).heads, drops R y)
    (hstart : ∀ i, k0 ≤ i → (run i).act = false → ∃ j, i ≤ j ∧ lab j = .start)
    (hcore : ∀ i, k0 ≤ i → (run i).act = true → ∃ j, i ≤ j ∧
      (lab j = .step ∨ lab j = .idle ∨ lab j = .poll ∨ lab j = .push ∨ lab j = .maint)) :
    ∃ k, k0 ≤ k ∧ ∀ i, k ≤ i → Entry R w (run i) := by
  have hinv : ∀ d, LInv (run (k0 + d)) := by
    intro d
    induction d with
    | zero => exact h0
    | succ d ih => exact linv_ev ih (hev _ (by omega))
  have persist : ∀ k, k0 ≤ k → Entry R w (run k) → ∀ i, k ≤ i → Entry R w (run i) := by
    intro k hk he i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    induction d with
    | zero => exact he
    | succ d ih => exact entry_ev (ih (by omega)) (hev _ (by omega))
  suffices h : ∃ k, k0 ≤ k ∧ Entry R w (run k) by
    obtain ⟨k, hk, he⟩ := h
    exact ⟨k, hk, persist k hk he⟩
  apply Classical.byContradiction
  intro hno
  have noEntry : ∀ i, k0 ≤ i → ¬ Entry R w (run i) := fun i hi he => hno ⟨i, hi, he⟩
  -- With the records announced and not applied in a running round, the next event that is
  -- not a frame adopts them.
  have forced : ∀ j, k0 ≤ j → (run j).act = true → (run j).annc = some R →
      R ≠ (run j).ap → w ≤ (run j).known.1 → False := by
    intro j hj hact hann hne hw
    obtain ⟨j1, hj1, hl1⟩ := hcore j hj hact
    have hex : ∃ n, lab (j + n) ≠ .frame := by
      refine ⟨j1 - j, ?_⟩
      rw [show j + (j1 - j) = j1 by omega]
      rcases hl1 with h | h | h | h | h <;> rw [h] <;> exact fun e => ELab.noConfusion e
    obtain ⟨n, hn, hmin⟩ := exists_first hex
    have same : ∀ m, m ≤ n → run (j + m) = run j := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        have hf : lab (j + m) = .frame :=
          Classical.byContradiction fun h => hmin m (by omega) h
        have h := hev (j + m) (by omega)
        rw [hf] at h
        show run (j + m + 1) = run j
        rw [frame_eq h]
        exact ih (by omega)
    have h := hev (j + n) (by omega)
    rw [same n (Nat.le_refl n)] at h
    exact noEntry (j + n + 1) (by omega) (forced_step h hact hann hne (hE j hj) hw hn)
  -- So no poll is answered, nor does a round start.
  have noFetch : ∀ j, k0 ≤ j → (lab j = .poll ∨ lab j = .start) → False := by
    intro j hj hl
    have h := hev j hj
    obtain ⟨hw, hann, hap, hact⟩ := fetch_facts h hl
    by_cases hR : R = (run (j + 1)).ap
    · apply noEntry (j + 1) (by omega)
      refine ⟨hR.symm, hw, ?_⟩
      rcases hann with h | ⟨h, -⟩
      · exact Or.inr h
      · exact Or.inl h
    · have hann' : (run (j + 1)).annc = some R := by
        rcases hann with h | ⟨-, h⟩
        · exact h
        · exact absurd (h.trans hap.symm) hR
      exact forced (j + 1) (by omega) hact hann' hR hw
  -- A round is then always running,
  have actTrue : ∀ i, k0 ≤ i → (run i).act = true := by
    intro i hi
    cases ha : (run i).act with
    | true => rfl
    | false =>
      obtain ⟨j, hj, hl⟩ := hstart i hi ha
      exact (noFetch j (by omega) (Or.inr hl)).elim
  -- and every event a step or a frame: an idle would end the round, a notification needs none
  -- running, and a push answered by a head comes only at entry.
  have stepOrFrame : ∀ i, k0 ≤ i → lab i = .step ∨ lab i = .frame := by
    intro i hi
    have h := hev i hi
    cases hl : lab i with
    | step => exact Or.inl rfl
    | frame => exact Or.inr rfl
    | poll => exact (noFetch i hi (Or.inl hl)).elim
    | start => exact (noFetch i hi (Or.inr hl)).elim
    | idle =>
      rw [hl] at h
      have := idle_act' h
      rw [actTrue (i + 1) (by omega)] at this
      cases this
    | notify =>
      rw [hl] at h
      have := notify_act h
      rw [actTrue i hi] at this
      cases this
    | push =>
      rw [hl] at h
      exact (noEntry (i + 1) (by omega) (push_entry h)).elim
    | maint => exact absurd hl (nomaint i hi)
  -- The known pair is then frozen, and every step lowers the rank: an endless burst.
  have hK : ∀ d, (run (k0 + d)).known = (run k0).known := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      have h := hev (k0 + d) (by omega)
      show (run (k0 + d + 1)).known = (run k0).known
      rcases stepOrFrame (k0 + d) (by omega) with hl | hl <;> rw [hl] at h
      · rw [(step_facts h).2, ih]
      · rw [frame_eq h, ih]
  have hSI : ∀ d, NodeSettle.SInv (bctx R drops (run k0).known) (run (k0 + d)) := by
    intro d
    have := (hinv d).sinv R drops
    rwa [hK d] at this
  have mono : ∀ d,
      LexLe (rank (bctx R drops (run k0).known) (run (k0 + d + 1)))
        (rank (bctx R drops (run k0).known) (run (k0 + d))) ∧
      (lab (k0 + d) = .step →
        LexLt (rank (bctx R drops (run k0).known) (run (k0 + d + 1)))
          (rank (bctx R drops (run k0).known) (run (k0 + d)))) := by
    intro d
    have h := hev (k0 + d) (by omega)
    rcases stepOrFrame (k0 + d) (by omega) with hl | hl <;> rw [hl] at h
    · have hb := (step_facts h).1
      rw [hK d] at hb
      have hlt := rank_busy (hSI d) hb
      exact ⟨hlt.le, fun _ => hlt⟩
    · rw [frame_eq h]
      exact ⟨Or.inr rfl, fun e => by rw [hl] at e; cases e⟩
  obtain ⟨k1, hk1⟩ := lex_stabilizes 11
    (fun d => rank (bctx R drops (run k0).known) (run (k0 + d)))
    (fun _ => rank_length _ _) (fun d => (mono d).1)
  obtain ⟨j, hj, hl⟩ := hcore (k0 + k1) (by omega) (actTrue _ (by omega))
  have hstep : lab j = .step := by
    rcases stepOrFrame j (by omega) with h | h
    · exact h
    · rw [h] at hl
      rcases hl with e | e | e | e | e <;> cases e
  have hlt := (mono (j - k0)).2 (by rw [show k0 + (j - k0) = j by omega]; exact hstep)
  have e1 : rank (bctx R drops (run k0).known) (run (k0 + (j - k0))) =
      rank (bctx R drops (run k0).known) (run (k0 + k1)) := hk1 (j - k0) (by omega)
  have e2 : rank (bctx R drops (run k0).known) (run (k0 + (j - k0 + 1))) =
      rank (bctx R drops (run k0).known) (run (k0 + k1)) := hk1 (j - k0 + 1) (by omega)
  rw [show k0 + (j - k0 + 1) = k0 + (j - k0) + 1 by omega] at e2
  rw [e1, e2] at hlt
  exact lexLt_irrefl _ hlt

/-- After the record cut, before the hub settles, an eligible node comes to have the hub's
records applied and to know a pair from after the cut, and keeps both. Premises: the run's
events from `k0` on, with no failed call (a failure reopens the node, which root's RecordEpoch
shows eventually stops); the state well formed at `k0`; housekeeping that writes (`when_idle`)
eventually stops; the hub's records drop none of the node's op heads (it is eligible: its heads
survive its own drops, which include the records'); a round starts whenever none is running;
and a running round's next step happens, its calls completing. A round is never assumed to
finish. -/
theorem early_entry (R w : Nat) (drops : Nat → Nat → Prop) (run : Nat → NS) (lab : Nat → ELab)
    (k0 : Nat)
    (hev : ∀ i, k0 ≤ i → EEv R w drops (lab i) (run i) (run (i + 1)))
    (h0 : LInv (run k0))
    (hmaint : ∃ kb, ∀ i, kb ≤ i → lab i ≠ .maint)
    (hE : ∀ i, k0 ≤ i → ¬ ∃ y ∈ (run i).heads, drops R y)
    (hstart : ∀ i, k0 ≤ i → (run i).act = false → ∃ j, i ≤ j ∧ lab j = .start)
    (hcore : ∀ i, k0 ≤ i → (run i).act = true → ∃ j, i ≤ j ∧
      (lab j = .step ∨ lab j = .idle ∨ lab j = .poll ∨ lab j = .push ∨ lab j = .maint)) :
    ∃ k, k0 ≤ k ∧ ∀ i, k ≤ i → Entry R w (run i) := by
  obtain ⟨kb, hkb⟩ := hmaint
  have hinv : ∀ d, LInv (run (k0 + d)) := by
    intro d
    induction d with
    | zero => exact h0
    | succ d ih => exact linv_ev ih (hev _ (by omega))
  obtain ⟨k, hk, hent⟩ := early_entry_from R w drops run lab (k0 + kb)
    (fun i hi => hev i (by omega)) (hinv kb) (fun i hi => hkb i (by omega))
    (fun i hi => hE i (by omega)) (fun i hi ha => hstart i (by omega) ha)
    (fun i hi ha => hcore i (by omega) ha)
  exact ⟨k, by omega, hent⟩

end Musubi.EarlyEntry

namespace Musubi.EarlyEntry.Burst

open Musubi NodeSettle

/-- A no-RPC burst keeps one raw known closure. Locality reads those hub names; frontier
ancestry reads the node-space images and heads. The known head and its images are never
identified. Native conformance places both among distinct vertices of one raw DAG. -/
structure State where
  loc : Nat → Bool
  heads : List Nat
  plan : List Nat

def covered (anc : Nat → Nat → Bool) (heads : List Nat) (i : Nat) : Bool :=
  heads.any (anc i)

def rank (rawClosure images : List Nat) (anc : Nat → Nat → Bool) (s : State) : List Nat :=
  [(rawClosure.filter fun x => !s.loc x).length,
    (images.filter fun i => !(covered anc s.heads i)).length, s.heads.length, s.plan.length]

def LocalGrows (L : List Nat) (s t : State) : Prop :=
  ∀ x ∈ L, s.loc x = true → t.loc x = true

/-- The native locality question: there is at least one node-space image, and every
image has a local realization. Raw known names are not replaced by their originals. -/
def localFromImages (images : List Nat) (mapped : Nat → Bool) : Bool :=
  !images.isEmpty && images.all mapped

theorem localFromImages_mono (images : List Nat) {mapped mapped' : Nat → Bool}
    (hm : ∀ x, mapped x = true → mapped' x = true)
    (h : localFromImages images mapped = true) : localFromImages images mapped' = true := by
  simp only [localFromImages, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun x hx => hm x (h.2 x hx)⟩

/-- Partial naming may change when another ancestor body arrives. Finite immutable input
support derives a naming cutoff, without assuming complete metadata or a naming cutoff.
Thereafter append-only local realizations imply the burst's locality-monotonicity law.
`normalize` returns images only for the fixed relevant names; other names may map to []. -/
theorem local_grows_after_inputs {α : Type} (inputs : List Nat)
    (facts : Nat → Nat → Option α)
    (normalize : (Nat → Option α) → Nat → List Nat) (mapped : Nat → Nat → Bool)
    (hkeep : ∀ t x a, facts t x = some a → facts (t + 1) x = some a)
    (hsupport : ∀ f g, (∀ x ∈ inputs, f x = g x) → normalize f = normalize g)
    (hmapped : ∀ t x, mapped t x = true → mapped (t + 1) x = true) :
    ∃ T, ∀ t, T ≤ t → ∀ x,
      localFromImages (normalize (facts t) x) (mapped t) = true →
      localFromImages (normalize (facts (t + 1)) x) (mapped (t + 1)) = true := by
  obtain ⟨T, hT⟩ := PendingEpoch.finite_metadata_output_stabilizes inputs facts normalize
    hkeep hsupport
  refine ⟨T, fun t ht x h => ?_⟩
  have same := (hT (t + 1) (by omega)).trans (hT t ht).symm
  rw [same]
  exact localFromImages_mono _ (hmapped t) h

/-- Native core branches before the next request or idle. A queued entry can already be
local because the adapter realizes batches; dequeuing it still spends plan length. A NEW
survey's first entry was nonlocal when surveyed and becomes local after successful realize.
Merge and advance describe frontier effects, not a promised rank decrease. -/
inductive Step (rawClosure images : List Nat) (anc : Nat → Nat → Bool) :
    State → State → Prop
  | plan {s t : State} (x : Nat) (rest : List Nat) (hp : s.plan = x :: rest)
      (ht : t.plan = rest) (hh : t.heads = s.heads) (hl : LocalGrows rawClosure s t) :
      Step rawClosure images anc s t
  | survey {s t : State} (x : Nat) (hp : s.plan = []) (hx : x ∈ rawClosure)
      (hbefore : s.loc x = false) (hafter : t.loc x = true)
      (hh : t.heads = s.heads) (hl : LocalGrows rawClosure s t) : Step rawClosure images anc s t
  | merge {s t : State} (h : Nat) (h2 : 2 ≤ s.heads.length) (hh : t.heads = [h])
      (ha : ∀ p ∈ s.heads, anc p h = true) (hl : LocalGrows rawClosure s t) :
      Step rawClosure images anc s t
  | advance {s t : State} (h : Nat) (hh : s.heads = [h])
      (hmiss : ∃ i ∈ images, anc i h = false)
      (hcovers : ∀ i ∈ images, covered anc t.heads i = true) (hl : LocalGrows rawClosure s t) :
      Step rawClosure images anc s t

theorem missing_mono {s t : State} (L : List Nat) (hl : LocalGrows L s t) :
    (L.filter fun x => !t.loc x).length ≤ (L.filter fun x => !s.loc x).length := by
  apply PendingEpoch.filter_len_mono
  intro x hxm hx
  cases hs : s.loc x
  · rfl
  · simp [hl x hxm hs] at hx

theorem covered_merge {anc : Nat → Nat → Bool}
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    {s t : State} {h : Nat} (hh : t.heads = [h]) (ha : ∀ p ∈ s.heads, anc p h = true)
    (i : Nat) (hi : covered anc s.heads i = true) : covered anc t.heads i = true := by
  obtain ⟨p, hp, hip⟩ := List.any_eq_true.1 hi
  simpa [covered, hh] using trans i p h hip (ha p hp)

theorem step_rank {rawClosure images : List Nat} {anc : Nat → Nat → Bool}
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    {s t : State} (hs : Step rawClosure images anc s t) :
    LexLt (rank rawClosure images anc t) (rank rawClosure images anc s) := by
  cases hs with
  | plan x rest hp ht hh hl =>
    apply lt_cons (missing_mono rawClosure hl)
    intro _
    apply lt_cons (by simp [hh])
    intro _
    apply lt_cons (by simp [hh])
    intro _
    apply lt_hd
    simp [hp, ht]
  | survey x hp hx hb ha hh hl =>
    apply lt_hd
    apply PendingEpoch.filter_len_lt
    · intro y hym hy
      cases hs : s.loc y
      · rfl
      · simp [hl y hym hs] at hy
    · exact ⟨x, hx, by simp [hb], by simp [ha]⟩
  | merge h h2 hh ha hl =>
    apply lt_cons (missing_mono rawClosure hl)
    intro _
    apply lt_cons
      (PendingEpoch.filter_len_mono images _ _ (fun i _ hi => by
        cases hb : covered anc s.heads i
        · rfl
        · simp [covered_merge trans hh ha i hb] at hi))
    intro _
    apply lt_hd
    simp only [hh, List.length_singleton]
    omega
  | advance h hh hmiss hc hl =>
    apply lt_cons (missing_mono rawClosure hl)
    intro _
    apply lt_hd
    have empty : (images.filter fun i => !(covered anc t.heads i)) = [] := by
      apply List.filter_eq_nil_iff.2
      intro i hi
      simp [hc i hi]
    rw [empty]
    obtain ⟨i, hi, hm⟩ := hmiss
    have present : i ∈ images.filter (fun i => !(covered anc s.heads i)) :=
      List.mem_filter.2 ⟨hi, by simp [covered, hh, hm]⟩
    exact List.length_pos_iff.2 (fun hnil => by rw [hnil] at present; cases present)

/-- Frozen knowledge and finite raw closure cannot support infinitely many own core
branches without another RPC or idle. This prefix argument does not need complete metadata,
an original-label realization trace, or a fair round-completion premise. -/
theorem no_infinite_burst (rawClosure images : List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run : Nat → State)
    (hs : ∀ i, Step rawClosure images anc (run i) (run (i + 1))) : False := by
  have less := fun i => step_rank trans (hs i)
  obtain ⟨k, hk⟩ := lex_stabilizes 4 (fun i => rank rawClosure images anc (run i))
    (fun _ => rfl) (fun i => (less i).le)
  have bad := less k
  rw [hk (k + 1) (by omega)] at bad
  exact lexLt_irrefl _ bad

inductive Kind
  | realize (op : Nat)
  | merge
  | advance

def growsB (L : List Nat) (s t : State) : Bool :=
  L.all fun x => !s.loc x || t.loc x

/-- Executable per-branch contracts, checked against the core's actual before/after
snapshots. These check field effects; `step_rank` derives their decreasing rank. -/
def stepB (rawClosure images : List Nat) (anc : Nat → Nat → Bool)
    (kind : Kind) (s t : State) : Bool :=
  growsB rawClosure s t && match kind with
    | .realize x => decide (t.heads = s.heads) && match s.plan with
      | [] => rawClosure.contains x && !s.loc x && t.loc x
      | y :: rest => decide (x = y) && decide (t.plan = rest)
    | .merge => match t.heads with
      | [h] => decide (2 ≤ s.heads.length) && s.heads.all (fun p => anc p h)
      | _ => false
    | .advance => match s.heads with
      | [h] => images.any (fun i => !anc i h) && images.all (covered anc t.heads)
      | _ => false

theorem growsB_sound {L : List Nat} {s t : State} (h : growsB L s t = true) :
    LocalGrows L s t := by
  intro x hx hl
  have := List.all_eq_true.1 h x hx
  simpa [hl] using this

theorem stepB_sound {rawClosure images : List Nat} {anc : Nat → Nat → Bool}
    {kind : Kind} {s t : State} (h : stepB rawClosure images anc kind s t = true) :
    Step rawClosure images anc s t := by
  simp only [stepB, Bool.and_eq_true] at h
  obtain ⟨hg, hs⟩ := h
  have hl := growsB_sound hg
  cases kind with
  | realize x =>
    simp only [Bool.and_eq_true] at hs
    obtain ⟨hh, hs⟩ := hs
    have hh := of_decide_eq_true hh
    cases hp : s.plan with
    | nil =>
      simp only [hp, Bool.and_eq_true] at hs
      obtain ⟨⟨hx, hb⟩, ha⟩ := hs
      exact .survey x hp (List.contains_iff_mem.1 hx) (by simpa using hb) ha hh hl
    | cons y rest =>
      simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨rfl, ht⟩ := hs
      exact .plan x rest hp ht hh hl
  | merge =>
    cases hh : t.heads with
    | nil => simp [hh] at hs
    | cons x rest =>
      cases rest with
      | nil =>
        simp only [hh, Bool.and_eq_true, decide_eq_true_eq] at hs
        exact .merge x hs.1 hh (List.all_eq_true.1 hs.2) hl
      | cons y rest => simp [hh] at hs
  | advance =>
    cases hh : s.heads with
    | nil => simp [hh] at hs
    | cons x rest =>
      cases rest with
      | nil =>
        simp only [hh, Bool.and_eq_true] at hs
        obtain ⟨i, hi, hm⟩ := List.any_eq_true.1 hs.1
        exact .advance x hh ⟨i, hi, by simpa using hm⟩ (List.all_eq_true.1 hs.2) hl
      | cons y rest => simp [hh] at hs

end Musubi.EarlyEntry.Burst

/-! ## A pending node's raw control after the cuts

After the record and receipt cuts, with the hub's raw head `H` stable, its records current and
the known closure and images fixed, a node with pending drops reaches its pending push
(`pending_push_reached`). Each core step is chosen as `NodeCore::step` chooses it (`choose`),
from what it reads; with nothing announced, records current, drops pending and no concurrent
change of the op head, it never adopts, idles or polls (`choose_guarded`), the one idle a
survey could give being ruled out by NodeSettle's survey completeness, read on the raw survey
graph (`raw_survey_guard`). Every other step lowers one rank: a burst step Burst's, and a call,
with the reply the core waits for, the count of raw operations it lacks or lacks the objects
of (`call_rank`). Raw ids throughout: no original is identified with a raw id. -/

namespace Musubi.EarlyEntry.Control

open Musubi NodeSettle

/-- What a node's control reads after the cuts, raw: the burst's state; which raw operations
it has a body for to realize from (`stg`: staged, or its canonical body; realizing one does not
take it away); and which have their objects here. -/
structure State where
  burst : Burst.State
  stg : Nat → Bool
  obj : Nat → Bool

/-- Nothing in the raw known closure that is local, has a body or has its objects stops being
so. -/
def Grows (raw : List Nat) (s t : State) : Prop :=
  Burst.LocalGrows raw s.burst t.burst ∧ (∀ x ∈ raw, s.stg x = true → t.stg x = true) ∧
    (∀ x ∈ raw, s.obj x = true → t.obj x = true)

/-- The raw operations of the known closure neither local nor with a body. -/
def missOps (raw : List Nat) (s : State) : Nat :=
  (raw.filter fun x => !s.burst.loc x && !s.stg x).length

/-- The raw operations of the known closure not local whose objects are not all here. -/
def missObjs (raw : List Nat) (s : State) : Nat :=
  (raw.filter fun x => !s.burst.loc x && !s.obj x).length

def rank (raw images : List Nat) (anc : Nat → Nat → Bool) (s : State) : List Nat :=
  missOps raw s :: missObjs raw s :: Burst.rank raw images anc s.burst

/-- A core step after the cuts other than the pending push, with the replies to what it
sends: a burst step; a `Fetch` the survey sends for an operation it lacks, whose reply stages
it, or makes it local, as metadata of an alias the node had not seen can; or a `GetObjects`
for an operation whose objects it lacks, whose reply brings them, or makes it local. A call
changes neither the op heads nor the plan; what is local may grow. -/
inductive Call (raw images : List Nat) (anc : Nat → Nat → Bool) : State → State → Prop
  | burst {s t : State} (h : Burst.Step raw images anc s.burst t.burst) (hg : Grows raw s t) :
      Call raw images anc s t
  | fetch {s t : State} (x : Nat) (hx : x ∈ raw) (hl : s.burst.loc x = false)
      (hs : s.stg x = false) (ht : t.stg x = true ∨ t.burst.loc x = true)
      (hh : t.burst.heads = s.burst.heads) (hp : t.burst.plan = s.burst.plan)
      (hg : Grows raw s t) : Call raw images anc s t
  | objects {s t : State} (x : Nat) (hx : x ∈ raw) (hl : s.burst.loc x = false)
      (ho : s.obj x = false) (ht : t.obj x = true ∨ t.burst.loc x = true)
      (hh : t.burst.heads = s.burst.heads) (hp : t.burst.plan = s.burst.plan)
      (hg : Grows raw s t) : Call raw images anc s t

theorem false_of_grows {a b : Bool} (h : a = true → b = true) (hb : b = false) : a = false := by
  cases a
  · rfl
  · rw [h rfl] at hb; cases hb

theorem missOps_mono {raw : List Nat} {s t : State} (hg : Grows raw s t) :
    missOps raw t ≤ missOps raw s := by
  apply PendingEpoch.filter_len_mono
  intro x hx h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
  exact ⟨false_of_grows (hg.1 x hx) h.1, false_of_grows (hg.2.1 x hx) h.2⟩

theorem missObjs_mono {raw : List Nat} {s t : State} (hg : Grows raw s t) :
    missObjs raw t ≤ missObjs raw s := by
  apply PendingEpoch.filter_len_mono
  intro x hx h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
  exact ⟨false_of_grows (hg.1 x hx) h.1, false_of_grows (hg.2.2 x hx) h.2⟩

theorem call_rank {raw images : List Nat} {anc : Nat → Nat → Bool}
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    {s t : State} (h : Call raw images anc s t) :
    LexLt (rank raw images anc t) (rank raw images anc s) := by
  cases h with
  | burst h hg =>
    exact lt_cons (missOps_mono hg) fun _ =>
      lt_cons (missObjs_mono hg) fun _ => Burst.step_rank trans h
  | fetch x hx hl hs ht hh hp hg =>
    apply lt_hd
    apply PendingEpoch.filter_len_lt
    · intro y hy h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
      exact ⟨false_of_grows (hg.1 y hy) h.1, false_of_grows (hg.2.1 y hy) h.2⟩
    · refine ⟨x, hx, by simp [hl, hs], ?_⟩
      rcases ht with ht | ht <;> simp [ht]
  | objects x hx hl ho ht hh hp hg =>
    apply lt_cons (missOps_mono hg)
    intro _
    apply lt_hd
    apply PendingEpoch.filter_len_lt
    · intro y hy h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
      exact ⟨false_of_grows (hg.1 y hy) h.1, false_of_grows (hg.2.2 y hy) h.2⟩
    · refine ⟨x, hx, by simp [hl, ho], ?_⟩
      rcases ht with ht | ht <;> simp [ht]

/-- No run of such calls goes on forever. -/
theorem no_infinite_calls (raw images : List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run : Nat → State) (hs : ∀ i, Call raw images anc (run i) (run (i + 1))) : False := by
  have less := fun i => call_rank trans (hs i)
  obtain ⟨k, hk⟩ := lex_stabilizes 6 (fun i => rank raw images anc (run i))
    (fun _ => rfl) (fun i => (less i).le)
  have bad := less k
  rw [hk (k + 1) (by omega)] at bad
  exact lexLt_irrefl _ bad

theorem lexLt_trans : ∀ {x y z : List Nat}, LexLt x y → LexLt y z → LexLt x z
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (Nat.lt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexLt_trans h1 h2⟩
  | [], _, _, h1, _ => by simp [LexLt] at h1
  | _ :: _, [], _, h1, _ => by simp [LexLt] at h1
  | _ :: _, _ :: _, [], _, h2 => by simp [LexLt] at h2

theorem lexLt_of_le_lt {x y z : List Nat} (h1 : LexLe x y) (h2 : LexLt y z) : LexLt x z := by
  rcases h1 with h | rfl
  · exact lexLt_trans h h2
  · exact h2

/-- What may happen to a node's control state between its step's calls completing and its next
step's reading, after that step's prelude, in the same round, with no automatic write of the node
(the prelude's own writers, `before_sync`'s `reconcile_settings` and `show_other_workspaces`, a
`jj op abandon` passed on, are such, and the frame is asked only past their cut, `QuietAt`):
nothing in the raw closure stops being local, having a body or its objects (the prelude's
`prepare_records` writes rewrites beside what is there; nothing is removed), and the CANONICAL op
heads and the plan the core reads are the same. The prelude may move the physical heads
(`canonical_heads`, `check_abandon` and `realign_heads`, `reparent_late`), but their canonical
readings, under naming that does not change and once any recovery's own prelude has completed
before the readings, are unchanged (that completion, not entry: `fresh_head_reached` uses frames
before entry is derived, so entry is no premise of a frame); notices are handled between rounds
and user work is past. Locality is read through naming, which may change, so a frame is asked only
across steps naming does not change across (`Naming.Still`). -/
def Frame (raw : List Nat) (s t : State) : Prop :=
  Grows raw s t ∧ t.burst.heads = s.burst.heads ∧ t.burst.plan = s.burst.plan

/-- A frame never raises the control rank. -/
theorem frame_rank {raw images : List Nat} {anc : Nat → Nat → Bool} {s t : State}
    (h : Frame raw s t) : LexLe (rank raw images anc t) (rank raw images anc s) := by
  obtain ⟨hg, hh, hp⟩ := h
  refine le_cons (missOps_mono hg) fun _ => le_cons (missObjs_mono hg) fun _ =>
    le_cons (Burst.missing_mono raw hg.1) fun _ => ?_
  right
  simp only [hh, hp]

/-- No run of such calls, each followed by a frame, goes on forever. -/
theorem no_infinite_framed (raw images : List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run after : Nat → State) (hs : ∀ i, Call raw images anc (run i) (after i))
    (hf : ∀ i, Frame raw (after i) (run (i + 1))) : False := by
  have less : ∀ i, LexLt (rank raw images anc (run (i + 1))) (rank raw images anc (run i)) :=
    fun i => lexLt_of_le_lt (frame_rank (hf i)) (call_rank trans (hs i))
  obtain ⟨k, hk⟩ := lex_stabilizes 6 (fun i => rank raw images anc (run i))
    (fun _ => rfl) (fun i => (less i).le)
  have bad := less k
  rw [hk (k + 1) (by omega)] at bad
  exact lexLt_irrefl _ bad

/-! ### The core's choice -/

/-- What `NodeCore::step` reads to choose: records announced and not taken; whether taking
them drops an op head (`prepare_records`); two op heads or more; whether the known head is
local; a plan left; the survey's plan, missing operations and missing objects; whether an op
head descends from the known one; whether its records differ from the hub's as heard; pending
drops; the op head the known one; and the fix-up's new head the known one. -/
structure Reads where
  announced : Bool
  dropHead : Bool
  heads2 : Bool
  knownLocal : Bool
  planNe : Bool
  ready : Bool
  missOps : Bool
  missObjs : Bool
  descends : Bool
  differ : Bool
  pending : Bool
  headIsKnown : Bool
  newIsKnown : Bool

inductive Choice
  | adopt
  | merge
  | realize
  | fetch
  | objects
  | idle
  | advance
  | poll
  | push
  deriving DecidableEq

/-- `NodeCore::step`'s choice, in its order. A survey that finds an operation missing fetches,
with a `GetObjects` beside if objects are missing too; one finding only objects missing asks
for them. -/
def choose (r : Reads) : Choice :=
  if r.announced && !r.dropHead then .adopt
  else if r.heads2 then .merge
  else if !r.knownLocal then
    if r.planNe || r.ready then .realize
    else if r.missOps then .fetch
    else if r.missObjs then .objects
    else .idle
  else if r.dropHead || !r.descends then .advance
  else if r.differ then (if r.announced then .idle else .poll)
  else if !r.pending then (if r.headIsKnown then .idle else .push)
  else if r.newIsKnown then .poll
  else .push

/-- With nothing announced, records current, drops pending and the fix-up's head another
than the known one, and a survey that, finding nothing ready, finds something missing, the
core never adopts, idles or polls. -/
theorem choose_guarded {r : Reads} (ha : r.announced = false) (hdh : r.dropHead = false)
    (hd : r.differ = false) (hp : r.pending = true) (hn : r.newIsKnown = false)
    (hs : r.knownLocal = false → r.ready = false → r.missOps = true ∨ r.missObjs = true) :
    choose r = .merge ∨ choose r = .realize ∨ choose r = .fetch ∨ choose r = .objects ∨
      choose r = .advance ∨ choose r = .push := by
  obtain ⟨a, dh, h2, kl, pln, rd, mo, mb, de, di, pe, hk, nk⟩ := r
  simp only at ha hdh hd hp hn hs
  subst ha hdh hd hp hn
  cases h2 <;> cases kl <;> cases pln <;> cases rd <;> cases mo <;> cases mb <;> cases de <;>
    simp_all [choose]

/-- The core pushes only with one op head, the known head local and an op head descending
from it. -/
theorem choose_push {r : Reads} (h : choose r = .push) :
    r.descends = true ∧ r.knownLocal = true ∧ r.heads2 = false := by
  unfold choose at h
  split at h
  · cases h
  rename_i _
  split at h
  · cases h
  rename_i h2
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h <;> cases h
  rename_i kl
  split at h
  · cases h
  rename_i de
  refine ⟨?_, ?_, ?_⟩
  · cases hd : r.descends <;> simp_all
  · cases hk : r.knownLocal <;> simp_all
  · cases hh : r.heads2 <;> simp_all

/-- The survey's guard, from NodeSettle's survey completeness read on the raw survey graph:
the raw parents, and native locality, staging and objects of raw ids, from the known raw head.
Given that the native survey finds exactly what NodeSettle's walk does there, a known head that
is not local has something ready or something missing. -/
def rawSurvey (base : NS) (par : Nat → List Nat) (loc stg obj : Nat → Bool) (H : Nat) : NS :=
  { base with
    par := par
    loc := fun x => loc x = true
    stg := fun x => stg x = true
    obj := fun x => obj x = true
    known := (base.known.1, H) }

theorem raw_survey_guard {base : NS} {par : Nat → List Nat} {loc stg obj : Nat → Bool}
    {H : Nat} {r : Reads} (hlt : ParLt par) (hloc : r.knownLocal = loc H)
    (hready : r.ready = true ↔ ∃ x, Ready (rawSurvey base par loc stg obj H) x)
    (hops : r.missOps = true ↔ MissOps (rawSurvey base par loc stg obj H))
    (hobjs : r.missObjs = true ↔ MissObjs (rawSurvey base par loc stg obj H)) :
    r.knownLocal = false → r.ready = false → r.missOps = true ∨ r.missObjs = true := by
  intro hk hr
  have hl : ¬ (rawSurvey base par loc stg obj H).loc (rawSurvey base par loc stg obj H).known.2 :=
    by
      change ¬ loc H = true
      rw [← hloc, hk]
      exact Bool.false_ne_true
  rcases survey_complete hlt hl with h | h | h
  · rw [← hready, hr] at h; cases h
  · exact Or.inl (hops.2 h)
  · exact Or.inr (hobjs.2 h)

/-- A `Fetch` sent for a missing operation is such a call: the walk stays in the raw known
closure, and the reply about the stable head stages every operation of it not local, or makes
it local. -/
theorem fetch_call {raw images : List Nat} {anc : Nat → Nat → Bool} {base : NS}
    {par : Nat → List Nat} {H : Nat} {s t : State}
    (hm : MissOps (rawSurvey base par s.burst.loc s.stg s.obj H))
    (hwalk : ∀ x, Walk (rawSurvey base par s.burst.loc s.stg s.obj H) x → x ∈ raw)
    (hstage : ∀ x ∈ raw, s.burst.loc x = false → t.stg x = true ∨ t.burst.loc x = true)
    (hh : t.burst.heads = s.burst.heads) (hp : t.burst.plan = s.burst.plan)
    (hg : Grows raw s t) : Call raw images anc s t := by
  obtain ⟨x, hw, hl, hs⟩ := hm
  have hx := hwalk x hw
  exact .fetch x hx (by simpa [rawSurvey] using hl) (by simpa [rawSurvey] using hs)
    (hstage x hx (by simpa [rawSurvey] using hl)) hh hp hg

/-- A `GetObjects` for the operations whose objects are missing is such a call: its reply
brings them, or makes the operation local. -/
theorem objects_call {raw images : List Nat} {anc : Nat → Nat → Bool} {base : NS}
    {par : Nat → List Nat} {H : Nat} {s t : State}
    (hm : MissObjs (rawSurvey base par s.burst.loc s.stg s.obj H))
    (hwalk : ∀ x, Walk (rawSurvey base par s.burst.loc s.stg s.obj H) x → x ∈ raw)
    (hbring : ∀ x, Walk (rawSurvey base par s.burst.loc s.stg s.obj H) x →
      s.burst.loc x = false → s.stg x = true → s.obj x = false →
        t.obj x = true ∨ t.burst.loc x = true)
    (hh : t.burst.heads = s.burst.heads) (hp : t.burst.plan = s.burst.plan)
    (hg : Grows raw s t) : Call raw images anc s t := by
  obtain ⟨x, hw, hl, hs, ho⟩ := hm
  have hl' : s.burst.loc x = false := by simpa [rawSurvey] using hl
  have ho' : s.obj x = false := by simpa [rawSurvey] using ho
  exact .objects x (hwalk x hw) hl' ho'
    (hbring x hw hl' (by simpa [rawSurvey] using hs) ho') hh hp hg

/-- A node with pending drops, after the cuts, reaches its pending push: given at each core
step the guards `choose_guarded` takes, and the effect of the step it chooses (a burst step,
or a call with its reply), it pushes at some step. No step is assumed to push. -/
theorem pending_push_reached (raw images : List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run after : Nat → State) (reads : Nat → Reads)
    (hframe : ∀ i, Frame raw (after i) (run (i + 1)))
    (hguard : ∀ i, (reads i).announced = false ∧ (reads i).dropHead = false ∧
      (reads i).differ = false ∧ (reads i).pending = true ∧ (reads i).newIsKnown = false)
    (hsurvey : ∀ i, (reads i).knownLocal = false → (reads i).ready = false →
      (reads i).missOps = true ∨ (reads i).missObjs = true)
    (hburst : ∀ i, (choose (reads i) = .merge ∨ choose (reads i) = .realize ∨
      choose (reads i) = .advance) →
      Burst.Step raw images anc (run i).burst (after i).burst ∧ Grows raw (run i) (after i))
    (hcall : ∀ i, (choose (reads i) = .fetch ∨ choose (reads i) = .objects) →
      Call raw images anc (run i) (after i)) :
    ∃ i, choose (reads i) = .push := by
  apply Classical.byContradiction
  intro hno
  apply no_infinite_framed raw images anc trans run after _ hframe
  intro i
  obtain ⟨ha, hdh, hd, hp, hn⟩ := hguard i
  rcases choose_guarded ha hdh hd hp hn (hsurvey i) with h | h | h | h | h | h
  · obtain ⟨hs, hg⟩ := hburst i (Or.inl h); exact .burst hs hg
  · obtain ⟨hs, hg⟩ := hburst i (Or.inr (Or.inl h)); exact .burst hs hg
  · exact hcall i (Or.inl h)
  · exact hcall i (Or.inr h)
  · obtain ⟨hs, hg⟩ := hburst i (Or.inr (Or.inr h)); exact .burst hs hg
  · exact absurd ⟨i, h⟩ hno

/-! ### The survey and the choice, computed on the raw graph

What the survey finds is computed from the raw graph and the native bits alone, over the raw
known closure: the walk is ancestry through the parents of operations neither local nor
without a body (`walk_iff`), so `Exec.ancB` decides it, and readiness and what is missing are
found among the closure's operations (`readyB_iff`, `missOpsB_iff`, `missObjsB_iff`). So the
survey's guard is derived (`rawReads_survey`), not assumed, and `rawControl` computes the core's
choice from a state before a step and the primitive bits the native core reports, never from
the choice it made. `callB` checks a call's effect, soundly (`callB_sound`). -/

/-- The parents the survey walks through: an operation's own, if it is neither local nor
without a body; none otherwise. -/
def walkParents (par : Nat → List Nat) (loc stg : Nat → Bool) (x : Nat) : List Nat :=
  if (!loc x && stg x) = true then par x else []

theorem parLt_walkParents {par : Nat → List Nat} {loc stg : Nat → Bool} (hlt : ParLt par) :
    ParLt (walkParents par loc stg) := by
  intro y p hp
  unfold walkParents at hp
  split at hp
  · exact hlt y p hp
  · cases hp

theorem mem_walkParents {par : Nat → List Nat} {loc stg : Nat → Bool} {x p : Nat} :
    p ∈ walkParents par loc stg x ↔ loc x = false ∧ stg x = true ∧ p ∈ par x := by
  unfold walkParents
  split <;> rename_i h <;> simp_all

/-- NodeSettle's walk on the raw survey graph is ancestry through the walked parents. -/
theorem walk_iff {base : NS} {par : Nat → List Nat} {loc stg obj : Nat → Bool} {H x : Nat} :
    Walk (rawSurvey base par loc stg obj H) x ↔ Anc (walkParents par loc stg) x H := by
  constructor
  · intro h
    induction h with
    | top => exact Anc.refl
    | up _ hl hs hp ih =>
      refine (Anc.parent (mem_walkParents.2 ⟨?_, hs, hp⟩)).trans ih
      simpa [rawSurvey] using hl
  · intro h
    have key : ∀ y, Anc (walkParents par loc stg) x y →
        Walk (rawSurvey base par loc stg obj H) y →
          Walk (rawSurvey base par loc stg obj H) x := by
      intro y hxy
      induction hxy with
      | refl => exact id
      | step hp _ ih =>
        intro hy
        obtain ⟨hl, hs, hp⟩ := mem_walkParents.1 hp
        exact ih (Walk.up hy (by simp [rawSurvey, hl]) hs hp)
    exact key H h Walk.top

/-- The walk, decided. -/
def walkB (par : Nat → List Nat) (loc stg : Nat → Bool) (H x : Nat) : Bool :=
  Exec.ancB (walkParents par loc stg) x H

theorem walkB_iff {base : NS} {par : Nat → List Nat} {loc stg obj : Nat → Bool} {H x : Nat}
    (hlt : ParLt par) :
    walkB par loc stg H x = true ↔ Walk (rawSurvey base par loc stg obj H) x := by
  rw [walkB, Exec.ancB_iff (parLt_walkParents hlt), walk_iff]

/-- Something the survey can realize now, among the raw known closure `raw`. -/
def readyB (raw : List Nat) (par : Nat → List Nat) (loc stg obj : Nat → Bool) (H : Nat) :
    Bool :=
  raw.any fun x => walkB par loc stg H x && !loc x && stg x && obj x && (par x).all loc

/-- Something the survey reaches that has no body. -/
def missOpsB (raw : List Nat) (par : Nat → List Nat) (loc stg : Nat → Bool) (H : Nat) : Bool :=
  raw.any fun x => walkB par loc stg H x && !loc x && !stg x

/-- Something the survey reaches with a body whose objects are not all here. -/
def missObjsB (raw : List Nat) (par : Nat → List Nat) (loc stg obj : Nat → Bool) (H : Nat) :
    Bool :=
  raw.any fun x => walkB par loc stg H x && !loc x && stg x && !obj x

theorem walk_mem {base : NS} {par : Nat → List Nat} {loc stg obj : Nat → Bool} {H x : Nat}
    {raw : List Nat} (hraw : ∀ x, Anc par x H → x ∈ raw)
    (hw : Walk (rawSurvey base par loc stg obj H) x) : x ∈ raw :=
  hraw x hw.anc

theorem readyB_iff {base : NS} {raw : List Nat} {par : Nat → List Nat}
    {loc stg obj : Nat → Bool} {H : Nat} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) :
    readyB raw par loc stg obj H = true ↔ ∃ x, Ready (rawSurvey base par loc stg obj H) x := by
  unfold readyB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, -, h⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨hw, hl⟩, hs⟩, ho⟩, hp⟩ := h
    exact ⟨x, (walkB_iff hlt).1 hw, by simp [rawSurvey, hl], hs, ho, hp⟩
  · rintro ⟨x, hw, hl, hs, ho, hp⟩
    refine ⟨x, walk_mem hraw hw, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true]
    exact ⟨⟨⟨⟨(walkB_iff hlt).2 hw, by simpa [rawSurvey] using hl⟩, hs⟩, ho⟩, hp⟩

theorem missOpsB_iff {base : NS} {raw : List Nat} {par : Nat → List Nat}
    {loc stg obj : Nat → Bool} {H : Nat} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) :
    missOpsB raw par loc stg H = true ↔ MissOps (rawSurvey base par loc stg obj H) := by
  unfold missOpsB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, -, h⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨hw, hl⟩, hs⟩ := h
    exact ⟨x, (walkB_iff hlt).1 hw, by simp [rawSurvey, hl], by simp [rawSurvey, hs]⟩
  · rintro ⟨x, hw, hl, hs⟩
    refine ⟨x, walk_mem hraw hw, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨⟨(walkB_iff hlt).2 hw, by simpa [rawSurvey] using hl⟩,
      by simpa [rawSurvey] using hs⟩

theorem missObjsB_iff {base : NS} {raw : List Nat} {par : Nat → List Nat}
    {loc stg obj : Nat → Bool} {H : Nat} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) :
    missObjsB raw par loc stg obj H = true ↔ MissObjs (rawSurvey base par loc stg obj H) := by
  unfold missObjsB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, -, h⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨⟨hw, hl⟩, hs⟩, ho⟩ := h
    exact ⟨x, (walkB_iff hlt).1 hw, by simp [rawSurvey, hl], hs, by simp [rawSurvey, ho]⟩
  · rintro ⟨x, hw, hl, hs, ho⟩
    refine ⟨x, walk_mem hraw hw, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨⟨⟨(walkB_iff hlt).2 hw, by simpa [rawSurvey] using hl⟩, hs⟩,
      by simpa [rawSurvey] using ho⟩

/-- The primitive bits the native core reports at a step: records announced and not taken,
whether taking them drops an op head, whether its records differ from the hub's as heard,
pending drops, the op head the known one, and the fix-up's new head the known one. -/
structure Prims where
  announced : Bool
  dropHead : Bool
  differ : Bool
  pending : Bool
  headIsKnown : Bool
  newIsKnown : Bool

/-- What the core reads at a step, computed from the state before it: the survey on the raw
graph `par` from the known raw head `H`, over the raw known closure `raw`; whether an op head
descends from the known head (it has node-space images, and every one is below the head, in
`anc`: no images, none descends); and the primitive bits. -/
def rawReads (raw images : List Nat) (par : Nat → List Nat) (anc : Nat → Nat → Bool)
    (H : Nat) (s : State) (q : Prims) : Reads where
  announced := q.announced
  dropHead := q.dropHead
  heads2 := decide (2 ≤ s.burst.heads.length)
  knownLocal := s.burst.loc H
  planNe := !s.burst.plan.isEmpty
  ready := readyB raw par s.burst.loc s.stg s.obj H
  missOps := missOpsB raw par s.burst.loc s.stg H
  missObjs := missObjsB raw par s.burst.loc s.stg s.obj H
  descends := !images.isEmpty && s.burst.heads.any fun h => images.all fun i => anc i h
  differ := q.differ
  pending := q.pending
  headIsKnown := q.headIsKnown
  newIsKnown := q.newIsKnown

/-- The core's choice at a step, computed. -/
def rawControl (raw images : List Nat) (par : Nat → List Nat) (anc : Nat → Nat → Bool)
    (H : Nat) (s : State) (q : Prims) : Choice :=
  choose (rawReads raw images par anc H s q)

/-- A core state to read the raw survey graph into: `rawSurvey` replaces all that the survey
reads. -/
def surveyBase : NS :=
  ⟨(0, 0), [], none, none, 0, [], false, [], [], fun _ => [], 0, fun _ => False,
    fun _ => False, fun _ => False, false⟩

/-- The survey's guard, derived: on the raw graph, with the closure holding the known head's
ancestry, a known head that is not local has something ready or something missing. -/
theorem rawReads_survey {raw images : List Nat} {par : Nat → List Nat}
    {anc : Nat → Nat → Bool} {H : Nat} {s : State} {q : Prims} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) :
    (rawReads raw images par anc H s q).knownLocal = false →
      (rawReads raw images par anc H s q).ready = false →
      (rawReads raw images par anc H s q).missOps = true ∨
        (rawReads raw images par anc H s q).missObjs = true :=
  raw_survey_guard (base := surveyBase) (par := par) (loc := s.burst.loc) (stg := s.stg)
    (obj := s.obj) (H := H) hlt rfl
    (readyB_iff hlt hraw) (missOpsB_iff hlt hraw) (missObjsB_iff hlt hraw)

/-- With the primitive guards, the computed choice is a burst step, a call or the push. -/
theorem rawControl_guarded {raw images : List Nat} {par : Nat → List Nat}
    {anc : Nat → Nat → Bool} {H : Nat} {s : State} {q : Prims} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) (ha : q.announced = false) (hdh : q.dropHead = false)
    (hd : q.differ = false) (hp : q.pending = true) (hn : q.newIsKnown = false) :
    let c := rawControl raw images par anc H s q
    c = .merge ∨ c = .realize ∨ c = .fetch ∨ c = .objects ∨ c = .advance ∨ c = .push :=
  choose_guarded ha hdh hd hp hn (rawReads_survey hlt hraw)

/-! ### A call's effect, checked -/

/-- What a step was, as the native core reports it. -/
inductive CallKind
  | burst (k : Burst.Kind)
  | fetch
  | objects

def growsB (raw : List Nat) (s t : State) : Bool :=
  Burst.growsB raw s.burst t.burst && raw.all (fun x => !s.stg x || t.stg x) &&
    raw.all (fun x => !s.obj x || t.obj x)

/-- A step's effect, checked against its states before and after: a burst step Burst's; a
`Fetch` that brings a body, or locality, to an operation of the closure that had neither; a
`GetObjects` that brings the objects, or locality, of one that lacked them; neither call
moving the op heads or the plan, and nothing lost. -/
def callB (raw images : List Nat) (anc : Nat → Nat → Bool) (kind : CallKind) (s t : State) :
    Bool :=
  growsB raw s t && match kind with
    | .burst k => Burst.stepB raw images anc k s.burst t.burst
    | .fetch => decide (t.burst.heads = s.burst.heads) && decide (t.burst.plan = s.burst.plan) &&
        raw.any fun x => !s.burst.loc x && !s.stg x && (t.stg x || t.burst.loc x)
    | .objects => decide (t.burst.heads = s.burst.heads) &&
        decide (t.burst.plan = s.burst.plan) &&
        raw.any fun x => !s.burst.loc x && !s.obj x && (t.obj x || t.burst.loc x)

theorem growsB_sound {raw : List Nat} {s t : State} (h : growsB raw s t = true) :
    Grows raw s t := by
  simp only [growsB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hl, hs⟩, ho⟩ := h
  refine ⟨Burst.growsB_sound hl, fun x hx h => ?_, fun x hx h => ?_⟩
  · simpa [h] using hs x hx
  · simpa [h] using ho x hx

theorem callB_sound {raw images : List Nat} {anc : Nat → Nat → Bool} {kind : CallKind}
    {s t : State} (h : callB raw images anc kind s t = true) : Call raw images anc s t := by
  simp only [callB, Bool.and_eq_true] at h
  obtain ⟨hg, hk⟩ := h
  have hg := growsB_sound hg
  cases kind with
  | burst k => exact .burst (Burst.stepB_sound hk) hg
  | fetch =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hk
    obtain ⟨⟨hh, hp⟩, x, hx, hb⟩ := hk
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true] at hb
    obtain ⟨⟨hl, hs⟩, ht⟩ := hb
    exact .fetch x hx hl hs ht hh hp hg
  | objects =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hk
    obtain ⟨⟨hh, hp⟩, x, hx, hb⟩ := hk
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true] at hb
    obtain ⟨⟨hl, ho⟩, ht⟩ := hb
    exact .objects x hx hl ho ht hh hp hg

/-- Before a first fresh observation, even an eligible node can know an old raw head whose
node-space images differ. Its raw local burst still reaches an RPC or idle, without a
single embedding, current records, or a stable hub. `run` samples its successive scheduled
core steps during one frozen-known round. The finite record-disturbance cut excludes adoption
and prepared record-taking advances; local steps supply their checked raw field effects.
Idle ends the round, whose next start fetches; fairness of that start and of its call is a
separate driver obligation, not an assumed completed round here. -/
theorem raw_round_yields (raw images : List Nat) (par : Nat → List Nat)
    (anc : Nat → Nat → Bool) (H : Nat)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run : Nat → State) (prims : Nat → Prims)
    (hrecord : ∀ i, rawControl raw images par anc H (run i) (prims i) ≠ .adopt ∧
      (rawControl raw images par anc H (run i) (prims i) = .advance →
        (prims i).dropHead = false))
    (hburst : ∀ i, (rawControl raw images par anc H (run i) (prims i) = .merge ∨
        rawControl raw images par anc H (run i) (prims i) = .realize ∨
        (rawControl raw images par anc H (run i) (prims i) = .advance ∧
          (prims i).dropHead = false)) →
      ∃ k, Burst.stepB raw images anc k (run i).burst (run (i + 1)).burst = true) :
    ∃ i, let c := rawControl raw images par anc H (run i) (prims i)
      c = .fetch ∨ c = .objects ∨ c = .idle ∨ c = .poll ∨ c = .push := by
  apply Classical.byContradiction
  intro hno
  apply Burst.no_infinite_burst raw images anc trans (fun i => (run i).burst)
  intro i
  have hb : rawControl raw images par anc H (run i) (prims i) = .merge ∨
      rawControl raw images par anc H (run i) (prims i) = .realize ∨
      (rawControl raw images par anc H (run i) (prims i) = .advance ∧
        (prims i).dropHead = false) := by
    cases hc : rawControl raw images par anc H (run i) (prims i) with
    | adopt => exact False.elim ((hrecord i).1 hc)
    | merge => exact Or.inl rfl
    | realize => exact Or.inr (Or.inl rfl)
    | advance => exact Or.inr (Or.inr ⟨rfl, (hrecord i).2 hc⟩)
    | fetch | objects | idle | poll | push =>
      exact False.elim (hno ⟨i, by simp [hc]⟩)
  obtain ⟨k, hk⟩ := hburst i hb
  exact Burst.stepB_sound hk

/-! ### Naming, settling inside a frozen round

The core reads its known head's node-space images, and which raw operations are local, through
its naming (`to_node`), which changes as metadata arrives and as pending names normalize, past
the record cut too: no images are fixed for good. But with the known head fixed, naming reads
the metadata of finitely many raw operations only, the head's raw closure and the pending
names (with what a preparation of the announced records may make pending), which only
arrives, and which names are pending, which, past the one preparation from scratch, are renamed
against that one head at most once per original. So inside any round that goes on forever with
its known head fixed, naming settles (`Naming.settles`), at a step derived there, not
assumed. -/

/-- What the core's naming reads at its successive steps, each read after the step's prelude:
the metadata it holds of each raw operation (`facts`), and the raw names its naming takes as
pending drops (`names`: the operands `to_node` reads, a preparation's `Taking.pending`
included), with every raw operation's original (`orig`); the known head's node-space images then
(`images`, the native `to_node` of the known head); the finite raw operations whose metadata
the naming reads (`inputs`); whether, between a step's reading and the next step's, the
announced records are prepared again from scratch (`prep`: `prepare_again_if_moved` does so
whenever the op heads moved, as the core's own merge moves them); and whether the step's reading
has two op heads or more (`multi`). -/
structure Naming (α : Type) where
  inputs : List Nat
  facts : Nat → Nat → Option α
  names : Nat → List Nat
  orig : Nat → Nat
  images : Nat → List Nat
  prep : Nat → Prop
  multi : Nat → Bool

namespace Naming

variable {α : Type} (N : Naming α)

/-- Nothing naming reads changes across step `i`. -/
def Still (i : Nat) : Prop :=
  (∀ x ∈ N.inputs, N.facts (i + 1) x = N.facts i x) ∧ ∀ x, x ∈ N.names (i + 1) ↔ x ∈ N.names i

/-- Naming's native laws over the steps `P` holds of, the known raw head `H` fixed: metadata only
arrives; at two of those steps that agree on the metadata of `inputs` and on which names are
pending, the images agree (the naming's actual dependence, on the actual metadata); the known
head's raw closure holds one version of each original (the hub refuses a push that repeats one);
from a step to the next, both of them `P`'s, with no preparation from scratch between, the
pending names are renamed only to the version of their original below the known head, if it has
one, or leave (`PendingEpoch.PStep`, `name_pending_as`): the announcement being the same
throughout, its first preparation is in the first reading already; a step from one op head or
none leaves one or none (realizing is detached, calls do not move the op heads, an ordinary
advance leaves one, a taking advance and user work are excluded); and a preparation from scratch
comes only where the op heads moved, which, the announcement standing, only the core's merge of
two op heads or more does, leaving one. So such preparations come once at most
(`Naming.settles`), not assumed. -/
structure Laws (N : Naming α) (par : Nat → List Nat) (H : Nat) (P : Nat → Prop) : Prop where
  keep : ∀ i, P i → ∀ x a, N.facts i x = some a → N.facts (i + 1) x = some a
  support : ∀ i j, P i → P j → (∀ x ∈ N.inputs, N.facts i x = N.facts j x) →
    (∀ x, x ∈ N.names i ↔ x ∈ N.names j) → N.images i = N.images j
  unique : ∀ x y, Anc par x H → Anc par y H → N.orig x = N.orig y → x = y
  rename : ∀ i, P i → P (i + 1) → ¬ N.prep i →
    PendingEpoch.PStep par (fun _ => H) N.orig 0 (N.names i) (N.names (i + 1))
  single : ∀ i, P i → P (i + 1) → N.multi i = false → N.multi (i + 1) = false
  prepMerge : ∀ i, P i → P (i + 1) → N.prep i → N.multi i = true ∧ N.multi (i + 1) = false

variable {N}

theorem names_below {T : Nat} (hleave : ∀ i, T ≤ i → ∀ x ∈ N.names (i + 1), x ∈ N.names i) :
    ∀ d, ∀ x ∈ N.names (T + d), x ∈ N.names T
  | 0 => fun _ h => h
  | d + 1 => fun x h => names_below hleave d x (hleave (T + d) (by omega) x h)

/-- Inside a round that goes on forever, its known head fixed, naming settles: past some step,
nothing it reads changes, so neither do the images. Derived from the pointwise laws: past the
one preparation from scratch, if any, renaming against the one known head stops
(`PendingEpoch.pending_names_settle`), then the names only leave, and metadata stops arriving for
the finite inputs (`PendingEpoch.finite_metadata_stabilizes`). No cutoff is assumed. -/
theorem settles {par : Nat → List Nat} {H : Nat} {P : Nat → Prop} (L : N.Laws par H P)
    (hP : ∀ i, P i) :
    ∃ T, ∀ i, T ≤ i → N.Still i ∧ N.images i = N.images T := by
  -- past the preparation from scratch, if any, one op head or none stays so, and none comes
  have hS : ∃ S0, ∀ i, S0 ≤ i → ¬ N.prep i := by
    by_cases h : ∃ i, N.prep i
    · obtain ⟨i0, h0⟩ := h
      have hone : ∀ d, N.multi (i0 + 1 + d) = false := by
        intro d
        induction d with
        | zero => exact (L.prepMerge i0 (hP _) (hP _) h0).2
        | succ d ih => exact L.single _ (hP _) (hP _) ih
      refine ⟨i0 + 1, fun i hi hp => ?_⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
      have := (L.prepMerge _ (hP _) (hP _) hp).1
      rw [hone d] at this
      cases this
    · exact ⟨0, fun i _ hp => h ⟨i, hp⟩⟩
  obtain ⟨S0, hS0⟩ := hS
  obtain ⟨T0', hleave'⟩ := PendingEpoch.pending_names_settle
    (hist := fun _ => H) (w := 0) ⟨fun _ _ _ _ => Anc.refl, fun _ _ => L.unique⟩
    (fun t => N.names (S0 + t)) (fun _ => 0) (fun _ => Nat.le_refl 0)
    (fun t => L.rename (S0 + t) (hP _) (hP _) (hS0 _ (by omega)))
  let T0 := S0 + T0'
  have hleave : ∀ i, T0 ≤ i → ∀ x ∈ N.names (i + 1), x ∈ N.names i := by
    intro i hi x hx
    obtain ⟨d, rfl⟩ : ∃ d, i = S0 + d := ⟨i - S0, by omega⟩
    exact hleave' d (by omega) x hx
  obtain ⟨T1, h1⟩ := PendingEpoch.finite_metadata_stabilizes N.inputs N.facts
    (fun t => L.keep t (hP t))
  let m := fun d => ((N.names T0).filter fun x => decide (x ∈ N.names (T0 + d))).length
  have hm : ∀ d, m (d + 1) ≤ m d := fun d =>
    PendingEpoch.filter_len_mono _ _ _ fun x _ h => by
      simp only [decide_eq_true_eq] at h ⊢
      exact hleave (T0 + d) (by omega) x (by simpa [Nat.add_assoc] using h)
  obtain ⟨D, h2⟩ := nat_trace_stabilizes m hm
  have same : ∀ t, T0 + D ≤ t → ∀ x, x ∈ N.names (t + 1) ↔ x ∈ N.names t := by
    intro t ht x
    obtain ⟨d, rfl⟩ : ∃ d, t = T0 + d := ⟨t - T0, by omega⟩
    refine ⟨hleave (T0 + d) (by omega) x, fun hx => Classical.byContradiction fun hn => ?_⟩
    have lt : m (d + 1) < m d :=
      PendingEpoch.filter_len_lt _ _ _
        (fun y _ h => by
          simp only [decide_eq_true_eq] at h ⊢
          exact hleave (T0 + d) (by omega) y (by simpa [Nat.add_assoc] using h))
        ⟨x, names_below hleave d x hx, by simpa using hx,
          by simpa [Nat.add_assoc] using hn⟩
    rw [h2 d (by omega), h2 (d + 1) (by omega)] at lt
    exact Nat.lt_irrefl _ lt
  have stay : ∀ t, T0 + D ≤ t → ∀ x, x ∈ N.names t ↔ x ∈ N.names (T0 + D) := by
    intro t ht x
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    induction d with
    | zero => exact Iff.rfl
    | succ d ih => exact (same (T0 + D + d) (by omega) x).trans (ih (by omega))
  refine ⟨max T1 (T0 + D), fun i hi => ⟨⟨fun x hx => ?_, same i (by omega)⟩, ?_⟩⟩
  · exact (h1 (i + 1) (by omega) x hx).trans (h1 i (by omega) x hx).symm
  · exact L.support i _ (hP i) (hP _)
      (fun x hx => (h1 i (by omega) x hx).trans (h1 (max T1 (T0 + D)) (by omega) x hx).symm)
      (fun x => (stay i (by omega) x).trans (stay (max T1 (T0 + D)) (by omega) x).symm)

end Naming

/-! ### A first fresh head

Before the node first observes a fresh head (a reply from after the record cut naming the hub's
current head, `Head` or `Fetched`; an `Incomplete` answer to a push counts, since the driver
hands it to the core before failing the round, though nothing here says what follows that
failure), its known head, raw closure and offered records stay as they are; its images of that
head may change, as naming does, until naming settles inside the hypothetical frozen round
(`Naming.settles`). Each of its core steps is then chosen as computed (`rawControl`), from the
images then. A step that fetches or polls sends a
`Fetch`, and one that idles is followed by a round that starts with one (fair start); a `Fetch`
completes, naming the hub's head (fair individual call), so either brings a fresh head
(`idle_brings_fresh`). A push gets a `Head` reply, which names it too, when its records are the
hub's and the hub does not drop its new head (`is_dropped`, which is `is_superseded` of that
head as the hub's records name it, rewrites included: a primitive of an honest push, not a
consequence of matching records); one with other records is refused, and the node then hears
the hub's records, which differ from those it offers, so it never pushes again. So, with no
fresh head, the node pushes at most once, and every other step is a burst step or an objects
call, which lower the control rank (`no_infinite_calls`) from where naming settles on: a fresh
head comes (`fresh_head_reached`). No completed round, no eventual fresh head and no naming
cutoff is assumed. -/

/-- What a step's calls bring back, as far as a fresh head goes. -/
inductive Reply
  | none
  | objects
  | fresh
  | refused
  deriving DecidableEq

/-- No fresh head before step `i`. -/
def Before (reply : Nat → Reply) (i : Nat) : Prop := ∀ j, j < i → reply j ≠ .fresh

/-- The core pushes only when its records do not differ from those it last heard. -/
theorem choose_push_differ {r : Reads} (h : choose r = .push) : r.differ = false := by
  unfold choose at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h <;> cases h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  rename_i hd
  cases hdi : r.differ <;> simp_all

theorem choose_objects_missObjs {r : Reads} (h : choose r = .objects) : r.missObjs = true := by
  unfold choose at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · assumption
    · cases h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  split at h
  · split at h <;> cases h
  split at h <;> cases h

/-- An idle is followed by a fresh head: the next round starts (fair start), with a `Fetch`, and
the `Fetch` completes naming the hub's head (fair individual call). -/
theorem idle_brings_fresh {reply : Nat → Reply} {starts fetchCall : Nat → Prop} {i : Nat}
    (hstart : ∃ j, i < j ∧ starts j) (hstartFetch : ∀ j, starts j → fetchCall j)
    (hfetchCall : ∀ j, fetchCall j → reply j = .fresh) : ∃ j, i < j ∧ reply j = .fresh := by
  obtain ⟨j, hj, hs⟩ := hstart
  exact ⟨j, hj, hfetchCall j (hstartFetch j hs)⟩

/-- A node observes a fresh head. Its events are core steps (`core`) and round starts (`starts`);
before a fresh head: the record-credit cut (no adoption, no prepared taking advance); `differ` as
the core computes it against the records last heard, which, across a core step that does not idle,
change only by a refusal's (between rounds a notification may change them, but an idle is followed
by a fresh `Fetch` reply anyway); a core step's law by its computed choice (a burst step as
checked; an objects call bringing the objects, or locality, of the walked operations with a body
but not their objects, the op heads and plan as they were and nothing lost, or else, its reply
lacking them, failing the round, so that a round starts after it (the adapter's `stage_objects`
checks they are here, and the driver reopens and starts a round with an initial `Fetch`); a fetch
or poll sending a `Fetch`; an idle followed by a round start); a round starting with a `Fetch`; a
`Fetch` completing fresh; and a push whose reply is refused unless it has the hub's records `R`,
and is fresh when it has them and the hub does not drop it (`pushDropped`, its `is_dropped`). Each
step's law relates its reading to its state right after its calls complete (`after`), and that
state to the next step's reading by a frame (`Frame`: nothing lost, the canonical op heads and the
plan as they were), not one reading to the next directly. That primitive is asked only of a push
with the hub's records: one with other records is refused first, even if its head is newly
superseded at the hub. Naming's laws hold of the steps (metadata only arrives, and the images read
only that of finitely many raw operations) and pending names only leave; the checked burst and
objects laws are asked only of steps naming does not change across. -/
theorem fresh_head_reached {ρ α : Type} [DecidableEq ρ] (raw : List Nat) (nm : Naming α)
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
      (offered ≠ R → reply i = .refused)) :
    ∃ i, reply i = .fresh := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ i, Before reply i := fun _ j _ h => hno ⟨j, h⟩
  have hcore : ∀ i, core i := by
    intro i
    rcases hkind i (hall i) with h | h
    · exact h
    · exact absurd ⟨i, hfetchCall i (hall i) (hstartFetch i (hall i) h)⟩ hno
  -- the known head stays, so naming settles, at a step derived here
  obtain ⟨T, hT⟩ := nm.settles hnaming hall
  have hcall : ∀ i, T ≤ i → rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .push →
      Call raw (nm.images T) anc (run i) (after i) := by
    intro i hi hp
    have hb := hall i
    have hc' := hcore i
    obtain ⟨hs, himg⟩ := hT i hi
    cases hc : rawControl raw (nm.images i) par anc H (run i) (prims i) with
    | adopt => exact absurd hc (hrecord i hb hc').1
    | merge =>
      obtain ⟨k, hk⟩ := hburst i hb hc' hs (Or.inl hc)
      rw [himg] at hk
      exact callB_sound hk
    | realize =>
      obtain ⟨k, hk⟩ := hburst i hb hc' hs (Or.inr (Or.inl hc))
      rw [himg] at hk
      exact callB_sound hk
    | advance =>
      obtain ⟨k, hk⟩ := hburst i hb hc' hs (Or.inr (Or.inr hc))
      rw [himg] at hk
      exact callB_sound hk
    | fetch => exact absurd ⟨i, hfetchCall i hb (hpoll i hb hc' (Or.inl hc))⟩ hno
    | poll => exact absurd ⟨i, hfetchCall i hb (hpoll i hb hc' (Or.inr hc))⟩ hno
    | idle =>
      obtain ⟨j, -, hj⟩ := idle_brings_fresh (hstart i hb hc' hc)
        (fun j h => hstartFetch j (hall j) h) (fun j h => hfetchCall j (hall j) h)
      exact absurd ⟨j, hj⟩ hno
    | objects =>
      rcases hobjects i hb hc' hs hc with hfail | ⟨hbr, hh, hp', hg⟩
      · -- the reply lacked them: the round fails, and the next one starts with a `Fetch`
        obtain ⟨j, -, hj⟩ := idle_brings_fresh hfail
          (fun j h => hstartFetch j (hall j) h) (fun j h => hfetchCall j (hall j) h)
        exact absurd ⟨j, hj⟩ hno
      · exact objects_call (base := surveyBase)
          ((missObjsB_iff hlt hraw).1 (choose_objects_missObjs hc))
          (fun x hw => walk_mem hraw hw) (fun x hw => hbr x ((walkB_iff hlt).2 hw)) hh hp'
          (growsB_sound hg)
    | push => exact absurd hc hp
  have hnoidle : ∀ i, rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .idle := by
    intro i hc
    obtain ⟨j, -, hj⟩ := idle_brings_fresh (hstart i (hall i) (hcore i) hc)
      (fun j h => hstartFetch j (hall j) h) (fun j h => hfetchCall j (hall j) h)
    exact hno ⟨j, hj⟩
  -- with no push from `S` on, the calls from there go on forever
  have tail : ∀ S, T ≤ S →
      (∀ i, S ≤ i → rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .push) →
      False := fun S hS hnp =>
    no_infinite_framed raw (nm.images T) anc trans (fun j => run (S + j)) (fun j => after (S + j))
      (fun j => hcall (S + j) (by omega) (hnp (S + j) (by omega)))
      (fun j => hframe (S + j) (hall _) (hcore _) (hT (S + j) (by omega)).1)
  by_cases hp : ∃ i0, rawControl raw (nm.images i0) par anc H (run i0) (prims i0) = .push
  · obtain ⟨i0, hi0⟩ := hp
    have hl := hpush i0 (hall i0) (hcore i0) hi0
    have hoR : offered ≠ R := fun ho =>
      hno ⟨i0, hl.1 ho (hnd i0 (hall i0) (hcore i0) hi0 ho)⟩
    have href : reply i0 = .refused := hl.2 hoR
    have hR : ∀ j, heard (i0 + 1 + j) = some R := by
      intro j
      induction j with
      | zero =>
        have h := hheard i0 (hall i0) (hcore i0) (hnoidle i0) (fun h => hno ⟨i0, h⟩)
        rw [href] at h
        simpa using h
      | succ j ih =>
        have h := hheard (i0 + 1 + j) (hall _) (hcore _) (hnoidle _) (fun h => hno ⟨_, h⟩)
        rw [show i0 + 1 + (j + 1) = i0 + 1 + j + 1 by omega, h]
        split
        · rfl
        · exact ih
    apply tail (max T (i0 + 1)) (Nat.le_max_left _ _)
    intro i hi hc
    obtain ⟨j, rfl⟩ : ∃ j, i = i0 + 1 + j := ⟨i - (i0 + 1), by omega⟩
    have hd := choose_push_differ hc
    have h := hdiffer (i0 + 1 + j) (hall _) (hcore _)
    rw [hR j] at h
    change (prims (i0 + 1 + j)).differ = false at hd
    rw [hd] at h
    simp only at h
    have : R = offered := by
      cases hdec : decide (R = offered)
      · rw [hdec] at h; cases h
      · exact of_decide_eq_true hdec
    exact hoR this.symm
  · exact tail T (Nat.le_refl _) (fun i _ h => hp ⟨i, h⟩)

/-! ### Taking the hub's records after a fresh `Fetch`

Right after an eligible node handles a fresh `Fetch` it has the hub's current records announced
unless it has applied them already and holds no receipts, and every operation below the hub's
head that it does not have locally has its body and objects there: the reply brought them, the
node's drops being the hub's, so that the head's images are the head. Then, in its round, nothing
is missing: so long as the announcement stands, the core adopts it, or (if it drops an op head)
merges, realizes and finally advances taking it (`fresh_fetch_takes`). Past the cut after which
the node takes no more records, the announcement cannot stand, so the node has the hub's
records applied and no receipts (`fresh_fetch_current`). The hub need not be stable; the node's
own round keeps its known head. -/

theorem choose_adopt_of {r : Reads} (ha : r.announced = true) (hd : r.dropHead = false) :
    choose r = .adopt := by
  simp [choose, ha, hd]

/-- With an announcement that drops an op head, the core never gets as far as polling or
pushing: it advances, taking it, first. -/
theorem choose_late_dropHead {r : Reads} (hd : r.dropHead = true)
    (h : choose r = .poll ∨ choose r = .push) : False := by
  obtain ⟨a, dh, h2, kl, pln, rd, mo, mb, de, di, pe, hk, nk⟩ := r
  simp only at hd
  subst hd
  cases a <;> cases h2 <;> cases kl <;> cases pln <;> cases rd <;> cases mo <;> cases mb <;>
    simp_all [choose]

/-- With an announcement that drops an op head, the core idles only in its survey, with the
known head not local and nothing ready. -/
theorem choose_idle_dropHead {r : Reads} (hd : r.dropHead = true) (h : choose r = .idle) :
    r.knownLocal = false ∧ r.ready = false := by
  obtain ⟨a, dh, h2, kl, pln, rd, mo, mb, de, di, pe, hk, nk⟩ := r
  simp only at hd ⊢
  subst hd
  cases a <;> cases h2 <;> cases kl <;> cases pln <;> cases rd <;> cases mo <;> cases mb <;>
    simp_all [choose]

theorem choose_fetch_missOps {r : Reads} (h : choose r = .fetch) : r.missOps = true := by
  unfold choose at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · assumption
    split at h <;> cases h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  split at h
  · split at h <;> cases h
  split at h <;> cases h

/-- Every raw operation below the known head `H` has a body here (`stg`: staged, or its
canonical body in the node's store), local or not: what a fresh `Fetch` leaves, its objects
aside. Naming does not enter it, so it lasts while bodies are kept, as naming changes. -/
def RawBodies (par : Nat → List Nat) (H : Nat) (s : State) : Prop :=
  ∀ x, Anc par x H → s.stg x = true

theorem anc_of_walk {par : Nat → List Nat} {loc stg : Nat → Bool} {x y : Nat}
    (h : Anc (walkParents par loc stg) x y) : Anc par x y := by
  induction h with
  | refl => exact Anc.refl
  | step hp _ ih => exact Anc.step (mem_walkParents.1 hp).2.2 ih

/-- With every body here, the survey finds no operation missing. -/
theorem missOpsB_bodies {raw : List Nat} {par : Nat → List Nat} {H : Nat} {s : State}
    (hlt : ParLt par) (h : RawBodies par H s) : missOpsB raw par s.burst.loc s.stg H = false := by
  unfold missOpsB
  apply List.any_eq_false.2
  intro x _
  cases hw : walkB par s.burst.loc s.stg H x
  · simp
  · simp [h x (anc_of_walk ((Exec.ancB_iff (parLt_walkParents hlt)).1 hw))]

/-- The core idles in its survey only finding nothing missing. -/
theorem choose_idle_survey {r : Reads} (h : choose r = .idle) (hk : r.knownLocal = false) :
    r.missOps = false ∧ r.missObjs = false := by
  obtain ⟨a, dh, h2, kl, pln, rd, mo, mb, de, di, pe, hk', nk⟩ := r
  simp only at hk ⊢
  subst hk
  cases a <;> cases dh <;> cases h2 <;> cases pln <;> cases rd <;> cases mo <;> cases mb <;>
    simp_all [choose]

/-- After a fresh `Fetch` that brought the bodies of the known head's raw closure, an
announcement does not stand through the node's round: with no adoption and no taking advance,
it would have the core merge, realize and ask for objects forever. `active` marks the round's
own core steps from the reply on, the known head frozen: the first step is the round's, and a
step of it that merges, realizes or asks for objects, sending no `Fetch`, is followed by
another (the `GetObjects` reply comes, and the next core step, fairly); every law is asked of
those steps only, and the run past the round's end is arbitrary. Bodies are kept through the
round, but objects need not have come with the `Fetch`: a `GetObjects` brings what the survey
finds missing, or its reply lacks them (`failed`), and the round fails. That no `GetObjects` of
the round fails is no law of the round: `hserve` is to be derived from the hub keeping what it
can serve (the `SerialReply` credit), not assumed as an ordinary failure cutoff. Naming may
change in the round; it settles there (`Naming.settles`), and the checked burst and objects
laws are asked only of steps it does not change across. A round already settled ends at once;
none is assumed to go on. -/
theorem fresh_fetch_takes {α : Type} (raw : List Nat) (nm : Naming α) (par : Nat → List Nat)
    (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (hlt : ParLt par) (H : Nat) (hraw : ∀ x, Anc par x H → x ∈ raw)
    (run after : Nat → State) (prims : Nat → Prims) (active : Nat → Bool)
    (failed : Nat → Prop)
    (h0 : active 0 = true)
    (hnaming : nm.Laws par H fun i => active i = true)
    (hnext : ∀ i, active i = true →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
        (rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects ∧ ¬ failed i)) →
      active (i + 1) = true)
    (hrecord : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt ∧
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance →
        (prims i).dropHead = false))
    (hbodies : RawBodies par H (run 0))
    (hstg : ∀ i, active i = true → ∀ x ∈ raw, (run i).stg x = true → (run (i + 1)).stg x = true)
    (hann : ∀ i, active i = true → (prims i).announced = true →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt →
      ¬ (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance ∧
        (prims i).dropHead = true) → (prims (i + 1)).announced = true)
    (hburst : ∀ i, active i = true → nm.Still i →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize) →
      ∃ k, callB raw (nm.images i) anc (.burst k) (run i) (after i) = true)
    (hobjects : ∀ i, active i = true → nm.Still i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects →
      failed i ∨
      ((∀ x, walkB par (run i).burst.loc (run i).stg H x = true →
        (run i).burst.loc x = false → (run i).stg x = true → (run i).obj x = false →
        (after i).obj x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true))
    (hframe : ∀ i, active i = true → active (i + 1) = true → nm.Still i →
      Frame raw (after i) (run (i + 1)))
    (hserve : ∀ i, active i = true → ¬ failed i) :
    (prims 0).announced = false := by
  cases ha0 : (prims 0).announced with
  | false => rfl
  | true =>
    exfalso
    -- standing, the announcement drops an op head, and the round's step merges, realizes or
    -- asks for objects
    have step : ∀ i, active i = true → (prims i).announced = true → RawBodies par H (run i) →
        (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects) ∧
        (prims (i + 1)).announced = true ∧ active (i + 1) = true ∧
          RawBodies par H (run (i + 1)) := by
      intro i hact ha hb
      have hmo : missOpsB raw par (run i).burst.loc (run i).stg H = false := missOpsB_bodies hlt hb
      have hrec := hrecord i hact
      have hdh : (prims i).dropHead = true := by
        cases hd : (prims i).dropHead
        · exact absurd (choose_adopt_of
            (r := rawReads raw (nm.images i) par anc H (run i) (prims i)) ha hd) hrec.1
        · rfl
      have hmr : rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects := by
        cases hc' : rawControl raw (nm.images i) par anc H (run i) (prims i) with
        | adopt => exact absurd hc' hrec.1
        | merge => exact Or.inl rfl
        | realize => exact Or.inr (Or.inl rfl)
        | objects => exact Or.inr (Or.inr rfl)
        | fetch =>
          have h := choose_fetch_missOps hc'
          change missOpsB raw par (run i).burst.loc (run i).stg H = true at h
          rw [hmo] at h; cases h
        | idle =>
          obtain ⟨hk, hr⟩ := choose_idle_dropHead hdh hc'
          obtain ⟨hmo', hmb'⟩ := choose_idle_survey hc' hk
          rcases rawReads_survey (images := nm.images i) (anc := anc) (s := run i) (q := prims i)
              hlt hraw hk hr with h | h
          · rw [hmo'] at h; cases h
          · rw [hmb'] at h; cases h
        | advance =>
          have h := hrec.2 hc'
          rw [hdh] at h; cases h
        | poll => exact (choose_late_dropHead hdh (Or.inl hc')).elim
        | push => exact (choose_late_dropHead hdh (Or.inr hc')).elim
      have hgo : rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
          (rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects ∧
            ¬ failed i) := by
        rcases hmr with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨h, hserve i hact⟩)
      refine ⟨hmr, hann i hact ha hrec.1 ?_, hnext i hact hgo,
        fun x hx => hstg i hact x (hraw x hx) (hb x hx)⟩
      rintro ⟨hadv, -⟩
      rcases hmr with h | h | h <;> rw [h] at hadv <;> cases hadv
    have hall : ∀ i, active i = true ∧ (prims i).announced = true ∧
        RawBodies par H (run i) := by
      intro i
      induction i with
      | zero => exact ⟨h0, ha0, hbodies⟩
      | succ i ih =>
        obtain ⟨-, ha', hact', hb'⟩ := step i ih.1 ih.2.1 ih.2.2
        exact ⟨hact', ha', hb'⟩
    -- the round goes on forever with its known head, so naming settles, at a step derived here
    obtain ⟨T, hT⟩ := nm.settles hnaming fun i => (hall i).1
    apply no_infinite_framed raw (nm.images T) anc trans (fun j => run (T + j))
      (fun j => after (T + j)) _
      (fun j => hframe (T + j) (hall _).1 (hall _).1 (hT (T + j) (by omega)).1)
    intro j
    have hact := (hall (T + j)).1
    obtain ⟨hs, himg⟩ := hT (T + j) (by omega)
    rcases (step (T + j) hact (hall _).2.1 (hall _).2.2).1 with h | h | h
    · obtain ⟨k, hk⟩ := hburst _ hact hs (Or.inl h)
      rw [himg] at hk
      exact callB_sound hk
    · obtain ⟨k, hk⟩ := hburst _ hact hs (Or.inr h)
      rw [himg] at hk
      exact callB_sound hk
    · rcases hobjects _ hact hs h with hf | ⟨hbr, hh, hp', hg⟩
      · exact absurd hf (hserve _ hact)
      · exact objects_call (base := surveyBase)
          ((missObjsB_iff hlt hraw).1 (choose_objects_missObjs h))
          (fun x hw => walk_mem hraw hw) (fun x hw => hbr x ((walkB_iff hlt).2 hw)) hh hp'
          (growsB_sound hg)

/-- So, past the cut after which the node takes no more records, the node has the hub's records
`R` applied and holds no receipts when it has handled a fresh `Fetch`: the core announces them
otherwise (`note_announced`). -/
theorem fresh_fetch_current {ρ α : Type} (raw : List Nat) (nm : Naming α) (par : Nat → List Nat)
    (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (hlt : ParLt par) (H : Nat) (hraw : ∀ x, Anc par x H → x ∈ raw)
    (run after : Nat → State) (prims : Nat → Prims) (active : Nat → Bool)
    (failed : Nat → Prop) (ap R : ρ)
    (receipts : Bool)
    (hnote : (prims 0).announced = true ↔ (ap ≠ R ∨ receipts = true))
    (h0 : active 0 = true)
    (hnaming : nm.Laws par H fun i => active i = true)
    (hnext : ∀ i, active i = true →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
        (rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects ∧ ¬ failed i)) →
      active (i + 1) = true)
    (hrecord : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt ∧
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance →
        (prims i).dropHead = false))
    (hbodies : RawBodies par H (run 0))
    (hstg : ∀ i, active i = true → ∀ x ∈ raw, (run i).stg x = true → (run (i + 1)).stg x = true)
    (hann : ∀ i, active i = true → (prims i).announced = true →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt →
      ¬ (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance ∧
        (prims i).dropHead = true) → (prims (i + 1)).announced = true)
    (hburst : ∀ i, active i = true → nm.Still i →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize) →
      ∃ k, callB raw (nm.images i) anc (.burst k) (run i) (after i) = true)
    (hobjects : ∀ i, active i = true → nm.Still i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects →
      failed i ∨
      ((∀ x, walkB par (run i).burst.loc (run i).stg H x = true →
        (run i).burst.loc x = false → (run i).stg x = true → (run i).obj x = false →
        (after i).obj x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true))
    (hframe : ∀ i, active i = true → active (i + 1) = true → nm.Still i →
      Frame raw (after i) (run (i + 1)))
    (hserve : ∀ i, active i = true → ¬ failed i) :
    ap = R ∧ receipts = false := by
  have h := fresh_fetch_takes raw nm par anc trans hlt H hraw run after prims active failed h0
    hnaming hnext hrecord hbodies hstg hann hburst hobjects hframe hserve
  refine ⟨Classical.byContradiction fun hne => ?_, ?_⟩
  · rw [hnote.2 (Or.inl hne)] at h; cases h
  · cases hr : receipts
    · rfl
    · rw [hnote.2 (Or.inr hr)] at h; cases h

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

/-- The core pushes only with nothing announced. -/
theorem choose_push_announced {r : Reads} (h : choose r = .push) : r.announced = false := by
  unfold choose at h
  split at h
  · cases h
  rename_i ha
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h <;> cases h
  split at h
  · cases h
  rename_i hd
  cases hann : r.announced <;> cases hdh : r.dropHead <;> simp_all

/-- What the round right after a fresh `Fetched` reply reads, sampled from the node's actual
events: its raw closure, naming (whose images of the known head may change), raw graph and known
head (the fresh one), its core states and reads at its successive steps, which of those are the
round's own (`active`), its core states right after each step's calls complete (`after`), which of
its `GetObjects` replies lacked what they were asked for (`failed`), and the node's receipts after
the reply. Data only: its laws are `FetchLaws`. -/
structure FetchData (α : Type) where
  raw : List Nat
  naming : Naming α
  par : Nat → List Nat
  anc : Nat → Nat → Bool
  H : Nat
  run : Nat → State
  after : Nat → State
  prims : Nat → Prims
  active : Nat → Bool
  failed : Nat → Prop
  receipts : Bool

/-- The native laws of that round, as `fresh_fetch_current` takes them, `ap` being the records the
node had applied when it handled the reply. They are asked of the round's own steps only, so a
round that ends at once has them. That no `GetObjects` of the round fails is not one of them:
`FetchLaws.current` takes it apart. -/
structure FetchLaws {ρ α : Type} (ap R : ρ) (d : FetchData α) : Prop where
  trans : ∀ a b c, d.anc a b = true → d.anc b c = true → d.anc a c = true
  hlt : ParLt d.par
  hraw : ∀ x, Anc d.par x d.H → x ∈ d.raw
  note : (d.prims 0).announced = true ↔ (ap ≠ R ∨ d.receipts = true)
  active0 : d.active 0 = true
  naming : d.naming.Laws d.par d.H fun i => d.active i = true
  next : ∀ i, d.active i = true → (rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i)
    (d.prims i) = .merge ∨ rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i) (d.prims
    i) = .realize ∨ (rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i) (d.prims i) =
    .objects ∧ ¬ d.failed i)) → d.active (i + 1) = true
  record : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i)
    (d.prims i) ≠ .adopt ∧ (rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i) (d.prims
    i) = .advance → (d.prims i).dropHead = false)
  bodies : RawBodies d.par d.H (d.run 0)
  stg : ∀ i, d.active i = true → ∀ x ∈ d.raw, (d.run i).stg x = true → (d.run (i + 1)).stg x = true
  ann : ∀ i, d.active i = true → (d.prims i).announced = true → rawControl d.raw (d.naming.images i)
    d.par d.anc d.H (d.run i) (d.prims i) ≠ .adopt → ¬ (rawControl d.raw (d.naming.images i) d.par
    d.anc d.H (d.run i) (d.prims i) = .advance ∧ (d.prims i).dropHead = true) → (d.prims (i +
    1)).announced = true
  burst : ∀ i, d.active i = true → d.naming.Still i → (rawControl d.raw (d.naming.images i) d.par
    d.anc d.H (d.run i) (d.prims i) = .merge ∨ rawControl d.raw (d.naming.images i) d.par d.anc d.H
    (d.run i) (d.prims i) = .realize) → ∃ k, callB d.raw (d.naming.images i) d.anc (.burst k) (d.run
    i) (d.after i) = true
  objects : ∀ i, d.active i = true → d.naming.Still i → rawControl d.raw (d.naming.images i) d.par
    d.anc d.H (d.run i) (d.prims i) = .objects → d.failed i ∨ ((∀ x, walkB d.par (d.run i).burst.loc
    (d.run i).stg d.H x = true → (d.run i).burst.loc x = false → (d.run i).stg x = true → (d.run
    i).obj x = false → (d.after i).obj x = true ∨ (d.after i).burst.loc x = true) ∧ (d.after
    i).burst.heads = (d.run i).burst.heads ∧ (d.after i).burst.plan = (d.run i).burst.plan ∧ growsB
    d.raw (d.run i) (d.after i) = true)
  frame : ∀ i, d.active i = true → d.active (i + 1) = true → d.naming.Still i → Frame d.raw (d.after
    i) (d.run (i + 1))

theorem FetchLaws.current {ρ α : Type} {ap R : ρ} {d : FetchData α} (L : FetchLaws ap R d)
    (hserve : ∀ i, d.active i = true → ¬ d.failed i) :
    ap = R ∧ d.receipts = false :=
  fresh_fetch_current
    d.raw d.naming d.par d.anc L.trans L.hlt d.H L.hraw d.run d.after d.prims d.active d.failed
    ap R d.receipts L.note L.active0 L.naming L.next L.record L.bodies L.stg L.ann L.burst
    L.objects L.frame hserve

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
