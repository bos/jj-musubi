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
