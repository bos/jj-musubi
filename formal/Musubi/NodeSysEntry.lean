/-
Entry into the system simulation, derived rather than assumed (`node_settles_entry`).

`node_sim` starts from what it keeps (`SimInv`). Here that comes from what every run keeps from a
well-formed start: slots and the hub's answers (`SysOK`), replies and notifications made in the
past (`TimeOK`), a step that asks for objects being answered with them (`ObjsOK`), and the node's
own state well formed and scoped, its wait an `Issue` from it (`NodeOK`, kept through `Learn` by
its parents-first law). Once the hub has settled at `st` and the node takes no old reply and
processes no old notification (root's old-effects cuts, as `node_sim` takes them; old ones may
stay queued, never taken), the node's next step that learns a head, its first own fresh
observation (`Observes`), teaches it `st` with its records, and the simulation starts just after
it (`entry_of_obs`). A fair node makes one
(`observes`): without one its known pair stays put, its round keeps running, since an idle node
would start another with a `Fetch`, and every step of the round lowers NodeSettle's rank in a
context whose pair it doesn't know.

Before the hub settles, after the record cut, each step of the system is one of EarlyEntry's
events of the node's core (`eev_step`, labelled by `elabOf`), the replies it takes and the
notifications it processes being from after the cut (`CutOK`); so EarlyEntry holds over the
system (`early_entry_sys`).
Learning grows the node's graph within these events: each asks only that the state after be well
formed (`LInv`), which `nodeOK_step` keeps.
-/
import Musubi.NodeSys

namespace Musubi.NodeSysEntry

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys

/-! ## What every run keeps -/

/-- Every reply and notification was made in the past. -/
structure TimeOK (g : Sys) : Prop where
  reps : ∀ r ∈ g.reps, r.time < g.time
  notes : ∀ nt ∈ g.notes, nt.time < g.time

/-- The hub answers a request for objects with objects, and node `n`'s step that asks for
objects asks only for them. -/
structure ObjsOK (n : Nat) (g : Sys) : Prop where
  ans : ∀ r ∈ g.reps, r.req = .objs → r.ans = .objects
  reqs : ∀ w, (g.node n).wait = some w → w.kind = .fetchObjs →
    ∀ q ∈ g.reqs, q.node = n → q.slot ∈ w.slots → q.body = .objs
  reps : ∀ w, (g.node n).wait = some w → w.kind = .fetchObjs →
    ∀ r ∈ g.reps, r.node = n → r.slot ∈ w.slots → r.req = .objs

section Keep

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act} {g g' : Sys}

theorem timeOK_of (T : TimeOK g) (ht : g'.time = g.time + 1)
    (hr : ∀ r ∈ g'.reps, r ∈ g.reps ∨ r.time = g.time)
    (hn : ∀ x ∈ g'.notes, x ∈ g.notes ∨ x.time = g.time) : TimeOK g' where
  reps r h := by
    rcases hr r h with h | h
    · have := T.reps r h; omega
    · omega
  notes x h := by
    rcases hn x h with h | h
    · have := T.notes x h; omega
    · omega

theorem timeOK_step (T : TimeOK g) (hs : SysStep N D law a g g') : TimeOK g' := by
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq ht =>
    exact timeOK_of T ht (fun r h => Or.inl (by rw [hq.reps] at h; exact h))
      (fun x h => Or.inl (by rw [hq.notes] at h; exact h))
  | idle _ _ _ _ _ _ _ hq ht =>
    exact timeOK_of T ht (fun r h => Or.inl (by rw [hq.reps] at h; exact h))
      (fun x h => Or.inl (by rw [hq.notes] at h; exact h))
  | maint _ _ _ _ _ _ _ _ _ _ hq ht =>
    exact timeOK_of T ht (fun r h => Or.inl (by rw [hq.reps] at h; exact h))
      (fun x h => Or.inl (by rw [hq.notes] at h; exact h))
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest ht _ =>
    exact timeOK_of T ht (fun r h => Or.inl (by rw [hrest.2.1] at h; exact h))
      (fun x h => Or.inl (by rw [hrest.2.2] at h; exact h))
  | answer r ans _ _ acc hans hreps _ ht =>
    refine timeOK_of T ht (fun x h => ?_) (fun x h => ?_)
    · rw [hreps, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact Or.inl h
      · exact Or.inr rfl
    · have hn : g'.notes = g.notes ∨
          g'.notes = g.notes ++ (List.range N).map (fun m => ⟨m, g.time, g'.hub⟩) := by
        rcases hans with ⟨-, -, -, -, hn⟩ | ⟨-, -, -, -, hn⟩ |
          ⟨p, -, ⟨-, -, -, -, hn⟩ | ⟨-, -, -, -, -, hn⟩ | ⟨-, -, -, -, -, hn⟩⟩
        all_goals first | exact Or.inl hn | exact Or.inr hn
      rcases hn with hn | hn <;> rw [hn] at h
      · exact Or.inl h
      · rw [List.mem_append] at h
        rcases h with h | h
        · exact Or.inl h
        · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
          exact Or.inr rfl
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hreps hrest ht =>
    exact timeOK_of T ht (fun r h => Or.inl ((hreps r).1 h).1)
      (fun x h => Or.inl (by rw [hrest.2.2.1] at h; exact h))
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnotes hrest ht =>
    exact timeOK_of T ht (fun r h => Or.inl (by rw [hrest.2.2.1] at h; exact h))
      (fun x h => Or.inl ((by rw [hnotes] at h; exact List.mem_of_mem_erase h)))
  | ignore _ _ _ _ _ _ _ _ hnotes hrest ht =>
    exact timeOK_of T ht (fun r h => Or.inl (by rw [hrest.2.2.1] at h; exact h))
      (fun x h => Or.inl ((by rw [hnotes] at h; exact List.mem_of_mem_erase h)))
  | env _ _ hq ht =>
    exact timeOK_of T ht (fun r h => Or.inl (by rw [hq.reps] at h; exact h))
      (fun x h => Or.inl (by rw [hq.notes] at h; exact h))

theorem sysOK_step (S : SysOK law g) (hs : SysStep N D law a g g') : SysOK law g' := by
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ => exact sysOK_same S hq.reqs hq.reps hq.slot
  | idle _ _ _ _ _ _ _ hq _ => exact sysOK_same S hq.reqs hq.reps hq.slot
  | maint _ _ _ _ _ _ _ _ _ _ hq _ => exact sysOK_same S hq.reqs hq.reps hq.slot
  | issue _ _ _ _ _ _ _ _ _ _ hslot _ _ hreqs hslot' hrest _ hnd =>
    exact sysOK_issue S hreqs hrest.2.1 hslot' (fun q hq => (hslot q hq).2.2) hnd
  | answer r ans hr hreqs acc hans hreps hrest _ =>
    exact sysOK_answer S hr hreqs hans hreps hrest.2.2.2
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hreps hrest _ =>
    exact sysOK_sub S hrest.2.1 (fun r h => ((hreps r).1 h).1) hrest.2.2.2.1
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ =>
    exact sysOK_same S hrest.2.1 hrest.2.2.1 hrest.2.2.2.1
  | ignore _ _ _ _ _ _ _ _ _ hrest _ => exact sysOK_same S hrest.2.1 hrest.2.2.1 hrest.2.2.2.1
  | env _ _ hq _ => exact sysOK_same S hq.reqs hq.reps hq.slot

/-- Replies answered since `t0` stay the stable hub's while it stays stable. -/
theorem stable_step {t0 : Nat} {st : Snap} (R : StableReps t0 st g) (hs : SysStep N D law a g g')
    (hhub : g.hub = st) (hhub' : g'.hub = st) : StableReps t0 st g' := by
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ => exact stable_sub R (fun r h => by rw [hq.reps] at h; exact h)
  | idle _ _ _ _ _ _ _ hq _ => exact stable_sub R (fun r h => by rw [hq.reps] at h; exact h)
  | maint _ _ _ _ _ _ _ _ _ _ hq _ =>
    exact stable_sub R (fun r h => by rw [hq.reps] at h; exact h)
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ _ =>
    exact stable_sub R (fun r h => by rw [hrest.2.1] at h; exact h)
  | answer r ans _ _ acc hans hreps _ _ => exact stable_answer R hhub hhub' hans hreps
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hreps _ _ =>
    exact stable_sub R (fun r h => ((hreps r).1 h).1)
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ =>
    exact stable_sub R (fun r h => by rw [hrest.2.2.1] at h; exact h)
  | ignore _ _ _ _ _ _ _ _ _ hrest _ =>
    exact stable_sub R (fun r h => by rw [hrest.2.2.1] at h; exact h)
  | env _ _ hq _ => exact stable_sub R (fun r h => by rw [hq.reps] at h; exact h)

/-- When the hub has settled, every reply there is older than it. -/
theorem stable_init {st : Snap} (T : TimeOK g) : StableReps g.time st g :=
  fun r h ht => absurd ht (by have := T.reps r h; omega)

theorem objs_frame {n : Nat} (O : ObjsOK n g) (ha : ∀ r ∈ g'.reps, r.req = .objs → r.ans = .objects)
    (hn : (g'.node n).wait = (g.node n).wait)
    (hq : ∀ q ∈ g'.reqs, q.node = n → q ∈ g.reqs)
    (hp : ∀ r ∈ g'.reps, r.node = n → r ∈ g.reps ∨
      ∃ q ∈ g.reqs, q.node = n ∧ q.slot = r.slot ∧ q.body = r.req) : ObjsOK n g' where
  ans := ha
  reqs w hw hk q hq' hqn hs := O.reqs w (by rw [← hn]; exact hw) hk q (hq q hq' hqn) hqn hs
  reps w hw hk r hr hrn hs := by
    rcases hp r hr hrn with h | ⟨q, hq', hqn, hqs, hqb⟩
    · exact O.reps w (by rw [← hn]; exact hw) hk r h hrn hs
    · rw [← hqb]
      exact O.reqs w (by rw [← hn]; exact hw) hk q hq' hqn (by rw [hqs]; exact hs)

theorem objs_none {n : Nat} (ha : ∀ r ∈ g'.reps, r.req = .objs → r.ans = .objects)
    (hn : (g'.node n).wait = none) : ObjsOK n g' where
  ans := ha
  reqs w hw := by rw [hn] at hw; cases hw
  reps w hw := by rw [hn] at hw; cases hw

theorem objsOK_step {n : Nat} (O : ObjsOK n g) (S : SysOK law g) (hs : SysStep N D law a g g') :
    ObjsOK n g' := by
  cases hs with
  | busy m _ _ _ _ _ _ hnode hq _ =>
    have ha : ∀ r ∈ g'.reps, r.req = .objs → r.ans = .objects := by rw [hq.reps]; exact O.ans
    by_cases hm : m = n
    · subst hm; exact objs_none ha (by rw [hnode, upd_same])
    · exact objs_frame O ha (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        (fun q h _ => by rw [hq.reqs] at h; exact h)
        (fun r h _ => Or.inl (by rw [hq.reps] at h; exact h))
  | idle m _ _ _ _ hnode _ hq _ =>
    have ha : ∀ r ∈ g'.reps, r.req = .objs → r.ans = .objects := by rw [hq.reps]; exact O.ans
    by_cases hm : m = n
    · subst hm; exact objs_none ha (by rw [hnode, upd_same])
    · exact objs_frame O ha (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        (fun q h _ => by rw [hq.reqs] at h; exact h)
        (fun r h _ => Or.inl (by rw [hq.reps] at h; exact h))
  | maint m _ _ _ _ _ _ _ _ hnode hq _ =>
    have ha : ∀ r ∈ g'.reps, r.req = .objs → r.ans = .objects := by rw [hq.reps]; exact O.ans
    by_cases hm : m = n
    · subst hm; exact objs_none ha (by rw [hnode, upd_same])
    · exact objs_frame O ha (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        (fun q h _ => by rw [hq.reqs] at h; exact h)
        (fun r h _ => Or.inl (by rw [hq.reps] at h; exact h))
  | issue m k post new emb1 rq _ _ _ hb hslot _ hnode hreqs _ hrest _ _ =>
    have ha : ∀ r ∈ g'.reps, r.req = .objs → r.ans = .objects := by
      rw [hrest.2.1]; exact O.ans
    by_cases hm : m = n
    · subst hm
      have hw : (g'.node m).wait = some ⟨k, rq.map Req.slot, post, new, emb1⟩ := by
        rw [hnode, upd_same]
      refine ⟨ha, fun w hw' hk q hq hqn hs => ?_, fun w hw' hk r hr hrn hs => ?_⟩
      · rw [hw] at hw'
        cases hw'
        simp only at hk hs
        rw [hreqs, List.mem_append] at hq
        rcases hq with hq | hq
        · obtain ⟨q', hq', he⟩ := List.mem_map.1 hs
          have := S.reqs q hq
          have := (hslot q' hq').2.1
          omega
        · subst hk
          have hmem : q.body ∈ rq.map Req.body := List.mem_map_of_mem hq
          simp only [Bodies] at hb
          rw [hb, List.mem_singleton] at hmem
          exact hmem
      · rw [hw] at hw'
        cases hw'
        simp only at hs
        rw [hrest.2.1] at hr
        obtain ⟨q', hq', he⟩ := List.mem_map.1 hs
        have := S.reps r hr
        have := (hslot q' hq').2.1
        omega
    · exact objs_frame O ha (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        (fun q h hqn => by
          rw [hreqs, List.mem_append] at h
          rcases h with h | h
          · exact h
          · exact absurd ((hslot q h).1.symm.trans hqn) hm)
        (fun r h _ => Or.inl (by rw [hrest.2.1] at h; exact h))
  | answer r ans hr hreqs acc hans hreps hrest _ =>
    refine objs_frame O (fun x hx hb => ?_) (by rw [hrest.1])
      (fun q hq _ => (by rw [hreqs] at hq; exact List.mem_of_mem_erase hq)) (fun x hx hxn => ?_)
    · rw [hreps, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact O.ans x hx hb
      · simp only at hb ⊢
        rcases hans with ⟨hb', -⟩ | ⟨-, -, he, -⟩ | ⟨p, hb', -⟩
        · rw [hb'] at hb; cases hb
        · exact he
        · rw [hb'] at hb; cases hb
    · rw [hreps, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · exact Or.inr ⟨r, hr, hxn, rfl, rfl⟩
  | handle m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnode hreps hrest _ =>
    have ha : ∀ r ∈ g'.reps, r.req = .objs → r.ans = .objects :=
      fun r h => O.ans r ((hreps r).1 h).1
    by_cases hm : m = n
    · subst hm; exact objs_none ha (by rw [hnode, upd_same])
    · exact objs_frame O ha (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        (fun q h _ => by rw [hrest.2.1] at h; exact h)
        (fun r h _ => Or.inl ((hreps r).1 h).1)
  | notice m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnode _ hrest _ =>
    have ha : ∀ r ∈ g'.reps, r.req = .objs → r.ans = .objects := by
      rw [hrest.2.2.1]; exact O.ans
    by_cases hm : m = n
    · subst hm; exact objs_none ha (by rw [hnode, upd_same])
    · exact objs_frame O ha (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        (fun q h _ => by rw [hrest.2.1] at h; exact h)
        (fun r h _ => Or.inl (by rw [hrest.2.2.1] at h; exact h))
  | ignore _ _ _ _ _ _ _ hnode _ hrest _ =>
    exact objs_frame O (by rw [hrest.2.2.1]; exact O.ans) (by rw [hnode])
      (fun q h _ => by rw [hrest.2.1] at h; exact h)
      (fun r h _ => Or.inl (by rw [hrest.2.2.1] at h; exact h))
  | env _ hnode hq _ =>
    exact objs_frame O (by rw [hq.reps]; exact O.ans) (by rw [hnode])
      (fun q h _ => by rw [hq.reqs] at h; exact h)
      (fun r h _ => Or.inl (by rw [hq.reps] at h; exact h))

end Keep

/-! ## The node's own state is kept -/

theorem linv_same {σ σ' : NS} (I : LInv σ) (hp : σ'.par = σ.par) (hk : σ'.known = σ.known)
    (hn : σ'.next = σ.next) (hh : σ'.heads = σ.heads) (hi : σ'.img = σ.img) : LInv σ' :=
  ⟨by rw [hp]; exact I.parLt, by rw [hk, hn]; exact I.knownLt, by rw [hh]; exact I.headsNe,
    by rw [hh, hn]; exact I.headsLt, by rw [hi]; exact I.imgNe, by rw [hi, hn]; exact I.imgLt⟩

theorem linv_norm {σ : NS} (I : LInv σ) : LInv (norm σ) :=
  ⟨I.parLt, I.knownLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt⟩

theorem linv_plan {σ : NS} (I : LInv σ) (L : List Nat) : LInv { σ with plan := L } :=
  ⟨I.parLt, I.knownLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt⟩

theorem linv_recs {σ : NS} (I : LInv σ) (o : Option Nat) : LInv { σ with hubRecs := o } :=
  ⟨I.parLt, I.knownLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt⟩

theorem linv_fetched {c : Ctx} {σ σ' : NS} (I : LInv σ) (F : FetchedRep c σ σ')
    (hH : c.H < σ.next) : LInv σ' :=
  ⟨by rw [F.par]; exact I.parLt, by rw [F.known, F.next]; exact hH,
    by rw [F.heads]; exact I.headsNe, by rw [F.heads, F.next]; exact I.headsLt, F.imgNe,
    by rw [F.next]; exact F.imgLt⟩

theorem linv_headRep {c : Ctx} {σ σ' : NS} (I : LInv σ) (F : HeadRep c σ σ')
    (hH : c.H < σ.next) : LInv σ' :=
  ⟨by rw [F.par]; exact I.parLt, by rw [F.known, F.next]; exact hH,
    by rw [F.heads]; exact I.headsNe, by rw [F.heads, F.next]; exact I.headsLt, F.imgNe,
    by rw [F.next]; exact F.imgLt⟩

theorem linv_acc {c : Ctx} {σ σ' : NS} (I : LInv σ) (A : AccLearn c σ σ') (hH : c.H < σ.next) :
    LInv σ' :=
  ⟨by rw [A.par]; exact I.parLt, by rw [A.known, A.next]; exact hH,
    by rw [A.heads]; exact I.headsNe, by rw [A.heads, A.next]; exact I.headsLt, A.imgNe,
    by rw [A.next]; exact A.imgLt⟩

theorem linv_obj {σ σ' : NS} {M : Nat → Prop} (I : LInv σ) (O : ObjRep σ σ' M) : LInv σ' := by
  rw [O.rest]
  exact ⟨I.parLt, I.knownLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt⟩

/-- Learning only adds labels, parents first, above those there were. -/
theorem linv_learn {post posti : NS} (I : LInv post)
    (hc : posti = { post with par := posti.par, next := posti.next })
    (hn : post.next ≤ posti.next) (hp : ParLt posti.par) : LInv posti := by
  have hk : posti.known = post.known := by have h := congrArg NS.known hc; exact h
  have hh : posti.heads = post.heads := by have h := congrArg NS.heads hc; exact h
  have hi : posti.img = post.img := by have h := congrArg NS.img hc; exact h
  exact ⟨hp, by rw [hk]; exact Nat.lt_of_lt_of_le I.knownLt hn, by rw [hh]; exact I.headsNe,
    fun y hy => by rw [hh] at hy; exact Nat.lt_of_lt_of_le (I.headsLt y hy) hn,
    by rw [hi]; exact I.imgNe,
    fun i hi' => by rw [hi] at hi'; exact Nat.lt_of_lt_of_le (I.imgLt i hi') hn⟩

/-- The replies to a step leave its state well formed, the context's head being labelled where a
reply names it. -/
theorem linv_handle {c : Ctx} {d : Nat → Nat → Prop} {σ post σi posti σ' : NS} {k : Kind}
    {new : Nat} {as : List Ans} (hi : Issue d σ k post new) (hsame : post = σ → posti = σi)
    (I : LInv posti) (hH : k ≠ .push → k ≠ .fetchObjs → c.H < posti.next)
    (hHp : (∃ s, Ans.head s ∈ as) → c.H < posti.next) (hh : Handle c σi k posti as σ') :
    LInv σ' := by
  cases k with
  | start =>
    have e := hsame hi.2
    rw [← e] at hh
    obtain ⟨σ1, F, rfl⟩ := hh
    exact (linv_fetched I F (hH (by decide) (by decide))).act true
  | fetchPoll =>
    have e := hsame hi.2.2.2.2.2.2.2
    rw [← e] at hh
    obtain ⟨σ1, F, ho⟩ := hh
    have I1 := linv_fetched (linv_norm I) F (hH (by decide) (by decide))
    rcases ho with ⟨-, O⟩ | ⟨-, rfl⟩
    · exact linv_obj I1 O
    · exact I1
  | fetchObjs =>
    have e := hsame hi.2.2.2.2.2.2.2.2
    rw [← e] at hh
    have O : ObjRep (norm posti) σ'
        (fun x => Walk posti x ∧ ¬ posti.loc x ∧ posti.stg x ∧ ¬ posti.obj x) := hh
    exact linv_obj (linv_norm I) O
  | differPoll =>
    have e := hsame hi.2.2.2.2.2.2.2
    rw [← e] at hh
    exact linv_fetched (linv_plan (linv_norm I) []) hh (hH (by decide) (by decide))
  | push =>
    rcases hh with ⟨-, -, rfl⟩ | ⟨hs, -, F⟩ | ⟨hs, -, A⟩
    · exact linv_recs I _
    · exact linv_headRep I F (hHp hs)
    · exact linv_acc I A (hHp hs)
  | writePoll => exact linv_fetched I hh (hH (by decide) (by decide))

/-- Replies change no labels the step's writes and learning made. -/
theorem handle_graph' {c : Ctx} {d : Nat → Nat → Prop} {σ post σi posti σ' : NS} {k : Kind}
    {new : Nat} {as : List Ans} (hi : Issue d σ k post new) (hsame : post = σ → posti = σi)
    (hh : Handle c σi k posti as σ') : σ'.par = posti.par ∧ σ'.next = posti.next := by
  cases k with
  | start =>
    have e := hsame hi.2
    rw [← e] at hh
    obtain ⟨σ1, F, rfl⟩ := hh
    exact ⟨F.par, F.next⟩
  | fetchPoll =>
    have e := hsame hi.2.2.2.2.2.2.2
    rw [← e] at hh
    obtain ⟨σ1, F, ho⟩ := hh
    rcases ho with ⟨-, O⟩ | ⟨-, rfl⟩
    · exact ⟨(objRep_graph O).1.trans F.par, (objRep_graph O).2.trans F.next⟩
    · exact ⟨F.par, F.next⟩
  | fetchObjs =>
    have e := hsame hi.2.2.2.2.2.2.2.2
    rw [← e] at hh
    have O : ObjRep (norm posti) σ'
        (fun x => Walk posti x ∧ ¬ posti.loc x ∧ posti.stg x ∧ ¬ posti.obj x) := hh
    have h := objRep_graph O
    exact h
  | differPoll =>
    have e := hsame hi.2.2.2.2.2.2.2
    rw [← e] at hh
    exact ⟨hh.par, hh.next⟩
  | push =>
    rcases hh with ⟨-, -, rfl⟩ | ⟨-, -, F⟩ | ⟨-, -, A⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨F.par, F.next⟩
    · exact ⟨A.par, A.next⟩
  | writePoll => exact ⟨hh.par, hh.next⟩

section Node

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act} {g g' : Sys} {n : Nat}

theorem nodeOK_frame (I : NodeSys.NodeOK D n g) (hn : g'.node n = g.node n) (hr : RawGrow g g')
    (hq : ∀ q ∈ g'.reqs, q.node = n → q ∈ g.reqs)
    (hp : ∀ r ∈ g'.reps, r.node = n → r ∈ g.reps ∨
      ∃ q ∈ g.reqs, q.node = n ∧ q.slot = r.slot ∧ q.body = r.req) : NodeSys.NodeOK D n g' :=
  ⟨by rw [hn]; exact I.inv, by rw [hn]; exact scoped_raw I.scope hr,
    fun w hw => by rw [hn] at hw; exact waitOK_frame (I.wait w hw) hn hr hq hp⟩

/-- Every step keeps node `n` well formed and scoped, its wait an `Issue` from its state. -/
theorem nodeOK_step (I : NodeSys.NodeOK D n g) (S : SysOK law g) (hs : SysStep N D law a g g') :
    NodeSys.NodeOK D n g' := by
  cases hs with
  | busy m σ' emb' hw ha hsl hg hnode hq ht =>
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m = ⟨σ', emb', (g.node m).gen, none⟩ := by rw [hnode, upd_same]
      have hb : Busy (bctx 0 (D m) (g.node m).ns.known) (g.node m).ns σ' :=
        loc_busy hsl (I.inv.sinv 0 (D m)) rfl hg.next
      refine ⟨?_, ?_, ?_⟩
      · rw [hn']; exact linv_of_sinv (inv_busy (I.inv.sinv 0 (D m)) hb)
      · rw [hn']; exact scoped_growR I.scope I.inv.parLt hg
      · rw [hn']; intro w hw'; cases hw'
    · exact nodeOK_frame I (by rw [hnode, upd_ne _ _ (Ne.symm hm)]) hg.raw
        (fun q hq' _ => by rw [hq.reqs] at hq'; exact hq')
        (fun r hr' _ => Or.inl (by rw [hq.reps] at hr'; exact hr'))
  | idle m σ' hw ha hsl hnode hr hq ht =>
    have hraw : RawGrow g g' := ⟨Nat.le_of_eq hr.1.symm, fun y _ => by rw [hr.2]⟩
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m = ⟨σ', (g.node m).emb, (g.node m).gen, none⟩ := by
        rw [hnode, upd_same]
      have si := inv_idle (I.inv.sinv 0 (D m)) hsl
      obtain ⟨hgp, hgn, -⟩ := idle_graph hsl
      refine ⟨?_, ?_, ?_⟩
      · rw [hn']; exact linv_of_sinv si
      · rw [hn']; exact scoped_same I.scope hgp hgn hr.1 hr.2
      · rw [hn']; intro w hw'; cases hw'
    · exact nodeOK_frame I (by rw [hnode, upd_ne _ _ (Ne.symm hm)]) hraw
        (fun q hq' _ => by rw [hq.reqs] at hq'; exact hq')
        (fun r hr' _ => Or.inl (by rw [hq.reps] at hr'; exact hr'))
  | maint m σ1 σ' emb' hw ha hsl hx hg hnode hq ht =>
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m =
          ⟨σ', emb', (g.node m).gen + (σ'.next - (g.node m).ns.next), none⟩ := by
        rw [hnode, upd_same]
      refine ⟨?_, ?_, ?_⟩
      · rw [hn']; exact ((linv_of_sinv (inv_idle (I.inv.sinv 0 (D m)) hsl)).act true).ext hx
      · rw [hn']; exact scoped_growR I.scope I.inv.parLt hg
      · rw [hn']; intro w hw'; cases hw'
    · exact nodeOK_frame I (by rw [hnode, upd_ne _ _ (Ne.symm hm)]) hg.raw
        (fun q hq' _ => by rw [hq.reqs] at hq'; exact hq')
        (fun r hr' _ => Or.inl (by rw [hq.reps] at hr'; exact hr'))
  | issue m k post new emb1 rq hw hissue hg hb hslot hnodup hnode hreqs hslot' hrest ht hnd =>
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m = ⟨(g.node m).ns, (g.node m).emb,
          (g.node m).gen + (post.next - (g.node m).ns.next),
          some ⟨k, rq.map Req.slot, post, new, emb1⟩⟩ := by rw [hnode, upd_same]
      have hfresh : ∀ x ∈ rq.map Req.slot, g.slot ≤ x := by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact (hslot q hq).2.1
      refine ⟨by rw [hn']; exact I.inv, by rw [hn']; exact scoped_raw I.scope hg.raw, ?_⟩
      rw [hn']
      intro w hw'
      cases hw'
      refine ⟨by rw [hn']; exact hissue, scoped_growR I.scope I.inv.parLt hg,
        by rw [hn']; exact hg.next, by rw [hn']; exact hg.embOld, ?_, ?_, ?_⟩
      · intro he
        have := bodies_ne hb
        rw [List.map_eq_nil_iff] at he
        rw [he] at this
        exact this rfl
      · intro q hq' hqn hqs
        rw [hreqs, List.mem_append] at hq'
        rcases hq' with hq' | hq'
        · have := S.reqs q hq'
          have := hfresh _ hqs
          omega
        · refine ⟨fun hk => ?_, fun hh0 hk1 hk2 => ?_⟩
          · subst hk
            have hmem : q.body ∈ rq.map Req.body := List.mem_map_of_mem hq'
            simp only [Bodies] at hb
            rw [hb, List.mem_singleton] at hmem
            exact ⟨_, hmem, rfl⟩
          · have hne' : rq ≠ [] := List.ne_nil_of_mem hq'
            obtain ⟨q0, rest, hq0⟩ := List.exists_cons_of_ne_nil hne'
            subst hq0
            simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hh0
            have hqq : q = q0 := by
              rcases List.mem_cons.1 hq' with h' | h'
              · exact h'
              · exfalso
                have hnd' := hnodup
                simp only [List.map_cons, List.nodup_cons] at hnd'
                exact hnd'.1 (by rw [hh0]; exact List.mem_map_of_mem h')
            subst hqq
            cases k with
            | push => exact absurd rfl hk1
            | fetchObjs => exact absurd rfl hk2
            | start =>
              simp only [Bodies, List.map_cons, List.cons.injEq] at hb; exact hb.1
            | differPoll =>
              simp only [Bodies, List.map_cons, List.cons.injEq] at hb; exact hb.1
            | writePoll =>
              simp only [Bodies, List.map_cons, List.cons.injEq] at hb; exact hb.1
            | fetchPoll =>
              simp only [Bodies, List.map_cons, List.cons.injEq] at hb
              rcases hb with ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;> exact hb
      · intro r hr' hrn hrs
        rw [hrest.2.1] at hr'
        have := S.reps r hr'
        have := hfresh _ hrs
        omega
    · exact nodeOK_frame I (by rw [hnode, upd_ne _ _ (Ne.symm hm)]) hg.raw
        (fun q hq' hqn => by
          rw [hreqs, List.mem_append] at hq'
          rcases hq' with hq' | hq'
          · exact hq'
          · exact absurd ((hslot q hq').1.symm.trans hqn) hm)
        (fun r hr' _ => Or.inl (by rw [hrest.2.1] at hr'; exact hr'))
  | answer r ans hr hreqs acc hans hreps hrest ht =>
    refine nodeOK_frame I (by rw [hrest.1])
      ⟨Nat.le_of_eq hrest.2.1.symm, fun y _ => by rw [hrest.2.2.1]⟩
      (fun q hq' _ => (by rw [hreqs] at hq'; exact List.mem_of_mem_erase hq')) (fun x hx hxn => ?_)
    rw [hreps, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl hx
    · exact Or.inr ⟨r, hr, hxn, rfl, rfl⟩
  | handle m w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf hh hnode hreps hrest ht =>
    by_cases hm : m = n
    · subst hm
      have W := I.wait w hw
      have hn' : g'.node m = ⟨σ', embi, (g.node m).gen, none⟩ := by rw [hnode, upd_same]
      have hpost : LInv w.post := linv_of_sinv (post_inv W.issue (I.inv.sinv 0 (D m)))
      have hposti : LInv posti := linv_learn hpost hl.ctl.2 hl.grows.1 hl.parLt
      have hH : ∀ r ∈ rs, (∃ s, r.ans = .fetched s ∨ r.ans = .head s) → c.H < posti.next := by
        intro r hr' hsnap
        obtain ⟨s, hs⟩ := hsnap
        have := hf r hr'
        rcases hs with hs | hs <;> rw [hs] at this <;> exact this.2.1
      have hfetch : w.kind ≠ .push → w.kind ≠ .fetchObjs → c.H < posti.next := by
        intro hk1 hk2
        obtain ⟨s0, rest, hs0⟩ := List.exists_cons_of_ne_nil W.slots
        obtain ⟨r0, hr0, hr0s⟩ := hcov s0 (by rw [hs0]; exact List.mem_cons_self)
        have hbf := W.reps r0 (hrs r0 hr0).1 (hrs r0 hr0).2.1 (hrs r0 hr0).2.2
        have hreq : r0.req = .fetch := hbf.2 (by rw [hs0, hr0s]; rfl) hk1 hk2
        obtain ⟨s, hs⟩ := S.fetch r0 (hrs r0 hr0).1 hreq
        exact hH r0 hr0 ⟨s, Or.inl hs⟩
      have hpush : (∃ s, Ans.head s ∈ rs.map Rep.ans) → c.H < posti.next := by
        rintro ⟨s, hs⟩
        obtain ⟨r, hr', hra⟩ := List.mem_map.1 hs
        exact hH r hr' ⟨s, Or.inr hra⟩
      have hl' : LInv σ' := linv_handle W.issue hl.same hposti hfetch hpush hh
      obtain ⟨hgp, hgn⟩ := handle_graph' W.issue hl.same hh
      refine ⟨by rw [hn']; exact hl', ?_, by rw [hn']; intro w' hw'; cases hw'⟩
      rw [hn']
      exact scoped_same hl.scope hgp hgn hrest.2.2.2.2.1 hrest.2.2.2.2.2
    · exact nodeOK_frame I (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        ⟨Nat.le_of_eq hrest.2.2.2.2.1.symm, fun y _ => by rw [hrest.2.2.2.2.2]⟩
        (fun q hq' _ => by rw [hrest.2.1] at hq'; exact hq')
        (fun r hr' _ => Or.inl ((hreps r).1 hr').1)
  | notice m nt c σi posti σ' embi hw ha hn hnn hnew hl hc hf hh hnode hnotes hrest ht =>
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m = ⟨σ', embi, (g.node m).gen, none⟩ := by rw [hnode, upd_same]
      have e : posti = σi := hl.same rfl
      have hposti : LInv posti := linv_learn I.inv hl.ctl.2 hl.grows.1 hl.parLt
      rw [e] at hposti
      have hH : c.H < σi.next := hf.2.1
      refine ⟨by rw [hn']; exact linv_headRep hposti hh hH, ?_,
        by rw [hn']; intro w hw'; cases hw'⟩
      rw [hn']
      have hsc := hl.scope
      rw [e] at hsc
      exact scoped_same hsc hh.par hh.next hrest.2.2.2.2.1 hrest.2.2.2.2.2
    · exact nodeOK_frame I (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        ⟨Nat.le_of_eq hrest.2.2.2.2.1.symm, fun y _ => by rw [hrest.2.2.2.2.2]⟩
        (fun q hq' _ => by rw [hrest.2.1] at hq'; exact hq')
        (fun r hr' _ => Or.inl (by rw [hrest.2.2.1] at hr'; exact hr'))
  | ignore _ _ _ _ _ _ _ hnode _ hrest _ =>
    exact nodeOK_frame I (by rw [hnode])
      ⟨Nat.le_of_eq hrest.2.2.2.2.1.symm, fun y _ => by rw [hrest.2.2.2.2.2]⟩
      (fun q hq' _ => by rw [hrest.2.1] at hq'; exact hq')
      (fun r hr' _ => Or.inl (by rw [hrest.2.2.1] at hr'; exact hr'))
  | env hr hnode hq _ =>
    exact nodeOK_frame I (by rw [hnode]) hr
      (fun q hq' _ => by rw [hq.reqs] at hq'; exact hq')
      (fun r hr' _ => Or.inl (by rw [hq.reps] at hr'; exact hr'))

end Node

/-- What every run keeps from a well-formed start. -/
structure RunOK (law : HubLaw) (D : Nat → Nat → Nat → Prop) (n : Nat) (g : Sys) : Prop where
  node : NodeSys.NodeOK D n g
  sys : SysOK law g
  time : TimeOK g
  objs : ObjsOK n g

theorem runOK_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {n : Nat} {a : Act}
    {g g' : Sys} (K : RunOK law D n g) (hs : SysStep N D law a g g') : RunOK law D n g' :=
  ⟨nodeOK_step K.node K.sys hs, sysOK_step K.sys hs, timeOK_step K.time hs,
    objsOK_step K.objs K.sys hs⟩

theorem runOK_run {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {n k0 : Nat}
    (ρ : Nat → Sys) (acts : Nat → Act)
    (hstep : ∀ i, k0 ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (h0 : RunOK law D n (ρ k0)) : ∀ i, k0 ≤ i → RunOK law D n (ρ i) := by
  intro i hi
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero => exact h0
  | succ d ih => exact runOK_step (ih (by omega)) (hstep _ (by omega))

/-! ## The first own fresh observation -/

/-- Node `n` learns a head at this step: a notification, or the replies to its step that name
one, as every reply to a step that fetches does, and as a push's `Head` does. -/
def Observes (n : Nat) (g : Sys) (a : Act) (g' : Sys) : Prop :=
  (∃ nt, a = .notice n nt) ∨ (a = .handle n ∧ ∃ w, (g.node n).wait = some w ∧ w.kind ≠ .fetchObjs ∧
    (w.kind = .push → ∃ r ∈ g.reps, r ∉ g'.reps ∧ r.node = n ∧ ∃ s, r.ans = .head s))

theorem loc_known {d : Nat → Nat → Prop} {σ σ' : NS} (h : Loc d σ σ') : σ'.known = σ.known := by
  cases h with
  | adopt A ha hne hb ht => exact ht.known
  | merge _ _ _ _ he => subst he; rfl
  | mergeExisting _ _ _ _ _ _ _ he => subst he; rfl
  | prune _ _ _ _ he => subst he; rfl
  | realizePlan x rest hg h1 hl hp he => subst he; rfl
  | realizeSurvey x L hg h1 hl hp hr he => subst he; rfl
  | advanceTake A hg h1 hl ha ht => exact ht.known
  | advance hg h1 hl hd ha hv => exact hv.ext.known

theorem idle_known {c : Ctx} {σ σ' : NS} (h : Idle c σ σ') : σ'.known = σ.known := by
  cases h with
  | fetchIdle _ _ _ _ _ _ _ he => subst he; rfl
  | differIdle _ _ _ _ _ _ _ he => subst he; rfl
  | goal _ _ _ _ _ _ _ _ he => subst he; rfl

theorem writeRes_known {σ σ1 : NS} {new : Nat} (W : WriteRes σ σ1 new) : σ1.known = σ.known := by
  obtain ⟨y, -, (⟨-, F⟩ | ⟨-, he, -⟩)⟩ := W
  · exact F.ext.known
  · subst he; rfl

/-- What a step's replies teach, its own push's records being the hub's: the context's pair,
and its records. -/
theorem handle_knows {c : Ctx} {σi posti σ' : NS} {k : Kind} {as : List Ans}
    (hk : k ≠ .fetchObjs) (hap : k = .push → σi.ap = c.R) (hh : Handle c σi k posti as σ') :
    σ'.known = (c.S, c.H) ∧ σ'.hubRecs = some c.R := by
  cases k with
  | start => obtain ⟨σ1, F, rfl⟩ := hh; exact ⟨F.known, F.hubRecs⟩
  | fetchPoll =>
    obtain ⟨σ1, F, ho⟩ := hh
    rcases ho with ⟨-, O⟩ | ⟨-, rfl⟩
    · have h1 : σ'.known = σ1.known := by have h := congrArg NS.known O.rest; exact h
      have h2 : σ'.hubRecs = σ1.hubRecs := by have h := congrArg NS.hubRecs O.rest; exact h
      exact ⟨h1.trans F.known, h2.trans F.hubRecs⟩
    · exact ⟨F.known, F.hubRecs⟩
  | fetchObjs => exact absurd rfl hk
  | differPoll => exact ⟨hh.known, hh.hubRecs⟩
  | push =>
    rcases hh with ⟨-, hne, -⟩ | ⟨-, -, F⟩ | ⟨-, hne, -⟩
    · exact absurd (hap rfl) hne
    · exact ⟨F.known, F.hubRecs⟩
    · exact absurd (hap rfl) hne
  | writePoll => exact ⟨hh.known, hh.hubRecs⟩

theorem sinv_of_linv {c : Ctx} {σ : NS} (I : LInv σ) (hH : c.H < σ.next)
    (hr : σ.known = (c.S, c.H) → σ.hubRecs = some c.R) : NodeSettle.SInv c σ :=
  ⟨I.parLt, I.knownLt, hH, I.headsNe, I.headsLt, I.imgNe, I.imgLt, hr⟩

section Quiet

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act} {g g' : Sys} {n : Nat}

theorem quiet_frame {st : Snap} (hn : (g'.node n).ns = (g.node n).ns) (hb : a ≠ .core n .busy)
    (hh : a ≠ .handle n) (hi : a ≠ .core n .idle) :
    (g'.node n).ns.known = (g.node n).ns.known ∧
    ((a = .core n .busy ∨ a = .handle n) →
      Busy (bctx st.recs (D n) (g.node n).ns.known) (g.node n).ns (g'.node n).ns) ∧
    (a = .core n .idle → (g'.node n).ns.act = false) ∧
    (a ≠ .core n .busy → a ≠ .handle n → a ≠ .core n .idle → a ≠ .core n .maint →
      (g'.node n).ns = (g.node n).ns) :=
  ⟨by rw [hn], fun h => h.elim (fun e => absurd e hb) (fun e => absurd e hh),
    fun h => absurd h hi, fun _ _ _ _ => hn⟩

/-- A step at which node `n` learns no head, the replies it takes being the stable hub's: its
known pair stays; its own core step, or the replies it takes, is NodeSettle's `Busy` in the
context whose pair it doesn't know (`bctx`); an idle round ends; anything else but
housekeeping leaves the node's state alone. -/
theorem quiet_step {t0 : Nat} {st : Snap} (K : RunOK law D n g) (R : StableReps t0 st g)
    (hold : ∀ r ∈ g.reps, r ∉ g'.reps → r.node = n → t0 ≤ r.time)
    (hs : SysStep N D law a g g')
    (ho : ¬ Observes n g a g') :
    (g'.node n).ns.known = (g.node n).ns.known ∧
    ((a = .core n .busy ∨ a = .handle n) →
      Busy (bctx st.recs (D n) (g.node n).ns.known) (g.node n).ns (g'.node n).ns) ∧
    (a = .core n .idle → (g'.node n).ns.act = false) ∧
    (a ≠ .core n .busy → a ≠ .handle n → a ≠ .core n .idle → a ≠ .core n .maint →
      (g'.node n).ns = (g.node n).ns) := by
  cases hs with
  | busy m σ' emb' hw ha hsl hg hnode hq ht =>
    by_cases hm : m = n
    · subst hm
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      refine ⟨by rw [e]; exact loc_known hsl, fun _ => ?_, fun h => (by cases h),
        fun h => absurd rfl h⟩
      rw [e]
      exact loc_busy hsl (K.node.inv.sinv _ _) rfl hg.next
    · exact quiet_frame (by rw [hnode, upd_ne _ _ (Ne.symm hm)])
        (by intro e; cases e <;> exact hm rfl) (by intro e; cases e) (by intro e; cases e)
  | idle m σ' hw ha hsl hnode hr hq ht =>
    by_cases hm : m = n
    · subst hm
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      refine ⟨by rw [e]; exact idle_known hsl, fun h => ?_,
        fun _ => by rw [e]; exact NodeSettle.idle_act hsl, fun _ _ h _ => absurd rfl h⟩
      rcases h with h | h <;> cases h
    · exact quiet_frame (by rw [hnode, upd_ne _ _ (Ne.symm hm)]) (by intro e; cases e)
        (by intro e; cases e) (by intro e; cases e <;> exact hm rfl)
  | maint m σ1 σ' emb' hw ha hsl hx hg hnode hq ht =>
    by_cases hm : m = n
    · subst hm
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      refine ⟨?_, fun h => ?_, fun h => (by cases h), fun _ _ _ h => absurd rfl h⟩
      · rw [e]
        have h1 : σ'.known = σ1.known := by have h := hx.known; exact h
        exact h1.trans (idle_known hsl)
      · rcases h with h | h <;> cases h
    · exact quiet_frame (by rw [hnode, upd_ne _ _ (Ne.symm hm)]) (by intro e; cases e)
        (by intro e; cases e) (by intro e; cases e)
  | issue m k post new emb1 rq hw hissue hg hb hslot hnodup hnode hreqs hslot' hrest ht hnd =>
    have e : (g'.node n).ns = (g.node n).ns := by
      by_cases hm : m = n
      · subst hm; rw [hnode, upd_same]
      · rw [hnode, upd_ne _ _ (Ne.symm hm)]
    exact quiet_frame e (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
  | answer r ans hr hreqs acc hans hreps hrest ht =>
    exact quiet_frame (by rw [hrest.1]) (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h)
  | handle m w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf hh hnode hreps hrest ht =>
    by_cases hm : m = n
    · subst hm
      have W := K.node.wait w hw
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      -- the step's replies name no head
      have hkind : w.kind = .fetchObjs ∨
          (w.kind = .push ∧ ∀ r ∈ rs, ¬ ∃ s, r.ans = .head s) := by
        by_cases hk : w.kind = .fetchObjs
        · exact Or.inl hk
        · by_cases hp : w.kind = .push
          · refine Or.inr ⟨hp, fun r hr hex => ho (Or.inr ⟨rfl, w, hw, hk, fun _ => ?_⟩)⟩
            have hr' : r ∉ g'.reps := fun h => ((hreps r).1 h).2 hr
            exact ⟨r, (hrs r hr).1, hr', (hrs r hr).2.1, hex⟩
          · exact absurd (Or.inr ⟨rfl, w, hw, hk, fun h => absurd h hp⟩) ho
      have hnohead : ∀ r ∈ rs, r.ans.head? = none := by
        intro r hr
        rcases hkind with hk | ⟨hp, hno⟩
        · rw [K.objs.ans r (hrs r hr).1
            (K.objs.reps w hw hk r (hrs r hr).1 (hrs r hr).2.1 (hrs r hr).2.2)]
          rfl
        · obtain ⟨p, hp', -⟩ := (W.reps r (hrs r hr).1 (hrs r hr).2.1 (hrs r hr).2.2).1 hp
          rcases K.sys.pushAns r (hrs r hr).1 p hp' with ⟨x, hx⟩ | ⟨s, hs⟩
          · rw [hx]; rfl
          · exact absurd ⟨s, hs⟩ (hno r hr)
      have hdn : hd = none := by
        cases hd' : hd with
        | none => rfl
        | some h =>
          obtain ⟨r, hr, hrh⟩ := hhd' h hd'
          rw [hnohead r hr] at hrh
          cases hrh
      obtain ⟨rfl, rfl, rfl⟩ := hl.nothing (fun h hh' => by rw [hdn] at hh'; cases hh')
      have hi := W.issue
      rcases hkind with hk | ⟨hp, hno⟩
      · rw [hk] at hi hh
        have O : ObjRep (norm (g.node m).ns) σ' (fun x => Walk (g.node m).ns x ∧
            ¬ (g.node m).ns.loc x ∧ (g.node m).ns.stg x ∧ ¬ (g.node m).ns.obj x) := hh
        refine ⟨?_, fun _ => ?_, fun h => (by cases h), fun _ h _ _ => absurd rfl h⟩
        · rw [e]; have h1 := congrArg NS.known O.rest; exact h1
        · rw [e]
          exact issue_busy (c := bctx st.recs (D m) (g.node m).ns.known) (as := rs.map Rep.ans) hi
            (by decide) hh rfl
            (fun h => by cases h) (fun h => by cases h)
      · rw [hp] at hi hh
        have hrefuse : ∃ x, Ans.refused x ∈ rs.map Rep.ans ∧ (g.node m).ns.ap ≠ c.R ∧
            σ' = { w.post with hubRecs := some c.R } := by
          rcases hh with ⟨⟨x, hx⟩, hne, he⟩ | ⟨⟨s, hs⟩, -⟩ | ⟨⟨s, hs⟩, -⟩
          · exact ⟨x, hx, hne, he⟩
          · obtain ⟨r, hr, hra⟩ := List.mem_map.1 hs; exact absurd ⟨s, hra⟩ (hno r hr)
          · obtain ⟨r, hr, hra⟩ := List.mem_map.1 hs; exact absurd ⟨s, hra⟩ (hno r hr)
        obtain ⟨x, hx, hne, he⟩ := hrefuse
        obtain ⟨r, hr, hra⟩ := List.mem_map.1 hx
        have h1 : c.R = x := by have h := hf r hr; rw [hra] at h; exact h
        have h2 : x = st.recs := by
          have h := (R r (hrs r hr).1
            (hold r (hrs r hr).1 (fun h => ((hreps r).1 h).2 hr) (hrs r hr).2.1)).2
          rw [hra] at h
          exact h
        rw [h1.trans h2] at hne he
        have hh' : Handle (bctx st.recs (D m) (g.node m).ns.known) (g.node m).ns .push w.post
            (rs.map Rep.ans) σ' := Or.inl ⟨⟨x, hx⟩, hne, he⟩
        refine ⟨?_, fun _ => ?_, fun h => (by cases h), fun _ h _ _ => absurd rfl h⟩
        · rw [e, he]
          have h := writeRes_known hi.2.2.2.2.2.2.2.2.1
          exact h
        · rw [e]
          refine issue_busy hi (by decide) hh' rfl (fun _ h => ?_) (fun _ hc' => ?_)
          · have h1 := congrArg Prod.fst h
            simp only [bctx] at h1
            omega
          · obtain ⟨⟨s, hs⟩, -⟩ := hc'
            obtain ⟨r', hr', hra'⟩ := List.mem_map.1 hs
            exact hno r' hr' ⟨s, hra'⟩
    · exact quiet_frame (by rw [hnode, upd_ne _ _ (Ne.symm hm)]) (by intro e; cases e)
        (by intro e; cases e <;> exact hm rfl) (by intro e; cases e)
  | notice m nt c σi posti σ' embi hw ha hn hnn hnew hl hc hf hh hnode hnotes hrest ht =>
    by_cases hm : m = n
    · subst hm; exact absurd (Or.inl ⟨nt, rfl⟩) ho
    · exact quiet_frame (by rw [hnode, upd_ne _ _ (Ne.symm hm)]) (by intro e; cases e)
        (by intro e; cases e) (by intro e; cases e)
  | ignore _ _ _ _ _ _ _ hnode _ _ _ =>
    exact quiet_frame (by rw [hnode]) (by intro e; cases e) (by intro e; cases e)
      (by intro e; cases e)
  | env _ hnode _ _ =>
    exact quiet_frame (by rw [hnode]) (by intro e; cases e) (by intro e; cases e)
      (by intro e; cases e)

/-- At its first fresh observation, after the hub has settled at `st`, taking only new replies
and processing only the stable hub's notification, node `n` comes to know `st`'s pair, under a
label of `st`'s head, with its records, and waits on nothing. -/
theorem obs_knows {t0 : Nat} {st : Snap} (K : RunOK law D n g) (R : StableReps t0 st g)
    (hold : ∀ r ∈ g.reps, r ∉ g'.reps → r.node = n → t0 ≤ r.time)
    (hnotes : ∀ nt, a = .notice n nt → nt.snap = st)
    (hs : SysStep N D law a g g') (ho : Observes n g a g') :
    ∃ H, (g'.node n).ns.known = (st.seq, H) ∧ H < (g'.node n).ns.next ∧
      (g'.node n).emb H = st.head ∧ (g'.node n).ns.hubRecs = some st.recs ∧
      (g'.node n).wait = none := by
  rcases ho with ⟨nt0, rfl⟩ | ⟨rfl, w0, hw0, hk0, hpush0⟩
  · cases hs with
    | notice _ nt c σi posti σ' embi hw ha hn hnn hnew hl hc hf hh hnode hnotes' hrest ht =>
      have hN : g'.node n = ⟨σ', embi, (g.node n).gen, none⟩ := by rw [hnode, upd_same]
      have e1 : (g'.node n).ns = σ' := by rw [hN]
      have e2 : (g'.node n).emb = embi := by rw [hN]
      have e3 : (g'.node n).wait = none := by rw [hN]
      have hsn : nt0.snap = st := hnotes _ rfl
      rw [hsn] at hf
      obtain ⟨hS, hHlt, hemb, hR⟩ := hf
      refine ⟨c.H, ?_, ?_, ?_, ?_, e3⟩
      · rw [e1, hh.known, hS]
      · rw [e1, hh.next]; exact hHlt
      · rw [e2]; exact hemb
      · rw [e1, hh.hubRecs, hR]
  · cases hs with
    | handle _ w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf hh hnode hreps hrest ht =>
      have hww : w = w0 := Option.some.inj (hw.symm.trans hw0)
      subst hww
      have W := K.node.wait w hw
      have hN : g'.node n = ⟨σ', embi, (g.node n).gen, none⟩ := by rw [hnode, upd_same]
      have hst : ∀ r ∈ rs, r.acc = false ∧ AnsStable st r.ans := fun r hr' =>
        R r (hrs r hr').1 (hold r (hrs r hr').1 (fun h => ((hreps r).1 h).2 hr') (hrs r hr').2.1)
      -- a reply among them names the stable hub's head
      have hsnap : ∃ r ∈ rs, r.ans = .fetched st ∨ r.ans = .head st := by
        by_cases hp : w.kind = .push
        · obtain ⟨r, hrg, hrg', hrn, s, hs⟩ := hpush0 hp
          have hr : r ∈ rs := Classical.byContradiction fun h => hrg' ((hreps r).2 ⟨hrg, h⟩)
          have hs' := (hst r hr).2
          rw [hs] at hs'
          have : s = st := hs'
          exact ⟨r, hr, Or.inr (by rw [hs, this])⟩
        · obtain ⟨s0, rest, hs0⟩ := List.exists_cons_of_ne_nil W.slots
          obtain ⟨r0, hr0, hr0s⟩ := hcov s0 (by rw [hs0]; exact List.mem_cons_self)
          have hbf := W.reps r0 (hrs r0 hr0).1 (hrs r0 hr0).2.1 (hrs r0 hr0).2.2
          have hreq : r0.req = .fetch := hbf.2 (by rw [hs0, hr0s]; rfl) hp hk0
          obtain ⟨s, hs⟩ := K.sys.fetch r0 (hrs r0 hr0).1 hreq
          have hs' := (hst r0 hr0).2
          rw [hs] at hs'
          have : s = st := hs'
          exact ⟨r0, hr0, Or.inl (by rw [hs, this])⟩
      obtain ⟨r, hr, hra⟩ := hsnap
      have hfit : c.S = st.seq ∧ c.H < posti.next ∧ embi c.H = st.head ∧ c.R = st.recs := by
        have h := hf r hr
        rcases hra with hra | hra <;> rw [hra] at h <;> exact h
      -- a push answered with the hub's `Head` had the hub's records
      have hap : w.kind = .push → σi.ap = c.R := by
        intro hp
        obtain ⟨p, hp', hpr⟩ := (W.reps r (hrs r hr).1 (hrs r hr).2.1 (hrs r hr).2.2).1 hp
        rcases hra with hra | hra
        · rcases K.sys.pushAns r (hrs r hr).1 p hp' with ⟨x, hx⟩ | ⟨s, hs⟩
          · rw [hra] at hx; cases hx
          · rw [hra] at hs; cases hs
        · have h1 := (K.sys.push r (hrs r hr).1 p hp' (hst r hr).1).2 st hra
          have hi := W.issue
          rw [hp] at hi
          have hpost : w.post.ap = (g.node n).ns.ap := by
            have h := write_ap hi.2.2.2.2.2.2.2.2.1
            exact h
          have hσi : σi.ap = (g.node n).ns.ap := by
            have h := congrArg NS.ap hl.ctl.1
            exact h
          rw [hσi, ← hpost, ← hpr, h1, hfit.2.2.2]
      obtain ⟨hkn, hrc⟩ := handle_knows hk0 hap hh
      obtain ⟨-, hgn⟩ := handle_graph' W.issue hl.same hh
      have e1 : (g'.node n).ns = σ' := by rw [hN]
      have e2 : (g'.node n).emb = embi := by rw [hN]
      have e3 : (g'.node n).wait = none := by rw [hN]
      refine ⟨c.H, ?_, ?_, ?_, ?_, e3⟩
      · rw [e1, hkn, hfit.1]
      · rw [e1, hgn]; exact hfit.2.1
      · rw [e2]; exact hfit.2.2.1
      · rw [e1, hrc, hfit.2.2.2]

/-- Just after its first fresh observation, the simulation's invariant holds, with the label of
`st`'s head the node learnt. -/
theorem entry_of_obs {t0 : Nat} {st : Snap} (K : RunOK law D n g) (K' : RunOK law D n g')
    (R : StableReps t0 st g) (R' : StableReps t0 st g')
    (hold : ∀ r ∈ g.reps, r ∉ g'.reps → r.node = n → t0 ≤ r.time)
    (hnotes : ∀ nt, a = .notice n nt → nt.snap = st)
    (hs : SysStep N D law a g g') (ho : Observes n g a g') :
    ∃ H, SimInv law D n ⟨st.seq, H, st.recs, D n⟩ t0 st H g' := by
  obtain ⟨H, -, hH, he, hr, hw⟩ := obs_knows K R hold hnotes hs ho
  refine ⟨H, K'.node, K'.sys, R', hH, he, sinv_of_linv K'.node.inv hH (fun _ => hr), ?_⟩
  intro w hw'
  rw [hw] at hw'
  cases hw'

end Quiet

section Entry

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}

/-- Once the hub has settled at `st` and node `n` takes no old reply, a fair node makes a fresh
observation. Without one its known pair stays put; its round keeps running, since an idle
node starts a round with a `Fetch`, whose reply would be one; and every step of the round, its
own core step or the replies to a request for objects or to a refused push, lowers NodeSettle's
rank in the context whose pair it doesn't know. Housekeeping that writes is assumed to stop. -/
theorem observes (ρ : Nat → Sys) (acts : Nat → Act) (n k k1 : Nat) (st : Snap)
    (hstep : ∀ i, k ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (hK : ∀ i, k ≤ i → RunOK law D n (ρ i)) (hk1 : k ≤ k1)
    (hR : ∀ i, k ≤ i → StableReps (ρ k).time st (ρ i))
    (hold : ∀ i, k1 ≤ i → ∀ r ∈ (ρ i).reps, r ∉ (ρ (i + 1)).reps → r.node = n →
      (ρ k).time ≤ r.time)
    (hfair : Fair ρ acts n k1) (hmaint : ∃ kb, ∀ i, kb ≤ i → acts i ≠ .core n .maint) :
    ∃ j, k1 ≤ j ∧ Observes n (ρ j) (acts j) (ρ (j + 1)) := by
  apply Classical.byContradiction
  intro hno
  have hq : ∀ i, k1 ≤ i → ¬ Observes n (ρ i) (acts i) (ρ (i + 1)) :=
    fun i hi h => hno ⟨i, hi, h⟩
  have hstep1 : ∀ i, k1 ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)) :=
    fun i hi => hstep i (by omega)
  have Q := fun i (hi : k1 ≤ i) =>
    quiet_step (hK i (by omega)) (hR i (by omega)) (hold i hi) (hstep i (by omega)) (hq i hi)
  -- the known pair stays put
  have hkn : ∀ d, ((ρ (k1 + d)).node n).ns.known = ((ρ k1).node n).ns.known := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih => exact ((Q (k1 + d) (by omega)).1).trans ih
  have hknM : ∀ i, k1 ≤ i → ((ρ i).node n).ns.known = ((ρ k1).node n).ns.known := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact hkn d
  -- a round is always running: a start's reply would be an observation
  have obs_start : ∀ j, k1 ≤ j → acts j = .handle n → ∀ w, ((ρ j).node n).wait = some w →
      w.kind = .start → False := by
    intro j hj ha w hw hk
    exact hq j hj (Or.inr ⟨ha, w, hw, by rw [hk]; decide, fun h => by rw [hk] at h; cases h⟩)
  have kind_start : ∀ i, k ≤ i → ∀ w, ((ρ i).node n).wait = some w →
      ((ρ i).node n).ns.act = false → w.kind = .start := by
    intro i hi w hw ha
    have hiss := ((hK i hi).node.wait w hw).issue
    cases hkk : w.kind
    · rfl
    all_goals (rw [hkk] at hiss; exact absurd (hiss.1.symm.trans ha) (by decide))
  have act_true : ∀ i, k1 ≤ i → ((ρ i).node n).ns.act = true := by
    intro i hi
    cases ha : ((ρ i).node n).ns.act with
    | true => rfl
    | false =>
      exfalso
      cases hw : ((ρ i).node n).wait with
      | some w =>
        obtain ⟨j, hj, hh, hsame⟩ := reaches_handle ρ acts k1 hstep1 hfair.reply i hi
          (by rw [hw]; exact Option.some_ne_none _)
        have hwj : ((ρ j).node n).wait = some w := by rw [hsame]; exact hw
        exact obs_start j (by omega) hh w hwj (kind_start i (by omega) w hw ha)
      | none =>
        obtain ⟨j0, hj0, hiss⟩ := hfair.start i hi hw ha
        have h1 := hstep1 j0 (by omega)
        rw [hiss] at h1
        cases h1 with
        | issue _ _ post new emb1 rq _ _ _ _ _ _ hnode =>
          have hw1 : ((ρ (j0 + 1)).node n).wait =
              some ⟨.start, rq.map Req.slot, post, new, emb1⟩ := by rw [hnode, upd_same]
          obtain ⟨j, hj, hh, hsame⟩ := reaches_handle ρ acts k1 hstep1 hfair.reply (j0 + 1)
            (by omega) (by rw [hw1]; exact Option.some_ne_none _)
          have hwj : ((ρ j).node n).wait = some ⟨.start, rq.map Req.slot, post, new, emb1⟩ := by
            rw [hsame]; exact hw1
          exact obs_start j (by omega) hh _ hwj rfl
  -- so every step lowers the rank, or leaves the node alone
  obtain ⟨kb, hkb⟩ := hmaint
  have hSI : ∀ i, k1 ≤ i → NodeSettle.SInv (bctx st.recs (D n) ((ρ k1).node n).ns.known)
      ((ρ i).node n).ns := by
    intro i hi
    have h := (hK i (by omega)).node.inv.sinv st.recs (D n)
    rw [hknM i hi] at h
    exact h
  have mono : ∀ i, k1 + kb ≤ i →
      LexLe (rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ (i + 1)).node n).ns)
        (rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ i).node n).ns) ∧
      ((acts i = .core n .busy ∨ acts i = .handle n) →
        LexLt (rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ (i + 1)).node n).ns)
          (rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ i).node n).ns)) := by
    intro i hi
    obtain ⟨-, hbusy, hidle, hframe⟩ := Q i (by omega)
    have hbusy' : (acts i = .core n .busy ∨ acts i = .handle n) →
        LexLt (rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ (i + 1)).node n).ns)
          (rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ i).node n).ns) := by
      intro h
      have hb := hbusy h
      rw [hknM i (by omega)] at hb
      exact rank_busy (hSI i (by omega)) hb
    refine ⟨?_, hbusy'⟩
    by_cases h1 : acts i = .core n .busy
    · exact (hbusy' (Or.inl h1)).le
    by_cases h2 : acts i = .handle n
    · exact (hbusy' (Or.inr h2)).le
    by_cases h3 : acts i = .core n .idle
    · have h := act_true (i + 1) (by omega)
      rw [hidle h3] at h
      cases h
    by_cases h4 : acts i = .core n .maint
    · exact absurd h4 (hkb i (by omega))
    · rw [hframe h1 h2 h3 h4]
      exact Or.inr rfl
  obtain ⟨d0, hd0⟩ := lex_stabilizes 11
    (fun d => rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ (k1 + kb + d)).node n).ns)
    (fun _ => rank_length _ _) (fun d => (mono (k1 + kb + d) (by omega)).1)
  -- yet the running round's next own step, or the replies it waits on, comes
  have hev : ∃ j, k1 + kb + d0 ≤ j ∧ (acts j = .core n .busy ∨ acts j = .handle n) := by
    have hi : k1 ≤ k1 + kb + d0 := by omega
    have ha := act_true (k1 + kb + d0) hi
    cases hw : ((ρ (k1 + kb + d0)).node n).wait with
    | some w =>
      obtain ⟨j, hj, hh, -⟩ := reaches_handle ρ acts k1 hstep1 hfair.reply (k1 + kb + d0) hi
        (by rw [hw]; exact Option.some_ne_none _)
      exact ⟨j, hj, Or.inr hh⟩
    | none =>
      obtain ⟨j1, hj1, hc⟩ := hfair.core (k1 + kb + d0) hi hw ha
      rcases hc with ⟨ck, he⟩ | ⟨kk, he⟩
      · cases ck with
        | busy => exact ⟨j1, hj1, Or.inl he⟩
        | idle =>
          have h := act_true (j1 + 1) (by omega)
          rw [(Q j1 (by omega)).2.2.1 he] at h
          cases h
        | maint => exact absurd he (hkb j1 (by omega))
      · have h1 := hstep1 j1 (by omega)
        rw [he] at h1
        cases h1 with
        | issue _ _ post new emb1 rq _ _ _ _ _ _ hnode =>
          have hw1 : ((ρ (j1 + 1)).node n).wait =
              some ⟨kk, rq.map Req.slot, post, new, emb1⟩ := by rw [hnode, upd_same]
          obtain ⟨j, hj, hh, -⟩ := reaches_handle ρ acts k1 hstep1 hfair.reply (j1 + 1)
            (by omega) (by rw [hw1]; exact Option.some_ne_none _)
          exact ⟨j, by omega, Or.inr hh⟩
  obtain ⟨j, hj, hl⟩ := hev
  have hj' : k1 + kb + (j - (k1 + kb)) = j := by omega
  have hlt := (mono (k1 + kb + (j - (k1 + kb))) (by omega)).2 (by rw [hj']; exact hl)
  have e1 : rank (bctx st.recs (D n) ((ρ k1).node n).ns.known)
      ((ρ (k1 + kb + (j - (k1 + kb)))).node n).ns =
      rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ (k1 + kb + d0)).node n).ns :=
    hd0 (j - (k1 + kb)) (by omega)
  have e2 : rank (bctx st.recs (D n) ((ρ k1).node n).ns.known)
      ((ρ (k1 + kb + (j - (k1 + kb) + 1))).node n).ns =
      rank (bctx st.recs (D n) ((ρ k1).node n).ns.known) ((ρ (k1 + kb + d0)).node n).ns :=
    hd0 (j - (k1 + kb) + 1) (by omega)
  rw [show k1 + kb + (j - (k1 + kb) + 1) = k1 + kb + (j - (k1 + kb)) + 1 by omega] at e2
  rw [e1, e2] at hlt
  exact lexLt_irrefl _ hlt

/-- Node `n` in the system, from a well-formed start, once the hub has settled at `st` and the
node takes no reply answered before that and processes no notification but the stable hub's
(old ones may stay queued forever, never taken): just after its first fresh observation
it knows `st` under a label `H` of `st`'s head, and from there it settles at it, or sends a push
from it, an actual `issue n .push` labelled `emit`, which the stable hub would accept. Fair
scheduling of its events and housekeeping that writes stopping are assumed; nothing assumes a
round ends, nor `SimInv` anywhere. -/
theorem node_settles_entry (ρ : Nat → Sys) (acts : Nat → Act) (n k0 k k1 : Nat) (st : Snap)
    (hstep : ∀ i, k0 ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (h0 : RunOK law D n (ρ k0)) (hk : k0 ≤ k) (hk1 : k ≤ k1)
    (hstable : ∀ i, k ≤ i → (ρ i).hub = st)
    (hold : ∀ i, k1 ≤ i → ∀ r ∈ (ρ i).reps, r ∉ (ρ (i + 1)).reps → r.node = n →
      (ρ k).time ≤ r.time)
    (hnotes : ∀ i, k1 ≤ i → ∀ nt, acts i = .notice n nt → nt.snap = st)
    (hfair : Fair ρ acts n k1) (hmaint : ∃ kb, ∀ i, kb ≤ i → acts i ≠ .core n .maint) :
    ∃ k' H, k1 < k' ∧ H < ((ρ k').node n).ns.next ∧ ((ρ k').node n).emb H = st.head ∧
      ((∃ i, k' ≤ i ∧ labOf n ⟨st.seq, H, st.recs, D n⟩ (ρ i) (acts i) = .emit ∧
          ∃ post new, Emit ⟨st.seq, H, st.recs, D n⟩ ((ρ i).node n).ns post new) ∨
        ∃ K, ∀ i, K ≤ i → NodeSettle.Settled ⟨st.seq, H, st.recs, D n⟩ ((ρ i).node n).ns) := by
  have hK := runOK_run ρ acts hstep h0
  have hR : ∀ i, k ≤ i → StableReps (ρ k).time st (ρ i) := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    induction d with
    | zero => exact stable_init (hK k hk).time
    | succ d ih =>
      exact stable_step (ih (by omega)) (hstep _ (by omega)) (hstable _ (by omega))
        (hstable _ (by omega))
  obtain ⟨j, hj, ho⟩ := observes ρ acts n k k1 st (fun i hi => hstep i (by omega))
    (fun i hi => hK i (by omega)) hk1 hR hold hfair hmaint
  obtain ⟨H, I⟩ := entry_of_obs (hK j (by omega)) (hK (j + 1) (by omega)) (hR j (by omega))
    (hR (j + 1) (by omega)) (hold j hj) (hnotes j hj) (hstep j (by omega)) ho
  refine ⟨j + 1, H, by omega, I.hl, I.he, ?_⟩
  exact node_settles_sys ρ acts n k (j + 1) H st (fun i hi => hstep i (by omega)) (by omega)
    hstable (fun i hi => hold i (by omega)) (fun i hi => hnotes i (by omega)) I
    ⟨fun i hi => hfair.start i (by omega), fun i hi => hfair.core i (by omega),
      fun i hi => hfair.reply i (by omega)⟩ hmaint

end Entry

/-! ## Before the hub settles: EarlyEntry's events -/

/-- What a reply says once the hub's records are `R` and its sequence at least `sq`. -/
def CutAns (R sq : Nat) : Ans → Prop
  | .fetched s => sq ≤ s.seq ∧ s.recs = R
  | .head s => sq ≤ s.seq ∧ s.recs = R
  | .refused x => x = R
  | .objects => True

/-- Replies and notifications made since `t`, after the record cut, say what the hub said
then, and a push it accepted then had its records. -/
structure CutOK (R sq t : Nat) (g : Sys) : Prop where
  reps : ∀ r ∈ g.reps, t ≤ r.time →
    CutAns R sq r.ans ∧ (r.acc = true → ∀ p, r.req = .push p → p.recs = R)
  notes : ∀ nt ∈ g.notes, t ≤ nt.time → sq ≤ nt.snap.seq ∧ nt.snap.recs = R

section Cut

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act} {g g' : Sys}

theorem cutOK_init {R sq : Nat} (T : TimeOK g) : CutOK R sq g.time g :=
  ⟨fun r h ht => absurd ht (by have := T.reps r h; omega),
    fun x h ht => absurd ht (by have := T.notes x h; omega)⟩

theorem cutOK_sub {R sq t : Nat} (C : CutOK R sq t g) (hr : ∀ r ∈ g'.reps, r ∈ g.reps)
    (hn : ∀ x ∈ g'.notes, x ∈ g.notes) : CutOK R sq t g' :=
  ⟨fun r h ht => C.reps r (hr r h) ht, fun x h ht => C.notes x (hn x h) ht⟩

/-- With the hub's records `R` and its sequence at least `sq` before and after, a step keeps
`CutOK`. -/
theorem cutOK_step {R sq t : Nat} (C : CutOK R sq t g) (hs : SysStep N D law a g g')
    (hh : g.hub.recs = R ∧ sq ≤ g.hub.seq) (hh' : g'.hub.recs = R ∧ sq ≤ g'.hub.seq) :
    CutOK R sq t g' := by
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ =>
    exact cutOK_sub C (fun r h => by rw [hq.reps] at h; exact h)
      (fun x h => by rw [hq.notes] at h; exact h)
  | idle _ _ _ _ _ _ _ hq _ =>
    exact cutOK_sub C (fun r h => by rw [hq.reps] at h; exact h)
      (fun x h => by rw [hq.notes] at h; exact h)
  | maint _ _ _ _ _ _ _ _ _ _ hq _ =>
    exact cutOK_sub C (fun r h => by rw [hq.reps] at h; exact h)
      (fun x h => by rw [hq.notes] at h; exact h)
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ _ =>
    exact cutOK_sub C (fun r h => by rw [hrest.2.1] at h; exact h)
      (fun x h => by rw [hrest.2.2] at h; exact h)
  | answer r ans _ _ acc hans hreps _ _ =>
    refine ⟨fun x hx ht' => ?_, fun x hx ht' => ?_⟩
    · rw [hreps, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact C.reps x hx ht'
      · show CutAns R sq ans ∧ (acc = true → ∀ p, r.body = .push p → p.recs = R)
        rcases hans with ⟨-, ha, he, -⟩ | ⟨-, ha, he, -⟩ |
          ⟨p, hb, ⟨hacc, ha, -, he, -⟩ | ⟨-, ha, -, he, -⟩ | ⟨-, ha, -, he, -⟩⟩
        · rw [he]; exact ⟨⟨hh.2, hh.1⟩, fun h => by rw [ha] at h; cases h⟩
        · rw [he]; exact ⟨trivial, fun h => by rw [ha] at h; cases h⟩
        · rw [he]
          refine ⟨⟨hh'.2, hh'.1⟩, fun _ p' hp' => ?_⟩
          rw [hb] at hp'
          cases hp'
          rw [(law.guards g.hub g.par p hacc).1]
          exact hh.1
        · rw [he]; exact ⟨hh.1, fun h => by rw [ha] at h; cases h⟩
        · rw [he]; exact ⟨⟨hh.2, hh.1⟩, fun h => by rw [ha] at h; cases h⟩
    · have hn : g'.notes = g.notes ∨
          g'.notes = g.notes ++ (List.range N).map (fun m => ⟨m, g.time, g'.hub⟩) := by
        rcases hans with ⟨-, -, -, -, hn⟩ | ⟨-, -, -, -, hn⟩ |
          ⟨p, -, ⟨-, -, -, -, hn⟩ | ⟨-, -, -, -, -, hn⟩ | ⟨-, -, -, -, -, hn⟩⟩
        all_goals first | exact Or.inl hn | exact Or.inr hn
      rcases hn with hn | hn <;> rw [hn] at hx
      · exact C.notes x hx ht'
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact C.notes x hx ht'
        · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
          exact ⟨hh'.2, hh'.1⟩
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hreps hrest _ =>
    exact cutOK_sub C (fun r h => ((hreps r).1 h).1) (fun x h => by rw [hrest.2.2.1] at h; exact h)
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnotes hrest _ =>
    exact cutOK_sub C (fun r h => by rw [hrest.2.2.1] at h; exact h)
      (fun x h => (by rw [hnotes] at h; exact List.mem_of_mem_erase h))
  | ignore _ _ _ _ _ _ _ _ hnotes hrest _ =>
    exact cutOK_sub C (fun r h => by rw [hrest.2.2.1] at h; exact h)
      (fun x h => (by rw [hnotes] at h; exact List.mem_of_mem_erase h))
  | env _ _ hq _ =>
    exact cutOK_sub C (fun r h => by rw [hq.reps] at h; exact h)
      (fun x h => by rw [hq.notes] at h; exact h)

end Cut

open Classical in
/-- EarlyEntry's label for the replies to node `n`'s step of kind `k`: a start; a poll; a push
answered by a `Head`; and otherwise, a request for objects or a refused push, a step. -/
noncomputable def hlab (n : Nat) (g g' : Sys) (k : Kind) : ELab :=
  match k with
  | .start => .start
  | .fetchObjs => .step
  | .push =>
    if ∃ r ∈ g.reps, r ∉ g'.reps ∧ r.node = n ∧ ∃ s, r.ans = .head s then .push else .step
  | .fetchPoll => .poll
  | .differPoll => .poll
  | .writePoll => .poll

/-- What a system step is to node `n`'s core before the hub settles, in EarlyEntry's terms. -/
noncomputable def elabOf (n : Nat) (g : Sys) (a : Act) (g' : Sys) : ELab :=
  match a with
  | .core m .busy => if m = n then .step else .frame
  | .core m .idle => if m = n then .idle else .frame
  | .core m .maint => if m = n then .maint else .frame
  | .handle m => if m = n then (g.node n).wait.elim .frame (fun w => hlab n g g' w.kind)
      else .frame
  | .notice m _ => if m = n then .notify else .frame
  | _ => .frame

theorem hlab_ne {n : Nat} {g g' : Sys} {k : Kind} (hk : k ≠ .start) :
    hlab n g g' k ≠ .start ∧ hlab n g g' k ≠ .notify ∧ hlab n g g' k ≠ .frame ∧
      hlab n g g' k ≠ .maint := by
  cases k <;> simp only [hlab]
  · exact absurd rfl hk
  all_goals first
    | (split <;> exact ⟨fun h => ELab.noConfusion h, fun h => ELab.noConfusion h,
        fun h => ELab.noConfusion h, fun h => ELab.noConfusion h⟩)
    | exact ⟨fun h => ELab.noConfusion h, fun h => ELab.noConfusion h,
        fun h => ELab.noConfusion h, fun h => ELab.noConfusion h⟩

theorem elab_maint {n : Nat} {g g' : Sys} {a : Act} (h : elabOf n g a g' = .maint) :
    a = .core n .maint := by
  cases a with
  | core m ck =>
    cases ck <;> simp only [elabOf] at h <;> split at h <;> try cases h
    rename_i hmn
    rw [hmn]
  | handle m =>
    simp only [elabOf] at h
    split at h
    · cases hw : (g.node n).wait with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h
        by_cases hk : w.kind = .start
        · simp only [Option.elim, hk, hlab] at h; cases h
        · exact absurd h (hlab_ne hk).2.2.2
    · cases h
  | notice m _ => simp only [elabOf] at h; split at h <;> cases h
  | issue _ _ => simp [elabOf] at h
  | ignore _ => simp [elabOf] at h
  | answer => simp [elabOf] at h
  | env => simp [elabOf] at h

theorem fetchAny_mk {c : Ctx} {R sq : Nat} {σ σ' : NS} (hk : σ'.known = (c.S, c.H))
    (hS : sq ≤ c.S) (hR : c.R = R) (hann : σ'.annc = some c.R ∨ (σ'.annc = none ∧ c.R = σ.ap))
    (hap : σ'.ap = σ.ap) (hact : σ'.act = σ.act) (I : LInv σ') : FetchAny R sq σ σ' :=
  ⟨by rw [hk]; exact hS, by rw [← hR]; exact hann, hap, hact, I⟩

theorem headAny_mk {c : Ctx} {sq : Nat} {σ σ' : NS} (hk : σ'.known = (c.S, c.H))
    (hS : sq ≤ c.S) (hann : σ'.annc = σ.annc) (hap : σ'.ap = σ.ap) (hact : σ'.act = σ.act)
    (I : LInv σ') : HeadAny sq σ σ' :=
  ⟨by rw [hk]; exact hS, hann, hap, hact, I⟩

theorem writeRes_annc {σ σ1 : NS} {new : Nat} (W : WriteRes σ σ1 new) : σ1.annc = σ.annc := by
  obtain ⟨y, -, (⟨-, F⟩ | ⟨-, he, -⟩)⟩ := W
  · exact F.ext.annc
  · subst he; rfl

theorem writeRes_act {σ σ1 : NS} {new : Nat} (W : WriteRes σ σ1 new) : σ1.act = σ.act := by
  obtain ⟨y, -, (⟨-, F⟩ | ⟨-, he, -⟩)⟩ := W
  · exact F.ext.act
  · subst he; rfl

section Early

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act} {g g' : Sys} {n : Nat}

/-- After the record cut, the replies node `n` takes and the notification it processes being
made since then, each step of the system is one of EarlyEntry's events of node `n`'s core
(`elabOf`). The graph's growth by learning is in each event's `LInv` of the state after, which
`nodeOK_step` keeps. -/
theorem eev_step {R sq t : Nat} (K : RunOK law D n g) (K' : RunOK law D n g')
    (C : CutOK R sq t g) (hold : ∀ r ∈ g.reps, r ∉ g'.reps → r.node = n → t ≤ r.time)
    (hnold : ∀ nt, a = .notice n nt → t ≤ nt.time) (hs : SysStep N D law a g g') :
    EEv R sq (D n) (elabOf n g a g') (g.node n).ns (g'.node n).ns := by
  cases hs with
  | busy m σ' emb' hw ha hsl hg hnode hq ht =>
    by_cases hm : m = n
    · subst hm
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      have hl0 : elabOf m g (.core m .busy) g' = .step := by simp [elabOf]
      rw [hl0, e]
      exact .step ha (loc_busy hsl (K.node.inv.sinv R (D m)) rfl hg.next) (loc_known hsl)
    · have e : (g'.node n).ns = (g.node n).ns := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hl0 : elabOf n g (.core m .busy) g' = .frame := by simp [elabOf, hm]
      rw [hl0, e]; exact .frame
  | idle m σ' hw ha hsl hnode hr hq ht =>
    by_cases hm : m = n
    · subst hm
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      have hl0 : elabOf m g (.core m .idle) g' = .idle := by simp [elabOf]
      rw [hl0, e]
      exact .idle ha (idle_congr hsl rfl)
    · have e : (g'.node n).ns = (g.node n).ns := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hl0 : elabOf n g (.core m .idle) g' = .frame := by simp [elabOf, hm]
      rw [hl0, e]; exact .frame
  | maint m σ1 σ' emb' hw ha hsl hx hg hnode hq ht =>
    by_cases hm : m = n
    · subst hm
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      have hl0 : elabOf m g (.core m .maint) g' = .maint := by simp [elabOf]
      rw [hl0, e]
      exact .maint ha (idle_congr hsl rfl) hx
    · have e : (g'.node n).ns = (g.node n).ns := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hl0 : elabOf n g (.core m .maint) g' = .frame := by simp [elabOf, hm]
      rw [hl0, e]; exact .frame
  | issue m k post new emb1 rq hw hissue hg hb hslot hnodup hnode hreqs hslot' hrest ht hnd =>
    have e : (g'.node n).ns = (g.node n).ns := by
      by_cases hm : m = n
      · subst hm; rw [hnode, upd_same]
      · rw [hnode, upd_ne _ _ (Ne.symm hm)]
    have hl0 : elabOf n g (.issue m k) g' = .frame := by simp [elabOf]
    rw [hl0, e]; exact .frame
  | answer r ans hr hreqs acc hans hreps hrest ht =>
    have e : (g'.node n).ns = (g.node n).ns := by rw [hrest.1]
    have hl0 : elabOf n g .answer g' = .frame := by simp [elabOf]
    rw [hl0, e]; exact .frame
  | handle m w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf hh hnode hreps hrest ht =>
    by_cases hm : m = n
    · subst hm
      have W := K.node.wait w hw
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      have I' : LInv σ' := by have h := K'.node.inv; rw [e] at h; exact h
      have hcut : ∀ r ∈ rs, CutAns R sq r.ans ∧
          (r.acc = true → ∀ p, r.req = .push p → p.recs = R) :=
        fun r hr => C.reps r (hrs r hr).1
          (hold r (hrs r hr).1 (fun h => ((hreps r).1 h).2 hr) (hrs r hr).2.1)
      have hσi : σi.ap = (g.node m).ns.ap ∧ σi.annc = (g.node m).ns.annc ∧
          σi.act = (g.node m).ns.act := by
        have h1 := congrArg NS.ap hl.ctl.1
        have h2 := congrArg NS.annc hl.ctl.1
        have h3 := congrArg NS.act hl.ctl.1
        exact ⟨h1, h2, h3⟩
      -- a reply naming a head says a sequence from after the cut, and the records `R`
      have hctx : ∀ r ∈ rs, (∃ s, r.ans = .fetched s ∨ r.ans = .head s) → sq ≤ c.S ∧ c.R = R := by
        intro r hr hsnap
        obtain ⟨s, hs⟩ := hsnap
        have h1 := hf r hr
        have h2 := (hcut r hr).1
        rcases hs with hs | hs <;> rw [hs] at h1 h2 <;>
          exact ⟨by rw [h1.1]; exact h2.1, h1.2.2.2.trans h2.2⟩
      have hfetch : w.kind ≠ .push → w.kind ≠ .fetchObjs → sq ≤ c.S ∧ c.R = R := by
        intro hk1 hk2
        obtain ⟨s0, rest, hs0⟩ := List.exists_cons_of_ne_nil W.slots
        obtain ⟨r0, hr0, hr0s⟩ := hcov s0 (by rw [hs0]; exact List.mem_cons_self)
        have hbf := W.reps r0 (hrs r0 hr0).1 (hrs r0 hr0).2.1 (hrs r0 hr0).2.2
        have hreq : r0.req = .fetch := hbf.2 (by rw [hs0, hr0s]; rfl) hk1 hk2
        obtain ⟨s, hs⟩ := K.sys.fetch r0 (hrs r0 hr0).1 hreq
        exact hctx r0 hr0 ⟨s, Or.inl hs⟩
      have hi := W.issue
      cases hk : w.kind with
      | start =>
        rw [hk] at hi hh
        obtain ⟨hS, hR⟩ := hfetch (by rw [hk]; decide) (by rw [hk]; decide)
        have e2 : posti = σi := hl.same hi.2
        obtain ⟨σ1, F, he⟩ := hh
        have hl0 : elabOf m g (.handle m) g' = .start := by simp [elabOf, hw, hk, hlab]
        rw [hl0, e]
        refine .start hi.1 (fetchAny_mk F.known hS hR ?_ (F.ap.trans hσi.1)
          (F.act.trans hσi.2.2) ?_) he
        · rw [← hσi.1]; exact F.annc
        · rw [he] at I'
          exact ⟨I'.parLt, I'.knownLt, I'.headsNe, I'.headsLt, I'.imgNe, I'.imgLt⟩
      | fetchPoll =>
        rw [hk] at hi hh
        obtain ⟨hS, hR⟩ := hfetch (by rw [hk]; decide) (by rw [hk]; decide)
        obtain ⟨σ1, F, ho⟩ := hh
        have hσ' : σ'.known = σ1.known ∧ σ'.annc = σ1.annc ∧ σ'.ap = σ1.ap ∧
            σ'.act = σ1.act := by
          rcases ho with ⟨-, O⟩ | ⟨-, rfl⟩
          · have h1 := congrArg NS.known O.rest
            have h2 := congrArg NS.annc O.rest
            have h3 := congrArg NS.ap O.rest
            have h4 := congrArg NS.act O.rest
            exact ⟨h1, h2, h3, h4⟩
          · exact ⟨rfl, rfl, rfl, rfl⟩
        have hl0 : elabOf m g (.handle m) g' = .poll := by simp [elabOf, hw, hk, hlab]
        rw [hl0, e]
        refine .poll hi.1 (go_congr rfl hi.2.1)
          (fetchAny_mk (hσ'.1.trans F.known) hS hR ?_ (hσ'.2.2.1.trans (F.ap.trans hσi.1))
            (hσ'.2.2.2.trans (F.act.trans hσi.2.2)) I')
        rw [hσ'.2.1, ← hσi.1]
        exact F.annc
      | fetchObjs =>
        rw [hk] at hi hh
        have hnohead : ∀ r ∈ rs, r.ans.head? = none := by
          intro r hr
          rw [K.objs.ans r (hrs r hr).1
            (K.objs.reps w hw hk r (hrs r hr).1 (hrs r hr).2.1 (hrs r hr).2.2)]
          rfl
        have hdn : hd = none := by
          cases hd' : hd with
          | none => rfl
          | some h =>
            obtain ⟨r, hr, hrh⟩ := hhd' h hd'
            rw [hnohead r hr] at hrh
            cases hrh
        obtain ⟨rfl, rfl, rfl⟩ := hl.nothing (fun h hh' => by rw [hdn] at hh'; cases hh')
        have O : ObjRep (norm (g.node m).ns) σ' (fun x => Walk (g.node m).ns x ∧
            ¬ (g.node m).ns.loc x ∧ (g.node m).ns.stg x ∧ ¬ (g.node m).ns.obj x) := hh
        have hl0 : elabOf m g (.handle m) g' = .step := by simp [elabOf, hw, hk, hlab]
        rw [hl0, e]
        refine .step hi.1 (issue_busy (c := bctx R (D m) (g.node m).ns.known)
          (as := rs.map Rep.ans) hi (by decide) hh rfl (fun h => by cases h)
          (fun h => by cases h)) ?_
        have h1 := congrArg NS.known O.rest
        exact h1
      | differPoll =>
        rw [hk] at hi hh
        obtain ⟨hS, hR⟩ := hfetch (by rw [hk]; decide) (by rw [hk]; decide)
        have hl0 : elabOf m g (.handle m) g' = .poll := by simp [elabOf, hw, hk, hlab]
        rw [hl0, e]
        exact .poll hi.1 (go_congr rfl hi.2.1) (fetchAny_mk hh.known hS hR
          (by rw [← hσi.1]; exact hh.annc) (hh.ap.trans hσi.1) (hh.act.trans hσi.2.2) I')
      | writePoll =>
        -- the write, then the poll: what is announced, applied and running is as it was
        rw [hk] at hi hh
        obtain ⟨hS, hR⟩ := hfetch (by rw [hk]; decide) (by rw [hk]; decide)
        have hw' := hi.2.2.2.2.2.2.2.2.1
        have hpa : posti.ap = w.post.ap ∧ posti.act = w.post.act := by
          have h1 := congrArg NS.ap hl.ctl.2
          have h2 := congrArg NS.act hl.ctl.2
          exact ⟨h1, h2⟩
        have hap : posti.ap = (g.node m).ns.ap := by
          rw [hpa.1]; have h := write_ap hw'; exact h
        have hact : posti.act = (g.node m).ns.act := by
          rw [hpa.2]; have h := writeRes_act hw'; exact h
        have hl0 : elabOf m g (.handle m) g' = .poll := by simp [elabOf, hw, hk, hlab]
        rw [hl0, e]
        exact .poll hi.1 (go_congr rfl hi.2.1) (fetchAny_mk hh.known hS hR
          (by rw [← hap]; exact hh.annc) (hh.ap.trans hap) (hh.act.trans hact) I')
      | push =>
        rw [hk] at hi hh
        by_cases hex : ∃ r ∈ g.reps, r ∉ g'.reps ∧ r.node = m ∧ ∃ s, r.ans = .head s
        · have hl0 : elabOf m g (.handle m) g' = .push := by simp [elabOf, hw, hk, hlab, hex]
          obtain ⟨r, hrg, hrg', hrn, s, hs⟩ := hex
          have hr : r ∈ rs := Classical.byContradiction fun h => hrg' ((hreps r).2 ⟨hrg, h⟩)
          obtain ⟨hS, hR⟩ := hctx r hr ⟨s, Or.inr hs⟩
          -- the push's records were `R`
          obtain ⟨p, hp', hpr⟩ := (W.reps r (hrs r hr).1 (hrs r hr).2.1 (hrs r hr).2.2).1 hk
          have hpR : p.recs = R := by
            cases hacc : r.acc with
            | true => exact (hcut r hr).2 hacc p hp'
            | false =>
              have h1 := (K.sys.push r (hrs r hr).1 p hp' hacc).2 s hs
              have h2 := (hcut r hr).1
              rw [hs] at h2
              exact h1.trans h2.2
          have hw' := hi.2.2.2.2.2.2.2.2.1
          have hpost : w.post.ap = (g.node m).ns.ap := by have h := write_ap hw'; exact h
          have hap : (g.node m).ns.ap = R := by rw [← hpost, ← hpr, hpR]
          have F : HeadRep c posti σ' := by
            rcases hh with ⟨-, hne, -⟩ | ⟨-, -, F⟩ | ⟨-, hne, -⟩
            · exact absurd (by rw [hσi.1, hap, hR]) hne
            · exact F
            · exact absurd (by rw [hσi.1, hap, hR]) hne
          have hpa : posti.annc = w.post.annc ∧ posti.ap = w.post.ap ∧
              posti.act = w.post.act := by
            have h1 := congrArg NS.annc hl.ctl.2
            have h2 := congrArg NS.ap hl.ctl.2
            have h3 := congrArg NS.act hl.ctl.2
            exact ⟨h1, h2, h3⟩
          rw [hl0, e]
          refine .push hi.1 (go_congr rfl hi.2.1) hap hi.2.2.2.2.2.1
            (headAny_mk F.known hS ?_ ?_ ?_ I')
          · rw [F.annc, hpa.1]; have h := writeRes_annc hw'; exact h
          · rw [F.ap, hpa.2.1]; have h := write_ap hw'; exact h
          · rw [F.act, hpa.2.2]; have h := writeRes_act hw'; exact h
        · have hl0 : elabOf m g (.handle m) g' = .step := by simp [elabOf, hw, hk, hlab, hex]
          have hno : ∀ r ∈ rs, ¬ ∃ s, r.ans = .head s := fun r hr hs' =>
            hex ⟨r, (hrs r hr).1, fun h => ((hreps r).1 h).2 hr, (hrs r hr).2.1, hs'⟩
          have hnohead : ∀ r ∈ rs, r.ans.head? = none := by
            intro r hr
            obtain ⟨p, hp', -⟩ := (W.reps r (hrs r hr).1 (hrs r hr).2.1 (hrs r hr).2.2).1 hk
            rcases K.sys.pushAns r (hrs r hr).1 p hp' with ⟨x, hx⟩ | ⟨s, hs⟩
            · rw [hx]; rfl
            · exact absurd ⟨s, hs⟩ (hno r hr)
          have hdn : hd = none := by
            cases hd' : hd with
            | none => rfl
            | some h =>
              obtain ⟨r, hr, hrh⟩ := hhd' h hd'
              rw [hnohead r hr] at hrh
              cases hrh
          obtain ⟨rfl, rfl, rfl⟩ := hl.nothing (fun h hh' => by rw [hdn] at hh'; cases hh')
          have hrefuse : ∃ x, Ans.refused x ∈ rs.map Rep.ans ∧ (g.node m).ns.ap ≠ c.R ∧
              σ' = { w.post with hubRecs := some c.R } := by
            rcases hh with ⟨⟨x, hx⟩, hne, he⟩ | ⟨⟨s, hs⟩, -⟩ | ⟨⟨s, hs⟩, -⟩
            · exact ⟨x, hx, hne, he⟩
            · obtain ⟨r, hr, hra⟩ := List.mem_map.1 hs; exact absurd ⟨s, hra⟩ (hno r hr)
            · obtain ⟨r, hr, hra⟩ := List.mem_map.1 hs; exact absurd ⟨s, hra⟩ (hno r hr)
          obtain ⟨x, hx, hne, he⟩ := hrefuse
          obtain ⟨r, hr, hra⟩ := List.mem_map.1 hx
          have h1 : c.R = x := by have h := hf r hr; rw [hra] at h; exact h
          have h2 : x = R := by have h := (hcut r hr).1; rw [hra] at h; exact h
          rw [h1.trans h2] at hne he
          have hh' : Handle (bctx R (D m) (g.node m).ns.known) (g.node m).ns .push w.post
              (rs.map Rep.ans) σ' := Or.inl ⟨⟨x, hx⟩, hne, he⟩
          rw [hl0, e]
          refine .step hi.1 (issue_busy hi (by decide) hh' rfl (fun _ h => ?_) (fun _ hc' => ?_)) ?_
          · have h1 := congrArg Prod.fst h
            simp only [bctx] at h1
            omega
          · obtain ⟨⟨s, hs⟩, -⟩ := hc'
            obtain ⟨r', hr', hra'⟩ := List.mem_map.1 hs
            exact hno r' hr' ⟨s, hra'⟩
          · rw [he]
            have h := writeRes_known hi.2.2.2.2.2.2.2.2.1
            exact h
    · have e : (g'.node n).ns = (g.node n).ns := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hl0 : elabOf n g (.handle m) g' = .frame := by simp [elabOf, hm]
      rw [hl0, e]; exact .frame
  | notice m nt c σi posti σ' embi hw ha hn hnn hnew hl hc hf hh hnode hnotes hrest ht =>
    by_cases hm : m = n
    · subst hm
      have e : (g'.node m).ns = σ' := by rw [hnode, upd_same]
      have I' : LInv σ' := by have h := K'.node.inv; rw [e] at h; exact h
      have hl0 : elabOf m g (.notice m nt) g' = .notify := by simp [elabOf]
      have hcn := C.notes nt hn (hnold _ rfl)
      have hS : sq ≤ c.S := by rw [hf.1]; exact hcn.1
      have h1 := congrArg NS.annc hl.ctl.1
      have h2 := congrArg NS.ap hl.ctl.1
      have h3 := congrArg NS.act hl.ctl.1
      rw [hl0, e]
      exact .notify ha (headAny_mk hh.known hS (hh.annc.trans h1) (hh.ap.trans h2)
        (hh.act.trans h3) I')
    · have e : (g'.node n).ns = (g.node n).ns := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hl0 : elabOf n g (.notice m nt) g' = .frame := by simp [elabOf, hm]
      rw [hl0, e]; exact .frame
  | ignore m _ _ _ _ _ _ hnode _ _ _ =>
    have e : (g'.node n).ns = (g.node n).ns := by rw [hnode]
    have hl0 : elabOf n g (.ignore m) g' = .frame := by simp [elabOf]
    rw [hl0, e]; exact .frame
  | env _ hnode _ _ =>
    have e : (g'.node n).ns = (g.node n).ns := by rw [hnode]
    have hl0 : elabOf n g .env g' = .frame := by simp [elabOf]
    rw [hl0, e]; exact .frame

end Early

section EarlyRun

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}

/-- EarlyEntry over the system: after the record cut (the hub's records `R` and its sequence at
least `sq` from `kr` on), once node `n` takes no reply and processes no notification made
before it (old ones may stay queued, never taken), a fair eligible node comes to have `R`
applied and to know a pair from after the cut, and keeps both. From a well-formed start;
housekeeping that writes is assumed to stop; nothing assumes a round ends or the hub
settles. -/
theorem early_entry_sys (ρ : Nat → Sys) (acts : Nat → Act) (n k0 kr k1 R sq : Nat)
    (hstep : ∀ i, k0 ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (h0 : RunOK law D n (ρ k0)) (hk : k0 ≤ kr) (hk1 : kr ≤ k1)
    (hrec : ∀ i, kr ≤ i → (ρ i).hub.recs = R ∧ sq ≤ (ρ i).hub.seq)
    (hold : ∀ i, k1 ≤ i → ∀ r ∈ (ρ i).reps, r ∉ (ρ (i + 1)).reps → r.node = n →
      (ρ kr).time ≤ r.time)
    (hnold : ∀ i, k1 ≤ i → ∀ nt, acts i = .notice n nt → (ρ kr).time ≤ nt.time)
    (hE : ∀ i, k1 ≤ i → ¬ ∃ y ∈ ((ρ i).node n).ns.heads, D n R y)
    (hfair : Fair ρ acts n k1) (hmaint : ∃ kb, ∀ i, kb ≤ i → acts i ≠ .core n .maint) :
    ∃ k, k1 ≤ k ∧ ∀ i, k ≤ i → Entry R sq ((ρ i).node n).ns := by
  have hK := runOK_run ρ acts hstep h0
  have hC : ∀ i, kr ≤ i → CutOK R sq (ρ kr).time (ρ i) := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    induction d with
    | zero => exact cutOK_init (hK kr hk).time
    | succ d ih =>
      exact cutOK_step (ih (by omega)) (hstep _ (by omega)) (hrec _ (by omega))
        (hrec _ (by omega))
  have hstep1 : ∀ i, k1 ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)) :=
    fun i hi => hstep i (by omega)
  have hev : ∀ i, k1 ≤ i → EEv R sq (D n) (elabOf n (ρ i) (acts i) (ρ (i + 1)))
      ((ρ i).node n).ns ((ρ (i + 1)).node n).ns := fun i hi =>
    eev_step (hK i (by omega)) (hK (i + 1) (by omega)) (hC i (by omega)) (hold i hi) (hnold i hi)
      (hstep i (by omega))
  -- the kind of a step's wait follows from whether the round is running
  have kind_of : ∀ i, k0 ≤ i → ∀ w, ((ρ i).node n).wait = some w →
      (w.kind = .start ↔ ((ρ i).node n).ns.act = false) := by
    intro i hi w hw
    have hiss := ((hK i hi).node.wait w hw).issue
    constructor
    · intro hk
      rw [hk] at hiss
      exact hiss.1
    · intro ha
      cases hkk : w.kind
      · rfl
      all_goals (rw [hkk] at hiss; exact absurd (hiss.1.symm.trans ha) (by decide))
  have lab_handle : ∀ j, acts j = .handle n → ∀ w, ((ρ j).node n).wait = some w →
      elabOf n (ρ j) (acts j) (ρ (j + 1)) = hlab n (ρ j) (ρ (j + 1)) w.kind := by
    intro j hj w hw
    rw [hj]
    simp [elabOf, hw]
  -- the replies to a step of a running round are a step, a poll or a push
  have handle_core : ∀ j, acts j = .handle n → ∀ w, ((ρ j).node n).wait = some w →
      w.kind ≠ .start → (elabOf n (ρ j) (acts j) (ρ (j + 1)) = .step ∨
        elabOf n (ρ j) (acts j) (ρ (j + 1)) = .idle ∨
        elabOf n (ρ j) (acts j) (ρ (j + 1)) = .poll ∨
        elabOf n (ρ j) (acts j) (ρ (j + 1)) = .push ∨
        elabOf n (ρ j) (acts j) (ρ (j + 1)) = .maint) := by
    intro j hj w hw hk
    rw [lab_handle j hj w hw]
    have hne := hlab_ne (n := n) (g := ρ j) (g' := ρ (j + 1)) hk
    cases hl : hlab n (ρ j) (ρ (j + 1)) w.kind
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact absurd hl hne.1
    · exact absurd hl hne.2.1
    · exact absurd hl hne.2.2.1
  refine early_entry R sq (D n) (fun i => ((ρ i).node n).ns)
    (fun i => elabOf n (ρ i) (acts i) (ρ (i + 1))) k1 hev (hK k1 (by omega)).node.inv ?_ hE ?_ ?_
  · obtain ⟨kb, hkb⟩ := hmaint
    exact ⟨kb, fun i hi h => hkb i hi (elab_maint h)⟩
  · intro i hi ha
    cases hw : ((ρ i).node n).wait with
    | some w =>
      obtain ⟨j, hj, hh, hsame⟩ := reaches_handle ρ acts k1 hstep1 hfair.reply i hi
        (by rw [hw]; exact Option.some_ne_none _)
      have hwj : ((ρ j).node n).wait = some w := by rw [hsame]; exact hw
      have hk : w.kind = .start := (kind_of i (by omega) w hw).2 ha
      refine ⟨j, hj, ?_⟩
      show elabOf n (ρ j) (acts j) (ρ (j + 1)) = .start
      rw [lab_handle j hh w hwj, hk]
      rfl
    | none =>
      obtain ⟨j0, hj0, hiss⟩ := hfair.start i hi hw ha
      have h1 := hstep1 j0 (by omega)
      rw [hiss] at h1
      cases h1 with
      | issue _ _ post new emb1 rq _ _ _ _ _ _ hnode =>
        have hw1 : ((ρ (j0 + 1)).node n).wait =
            some ⟨.start, rq.map Req.slot, post, new, emb1⟩ := by rw [hnode, upd_same]
        obtain ⟨j, hj, hh, hsame⟩ := reaches_handle ρ acts k1 hstep1 hfair.reply (j0 + 1)
          (by omega) (by rw [hw1]; exact Option.some_ne_none _)
        have hwj : ((ρ j).node n).wait = some ⟨.start, rq.map Req.slot, post, new, emb1⟩ := by
          rw [hsame]; exact hw1
        refine ⟨j, by omega, ?_⟩
        show elabOf n (ρ j) (acts j) (ρ (j + 1)) = .start
        rw [lab_handle j hh _ hwj]
        rfl
  · intro i hi ha
    show ∃ j, i ≤ j ∧ (elabOf n (ρ j) (acts j) (ρ (j + 1)) = .step ∨
      elabOf n (ρ j) (acts j) (ρ (j + 1)) = .idle ∨ elabOf n (ρ j) (acts j) (ρ (j + 1)) = .poll ∨
      elabOf n (ρ j) (acts j) (ρ (j + 1)) = .push ∨ elabOf n (ρ j) (acts j) (ρ (j + 1)) = .maint)
    have after : ∀ i', k1 ≤ i' → ((ρ i').node n).ns.act = true → ((ρ i').node n).wait ≠ none →
        ∃ j, i' ≤ j ∧ (elabOf n (ρ j) (acts j) (ρ (j + 1)) = .step ∨
          elabOf n (ρ j) (acts j) (ρ (j + 1)) = .idle ∨
          elabOf n (ρ j) (acts j) (ρ (j + 1)) = .poll ∨
          elabOf n (ρ j) (acts j) (ρ (j + 1)) = .push ∨
          elabOf n (ρ j) (acts j) (ρ (j + 1)) = .maint) := by
      intro i' hi' ha' hw'
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hw'
      obtain ⟨j, hj, hh, hsame⟩ := reaches_handle ρ acts k1 hstep1 hfair.reply i' hi' hw'
      have hwj : ((ρ j).node n).wait = some w := by rw [hsame]; exact hw
      have hk : w.kind ≠ .start := fun hk => by
        have := (kind_of i' (by omega) w hw).1 hk
        rw [ha'] at this
        cases this
      exact ⟨j, hj, handle_core j hh w hwj hk⟩
    cases hw : ((ρ i).node n).wait with
    | some w => exact after i hi ha (by rw [hw]; exact Option.some_ne_none _)
    | none =>
      obtain ⟨j1, hj1, hc⟩ := hfair.core i hi hw ha
      have hab1 : (acts j1).about n := by
        rcases hc with ⟨ck, he⟩ | ⟨kk, he⟩ <;> simp [he, Act.about]
      obtain ⟨j0, hj0, hab, hsame⟩ := reaches_own ρ acts k1 hstep1 i hi ⟨j1, hj1, hab1⟩
      have hstp := hstep1 j0 (by omega)
      cases ha0 : acts j0 with
      | core m ck =>
        rw [ha0] at hab
        simp only [Act.about] at hab
        subst hab
        refine ⟨j0, hj0, ?_⟩
        rw [ha0]
        cases ck <;> simp [elabOf]
      | issue m kk =>
        rw [ha0] at hab hstp
        simp only [Act.about] at hab
        subst hab
        cases hstp with
        | issue _ _ post new emb1 rq _ _ _ _ _ _ hnode =>
          have hw1 : ((ρ (j0 + 1)).node m).wait =
              some ⟨kk, rq.map Req.slot, post, new, emb1⟩ := by rw [hnode, upd_same]
          have ha1 : ((ρ (j0 + 1)).node m).ns.act = true := by
            rw [hnode, upd_same]; show ((ρ j0).node m).ns.act = true; rw [hsame]; exact ha
          obtain ⟨j, hj, hl⟩ := after (j0 + 1) (by omega) ha1
            (by rw [hw1]; exact Option.some_ne_none _)
          exact ⟨j, by omega, hl⟩
      | handle m =>
        rw [ha0] at hab hstp
        simp only [Act.about] at hab
        subst hab
        cases hstp with
        | handle _ _ _ _ _ _ _ _ _ hw' =>
          rw [hsame, hw] at hw'
          cases hw'
      | notice m _ =>
        rw [ha0] at hab hstp
        simp only [Act.about] at hab
        subst hab
        cases hstp with
        | notice _ _ _ _ _ _ _ _ ha' =>
          rw [hsame, ha] at ha'
          cases ha'
      | ignore m =>
        rw [ha0] at hab hstp
        simp only [Act.about] at hab
        subst hab
        cases hstp with
        | ignore _ _ _ ha' =>
          rw [hsame, ha] at ha'
          cases ha'
      | answer => rw [ha0] at hab; exact hab.elim
      | env => rw [ha0] at hab; exact hab.elim

end EarlyRun

/-! ## The eligible nodes' system, filtered from the hive's run

The observation starts at the entry cut, not at the record cut: a finite cut after it by which
every eligible node has handled a fresh head from after the record cut and taken the current
records, so that its known head is named in the current records' namespace and its embedding
is scoped. Before it, an eligible node may still know an old raw head whose node-space image
the current drops have changed, and its steps are not claimed to be the fine system's. From the
entry cut on, the hive's run is observed coarsely (`HiveStep`): an eligible node's events, the
environment's, and the hub's answers to requests eligible nodes sent or that were in flight at
the entry cut (`old`, finitely many, which may still move the hub) are steps of the fine
system; a node that is not eligible is raw. What it writes only grows the raw graph; it may
send requests, which take no virtual slot from the system's counter (the projection maps each
call it actually sends injectively, apart from the system's); the replies and notifications
it takes stay in the observation as ghosts, its state being unmodelled; and the hub answers its
fresh requests without moving (`answerRaw`'s `hhub`). That is a law of the native run, from
the records alone once they are fixed: an accepted push whose record effect leaves the records
as they were has its sender's raw pending originals among what they drop, which its custody
excludes (`Recovery.raw_pending_empty_of_fixed_records`, from
`Recovery.PendingOriginals.unpublished`). It needs no original history and no embedding;
`Recovery.pending_push_not_accepted_fixed` is the same fact for the executable model's own
traces, not this law. So the observation is not every field of the native run: it is what the
fine system reads of it.

The eligible nodes' system is a function of that observation (`filt`): the other nodes' slots
frozen, their fresh requests and the replies to them left out. Each observed step is a step of
it (`filt_step`), so a run of the hive from the entry cut is a run of the fine system
(`filt_run`, `filt_run_from`), with the hub, the raw graph and the eligible nodes as they are.
-/

section Filter

/-- One step of the hive from the entry cut, as the fine system observes it. An answer is the
fine system's own step; the request it answers is the one its reply names, an eligible node's
or one in flight at the entry cut. -/
inductive HiveStep (N : Nat) (D : Nat → Nat → Nat → Prop) (law : HubLaw) (E : Nat → Prop)
    (old : List Req) : Act → Sys → Sys → Prop
  | node {a : Act} {g g' : Sys} (n : Nat) (hE : E n) (ha : a.about n)
      (hs : SysStep N D law a g g') : HiveStep N D law E old a g g'
  | env {g g' : Sys} (hs : SysStep N D law .env g g') : HiveStep N D law E old .env g g'
  | answer {g g' : Sys} (hs : SysStep N D law .answer g g')
      (hk : ∀ rep, g'.reps = g.reps ++ [rep] →
        E rep.node ∨ (⟨rep.node, rep.slot, rep.req⟩ : Req) ∈ old) :
      HiveStep N D law E old .answer g g'
  | raw {g g' : Sys} (n : Nat) (hn : ¬ E n) (rq : List Req) (hr : RawGrow g g')
      (hnode : ∀ m, E m → g'.node m = g.node m) (hreqs : g'.reqs = g.reqs ++ rq)
      (hrq : ∀ q ∈ rq, q.node = n ∧ q ∉ old)
      (hrest : g'.hub = g.hub ∧ g'.reps = g.reps ∧ g'.notes = g.notes ∧ g'.slot = g.slot)
      (ht : g'.time = g.time + 1) : HiveStep N D law E old .env g g'
  | answerRaw {g g' : Sys} (r : Req) (hr : r ∈ g.reqs) (hn : ¬ E r.node) (hold : r ∉ old)
      (rep : Rep) (hrep : rep.node = r.node ∧ rep.slot = r.slot ∧ rep.req = r.body)
      (hreqs : g'.reqs = g.reqs.erase r) (hreps : g'.reps = g.reps ++ [rep])
      (hhub : g'.hub = g.hub)
      (hrest : g'.node = g.node ∧ g'.notes = g.notes ∧ g'.slot = g.slot ∧
        g'.next = g.next ∧ g'.par = g.par)
      (ht : g'.time = g.time + 1) : HiveStep N D law E old .env g g'

variable (E : Nat → Prop) [DecidablePred E] (frozen : Nat → NodeC) (old : List Req)

def keepReq (q : Req) : Bool := decide (E q.node) || old.contains q

def keepRep (r : Rep) : Bool := decide (E r.node) || old.contains ⟨r.node, r.slot, r.req⟩

/-- The eligible nodes' system read off an observation: the other nodes' slots frozen, and
only the requests eligible nodes sent or that were in flight at the entry cut, with their
replies. -/
def filt (g : Sys) : Sys :=
  { g with
    node := fun m => if E m then g.node m else frozen m
    reqs := g.reqs.filter (keepReq E old)
    reps := g.reps.filter (keepRep E old) }

variable {E frozen old}

theorem filter_erase_keep {α : Type} [DecidableEq α] {p : α → Bool} {a : α}
    (h : p a = true) : ∀ l : List α, (l.erase a).filter p = (l.filter p).erase a
  | [] => rfl
  | b :: l => by
    by_cases hb : b = a
    · subst hb
      simp [h]
    · have ih := filter_erase_keep h l
      have e1 : (b :: l).erase a = b :: l.erase a := by simp [hb]
      rw [e1]
      cases hp : p b
      · simp [hp, ih]
      · have e2 : (b :: List.filter p l).erase a = b :: (List.filter p l).erase a := by
          simp [hb]
        simp [hp, ih, e2]

theorem filter_erase_drop {α : Type} [DecidableEq α] {p : α → Bool} {a : α}
    (h : p a = false) : ∀ l : List α, (l.erase a).filter p = l.filter p
  | [] => rfl
  | b :: l => by
    by_cases hb : b = a
    · subst hb
      simp [h]
    · have e1 : (b :: l).erase a = b :: l.erase a := by simp [hb]
      rw [e1]
      simp only [List.filter_cons]
      rw [filter_erase_drop h l]

/-- What reads only the raw graph reads the eligible nodes' system as the hive. -/
theorem scoped_congr {σ : NS} {emb : Nat → Nat} {g h : Sys} (S : Scoped σ emb g)
    (hn : h.next = g.next) (hp : h.par = g.par) : Scoped σ emb h := by
  obtain ⟨i, l, p⟩ := S
  exact ⟨i, fun x hx => hn ▸ l x hx, fun x hx => hp ▸ p x hx⟩

theorem grow_congr {g g' h h' : Sys} {σ σ' : NS} {emb emb' : Nat → Nat}
    (G : Grow g g' σ σ' emb emb') (hn : h.next = g.next) (hp : h.par = g.par)
    (hn' : h'.next = g'.next) (hp' : h'.par = g'.par) : Grow h h' σ σ' emb emb' := by
  obtain ⟨a, b, c, d, e, f, k⟩ := G
  refine ⟨a, ?_, c, ?_, ?_, ?_, k⟩
  · rw [hn', hn]; exact b
  · intro x h1 h2; rw [d x h1 h2, hn]
  · intro y hy; rw [hp', hp]; exact e y (hn ▸ hy)
  · intro x h1 h2; rw [hp']; exact f x h1 h2

theorem growR_congr {g g' h h' : Sys} {σ σ' : NS} {emb emb' : Nat → Nat}
    (G : GrowR g g' σ σ' emb emb') (hn : h.next = g.next) (hp : h.par = g.par)
    (hn' : h'.next = g'.next) (hp' : h'.par = g'.par) : GrowR h h' σ σ' emb emb' where
  next := G.next
  rawGrows := by rw [hn, hn']; exact G.rawGrows
  embOld := G.embOld
  parRaw := fun y hy => by rw [hp', hp]; exact G.parRaw y (hn ▸ hy)
  parOld := G.parOld
  bound := fun x h1 h2 => by rw [hn']; exact G.bound x h1 h2
  parNew := fun x h1 h2 => by rw [hp']; exact G.parNew x h1 h2
  reuse := fun x h1 h2 hr => G.reuse x h1 h2 (hn ▸ hr)
  injNew := G.injNew
  cover := fun y h1 h2 => G.cover y (hn ▸ h1) (hn' ▸ h2)

theorem learn_congr {g h : Sys} {σ post : NS} {emb : Nat → Nat} {hd : Option Nat}
    {σi posti : NS} {embi : Nat → Nat} (L : Learn g σ post emb hd σi posti embi)
    (hn : h.next = g.next) (hp : h.par = g.par) : Learn h σ post emb hd σi posti embi := by
  obtain ⟨a, b, c, d, e, f, k, l⟩ := L
  refine ⟨fun hc => a fun x hx => ?_, scoped_congr b hn hp, c, d, e, f, k, l⟩
  intro y hy
  exact hc x hx y (hp ▸ hy)

theorem filt_node_of {g : Sys} {n : Nat} (hE : E n) : (filt E frozen old g).node n = g.node n :=
  by simp [filt, hE]

theorem filt_node_upd {g g' : Sys} {n : Nat} {c : NodeC} (hE : E n)
    (h : g'.node = upd g.node n c) :
    (filt E frozen old g').node = upd (filt E frozen old g).node n c := by
  funext m
  by_cases hm : m = n
  · subst hm; simp [filt, hE, h]
  · simp [filt, h, hm]

theorem filt_node_eq {g g' : Sys} (h : ∀ m, E m → g'.node m = g.node m) :
    (filt E frozen old g').node = (filt E frozen old g).node := by
  funext m
  by_cases hm : E m <;> simp [filt, hm, h m]

theorem filt_quiet {g g' : Sys} (h : Quiet g g') :
    Quiet (filt E frozen old g) (filt E frozen old g') :=
  ⟨h.hub, by simp [filt, h.reqs], by simp [filt, h.reps], h.notes, h.slot⟩

theorem keepRep_of {r : Rep} (hE : E r.node) : keepRep E old r = true := by
  simp [keepRep, hE]

/-- Each observed step is a step of the eligible nodes' system. -/
theorem filt_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act}
    {g g' : Sys} (hs : HiveStep N D law E old a g g') :
    SysStep N D law a (filt E frozen old g) (filt E frozen old g') := by
  cases hs with
  | node n hE ha hs =>
    cases hs with
    | busy m σ' emb' hw hac hl hg hnode hq ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .busy m σ' emb' ?_ ?_ ?_ ?_ ?_ (filt_quiet hq) ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hl
      · rw [hf]; exact growR_congr hg rfl rfl rfl rfl
      · rw [hf]; exact filt_node_upd hE hnode
    | idle m σ' hw hac hl hnode hr hq ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .idle m σ' ?_ ?_ ?_ ?_ hr (filt_quiet hq) ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hl
      · rw [hf]; exact filt_node_upd hE hnode
    | maint m σ1 σ' emb' hw hac hl hx hg hnode hq ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .maint m σ1 σ' emb' ?_ ?_ ?_ hx ?_ ?_ (filt_quiet hq) ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hl
      · rw [hf]; exact growR_congr hg rfl rfl rfl rfl
      · rw [hf]; exact filt_node_upd hE hnode
    | issue m k post new emb1 rq hw hi hg hb hslot hnodup hnode hreqs hslot' hrest ht hnd =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      have hkeep : ∀ q ∈ rq, keepReq E old q = true := fun q hq => by
        simp [keepReq, (hslot q hq).1, hE]
      refine .issue m k post new emb1 rq ?_ ?_ ?_ ?_ hslot hnodup ?_ ?_ hslot' ⟨hrest.1, ?_,
        hrest.2.2⟩ ht hnd
      · rw [hf]; exact hw
      · rw [hf]; exact hi
      · rw [hf]; exact growR_congr hg rfl rfl rfl rfl
      · rw [hf]; exact hb
      · rw [hf]; exact filt_node_upd hE hnode
      · simp only [filt, hreqs, List.filter_append]
        rw [List.filter_eq_self.2 hkeep]
      · simp [filt, hrest.2.1]
    | handle m w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf' hh hnode hreps hrest
        ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .handle m w rs hd c σi posti σ' embi ?_ ?_ hcov hhd hhd' ?_ hc hf' hh ?_ ?_
        ⟨hrest.1, ?_, hrest.2.2⟩ ht
      · rw [hf]; exact hw
      · intro r hr
        obtain ⟨h1, h2, h3⟩ := hrs r hr
        refine ⟨List.mem_filter.2 ⟨h1, ?_⟩, h2, h3⟩
        exact keepRep_of (by rw [h2]; exact hE)
      · rw [hf]; exact learn_congr hl rfl rfl
      · rw [hf]; exact filt_node_upd hE hnode
      · intro r
        simp only [filt, List.mem_filter, hreps r]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
        · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · simp [filt, hrest.2.1]
    | notice m nt c σi posti σ' embi hw hac hn hnn hnew hl hc hf' hh hnode hnotes hrest ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .notice m nt c σi posti σ' embi ?_ ?_ hn hnn ?_ ?_ hc hf' hh ?_ hnotes
        ⟨hrest.1, ?_, ?_, hrest.2.2.2⟩ ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hnew
      · rw [hf]; exact learn_congr hl rfl rfl
      · rw [hf]; exact filt_node_upd hE hnode
      · simp [filt, hrest.2.1]
      · simp [filt, hrest.2.2.1]
    | ignore m nt hw hac hn hnn hold hnode hnotes hrest ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .ignore m nt ?_ ?_ hn hnn ?_ ?_ hnotes ⟨hrest.1, ?_, ?_, hrest.2.2.2⟩ ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hold
      · exact filt_node_eq (fun m _ => by rw [hnode])
      · simp [filt, hrest.2.1]
      · simp [filt, hrest.2.2.1]
    | answer => simp [Act.about] at ha
    | env => simp [Act.about] at ha
  | env hs =>
    cases hs with
    | env hr hnode hq ht =>
      exact .env hr (filt_node_eq (fun m _ => by rw [hnode])) (filt_quiet hq) ht
  | answer hs hk =>
    cases hs with
    | answer r ans hr hreqs acc hans hreps hrest ht =>
      have hkr : keepReq E old r = true := by
        rcases hk _ hreps with h | h
        · simp [keepReq, h]
        · cases r; simp [keepReq, h]
      have hkrep : keepRep E old ⟨r.node, r.slot, g.time, r.body, acc, ans⟩ = true := by
        rcases hk _ hreps with h | h
        · exact keepRep_of h
        · simp [keepRep, h]
      refine .answer r ans (List.mem_filter.2 ⟨hr, hkr⟩) ?_ acc hans ?_
        ⟨filt_node_eq (fun m _ => by rw [hrest.1]), hrest.2⟩ ht
      · simp only [filt, hreqs]
        exact filter_erase_keep hkr _
      · simp only [filt, hreps, List.filter_append, List.filter_cons, hkrep, List.filter_nil,
          ite_true]
  | raw n hn rq hr hnode hreqs hrq hrest ht =>
    refine .env hr (filt_node_eq hnode) ⟨hrest.1, ?_, ?_, hrest.2.2.1, hrest.2.2.2⟩ ht
    · simp only [filt, hreqs, List.filter_append]
      have : rq.filter (keepReq E old) = [] := by
        apply List.filter_eq_nil_iff.2
        intro q hq
        obtain ⟨h1, h2⟩ := hrq q hq
        simp [keepReq, h1, hn, h2]
      rw [this, List.append_nil]
    · simp [filt, hrest.2.1]
  | answerRaw r hr hn hold rep hrep hreqs hreps hhub hrest ht =>
    have hkr : keepReq E old r = false := by
      have hc : old.contains r = false := by simpa using hold
      unfold keepReq
      rw [hc]
      simp [hn]
    have hkrep : keepRep E old rep = false := by
      obtain ⟨h1, h2, h3⟩ := hrep
      have he : (⟨rep.node, rep.slot, rep.req⟩ : Req) = r := by cases r; simp_all
      have hc : old.contains ⟨rep.node, rep.slot, rep.req⟩ = false := by
        rw [he]; simpa using hold
      unfold keepRep
      rw [hc, h1]
      simp [hn]
    refine .env ⟨Nat.le_of_eq hrest.2.2.2.1.symm, fun y _ => by
      show g'.par y = g.par y; rw [hrest.2.2.2.2]⟩
      (filt_node_eq (fun m _ => by rw [hrest.1])) ⟨hhub, ?_, ?_, hrest.2.1, hrest.2.2.1⟩ ht
    · simp only [filt, hreqs]
      exact filter_erase_drop hkr _
    · simp only [filt, hreps, List.filter_append, List.filter_cons, hkrep, List.filter_nil]
      simp

/-- So a run of the hive from the entry cut is a run of the eligible nodes' system, with the
same acts. -/
theorem filt_run {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} (run : Nat → Sys)
    (acts : Nat → Act) (hs : ∀ i, HiveStep N D law E old (acts i) (run i) (run (i + 1))) :
    ∀ i, SysStep N D law (acts i) (filt E frozen old (run i)) (filt E frozen old (run (i + 1))) :=
  fun i => filt_step (hs i)

/-- The same, for a run observed from the entry cut `k` on, read from there: the steps before
`k` are not claimed. -/
theorem filt_run_from {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (run : Nat → Sys) (acts : Nat → Act) (k : Nat)
    (hs : ∀ i, k ≤ i → HiveStep N D law E old (acts i) (run i) (run (i + 1))) :
    ∀ i, SysStep N D law (acts (k + i)) (filt E frozen old (run (k + i)))
      (filt E frozen old (run (k + i + 1))) :=
  fun i => filt_step (hs (k + i) (Nat.le_add_right _ _))

/-! ### Where the eligible nodes' system starts

A node that is not eligible stands in it as an inactive dummy on the raw root, waiting for
nothing:
none of its core steps ever runs, so its drop relation never matters, and the requests of it in
flight at the entry cut, and their replies, are orphans that only the initial budget counts.
What the system's run keeps (`RunOK`) holds of its start from what the observation has there:
the eligible nodes' own invariants and the global ones of the requests, replies and
notifications, which filtering only thins (`runOK_filt_init`). -/

/-- The dummy's core state: one label, `0`, its known head and only op head, and inactive. -/
def dummyNS : NS where
  known := (0, 0)
  plan := []
  hubRecs := none
  annc := none
  ap := 0
  pending := []
  written := false
  heads := [0]
  img := [0]
  par := fun _ => []
  next := 1
  loc := fun x => x = 0
  stg := fun _ => False
  obj := fun _ => False
  act := false

/-- A node that is not eligible, in the eligible nodes' system: the dummy, its one label (`0`)
on the raw root `rawRoot`, waiting for nothing. -/
def dummy (rawRoot : Nat) : NodeC := ⟨dummyNS, fun _ => rawRoot, 0, none⟩

theorem linv_dummy : LInv dummyNS where
  parLt := fun _ _ h => by cases h
  knownLt := by decide
  headsNe := by simp [dummyNS]
  headsLt := by simp [dummyNS]
  imgNe := by simp [dummyNS]
  imgLt := by simp [dummyNS]

theorem scoped_dummy {g : Sys} {rawRoot : Nat} (hroot : rawRoot < g.next)
    (hpar : g.par rawRoot = []) : Scoped dummyNS (fun _ => rawRoot) g where
  inj := fun x y hx hy _ => by
    change x < 1 at hx; change y < 1 at hy; omega
  lt := fun _ _ => hroot
  par := fun _ _ => by simp [dummyNS, hpar]

theorem waitOK_filt {D : Nat → Nat → Nat → Prop} {g : Sys} {n : Nat} {w : Wait} (hE : E n)
    (W : WaitOK D n g w) : WaitOK D n (filt E frozen old g) w where
  issue := by rw [filt_node_of hE]; exact W.issue
  scope := scoped_congr W.scope rfl rfl
  next := by rw [filt_node_of hE]; exact W.next
  emb := by rw [filt_node_of hE]; exact W.emb
  slots := W.slots
  reqs := fun q hq => W.reqs q (List.mem_filter.1 hq).1
  reps := fun r hr => W.reps r (List.mem_filter.1 hr).1

theorem nodeOK_filt {D : Nat → Nat → Nat → Prop} {g : Sys} {n : Nat} (hE : E n)
    (K : NodeSys.NodeOK D n g) : NodeSys.NodeOK D n (filt E frozen old g) where
  inv := by rw [filt_node_of hE]; exact K.inv
  scope := by rw [filt_node_of hE]; exact scoped_congr K.scope rfl rfl
  wait := fun w hw => waitOK_filt hE (K.wait w (by rw [filt_node_of hE] at hw; exact hw))

theorem objsOK_filt {g : Sys} {n : Nat} (hE : E n) (O : ObjsOK n g) :
    ObjsOK n (filt E frozen old g) where
  ans := fun r hr => O.ans r (List.mem_filter.1 hr).1
  reqs := fun w hw hk q hq => O.reqs w (by rw [filt_node_of hE] at hw; exact hw) hk q
    (List.mem_filter.1 hq).1
  reps := fun w hw hk r hr => O.reps w (by rw [filt_node_of hE] at hw; exact hw) hk r
    (List.mem_filter.1 hr).1

theorem sysOK_filt {law : HubLaw} {g : Sys} (S : SysOK law g) :
    SysOK law (filt E frozen old g) where
  reqs := fun q hq => S.reqs q (List.mem_filter.1 hq).1
  reps := fun r hr => S.reps r (List.mem_filter.1 hr).1
  fetch := fun r hr => S.fetch r (List.mem_filter.1 hr).1
  push := fun r hr => S.push r (List.mem_filter.1 hr).1
  pushAns := fun r hr => S.pushAns r (List.mem_filter.1 hr).1
  honest := fun q hq => S.honest q (List.mem_filter.1 hq).1

theorem timeOK_filt {g : Sys} (T : TimeOK g) : TimeOK (filt E frozen old g) where
  reps := fun r hr => T.reps r (List.mem_filter.1 hr).1
  notes := T.notes

/-- Where the eligible nodes' system starts, every node keeps what a run keeps: an eligible
node from its own invariants in the observation, a dummy by construction, given the root, and
the global invariants from the observation's. -/
theorem runOK_filt_init {D : Nat → Nat → Nat → Prop} {law : HubLaw} {g : Sys}
    (hE : ∀ n, E n → NodeSys.NodeOK D n g ∧ ObjsOK n g) (hs : SysOK law g) (ht : TimeOK g)
    (hans : ∀ r ∈ g.reps, r.req = .objs → r.ans = .objects)
    {rawRoot : Nat} (hroot : rawRoot < g.next) (hpar : g.par rawRoot = []) :
    ∀ n, RunOK law D n (filt E (fun _ => dummy rawRoot) old g) := by
  intro n
  refine ⟨?_, sysOK_filt hs, timeOK_filt ht, ?_⟩
  · by_cases he : E n
    · exact nodeOK_filt he (hE n he).1
    · have hd : (filt E (fun _ => dummy rawRoot) old g).node n = dummy rawRoot := by
        simp [filt, he]
      exact ⟨by rw [hd]; exact linv_dummy, by rw [hd]; exact scoped_dummy hroot hpar,
        fun w hw => by (rw [hd] at hw; cases hw)⟩
  · by_cases he : E n
    · exact objsOK_filt he (hE n he).2
    · have hd : (filt E (fun _ => dummy rawRoot) old g).node n = dummy rawRoot := by
        simp [filt, he]
      refine ⟨fun r hr => hans r (List.mem_filter.1 hr).1, fun w hw => ?_, fun w hw => ?_⟩
      · rw [hd] at hw; cases hw
      · rw [hd] at hw; cases hw

/-- The eligible nodes' system has the hive's hub, raw graph and eligible nodes. -/
theorem filt_hub (g : Sys) : (filt E frozen old g).hub = g.hub := rfl
theorem filt_next (g : Sys) : (filt E frozen old g).next = g.next := rfl
theorem filt_par (g : Sys) : (filt E frozen old g).par = g.par := rfl

end Filter

end Musubi.NodeSysEntry
