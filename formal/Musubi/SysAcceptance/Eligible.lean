/-
Filter the actual hive to eligible nodes and assemble their stable-hub convergence.
See `Musubi.SysAcceptance` for the layers of the complete convergence argument.
-/
import Musubi.SysAcceptance.Acceptance

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

/-! ## The eligible nodes settle in the hive's actual run

`eligible_system_converges` read through the eligible nodes' system (`Recovery.HubSys.hiveSys`):
a node's fair scheduling reads only its own slot and the acts, its pushes' completion only its
own requests, which the system keeps, and the hub's decision on a push only the hub, so each
carries over from the actual run, and what the theorem concludes of the hub and of the eligible
nodes is of the actual run. -/

section Hive

open Musubi.Recovery.HubSys

variable {E : Nat → Prop} [DecidablePred E] {frozen : Nat → NodeC} {old : List Req}

theorem fair_filt {run : Nat → Sys} {acts : Nat → Act} {n kf : Nat} (hE : E n)
    (h : Fair run acts n kf) : Fair (fun j => filt E frozen old (run j)) acts n kf where
  start := fun i hi hw ha => h.start i hi (by rw [← filt_node_of hE]; exact hw)
    (by rw [← filt_node_of hE]; exact ha)
  core := fun i hi hw ha => h.core i hi (by rw [← filt_node_of hE]; exact hw)
    (by rw [← filt_node_of hE]; exact ha)
  reply := fun i hi hw => h.reply i hi (by rw [← filt_node_of hE]; exact hw)

theorem pushFair_filt {run : Nat → Sys} {acts : Nat → Act} {n k : Nat} (hE : E n)
    (h : PushFair run acts n k) : PushFair (fun j => filt E frozen old (run j)) acts n k := by
  intro i hi ha q hq hq' hn
  have keep : keepReq E old q = true := by simp [keepReq, hn, hE]
  obtain ⟨j, hj, h1, h2⟩ := h i hi ha q (List.mem_filter.1 hq).1
    (fun h' => hq' (List.mem_filter.2 ⟨h', keep⟩)) hn
  exact ⟨j, hj, List.mem_filter.2 ⟨h1, keep⟩, fun h' => h2 (List.mem_filter.1 h').1⟩

theorem lawful_filt {M : Nat} {decode : Nat → List Exec.Rec} {g g' : Sys} {P : Pkt}
    (h : Nonempty (LawfulDecision M decode g g' P)) :
    Nonempty (LawfulDecision M decode (filt E frozen old g) (filt E frozen old g') P) := by
  obtain ⟨d⟩ := h
  exact ⟨{
    toHubDecision := {
      before := d.before
      after := d.after
      packet := d.packet
      handled := d.handled
      expected := d.expected
      new := d.new
      records := d.records
      head := d.head
      recs := d.recs
      seqBefore := d.seqBefore
      seqAfter := d.seqAfter
    }
    primitives := d.primitives
  }⟩

end Hive

open Musubi.Recovery.HubSys in
/-- The eligible system's starting snapshot. These are correspondence obligations of the
actual observation at `k`; raw entry alone does not establish them.

`distinctHeads` is a supplied snapshot obligation: native prelude realignment and a completed
merge establish it, while an active sampled event alone does not. `heads_nodup_step` preserves
it afterwards. The remaining fields describe the snapshot's
well-formed state, root, request bounds and supplied history window. -/
structure FineStart (D : Nat → Nat → Nat → Prop) (law : HubLaw) (E : Nat → Prop)
    (run : Nat → Sys) (k w : Nat) (initial : Nat → Nat) where
  rawRoot : Nat
  nodes : ∀ n, E n → NodeSys.NodeOK D n (run k) ∧ ObjsOK n (run k)
  system : SysOK law (run k)
  time : TimeOK (run k)
  objectReplies : ∀ r ∈ (run k).reps, r.req = .objs → r.ans = .objects
  rootBound : rawRoot < (run k).next
  rootParents : (run k).par rawRoot = []
  requestBounds : RequestBounds (run k)
  historyWindow : Recovery.HistoryWindow w (state (run k) initial)
  distinctHeads : ∀ n, E n → Recovery.HubNodeSteps.HeadsNodup (run k) n

open Musubi.Recovery.HubSys in
/-- The eligible system after the fine cut. `FineStart` holds the snapshot; the fields here
hold its subsequent steps, graph law, fixed records, quiet maintenance, decisions and fairness.
`FineAssembly.fineAt_of` builds this interface from native event replay.

The known pair's honesty and eligibility's node bound are derived separately and supplied to
`converges`. Completion and scheduling (`fair`, `pushFair`) remain explicit assumptions. -/
structure FineAt (N : Nat) (D : Nat → Nat → Nat → Prop) (law : HubLaw) (E : Nat → Prop)
    [DecidablePred E] (run : Nat → Sys) (acts : Nat → Act) (k w : Nat) (initial : Nat → Nat)
    extends FineStart D law E run k w initial where
  /-- Node count used by the executable packet-decision model. -/
  decisionNodes : Nat
  decodeRecords : Nat → List Exec.Rec
  steps : ∀ i, k ≤ i → HiveStep N D law E (run k).reqs (acts i) (run i) (run (i + 1))
  parentsFirst : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x
  nodeLaws : ∀ i, NodeStepLaws E D w (histories (fun j => run (k + j)) initial i)
    (acts (k + i)) (run (k + i)) (run (k + i + 1))
  noMaintenance : ∀ i, k ≤ i → ∀ n, E n → acts i ≠ .core n .maint
  recordsFixed : ∀ i, k ≤ i → (run i).hub.recs = (run k).hub.recs
  fair : ∀ n, E n → ∃ kf, Fair (fun j => run (k + j)) (fun j => acts (k + j)) n kf
  pushFair : ∀ n, E n → PushFair (fun j => run (k + j)) (fun j => acts (k + j)) n 0
  pushDecisions : ∀ n, E n → ∀ j q, q ∈ (run (k + j)).reqs → q ∉ (run (k + j + 1)).reqs →
    q.node = n →
    ∀ P, q.body = .push P →
      Nonempty (LawfulDecision decisionNodes decodeRecords (run (k + j)) (run (k + j + 1)) P)

open Musubi.Recovery.HubSys in
theorem FineAt.converges {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {run : Nat → Sys} {acts : Nat → Act} {k w : Nat}
    {initial : Nat → Nat} (F : FineAt N D law E run acts k w initial)
    (hknown : ∀ n, E n →
      Recovery.HubNodeSteps.HonestSnap w initial (run k) ⟨(known (run k) n).1,
        (known (run k) n).2, (run k).hub.recs⟩)
    (hN : ∀ n, E n → n < N) :
    ∃ K cut, k ≤ K ∧ K ≤ cut ∧ (∀ i, cut ≤ i → (run i).hub = (run K).hub) ∧
      ∀ n, E n → ∃ H, ∀ i, cut ≤ i →
        NodeSettle.Settled ⟨(run K).hub.seq, H, (run K).hub.recs, D n⟩ ((run i).node n).ns ∧
        ((run i).node n).emb H = (run K).hub.head ∧
        ∀ x, heads (run i) n x ↔ x = (run K).hub.head := by
  obtain ⟨hρ, hk0, hb0, hi0, hkn0, hl0, -⟩ :=
    hive_filtered (N := N) (law := law) run acts initial k F.rawRoot F.steps F.nodes
      F.system F.time F.objectReplies F.rootBound F.rootParents F.requestBounds F.historyWindow
      hknown F.nodeLaws F.noMaintenance F.distinctHeads
  have hdecide' : ∀ n, E n → ∀ j q, q ∈ (hiveSys E F.rawRoot run k j).reqs →
      q ∉ (hiveSys E F.rawRoot run k (j + 1)).reqs → q.node = n → ∀ P, q.body = .push P →
        Nonempty (LawfulDecision F.decisionNodes F.decodeRecords (hiveSys E F.rawRoot run k j)
          (hiveSys E F.rawRoot run k (j + 1)) P) := by
    intro n hE j q hq hq' hn P hP
    have keep : keepReq E (run k).reqs q = true := by simp [keepReq, hn, hE]
    exact lawful_filt (F.pushDecisions n hE j q (List.mem_filter.1 hq).1
      (fun h' => hq' (List.mem_filter.2 ⟨h', keep⟩)) hn P hP)
  obtain ⟨K, cut, hKc, hhub, hnodes⟩ := eligible_system_converges (E := E) (w := w)
    (hiveSys E F.rawRoot run k) (fun j => acts (k + j)) initial F.decisionNodes F.decodeRecords hρ hk0
    (fun i => F.parentsFirst (k + i)) hb0 hi0 hkn0 hl0 hN 0
    (fun i _ n hE => F.noMaintenance (k + i) (Nat.le_add_right k i) n hE)
    (fun i => (F.recordsFixed (k + i) (by omega)).trans (F.recordsFixed k (Nat.le_refl _)).symm)
    (fun n hE => by
      obtain ⟨kf, h⟩ := F.fair n hE
      exact ⟨kf, fair_filt hE h⟩)
    (fun n hE => pushFair_filt hE (F.pushFair n hE)) hdecide'
  refine ⟨k + K, k + cut, by omega, by omega, fun i hi => ?_, fun n hE => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    exact hhub j (by omega)
  · obtain ⟨H, hH⟩ := hnodes n hE
    refine ⟨H, fun i hi => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    obtain ⟨h1, h2, h3⟩ := hH j (by omega)
    have hn : (hiveSys E F.rawRoot run k j).node n = (run (k + j)).node n := filt_node_of hE
    refine ⟨by rw [← hn]; exact h1, by rw [← hn]; exact h2, fun x => ?_⟩
    have := h3 x
    unfold heads at this ⊢
    rw [hn] at this
    exact this

end Musubi.SysAcceptance
