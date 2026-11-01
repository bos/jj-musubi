/-
Axiom audit: every main theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.
-/
import Musubi.Safety
import Musubi.Liveness
import Musubi.Merged
import Musubi.Regress
import Musubi.Chunks
import Musubi.Scenario
import Musubi.ExecSound
import Musubi.SupersedeExecSound
import Musubi.RecordLiveness
import Musubi.RegressScenario
import Musubi.Refs
import Musubi.AbandonRefs
import Musubi.Expected
import Musubi.Presence
import Musubi.PresenceExec
import Musubi.Copies
import Musubi.Names
import Musubi.Contract
import Musubi.Supersede

open Musubi

#print axioms AbandonRefs.abstraction_unique
#print axioms AbandonRefs.adoption_composes
#print axioms AbandonRefs.publish_current
#print axioms AbandonRefs.publish_refines
#print axioms AbandonRefs.fixup_retains

-- Safety
#print axioms inv_reachable
#print axioms hubClosed
#print axioms hubMonotone
#print axioms histStable
#print axioms acceptedStays
#print axioms nodeClosed
#print axioms knownIsHubHistory
#print axioms hubHistory
#print axioms headMsgsTruthful
#print axioms locality
#print axioms mergeOwnership
#print axioms mergeOwnershipGhost
#print axioms noDuplicateMerge
#print axioms mergeNeverRepeats
#print axioms advance_result
#print axioms advance_merge_parents
#print axioms advance_merge_refines
-- No feedback
#print axioms noFeedback
#print axioms envCreatesOne
#print axioms converged_quiescent
-- Liveness
#print axioms pstep_reachable
#print axioms progress
#print axioms measure_decreases
#print axioms no_infinite_policy_run
#print axioms terminal_iff_converged
#print axioms eventually_converges
#print axioms maximal_run_converges
#print axioms converged_all_accepted
-- Merged requests
#print axioms measure_agree
#print axioms converged_agree
#print axioms pushAccept_merged
#print axioms pushIdem_merged
#print axioms pushReject_merged
#print axioms fetch_merged
#print axioms realize_agree
#print axioms rmeasure_agree
#print axioms pushAcceptR_merged
#print axioms pushIdemR_merged
#print axioms pushRejectR_merged
#print axioms fetchR_merged
#print axioms fetchR_current
-- A hub that goes back
#print axioms invR_reachable
#print axioms hubClosedR
#print axioms hubHistoryR
#print axioms nodeClosedR
#print axioms noFeedbackR
#print axioms remake_reachable
#print axioms pstepR_reachable
#print axioms progressR
#print axioms measureR_decreases
#print axioms no_infinite_policy_runR
#print axioms terminal_iff_convergedR
#print axioms eventually_convergesR
#print axioms maximal_run_convergesR
#print axioms converged_all_acceptedR
#print axioms RegressScenario.duplicateMerge
#print axioms RegressScenario.rreachable_not_reachable
-- Chunked blobs
#print axioms Chunks.stored_identical
#print axioms Chunks.session_finishes
#print axioms Chunks.preach_abs
#print axioms Chunks.prefix_stored_identical
#print axioms Chunks.prefix_finishes
-- Non-vacuity
#print axioms Scenario.scenario
-- Executable model
#print axioms Exec.exec_sound
#print axioms Exec.abs_initE
#print axioms Exec.exec_reachable
#print axioms Exec.exec_inv
#print axioms Exec.exec_rsound
#print axioms Exec.exec_rreachable
#print axioms Exec.exec_invR
#print axioms Exec.exec_remake
#print axioms Exec.measureE_eq
#print axioms Exec.rmeasureE_eq
#print axioms Exec.convergedE_iff
#print axioms Exec.mem_upOpsL
#print axioms Exec.mem_upObjsL
#print axioms Exec.sexec_sound
#print axioms Exec.sabs_initSE
#print axioms Exec.sexec_ok
#print axioms Exec.sexec_allPruned
#print axioms Exec.sexec_reachable
#print axioms Exec.sexec_inv
#print axioms Exec.smeasureE_eq
#print axioms Exec.sconvergedE_iff
-- Ordered-record reconciliation
#print axioms Exec.recordMeasureE_eq
#print axioms Exec.recordConvergedE_iff
#print axioms Exec.recordMeasure_decreases
#print axioms Exec.recordPolicy_wf
#print axioms Exec.reconcile_executable
#print axioms Exec.record_progress_at_convergence
#print axioms Exec.record_finish
-- Per-machine and shared view state
#print axioms Refs.noSpuriousRevert
#print axioms Refs.import_moves_only_after_git
#print axioms Refs.verbatim_reverts
#print axioms Refs.realize_noninterference
#print axioms Refs.verbatim_interferes
#print axioms Refs.merge_in_sync
#print axioms Refs.remoteNoSpuriousRevert
#print axioms Refs.remote_reset_without_export
#print axioms Refs.merge3_synced
#print axioms Refs.FReach.inv
#print axioms Refs.fork_merge_inv
#print axioms Refs.fork_merged_reach
#print axioms Refs.fork_noSpuriousRevert
#print axioms Refs.concurrent_records_revert
#print axioms Refs.TSlot.import_toSlot
#print axioms Refs.TSlot.import_self
#print axioms Refs.TSlot.track_toSlot
#print axioms Refs.TSlot.exportLocal_toSlot
#print axioms Refs.TSlot.merge_toSlot
#print axioms Refs.TSlot.merge_WF
#print axioms Refs.shortcut_agrees
#print axioms Refs.realizeMerge_eq
#print axioms Refs.shortcutUnguarded_keeps_absent
#print axioms Refs.shortcutUnguarded_untracks
#print axioms Refs.realize_not_WF
#print axioms Refs.firstBase_reverts
#print axioms Refs.restoreLocal_inv
#print axioms Refs.restoreLocal_reach
#print axioms Refs.restoreRemote_inv
#print axioms Refs.restoreRemote_cinv
#print axioms Refs.restore_reverts
#print axioms Refs.CReach.inv
#print axioms Refs.conflictedNoSpuriousRevert
#print axioms Refs.conflicted_import_agrees
#print axioms Refs.conflicted_resolves
#print axioms Refs.restore_import_agrees
#print axioms Refs.restore_conflict_resolves_back
#print axioms Refs.conflicted_restore_resolves
#print axioms Refs.besideLocal_inv
#print axioms Refs.LStep.agrees
#print axioms Refs.cbeside_inv
#print axioms Refs.beside_keeps_fetch
#print axioms Refs.beside_published_apart_disagrees
-- Which copies a hive shows
#print axioms Presence.Hist.present_local
#print axioms Presence.Hist.present_congr
#print axioms Presence.Hist.work_present
#print axioms Presence.Hist.forget_absent
#print axioms Presence.Hist.only_work_returns
#print axioms Presence.Hist.absence_persists
#print axioms Presence.Hist.leave_sticks
#print axioms Presence.Hist.unseen_work_survives
#print axioms Presence.Hist.forgets_need_fresh_work
#print axioms Presence.Hist.no_forget_after_complete
#print axioms Presence.Hist.forget_chain_bounded
#print axioms Presence.Hist.redundant_forget_noop
#print axioms Presence.Hist.concurrent_forget_noop
#print axioms Presence.Hist.present_iff_latest
#print axioms Presence.Hist.present_iff_umax
#print axioms Presence.Hist.umax_work
#print axioms Presence.Hist.umax_forget
#print axioms Presence.Hist.umax_merge
#print axioms Presence.Hist.fixup_present
#print axioms Presence.Hist.pass_present
#print axioms Presence.EHist.presentB_iff
#print axioms Presence.EHist.mem_latestB
-- Copies, duplicates and moves
#print axioms Copies.right_hive
#print axioms Copies.duplicates_refused
#print axioms Copies.only_join_makes_keys
#print axioms Copies.moves_followed
#print axioms Copies.daemon_writes_nothing
#print axioms Copies.jj_records_path
#print axioms Copies.refine_ne_copy
#print axioms Copies.join_refuses_duplicate
#print axioms Copies.duplicate_taken_for_moved
#print axioms Copies.move_taken_for_duplicate

-- Names
#print axioms Names.choose_free
#print axioms Names.localName_injective

-- Contracting abandoned operations out of a history
#print axioms Contract.cpar_union
#print axioms Contract.cid_union
#print axioms Contract.cid_comm
#print axioms Contract.cid_eq
#print axioms Contract.superseded_ne
#print axioms Contract.anc_cpar_iff

-- Replicated op abandon
#print axioms SReachable.base
#print axioms SRReachable.base
#print axioms noDuplicateMergeS
#print axioms sinv_reachable
#print axioms nodeD_grows
#print axioms hubD_grows
#print axioms superseded_never_returns
#print axioms superseded_never_returns_hub
#print axioms dropped_never_head
#print axioms behind_not_carried
#print axioms allPruned_step
#print axioms spstepR_reachable
#print axioms smeasure_decreases
#print axioms no_infinite_policy_runS
#print axioms progressS
#print axioms converged_quiescentS
#print axioms terminal_iff_convergedS
#print axioms eventually_convergesS
#print axioms maximal_run_convergesS
#print axioms converged_all_droppedS
#print axioms converged_all_acceptedS

-- Expected values derived from history
#print axioms Refs.Expected.eval_congr_on
#print axioms Refs.Expected.eval_congr
#print axioms Refs.Expected.eval_terminates
#print axioms Refs.Expected.eval_stable
#print axioms Refs.Expected.eval_computes
#print axioms Refs.Expected.eval_without_known_agrees
#print axioms Refs.Expected.checkpoint
#print axioms Refs.Expected.conflicted_import_agrees_of_history
