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
import Musubi.RegressScenario
import Musubi.Refs
import Musubi.Presence
import Musubi.PresenceExec

open Musubi

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
-- Per-machine and shared view state
#print axioms Refs.noSpuriousRevert
#print axioms Refs.import_moves_only_after_git
#print axioms Refs.verbatim_reverts
#print axioms Refs.realize_noninterference
#print axioms Refs.verbatim_interferes
#print axioms Refs.merge_in_sync
#print axioms Refs.remoteNoSpuriousRevert
#print axioms Refs.remote_reset_without_export
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
#print axioms Presence.EHist.presentB_iff
#print axioms Presence.EHist.mem_latestB
