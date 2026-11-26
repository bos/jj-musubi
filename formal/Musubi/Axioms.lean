/-
Axiom audit: every main theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
`#assert_axioms` fails the build otherwise; a proof left unfinished depends on `sorryAx`.
-/
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Musubi.Safety
import Musubi.Liveness
import Musubi.Merged
import Musubi.Regress
import Musubi.Chunks
import Musubi.Scenario
import Musubi.ExecSound
import Musubi.ExecJson
import Musubi.RegressScenario
import Musubi.Refs
import Musubi.Expected
import Musubi.Presence
import Musubi.PresenceExec
import Musubi.Copies
import Musubi.Names
import Musubi.Identity
import Musubi.Contract
import Musubi.OpHeadsRace
import Musubi.Realize
import Musubi.Publication

open Lean Elab Command in
/-- `#assert_axioms t` fails unless `t` is a theorem that depends on no axiom beyond Lean's
standard three. -/
elab "#assert_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  unless (← getConstInfo name).isTheorem do
    throwErrorAt id m!"{name} is not a theorem"
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := (← collectAxioms name).filter fun a => !standard.contains a
  unless extra.isEmpty do
    logErrorAt id m!"{name} depends on {extra.toList}"

open Musubi

#assert_axioms Publication.protected_not_charged
#assert_axioms Publication.known_not_charged
#assert_axioms Publication.protected_content_free
#assert_axioms Publication.cleanup_keeps_current_view
#assert_axioms Publication.cleanup_keeps_intentional
#assert_axioms Publication.cleanup_requires_intentional
#assert_axioms Publication.cleanup_keeps_intentional_files
#assert_axioms Publication.cleanup_keeps_context
#assert_axioms Publication.survivor_parent_survives
#assert_axioms Publication.survivor_ancestry
#assert_axioms Publication.installed_keeps_intentional_files
#assert_axioms Publication.installed_keeps_view_context
#assert_axioms Publication.cleanup_keeps_unselected
#assert_axioms Publication.uncertain_cleanup_refused
#assert_axioms Publication.stale_cleanup_refused
#assert_axioms Publication.changed_plan_held

-- Shared run facts
#assert_axioms Musubi.acc_no_infinite_chain
#assert_axioms Musubi.no_infinite_run_of_invariant
#assert_axioms Musubi.terminal_iff_of_progress
#assert_axioms Musubi.Steps.head
#assert_axioms Musubi.Steps.invariant
#assert_axioms Musubi.eventually_done_of_progress
#assert_axioms Musubi.done_of_maximal_run

-- Contraction (`musubi sync --prune`)
#assert_axioms Contract.anc_cpar_survives
#assert_axioms Contract.anc_cpar_iff

-- Safety
#assert_axioms inv_reachable
#assert_axioms hubClosed
#assert_axioms hubMonotone
#assert_axioms histStable
#assert_axioms acceptedStays
#assert_axioms nodeClosed
#assert_axioms knownIsHubHistory
#assert_axioms hubHistory
#assert_axioms headMsgsTruthful
#assert_axioms locality
#assert_axioms mergeOwnership
#assert_axioms mergeOwnershipGhost
#assert_axioms noDuplicateMerge
#assert_axioms mergeNeverRepeats
#assert_axioms advance_result
#assert_axioms advance_merge_parents
#assert_axioms advance_merge_refines
-- No feedback
#assert_axioms noFeedback
#assert_axioms envCreatesOne
#assert_axioms converged_quiescent
-- Liveness
#assert_axioms pstep_reachable
#assert_axioms progress
#assert_axioms measure_decreases
#assert_axioms no_infinite_policy_run
#assert_axioms terminal_iff_converged
#assert_axioms eventually_converges
#assert_axioms maximal_run_converges
#assert_axioms Core.converged_all_accepted
#assert_axioms converged_all_accepted
-- Merged requests
#assert_axioms measure_agree
#assert_axioms converged_agree
#assert_axioms pushAccept_merged
#assert_axioms pushIdem_merged
#assert_axioms pushReject_merged
#assert_axioms fetch_merged
#assert_axioms realize_agree
#assert_axioms rmeasure_agree
#assert_axioms pushAcceptR_merged
#assert_axioms pushIdemR_merged
#assert_axioms pushRejectR_merged
#assert_axioms fetchR_merged
#assert_axioms fetchR_current
-- A hub that goes back
#assert_axioms invR_reachable
#assert_axioms hubClosedR
#assert_axioms hubHistoryR
#assert_axioms nodeClosedR
#assert_axioms noFeedbackR
#assert_axioms remake_reachable
#assert_axioms pstepR_reachable
#assert_axioms progressR
#assert_axioms measureR_decreases
#assert_axioms no_infinite_policy_runR
#assert_axioms terminal_iff_convergedR
#assert_axioms eventually_convergesR
#assert_axioms maximal_run_convergesR
#assert_axioms converged_all_acceptedR
#assert_axioms RegressScenario.duplicateMerge
#assert_axioms RegressScenario.rreachable_not_reachable
-- Chunked blobs
#assert_axioms Chunks.stored_identical
#assert_axioms Chunks.session_finishes
#assert_axioms Chunks.preach_abs
#assert_axioms Chunks.prefix_stored_identical
#assert_axioms Chunks.prefix_finishes
#assert_axioms Chunks.attempt_progress
#assert_axioms Chunks.restart_stalls
#assert_axioms Chunks.attempt_decreases
#assert_axioms Chunks.late_le
#assert_axioms Chunks.ameasure_reread
#assert_axioms Chunks.attempts_finish
#assert_axioms Chunks.attempts_bounded
#assert_axioms Chunks.fair_tsteps
#assert_axioms Chunks.fair_unswept
#assert_axioms Chunks.fair_arun
#assert_axioms Chunks.fair_finishes
#assert_axioms Chunks.swept_source_stalls
-- Non-vacuity
#assert_axioms Scenario.scenario
-- Executable model
#assert_axioms Exec.exec_sound
#assert_axioms Exec.abs_initE
#assert_axioms Exec.exec_reachable
#assert_axioms Exec.exec_inv
#assert_axioms Exec.exec_rsound
#assert_axioms Exec.exec_rreachable
#assert_axioms Exec.exec_invR
#assert_axioms Exec.exec_remake
#assert_axioms Exec.measureE_eq
#assert_axioms Exec.rmeasureE_eq
#assert_axioms Exec.convergedE_iff
#assert_axioms Exec.mem_upOpsL
#assert_axioms Exec.mem_upObjsL
-- Per-machine and shared view state
#assert_axioms Refs.noSpuriousRevert
#assert_axioms Refs.import_moves_only_after_git
#assert_axioms Refs.verbatim_reverts
#assert_axioms Refs.realize_noninterference
#assert_axioms Refs.verbatim_interferes
#assert_axioms Refs.merge_in_sync
#assert_axioms Refs.remoteNoSpuriousRevert
#assert_axioms Refs.remote_reset_without_export
#assert_axioms Refs.merge3_synced
#assert_axioms Refs.FReach.inv
#assert_axioms Refs.fork_merge_inv
#assert_axioms Refs.fork_merged_reach
#assert_axioms Refs.fork_noSpuriousRevert
#assert_axioms Refs.concurrent_records_revert
#assert_axioms Refs.TSlot.import_toSlot
#assert_axioms Refs.TSlot.import_remote
#assert_axioms Refs.TSlot.import_record
#assert_axioms Refs.TSlot.import_following
#assert_axioms Refs.TSlot.import_self
#assert_axioms Refs.TSlot.track_toSlot
#assert_axioms Refs.TSlot.exportLocal_toSlot
#assert_axioms Refs.TSlot.merge_toSlot
#assert_axioms Refs.TSlot.merge_WF
#assert_axioms Refs.shortcut_agrees
#assert_axioms Refs.realizeMerge_eq
#assert_axioms Refs.shortcutUnguarded_keeps_absent
#assert_axioms Refs.shortcutUnguarded_untracks
#assert_axioms Refs.realize_not_WF
#assert_axioms Refs.firstBase_reverts
#assert_axioms Refs.restoreLocal_inv
#assert_axioms Refs.restoreLocal_reach
#assert_axioms Refs.restoreRemote_inv
#assert_axioms Refs.restoreRemote_cinv
#assert_axioms Refs.restore_reverts
#assert_axioms Refs.CReach.inv
#assert_axioms Refs.conflictedNoSpuriousRevert
#assert_axioms Refs.conflicted_import_agrees
#assert_axioms Refs.conflicted_resolves
#assert_axioms Refs.restore_import_agrees
#assert_axioms Refs.restore_conflict_resolves_back
#assert_axioms Refs.conflicted_restore_resolves
#assert_axioms Refs.besideLocal_inv
#assert_axioms Refs.LStep.agrees
#assert_axioms Refs.cbeside_inv
#assert_axioms Refs.beside_keeps_fetch
#assert_axioms Refs.beside_published_apart_disagrees
-- Which copies a hive shows
#assert_axioms Presence.Hist.present_local
#assert_axioms Presence.Hist.present_congr
#assert_axioms Presence.Hist.work_present
#assert_axioms Presence.Hist.forget_absent
#assert_axioms Presence.Hist.only_work_returns
#assert_axioms Presence.Hist.absence_persists
#assert_axioms Presence.Hist.leave_sticks
#assert_axioms Presence.Hist.unseen_work_survives
#assert_axioms Presence.Hist.forgets_need_fresh_work
#assert_axioms Presence.Hist.no_forget_after_complete
#assert_axioms Presence.Hist.forget_chain_bounded
#assert_axioms Presence.Hist.redundant_forget_noop
#assert_axioms Presence.Hist.concurrent_forget_noop
#assert_axioms Presence.Hist.present_iff_latest
#assert_axioms Presence.Hist.present_iff_umax
#assert_axioms Presence.Hist.umax_work
#assert_axioms Presence.Hist.umax_forget
#assert_axioms Presence.Hist.umax_merge
#assert_axioms Presence.EHist.presentB_iff
#assert_axioms Presence.EHist.mem_latestB
-- Copies, duplicates and moves
#assert_axioms Copies.right_hive
#assert_axioms Copies.duplicates_refused
#assert_axioms Copies.only_join_makes_keys
#assert_axioms Copies.moves_followed
#assert_axioms Copies.daemon_writes_nothing
#assert_axioms Copies.jj_records_path
#assert_axioms Copies.refine_ne_copy
#assert_axioms Copies.join_refuses_duplicate
#assert_axioms Copies.duplicate_taken_for_moved
#assert_axioms Copies.move_taken_for_duplicate
#assert_axioms Copies.Detach.leave_retry
#assert_axioms Copies.Detach.leave_retry_prefix
#assert_axioms Copies.Detach.leave_prefix_safe
#assert_axioms Copies.Detach.join_retry
#assert_axioms Copies.Detach.join_retry_prefix
#assert_axioms Copies.Detach.join_prefix_safe
#assert_axioms Copies.Detach.fresh_retry
#assert_axioms Copies.Detach.fresh_retry_again
#assert_axioms Copies.Detach.fresh_prefix_safe

-- Names
#assert_axioms Names.choose_free

-- Names copies record, and naming among the copies present
#assert_axioms Identity.NHist.nameIs_unique
#assert_axioms Identity.NHist.nameIs_exists
#assert_axioms Identity.NHist.nameIs_congr
#assert_axioms Identity.NHist.nameIs_local
#assert_axioms Identity.NHist.rename_sticks
#assert_axioms Identity.NHist.rename_present
#assert_axioms Identity.NHist.sinceIs_unique
#assert_axioms Identity.NHist.since_stable
#assert_axioms Identity.NHist.later_mark
#assert_axioms Identity.sinceIs_local
#assert_axioms Identity.Naming.localName_injective
#assert_axioms Identity.Naming.assign_congr
#assert_axioms Identity.Naming.naming_local
#assert_axioms Identity.Naming.resolve_at_origin
#assert_axioms Identity.Naming.winner_label
#assert_axioms Identity.Naming.keeps_label
#assert_axioms Identity.Rejoin.leave_sticks_until_rejoin
#assert_axioms Identity.Rejoin.rejoin_returns
#assert_axioms Identity.Rejoin.late_work_same_key
#assert_axioms Presence.EHist.nameB_some
#assert_axioms Presence.EHist.nameB_none
#assert_axioms Presence.EHist.sinceB_some
#assert_axioms Presence.EHist.sinceB_present
#assert_axioms Presence.EHist.genB_mono

-- Expected values derived from history
#assert_axioms Refs.Expected.eval_congr_on
#assert_axioms Refs.Expected.eval_congr
#assert_axioms Refs.Expected.eval_terminates
#assert_axioms Refs.Expected.eval_stable
#assert_axioms Refs.Expected.eval_computes
#assert_axioms Refs.Expected.eval_without_known_agrees
#assert_axioms Refs.Expected.checkpoint
#assert_axioms Refs.Expected.conflicted_import_agrees_of_history

#assert_axioms Musubi.Exec.Json.encodeNet_eq_reference
#assert_axioms Musubi.Exec.Json.encodeNet_compress_eq_reference

-- Moving op heads that musubi read earlier (`OpHeads.lean`, `OpHeadsRace.lean`).
#assert_axioms OpHeads.Race.Inv.step
#assert_axioms OpHeads.Race.Reachable.inv
#assert_axioms OpHeads.Race.Inv.init
#assert_axioms OpHeads.Race.locked_blocks_commands
#assert_axioms OpHeads.Race.held_has_lock
#assert_axioms OpHeads.Race.writing_has_lock
#assert_axioms OpHeads.Race.check_no_event
#assert_axioms OpHeads.Race.check_step
#assert_axioms OpHeads.Race.Trace.landing_before_the_lock
#assert_axioms OpHeads.Race.Trace.landing_during_the_move

-- Realization against jj (`Realize.lean`).
#assert_axioms Realize.Reach.inv
#assert_axioms Realize.load_dom
#assert_axioms Realize.log_kept
#assert_axioms Realize.nothing_lost
#assert_axioms Realize.publish_shows_merge
#assert_axioms Realize.shown_step
#assert_axioms Realize.settled_shows
#assert_axioms Realize.crash_harmless
#assert_axioms Realize.crash_invisible
#assert_axioms Realize.musubi_writes
#assert_axioms Realize.ops_known
#assert_axioms Realize.quiet_check_passes
#assert_axioms Realize.finishes
#assert_axioms Realize.own_workspace_kept
#assert_axioms Realize.others_workspace_appears
#assert_axioms Realize.settled_sound
#assert_axioms Realize.mem_keptE
