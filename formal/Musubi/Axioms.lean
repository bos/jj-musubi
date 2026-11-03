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
import Musubi.AsyncLiveness
import Musubi.RetryControl
import Musubi.RecordStability
import Musubi.ContractOrder
import Musubi.SurvivorAdvance
import Musubi.ContractedExec
import Musubi.ContractedRecordCut
import Musubi.CutHistory
import Musubi.RecoveryEpoch
import Musubi.PacketCoupling
import Musubi.RecordReplies
import Musubi.RecordEpoch
import Musubi.NotificationControl
import Musubi.SerialReply
import Musubi.HubSuffix
import Musubi.NodeSettle
import Musubi.EarlyEntry
import Musubi.RecoveryBridge
import Musubi.HistoryWindow
import Musubi.FreshObservation
import Musubi.EntryAssembly
import Musubi.CallBatch
import Musubi.HubHistory
import Musubi.SysFreshCuts
import Musubi.SysAcceptance
import Musubi.RequestBounds
import Musubi.HistoryReplies
import Musubi.GlobalRaw
import Musubi.ContractedMeasure
import Musubi.RegressScenario
import Musubi.Refs
import Musubi.AbandonRefs
import Musubi.Expected
import Musubi.Presence
import Musubi.PresenceExec
import Musubi.Copies
import Musubi.Names
import Musubi.Contract
import Musubi.PresenceContract
import Musubi.Supersede
import Musubi.NodeSysExec
import Musubi.NativeEvents
import Musubi.FineAssembly

open Musubi

#print axioms NativeEvents.nodeOK_of_filt
#print axioms NativeEvents.BoundEvent.step
#print axioms NativeEvents.Event.bound
#print axioms NativeEvents.Event.removed_eligible_push
#print axioms NativeEvents.observed_invariants
#print axioms NativeEvents.observed_hs
#print axioms NativeEvents.observed_decisions
#print axioms NativeEvents.RecordView.applied_current
#print axioms NativeEvents.RecordView.pending_empty
#print axioms NativeEvents.RecordView.applied_stays
#print axioms FineAssembly.honest_step
#print axioms FineAssembly.honest_run
#print axioms FineAssembly.notice_mem
#print axioms FineAssembly.FineSource.steps
#print axioms FineAssembly.fineAt_of
#print axioms FineAssembly.recordView_mono
#print axioms FineAssembly.sched_le
#print axioms FineAssembly.later_event
#print axioms FineAssembly.hive_converges_observed

#print axioms Exec.cexec_sound
#print axioms Exec.cexec_ok
#print axioms Exec.cexecAction_sound
#print axioms Exec.cexecAction_ok
#print axioms Exec.cexec_reachable_step
#print axioms Exec.cexecAction_record_control
#print axioms Exec.contracted_step_node_drop_mono
#print axioms Exec.cexec_record_prefix_stabilizes
#print axioms Exec.cexec_record_and_drop_sets_stabilize
#print axioms Exec.cutInv_step
#print axioms Exec.cutHistory_step
#print axioms Exec.cutHistory_run
#print axioms Exec.post_cut_run
#print axioms Exec.stale_accepts_stop
#print axioms Exec.fresh_accept_aligned
#print axioms Exec.eventual_aligned_acceptance_witnesses
#print axioms Exec.packet_source_drops
#print axioms Exec.packet_accept_fields
#print axioms Exec.packet_accept_fixed_drops
#print axioms Exec.packet_sender_aligned
#print axioms Exec.packet_sender_after_cut_aligned
#print axioms Exec.packet_source_known
#print axioms Exec.packet_source_heads
#print axioms Exec.packet_upload_closes
#print axioms Exec.packet_upload_closes_from_bases
#print axioms Exec.packet_upload_closes_split
#print axioms Exec.packet_checks_of_emit
#print axioms Exec.packet_checks_force_accept
#print axioms Exec.cexec_reachable_heads_survive
#print axioms Exec.current_adoption_enabled
#print axioms Exec.aligned_records_no_pending
#print axioms Exec.cexecAction_held
#print axioms PendingEpoch.pending_names_settle
#print axioms PendingEpoch.pending_names_fixed
#print axioms PendingEpoch.pending_names_settle_with_old_known
#print axioms PendingEpoch.pending_names_settle_from_sources
#print axioms PendingEpoch.finite_metadata_stabilizes
#print axioms PendingEpoch.finite_metadata_output_stabilizes
#print axioms EarlyEntry.Burst.stepB_sound
#print axioms EarlyEntry.Burst.local_grows_after_inputs
#print axioms EarlyEntry.Burst.step_rank
#print axioms EarlyEntry.Burst.no_infinite_burst
#print axioms EarlyEntry.Control.call_rank
#print axioms EarlyEntry.Control.no_infinite_calls
#print axioms EarlyEntry.Control.frame_rank
#print axioms EarlyEntry.Control.no_infinite_framed
#print axioms EarlyEntry.Control.pending_push_reached
#print axioms EarlyEntry.Control.walkB_iff
#print axioms EarlyEntry.Control.rawControl_guarded
#print axioms EarlyEntry.Control.callB_sound
#print axioms EarlyEntry.Control.raw_round_yields
#print axioms EarlyEntry.Control.Naming.settles
#print axioms EarlyEntry.Control.fresh_head_reached
#print axioms EarlyEntry.Control.fresh_fetch_takes
#print axioms EarlyEntry.Control.fresh_fetch_current
#print axioms EarlyEntry.Control.FetchLaws.current
#print axioms EarlyEntry.Control.raw_entry_reached
#print axioms EarlyEntry.Control.EntryLaws.enters
#print axioms EarlyEntry.Control.raw_entry_persists
#print axioms Recovery.eligible_nodes_raw_enter
#print axioms RawPublish.pendingPush_accepted
#print axioms RawPublish.stable_no_pendingPush
#print axioms Recovery.HubSys.request_bounds_run
#print axioms Recovery.HubSys.history_messages_run
#print axioms Recovery.HubSys.raw_window_run
#print axioms Recovery.HubSys.rawStep_of_sys
#print axioms Recovery.HubSys.global_history_chain
#print axioms Recovery.HubSys.pending_history_of_sys
#print axioms SysAcceptance.no_accepting_emit
#print axioms SysAcceptance.node_settles_accepted
#print axioms Recovery.aligned_iff_pending_empty
#print axioms Recovery.HubSys.sys_step_expansion
#print axioms Recovery.HubSys.path_bk_quiet
#print axioms Recovery.HubSys.settled_raw_head
#print axioms Recovery.HubSys.hub_stabilizes_sys
#print axioms SysAcceptance.eligible_system_converges
#print axioms SysAcceptance.not_dropped_fixed
#print axioms SysAcceptance.not_dropped_of
#print axioms SysAcceptance.PendingLaws.hsurviveOf
#print axioms SysAcceptance.PendingLaws.hnoCacheOf
#print axioms SysAcceptance.no_forever_pending
#print axioms SysAcceptance.PendingLaws.absurd
#print axioms SysAcceptance.old_effects_stop
#print axioms SysAcceptance.known_truthful
#print axioms SysAcceptance.knows_stable_head
#print axioms SysAcceptance.hive_converges
#print axioms SysAcceptance.HubAnswer.fetch_step
#print axioms SysAcceptance.HubAnswer.objects_step
#print axioms SysAcceptance.HubAnswer.hive_step
#print axioms SysAcceptance.answer_refused_iff
#print axioms SysAcceptance.answer_ne_incomplete
#print axioms SysAcceptance.HubAnswer.push_step
#print axioms SysAcceptance.HubAnswer.store_step
#print axioms SysAcceptance.HubAnswer.push_handled
#print axioms SysAcceptance.HubAnswer.observed_step
#print axioms SysAcceptance.checkAnswer_expect
#print axioms Recovery.accepted_sender_pending_empty
#print axioms Recovery.pending_push_not_accepted_fixed
#print axioms Recovery.raw_pending_empty_of_fixed_records
#print axioms Recovery.raw_noneligible_answer_frame
#print axioms Exec.record_and_drop_sets_stabilize
#print axioms NodeSysEntry.filt_step
#print axioms NodeSysEntry.filt_run_from
#print axioms NodeSysEntry.runOK_filt_init
#print axioms Recovery.HubSys.hive_filtered
#print axioms Recovery.HubSys.hub_stabilizes_hive
#print axioms SysAcceptance.eligible_hive_converges
#print axioms Exec.current_pruned_reply_reconstructs
#print axioms Exec.fresh_record_reply_completes
#print axioms Exec.serialized_record_reply_completes
#print axioms Retry.project_own_start
#print axioms Retry.project_reserve
#print axioms Retry.project_other_start
#print axioms Retry.project_finish
#print axioms Retry.Serial.inv_step
#print axioms Retry.Serial.step_inbox
#print axioms Retry.Serial.old_call_effects_stop
#print axioms Retry.Serial.fresh_reply_no_restart
#print axioms Retry.Serial.own_reply_learns
#print axioms Retry.Serial.round_step_serial
#print axioms Retry.Serial.round_old_effects_stop
#print axioms Retry.Serial.object_recoveries_stop
#print axioms Retry.Records.record_disturbances_stop
#print axioms Retry.Records.no_receipts_when_quiet
#print axioms Retry.Records.State.guard_fetched
#print axioms Retry.Records.step_guard
#print axioms Retry.Records.exec_sound
#print axioms Retry.Records.step_credit
#print axioms Retry.Notifications.old_notifications_stop
#print axioms Retry.publication_empty_pending
#print axioms HubSuffix.hub_suffix_stabilizes
#print axioms NodeSettle.write_known
#print axioms NodeSettle.emit_packet
#print axioms NodeSettle.node_settles
#print axioms EarlyEntry.early_entry
#print axioms EarlyEntry.local_burst_finite
#print axioms Recovery.node_converges_at_stable_hub
#print axioms Recovery.refined_suffix_converges
#print axioms Recovery.accepted_emits_of_packet_handling
#print axioms Recovery.history_window_run
#print axioms Recovery.history_window_enters_suffix
#print axioms Recovery.fresh_observation_eventually
#print axioms Recovery.own_observation_truthful
#print axioms Recovery.notification_preserves_truth
#print axioms Recovery.eligible_nodes_enter
#print axioms Recovery.eligible_pending_empty
#print axioms Recovery.eligible_write_unchanged
#print axioms Recovery.history_reply_stays_truthful
#print axioms Recovery.history_old_targets_stop
#print axioms Expansion.expand
#print axioms Expansion.Path.invariant
#print axioms Expansion.stabilizes_of_expansion
#print axioms Retry.Batch.finish_relabel
#print axioms Retry.Batch.match_relabel
#print axioms Retry.Batch.finite_batch_completes
#print axioms NodeSys.node_settles_sys
#print axioms NodeSys.Grow.toR
#print axioms NodeSys.scoped_growR
#print axioms NodeSys.GrowR.same_next
#print axioms NodeSys.GrowR.one
#print axioms NodeSys.Exec.scopeB_sound
#print axioms NodeSys.Exec.growB_sound
#print axioms NodeSysEntry.early_entry_sys
#print axioms NodeSysEntry.node_settles_entry
#print axioms SysFreshCuts.old_replies_stop
#print axioms SysFreshCuts.old_notes_stop
#print axioms SysFreshCuts.early_entry_fresh
#print axioms SysFreshCuts.node_settles_fresh
#print axioms Recovery.raw_growth_expansion
#print axioms Recovery.raw_maintenance_expansion
#print axioms Recovery.HubSys.ledger_covers
#print axioms Recovery.HubSys.foreign_step_expansion
#print axioms Recovery.HubNodeSteps.own_step_expansion
#print axioms Recovery.HubNodeSteps.mid_mergeExisting
#print axioms Recovery.HubNodeSteps.issue_post_heads
#print axioms Recovery.HubNodeSteps.heads_nodup_step
#print axioms NodeSettle.inv_busy
#print axioms NodeSettle.rank_busy
#print axioms NodeSys.loc_busy
#print axioms Recovery.HubSys.suffixStepLaws_filt
#print axioms SysAcceptance.FineAt.converges
#print axioms SysAcceptance.NodeIssue.step
#print axioms SysAcceptance.NodeIssue.hive_step
#print axioms SysAcceptance.NodeIssue.raw_step
#print axioms SysAcceptance.namedHead_of_le
#print axioms SysAcceptance.learn_of_growB
#print axioms SysAcceptance.learn_new_bare
#print axioms SysAcceptance.NodeHandle.step
#print axioms SysAcceptance.NodeHandle.hive_step
#print axioms SysAcceptance.NodeCore.busy_step
#print axioms SysAcceptance.NodeCore.idle_step
#print axioms SysAcceptance.NodeCore.maint_step
#print axioms SysAcceptance.NodeNotice.step
#print axioms SysAcceptance.NodeNotice.ignore_step
#print axioms Recovery.HubSys.answer_step_expansion
#print axioms Recovery.HubSys.history_window_sys_run
#print axioms Exec.uncoveredImages_after_advance
#print axioms Exec.uncoveredImages_singleton_zero
#print axioms Exec.rmeasureCE_without_drops
#print axioms Exec.preparedAdvance_safe
#print axioms Exec.imageAdvance_safe
#print axioms Exec.imageAccept_safe
#print axioms Contracted.step_safe
#print axioms Contracted.step_retains
#print axioms Contracted.old_expected_accepts_eventually_stop

#print axioms Contract.advanceImages_set
#print axioms Contract.advanceImages_nodup
#print axioms Contract.advanceImages_survives
#print axioms Contract.advanceImages_covers
#print axioms Contract.advanceImages_singleton_ready
#print axioms Contract.advanceImages_merge_ready
#print axioms Contract.advanceImages_merge_keeps

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
#print axioms Exec.sexec_announced_held
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
-- Split asynchronous exchanges (the full retry bridge is still open)
#print axioms measureR_delayed_learn
#print axioms bad_accept_before_reply
#print axioms measureR_accept_before_reply
#print axioms settling_decreases
#print axioms settling_hub_stabilizes
-- Retry-control bounds under their explicit epoch constraints
#print axioms Retry.finish_missing
#print axioms Retry.start_fresh
#print axioms Retry.inbox_old_credit
#print axioms Retry.old_slots_eventually_stop
#print axioms Retry.fixup_step_credit
#print axioms Retry.fixup_writes_le_one
#print axioms Retry.fixups_eventually_stop
#print axioms Retry.publication_progress
#print axioms Retry.publication_retry
#print axioms Retry.publication_tip_cached
-- Stabilization of records, without assuming head stabilization
#print axioms Exec.sexec_record_control
#print axioms Exec.takeRecs_eq_iff
#print axioms Exec.eventual_original_chain
#print axioms Exec.record_prefix_eventually_stabilizes
#print axioms Exec.sexec_record_prefix_stabilizes
#print axioms Exec.adopt_pending_subset
#print axioms Exec.retry_adopt_of_extension
#print axioms Exec.node_drop_sets_eventually_stabilize
-- Contracted expected heads; the original-history embedding is still incomplete
#print axioms Contract.below_survivor_iff
#print axioms Contract.below_contracted_iff
#print axioms Contract.below_two_step
#print axioms Contract.below_mono
#print axioms Contract.below_trans
#print axioms Contract.belowB_iff
#print axioms Contract.stable_suffix_chain
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
#print axioms Contract.union_absorbs_subset
#print axioms Contract.cpar_absorbs_subset
#print axioms Contract.cid_absorbs_subset
#print axioms Contract.anc_cpar_survives
#print axioms Contract.image_absorbs_subset
#print axioms Contract.image_original_survives
#print axioms Contract.image_ne_dropped_original
#print axioms Contract.cid_comm
#print axioms Contract.cid_eq
#print axioms Contract.superseded_ne
#print axioms Contract.anc_cpar_iff

-- Presence through a contraction
#print axioms PresenceContract.pres_eq
#print axioms PresenceContract.stamp_union
#print axioms PresenceContract.sid_union
#print axioms PresenceContract.sid_absorbs_subset
#print axioms PresenceContract.sid_comm
#print axioms PresenceContract.stamp_none
#print axioms PresenceContract.sid_eq
#print axioms PresenceContract.sid_superseded_ne

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
