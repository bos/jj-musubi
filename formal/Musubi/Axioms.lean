/-
Axiom audit: every main theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.
-/
import Musubi.Safety
import Musubi.Liveness
import Musubi.Merged
import Musubi.Chunks
import Musubi.Scenario
import Musubi.ExecSound

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
