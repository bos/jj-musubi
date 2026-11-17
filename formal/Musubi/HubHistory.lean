/-
The hub's history of the joint system, indexed by sequence number: the head each sequence
number had when the hub last moved to it. The convergence proof uses this file.
-/
import Musubi.HubAnswers

namespace Musubi.Recovery.HubSys

open Musubi NodeSys HubSuffix

/-- `histories run initial i s` is the head that sequence number `s` had after `i` steps of
`run`, starting from `initial`; it is updated whenever the hub's sequence number advances. -/
noncomputable def histories (run : Nat → Sys) (initial : Nat → Nat) : Nat → Nat → Nat
  | 0 => initial
  | i + 1 => nextHistory (run i) (run (i + 1)) (histories run initial i)

end Musubi.Recovery.HubSys
