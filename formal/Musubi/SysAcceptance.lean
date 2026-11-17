/-
Convergence from one actual hive run. The layers keep the native correspondence and scheduling
obligations visible alongside the facts derived from them:

* `SysAcceptance.Acceptance`: actual request decisions and stable-hub node acceptance;
* `SysAcceptance.Pending`: the raw-control contradiction for a node that stays pending;
* `SysAcceptance.Eligible`: filtering and convergence of the eligible nodes;
* `SysAcceptance.Events`: individual hub and node events projected into system steps;
* `SysAcceptance.Observations`: grouped observations of the same actual run and sampled views;
* `SysAcceptance.Cuts`: record cuts, quiet suffixes and old-effect boundaries;
* `SysAcceptance.Contracts`: grouped source, completion and scheduling contracts;
* `SysAcceptance.Phases`: derived recovery, entry and fine cuts, knowledge and eligibility;
* `SysAcceptance.Convergence`: composition of those phases in `hive_converges`.

Importing this module exposes every layer. `FineAssembly.hive_converges_observed` supplies the
fine-system premise by replaying observed events. The contracts assume eventual handling,
restart and scheduling, and a separate `autoWritesStop` (automatic native writes eventually
stop); termination of those writes is not derived.

The convergence proof uses this file.
-/
import Musubi.SysAcceptance.Convergence
