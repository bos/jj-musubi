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
fine-system premise by replaying observed events. The contracts still include eventual handling,
restart and scheduling obligations, and the separate `autoWritesStop` assumption; the assembly
does not derive termination of automatic native writes.
-/
import Musubi.SysAcceptance.Convergence
