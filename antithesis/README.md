# Antithesis workloads

[Antithesis](https://antithesis.com/) runs a system in a deterministic simulation, injects
faults (killed, stopped and paused containers, network partitions and slow links), and searches
for executions that break its properties. This directory holds musubi's workload for it.

## `musubi/`

**What it tests.** A hub and three machines, `m1` to `m3`, each a container. Each machine runs
`musubi daemon` on a colocated jj repository at `/root/repo`, and reaches the hub over real ssh
with a key restricted to `musubi hub connect`, as `musubi join` sets up. The hub runs
`musubi hub`. Faults hit all four; the driver is spared.

**The driver** (`driver/`, Rust, a [hegel](https://hegel.dev) concurrent state machine) is the
user at all three machines. It sets the hive up (`jj git init`, `musubi create`, then `musubi
clone` on the others), then runs jj and musubi commands over ssh while the daemons sync. Each
machine runs one at a time, as one person typing would, under a lock on the machine itself, which
a command the driver gave up waiting for still holds. The commands: editing files, `jj new` (on
recent changes, bookmarks, other machines' working copies, and merges), `commit`, `describe`,
`rebase`, `squash`, `abandon`, `edit`, bookmark moves and deletes, branches moved with git behind
jj's back, `undo`, commands at an older operation, `jj op abandon` trimming history, a secondary
workspace added and forgotten, `musubi sync` (making the repair a failed sync names), and
`musubi.auto-snapshot` turned on and off. A stale working copy is updated as the user would.

**Properties.**

- *jj and musubi commands never crash*: no panic or `Internal error`, except three known jj
  behaviors, which `crashed` in `driver/src/workload.rs` tolerates: the duplicate-commit bug
  and the refusal of a workspace recorded at an operation an abandon rewrote
  ([races.md](../docs/internals/races.md#known-jj-limitations)), and, once an abandon has run,
  `jj undo` failing with "not found in index" ([FINDINGS.md](FINDINGS.md)). jj exits 255 for
  an internal error, as ssh does for its own failure, so the driver has the remote shell
  report the exit status itself.
- An eventually, at a random point, stops faults, records each working copy, and syncs every
  machine, repairing what a sync asks the user to (`jj op revert`, `jj op integrate`). Then:
  - *every machine serves its copy again once faults stop*;
  - *the machines converge on one history once faults stop*: the same hive head, all work
    sent, no problem reported, and the same visible heads, bookmarks, and workspaces with
    their working-copy commits;
  - *syncing leaves the files in working copies as they were*, on each machine where the
    user ran no repair;
  - *every commit a command made reaches every machine*: each recorded commit id is in every
    machine's git object store. A commit from a command sent before the latest `jj op
    abandon` finished is exempt: the abandon may have dropped its operation before it was
    sent, and musubi then rightly never sends it.
- In musubi itself, behind the `antithesis` cargo feature: *musubi never panics*, *the hub
  panics answering a request* (unreachable), *a panic caught from jj is its known graph
  cycle* (unreachable otherwise), and exploration assertions on paths only
  concurrency and faults reach: a push rejected because another came first, a merge before
  pushing, a request sent again after a timeout, a repeated request answered from the hub's
  record, a request the hub lets go unanswered, a daemon sync failing and recovering, and a
  failed ssh connection.
- Exploration assertions in the driver: stale working copies, divergent changes, conflicted
  bookmarks, building on another machine's working copy, and a sync naming an operation to
  revert.

**Build, run locally, launch.** All from `antithesis/musubi/`:

```sh
scripts/build.sh                 # musubi-node and musubi-driver images
snouty validate config           # setup completes locally
scripts/build.sh --coverage      # plus the coverage build, for the local loop
scripts/local-run.sh 300         # five minutes of workload: assertions, coverage, logs
EVENTUALLY_AFTER=120 scripts/local-run.sh 400   # the eventually runs after two minutes
scripts/launch.sh 12 "smoke"     # a 12-compute-hour run on Antithesis
```

The images build from the repository's root, with `image/Dockerfile.dockerignore`; a build
of musubi with instrumentation takes a while, and later builds reuse cargo's cache.

**OpenSSH.** The image builds OpenSSH 10.6p2's server in place of Debian's 10.0, whose
seccomp sandbox kills `sshd-auth` with SIGSYS when a paused container resumes it
(`restart_syscall` wasn't allowed), which Antithesis reports as an unexpected crash.

**Findings** are in [FINDINGS.md](FINDINGS.md).
