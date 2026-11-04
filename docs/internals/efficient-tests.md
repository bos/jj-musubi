# Writing efficient tests

musubi's tests run real `jj` and `git` against real repositories. Use the shared helpers for
temporary directories, fixtures and commands so that a new test avoids repeating setup and
waiting for disk writes. [testing.md](testing.md) gives approximate costs for each layer.

## When making tests faster

Measure before optimizing. The fault tests once spent 16 of 18 seconds copying hub snapshots,
not replaying requests. These measurements are for performance work; ordinary changes run only
the checks [AGENTS.md](../../AGENTS.md#checks) requires.

- Find the slow tests in a full run: nextest prints each test's time, and flags one that runs
  past 30 seconds. Measure a test there: in `just test` it competes for cores and the disk,
  which can make a fixture copy much slower than in an isolated run.
- A time says that something is slow, not why. Use perf and bpftrace (on macOS, `fs_usage` and
  Instruments) to count what a run starts and waits for, and see where the CPU goes and where
  threads wait off it; strace slows what it traces enough to change the answer. If a tool
  isn't installed, or tracing needs a permission you don't have, ask for it rather than guess.
  Tracing exposed thousands of `fdatasync` waits and two `tput` processes per jj command.
- Compare two versions by running them alternately, several times each, on the same machine,
  and compare averages.

## Keep tests off the disk

jj syncs every operation, view and index file it writes, and nothing a test writes needs to
survive a power cut. On a real disk, waiting for those syncs was most of the suite's time.

Make every test directory with `musubi_testutil::tempdir()`, never with `tempfile` directly: it
puts the directory in memory where it can ([testing.md, "Running the
tests"](testing.md#running-the-tests)). On 32 Linux cores that took the default suite from 17.5
seconds to 3.5; with `just test`'s RAM disk on an M4 Max, from 78 to 26.

## Know what the file system does

- A sync waits for the disk. On the cloud volumes and CI disks the suite was measured on, each
  of jj's `fdatasync` calls took 4 to 32 ms, and the waiting left a third of 32 cores idle. On
  tmpfs, which `/dev/shm` is, a sync returns at once.
- On macOS, a plain `fsync` doesn't wait for the SSD to empty its cache, but `F_FULLFSYNC`
  does, and Rust's `sync_data` and `sync_all` use `F_FULLFSYNC`. So every sync jj makes there
  waits for the flush, and a test that is fast on Linux in memory can be slow on a Mac's SSD.
  Don't infer the cost of a sync on macOS from what `fsync` costs.
- Follow [AGENTS.md, "Resilience"](../../AGENTS.md#resilience) on frequent write paths:
  overwrite in place or append, and avoid rewriting unchanged content. Replacing files can
  force writeback even without an explicit sync.
- APFS clones a whole directory tree, copy-on-write, in one `clonefile(2)` call, so copying a
  fixture costs almost nothing: a hub snapshot took 13 to 21 ms that way, against 240 to 280
  ms copying file by file. Linux clones one file at a time (`FICLONE`, on btrfs and XFS but
  not ext4), which saves nothing on small files, so `copy_tree` copies them there.

## Make an expensive fixture once per build

nextest runs each test in a process of its own, so a fixture cached in a `static` is made again
by every test, many at once in a full run. Make it once per build of the test binary instead,
and start each test from a copy.

- `musubi_testutil::recorded` makes a directory once per build, under `CARGO_TARGET_TMPDIR`:
  the first process records it while the others wait on a file lock, and a later run of the
  same build finds it made. `musubi_testutil::copy_tree` copies it for each test.
- A recording must still work once copied somewhere else. jj keeps no absolute path in a
  repository, so a copy opens as a repository that moved, and the race tests reopen a copied
  hub and its nodes as after a restart. Anything a test goes on generating, such as the seed
  for jj's change ids, must resume from the recorded value, or new ids collide with recorded
  ones.
- Record only the points tests start from, and replay the rest. The fault tests keep a snapshot
  of the hub where each call starts, rather than after every request, which was some seven
  thousand files a test.
- Leave out of a fixture whatever nothing reads, since every copy pays for it again. A hub's
  git repository is made without git's template, whose sample hooks every test that made or
  copied a hub would otherwise write.

## Start fewer processes

Starting a process costs milliseconds, more on Windows: reading git's config three times a
sync once pushed CI's daemon tests there past their timeout. A test that drives jj starts many.

- Read state in process where a command would only read it. `assert_converged` reads each
  repository with jj-lib, since every machine has just run `jj status` and a command would
  snapshot and import nothing. Before switching, confirm across a full run that the two
  ways agree.
- Tell a command what it would otherwise start something to find out. Without a terminal, jj asks
  `tput` for its width, two more processes for each command that prints, so the harness sets
  `COLUMNS`. jj also starts a thread per core, which nearly doubled the CPU a small command took
  on 32 cores, so the harness sets `RAYON_NUM_THREADS=1`. Such settings go only to the commands
  tests run ([testing-philosophy.md, "Realistic tests"](testing-philosophy.md#realistic-tests)).
- Don't start a process to do nothing. A transfer with no commits in it used to start git
  three times a hop for an empty pack. Skip building and importing an empty pack.
- Keep a long-lived helper across cases. The conformance test's Lean oracle (the executable
  model it checks each step against, [conformance.md](conformance.md)) takes 29 ms to start.
  A case that passes hands its oracle to the next; one that fails drops it, since its state is
  then unknown.

## Don't compute what nothing checks

- Build a value only where something compares it. `protocol_invariants` built the whole model
  state as JSON after every action even though it runs no Lean oracle.
- Compute a sort key once (`sort_by_cached_key`), not in every comparison. Rendering messages
  as JSON for each comparison was a fifth of the conformance test's time.

## Wait for a condition, never for a time

- Poll with backoff: look again after a millisecond, then twice as long each time, up to a cap.
  A fixed polling interval makes even a fast command wait for that interval.
- Don't sleep through a timeout: give the code under test a method that moves its clock on, and
  call that instead. A test of how long the hub keeps blobs calls
  `HubService::age_served_blobs` instead of sleeping.

## Schedule for the suite, not the test

- Start the longest test first. The conformance test, the longest by far, often started late
  on 4 cores and finished alone after everything else. Its nextest priority in
  `.config/nextest.toml` starts it first.
- Let an environment variable set a property test's number of cases, and default to as few as
  catch what the test is for. The conformance tests make 50 cases locally and 150 in CI
  (`MUSUBI_CONFORMANCE_CASES`); `just mutants` sets 150, so that
  mutation testing still catches what it caught. A search that takes minutes, like the
  generated end-to-end search, is opt-in (`just property`) and runs nightly in CI.

## Count build time

Each file under a crate's `tests/` is a binary of its own, linked against jj-lib and gix: 35 to
40 MB, linked again after every change to the crate. So musubi-jj's and musubi-sync's
integration examples are modules in `tests/it`. Add a new test file as a module there, not as
a new file under `tests/`, and select its tests with `-E 'test(/^module::/)'`. Only test sets
with a harness of their own, like `races` and `e2e_search`, get a binary of their own.

## Make generated cases replay exactly

Hegel ([testing.md](testing.md)) treats a test whose cases don't replay exactly as
nondeterministic: it replays a stored failure in batches to measure how often it fails, and
passes the run if that doesn't confirm it. So such a test costs every run and may never report
its failure: one search shard replayed a failure some thirty times, eleven seconds each, on
every run.

Nothing a case does may depend on the clock, the process, or timing; all randomness comes from
the case. jj's change ids come from a seed counter in musubi-testutil (jj's
`debug.randomness-seed`); the random suffix that tells machines of one name apart comes from
the same seeded generator rather than the clock; and rules pick among commits in change-id
order, since commit ids and `jj log`'s order depend on when commits were made.

Times come from the seed counter too, as in jj's own tests: each `jj` command's commits are a
second after the last command's (`JJ_TIMESTAMP`), and its operation a millisecond after
(`JJ_OP_TIMESTAMP`). jj merges concurrent operations in order of their end times, breaking ties
by id, and so does musubi, so with the real clock whether two operations tied within a
millisecond, and so how a case merged, depended on how fast it ran. A node in process takes its
times from its settings, which jj-lib reads once: its `Clock` (`musubi_sync::node::Clock`)
hands it the next seed's at each sync, and whenever the test takes the node to act on. Expiry,
which compares operation times with the clock, reads the environment's `musubi_testutil::Clock`,
which agrees with them; an hour of it takes millions of commands, so no copy goes unused in a
case unless a rule says so. The CLI tests run real daemons, which read the real clock, so their
operations keep the real time (`TestEnv::with_real_op_times`).

Operation ids still differ between runs: jj records each command's arguments in its operation,
and a test's paths are temporary. So nothing a case does may depend on the order of operation
ids, such as taking the first of several op heads; the search takes the one that ended last.
With all that, a failure that doesn't replay is a bug, so the search fails at once, saying
where the replay diverged.
