# Writing efficient tests

musubi's tests run real `jj` and `git` against real repositories, thousands of times in a
full run. Most of what that costs is work no test asserts on: waiting for the disk, starting
processes, and making the same fixtures over and over. Each rule below comes from a change
that made the suite measurably faster, and the figures with it are what that change saved.

## Measure before changing anything

Time rarely goes where you'd guess: the fault tests spent 16 of 18 seconds copying
snapshots of the hub, not replaying the requests they test.

- Find the slow tests in a full run: nextest prints each test's time, and flags one that
  runs past 30 seconds. Measure a test there, not alone. Alone, it has the machine to
  itself; in `just test` it competes for cores and the disk. Making the fault tests'
  snapshots took a second alone and 16 seconds in a full run.
- Use perf and bpftrace, and use them a lot, to see what is really going on: a time says
  that something is slow, not why. Count what a run starts and waits for, see where the CPU
  goes and where threads wait off it. They cost little, where strace slows what it traces
  enough to change the answer. On macOS, use `fs_usage` and Instruments. If a tool isn't
  installed, or tracing needs a permission you don't have, ask for it rather than guess.
  The suite's biggest wins came this way: some fifteen thousand `fdatasync` calls of 4 to
  32 ms each, and two processes per jj command spent asking `tput` for a width.
- Compare two versions by running them alternately, several times each, on the same
  machine, and compare averages. One run of each says little.

## Keep tests off the disk

jj syncs every operation, view and index file it writes, and nothing a test writes needs to
survive a power cut. On a real disk, waiting for those syncs was most of the suite's time.

- Make every test directory with `musubi_testutil::tempdir()`, never with `tempfile`
  directly. On Linux it is in `/dev/shm`, in memory.
- On macOS, where every sync waits for the SSD to flush its cache, `just test` puts
  `TMPDIR` on a RAM disk for the run; a bare `cargo nextest run` doesn't.

On 32 Linux cores the default suite went from 17.5 seconds to 3.5; on an M4 Max, from 78
to 26.

## Know what the file system does

What a write costs depends on the file system, and the differences are large enough to
decide where a test's time goes.

- A sync waits for the disk. On the cloud volumes and CI disks the suite was measured on,
  each of jj's `fdatasync` calls took 4 to 32 ms, and the waiting left a third of 32 cores
  idle. On tmpfs, which `/dev/shm` is, a sync returns at once.
- On macOS, a plain `fsync` doesn't wait for the SSD to empty its cache, but `F_FULLFSYNC`
  does, and Rust's `sync_data` and `sync_all` use `F_FULLFSYNC` on macOS. So every sync
  jj makes there waits for the flush, and a test that is fast on Linux in memory can be
  slow on a Mac's SSD. Don't infer the cost of a sync on macOS from what `fsync` costs.
- ext4 (with `auto_da_alloc`, its default) and btrfs write a file out without being asked
  when it replaces another by rename, or is truncated to nothing and closed. Code that
  tests run often should overwrite in place or append instead (AGENTS.md, "Resilience").
- APFS clones a whole directory tree in one `clonefile(2)` call, copy-on-write, so copying
  a fixture costs almost nothing: a hub snapshot took 13 to 21 ms that way, against 240 to
  280 ms copying file by file. Linux clones one file at a time (`FICLONE`, on btrfs and XFS
  but not ext4), which saves nothing on small files, so `copy_tree` copies them there.

## Make an expensive fixture once per build

nextest runs each test in a process of its own, so a fixture cached in a `static` is made
again by every test, many at once in a full run. Make it once per build of the test binary
instead, and start each test from a copy.

- `musubi_testutil::recorded` makes a directory once per build, under
  `CARGO_TARGET_TMPDIR`: the first process records it while the others wait on a file lock,
  and a later run of the same build finds it made. `musubi_testutil::copy_tree` copies it
  for each test, as one `clonefile(2)` of the whole tree on macOS.
- A recording must still work once copied somewhere else. jj keeps no absolute path in a
  repository, so a copy opens as a repository that moved, and the race tests reopen a
  copied hub and its nodes as after a restart. Anything a test goes on generating, such as
  the seed for jj's change ids, must resume from the recorded value, or new ids collide
  with recorded ones.
- Record only the points tests start from, and replay the rest. The fault tests
  snapshotted the hub after every request, some seven thousand files a test, though only
  one test starts partway through a call; they now keep a snapshot where each call starts.
- Leave out of a fixture whatever nothing reads, since every copy pays for it again. A
  hub's git repository is made without git's template, whose sample hooks every test that
  made or copied a hub was writing.

The race catalogue went from 769 seconds of test time to about 510, and the longest fault
test from over a minute to about 35 seconds.

## Start fewer processes

Starting a process costs milliseconds, and on Windows enough that reading git's config
three times a sync once pushed CI's daemon tests past their timeout. A test that drives jj
starts many.

- Read state in process where a command would only read it. `assert_converged` ran
  `jj log`, `jj bookmark list` and more on every machine, just after each had run
  `jj status`, so they would snapshot and import nothing; it now reads each repository with
  jj-lib, twelve jj commands fewer in a check of two machines. Confirm that the two agree,
  across a full run, before switching.
- Tell a command what it would otherwise start something to find out. Without a terminal,
  jj asks `tput` for its width, two more processes for each command that prints; the test
  harness sets `COLUMNS`. jj also starts a thread a core, which nearly doubled the CPU a
  small command took on 32 cores; the harness sets `RAYON_NUM_THREADS=1`. Set these only for
  the commands tests run, not for the musubi under test, so that what is tested is what
  ships.
- Don't start a process to do nothing. A transfer with no commits in it started git three
  times a hop for an empty pack, and now starts none: 3,222 git processes in the default
  suite instead of 3,628. Making musubi faster makes its tests faster.
- Keep a long-lived helper across cases. The conformance test started a Lean oracle (the
  executable model it checks each step against, docs/internals/conformance.md) for each
  case, 29 ms before it answered anything. A case that passes now hands its oracle to the
  next; one that fails drops it, since its state is then unknown. The test went from 17.1
  seconds to 12.5.

## Don't compute what nothing checks

- Build a value only where something compares it. `protocol_invariants` built the whole
  model state as JSON after every action, for comparison with a Lean oracle it doesn't
  run: 4.1 seconds, now 0.7.
- Compute a sort key once (`sort_by_cached_key`), not in every comparison. Rendering
  messages as JSON for each comparison was a fifth of the conformance test's time.

## Wait for a condition, never for a time

- Poll with backoff: look again after a millisecond, then twice as long each time, up to a
  cap. The CLI tests looked every 50 ms for commands that mostly take a few; with backoff
  they take 4.6 seconds in all instead of 6.9, and starting the daemon takes 12 ms instead
  of 56.
- Don't sleep through a timeout: give the code under test a method that moves its clock
  on, and call that instead. A test of how long the hub keeps blobs slept for 2.1 of its
  2.3 seconds; it now calls `HubService::age_served_blobs`, so it takes milliseconds and
  can't fail on a slow machine.

## Schedule for the suite, not the test

- Start the longest test first. The conformance test, the longest by far, often started
  late on 4 cores and finished alone after everything else. A nextest priority
  (`.config/nextest.toml`) now starts it first: `just test` takes 29 seconds instead of 35.
- Let an environment variable set a property test's number of cases, and default to as few
  as catch what the test is for. The conformance test makes 50 cases locally and 150 in CI,
  where it runs as a job of its own (`MUSUBI_CONFORMANCE_CASES`); `just mutants` sets 150,
  so that mutation testing still catches what it caught. A search that takes minutes, like
  the generated end-to-end search, is opt-in (`just property`) and runs nightly in CI.

## Count build time

Each file under a crate's `tests/` is a binary of its own, linked against jj-lib and gix:
35 to 40 MB, linked again after every change to the crate. So musubi-jj's and
musubi-sync's integration tests are modules of one binary each, `tests/it`, which took
rebuilding after an edit from 18 links to 11. Add a new test file as a module there, not as
a new file under `tests/`, and select its tests with `-E 'test(/^module::/)'`. Only test
sets with a harness of their own, like `races` and `e2e_search`, get a binary of their own.

## Make generated cases replay exactly

A generated case that doesn't replay exactly costs every run. Hegel, the property-testing
library the generated tests use, then treats the test as nondeterministic: it replays a
stored failure in batches to measure how often it fails, and passes the run if that doesn't
confirm it. One search shard replayed a failure some thirty times, eleven seconds each, on
every run, and never reported it.

- Nothing a case does may depend on the clock, the process, or timing; all randomness comes
  from the case. jj's change ids come from a seed counter in musubi-testutil (jj's
  `debug.randomness-seed`), the random suffix that tells machines of one name apart comes
  from the same seeded generator rather than the clock, and rules pick among commits in
  change-id order, since commit ids and `jj log`'s order depend on when commits were made.
- With that, a failure that doesn't replay is a bug, so the search fails at once, saying
  where the replay diverged.

## Keep the costs current

[testing.md](testing.md) gives what one test of each layer costs. When a change moves those
figures, update them, so that the next person knows what a normal test costs and which layer
is cheapest.
