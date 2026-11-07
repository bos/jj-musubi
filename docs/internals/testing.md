# Testing

The layers of musubi's tests, what each guards against, and how to run them.
[testing-philosophy.md](testing-philosophy.md) says what a test must protect, which layer a
new one belongs in, and what evidence each kind of change needs;
[efficient-tests.md](efficient-tests.md) says how to keep a test cheap. Terms such as hive,
node, hub and realization are defined in [design.md, "Vocabulary"](design.md#vocabulary).

Several layers use Hegel (the `hegeltest` crate), a Rust port of Python's Hypothesis. A Hegel
property test generates inputs and, on a failure, shrinks the failing input to a small case. A
stateful test is a state machine of *rules*, each with a precondition, which Hegel runs in
generated sequences. Hegel keeps failing cases in an example database and tries them again first
on the next run. *The search* is the generated end-to-end tests below, run with `just property`.

| Layer | Where | Guards against | Cost |
| --- | --- | --- | --- |
| Formal model | `formal/` (Lean) | Protocol design errors: lost operations, dangling references, duplicate merges, livelock | Proof effort, no runtime |
| Protocol property tests | `crates/musubi-core/tests` | The Rust state machines departing from the model, or not recovering from storage errors or a buggy hub | Milliseconds per case |
| Presence conformance | `crates/musubi-jj/tests/it/presence.rs` | Which copies (machines' repositories) a hive shows departing from `formal/Musubi/Presence.lean`, or changing where a contraction keeps an operation (`PresenceContract.lean`) ([conformance.md, "Presence"](conformance.md#presence); [design.md, "Copies that go away"](design.md#copies-that-go-away)) | Milliseconds per case |
| Copies conformance | `crates/musubi/src/copy/conformance.rs` | Which repository musubi takes for the copy of a key, and the daemon's check before each sync, departing from `formal/Musubi/Copies.lean` ([conformance.md, "Copies"](conformance.md#copies); [copies.md](copies.md)) | Under a second for all 4212 cases |
| Chunked blob conformance | `crates/musubi-sync/src/blobs.rs`, `crates/musubi-sync/src/remote.rs` | The blob receiver departing from the prefix receiver of `formal/Musubi/Chunks.lean`, and the senders from its attempts under a deadline ([conformance.md, "Chunked blobs"](conformance.md#chunked-blobs)) | A few milliseconds per case |
| Workspace names conformance | `crates/musubi-jj/src/workspaces.rs` | The names under which a machine shows other machines' workspaces departing from `formal/Musubi/Names.lean` ([conformance.md, "Workspace names"](conformance.md#workspace-names)) | A millisecond per case |
| Per-machine refs conformance | `crates/musubi-jj/tests/it/ref_laws.rs`, `crates/musubi-sync/tests/races/refs.rs` | jj's ref merge, import and export, and musubi's realization, departing from `formal/Musubi/Refs.lean` ([conformance.md, "Per-machine refs"](conformance.md#per-machine-refs)) | ~0.3 s per case |
| Race catalogue | `crates/musubi-sync/tests/races` | Concurrent changes on different machines resolving differently from jj's local behavior ([races.md](races.md)) | ~0.3 s per test |
| Unit tests | `#[cfg(test)]` modules | Pure logic: URL normalization and hive names across forges, matching joining repositories to hives | Microseconds |
| Example tests | each crate's `tests/` | jj integration details: translation, git refs, objects, joins, transports, the hub's hives, the CLI | ~0.2–0.5 s per test |
| Fault tests | `crates/musubi-sync/tests/it/faults.rs`, `crates/musubi-sync/tests/it/lies.rs` | Malformed requests reaching the hub's decoders, malformed replies reaching a node's, well-formed but wrong replies reaching its protocol core and repository, and links that die or stall partway through a sync | ~0.2–1.5 s per test |
| Fuzz targets | `fuzz/` | Bytes no honest peer sends reaching the decoders of frames, messages, bundles, and imported operations and views | Minutes to hours a run; opt-in |
| Kani proofs | `#[cfg(kani)]` modules | Arithmetic on sizes and offsets, and bounded hub pushes across storage failures and retries | Arithmetic under a second each; storage solver ~11 s on macOS arm64; opt-in |
| Generated end-to-end tests | `crates/musubi-sync/tests/e2e_search` | Everything interacting: real `jj` commands, real repositories, faults | Seconds per case; opt-in |

Costs are approximate measurements, mostly on 32 Linux cores; the Kani storage figure is from
macOS arm64. Use them as a rough guide; performance work needs fresh measurements alongside
the suite ([efficient-tests.md](efficient-tests.md#when-making-tests-faster)).

The core harness uses abstract operations and storage. Native tests cover repository effects it
cannot represent: advancing while merging concurrent heads, partial adoption of abandonment
records, cached restoration after rollback, and replies whose storage effects differ despite
an equal projected state. [Conformance](conformance.md) owns the correspondence to the models,
the tests at each boundary, and the limits of those checks.

## Running the tests

Documentation-only changes need review, link, spelling and formatting checks, without builds
or tests ([AGENTS.md, "Checks"](../../AGENTS.md#checks)).

`just test` runs the default suite and `just property` the search. `just check` runs formatting,
clippy, the Lean proofs and oracle smoke tests, the default suite, the rustdoc build, cargo-deny,
cargo-machete, typos and the fuzz runner's unit tests;
[testing-philosophy.md, "Beyond `just check`"](testing-philosophy.md#beyond-just-check) says when
to run the rest.

The tests need `jj` 0.47.1 and `git` on `PATH`. They don't read your own git config:
`.cargo/config.toml` hides the global and system config from the git they start, and the `jj`
and `git` they run as commands get a home directory of their own.

jj syncs each file it writes, which on a real disk takes most of the suite's time, so test
directories go in memory where they can. On Linux they go in `/dev/shm`, unless `TMPDIR` is
set or `/dev/shm` is mounted `noexec`. On macOS, `just test` makes a RAM disk for the run,
which makes the suite three times as fast; a bare `cargo nextest run` uses the disk. Setting
`MUSUBI_KEEP_TEST_DIRS` keeps the directories after a run, for inspecting a failure, and puts
them on the disk.

`clone_preflight_keeps_the_resolved_hive` creates a hive whose name equals another hive's
id, then keeps the id returned for the requested name through preflight. Reinterpreting that
id as a name switches hives and fails the test. `the_daemon_picks_up_new_repositories` also
renames a second hive to alpha's id and clones alpha through the binary, checking both the
printed hive name and the files checked out. Before the fix it printed the second hive's
name instead. A missing id must be refused even if another hive uses that string as its name.
Resolution returns a distinct `HiveId`, which clone carries through its preflight request;
passing that identity back to name resolution requires an explicit conversion to text.

`key_setup_retries_after_the_public_file_could_not_be_written` obstructs the public-key path with
a directory, or starts with an empty or stale read-only public file. A failed setup must leave
no published private key; a retry must publish a matching pair. Removing the public file from
that pair then repairs it without changing the private key. Before the fix, `ssh-keygen` saved
the private key first, and a public-file write failure left it blocking every retry. A nonempty
public file left from an older identity could also survive and be authorized on the next try.

`concurrent_first_joins_share_one_key` starts two key setups after both callers see no
key, using the real `ssh-keygen`. Both must succeed, only one may create the pair, and the
public key must match the private key. Without the key lock and recheck, the reproducer
fails when one `ssh-keygen` tries to overwrite the other's file. The existing SSH binary
workflow still checks key creation and authorization through the shipped commands.

`a_copy_without_workspaces_can_be_forgotten_by_name` removes beta's last workspace with jj,
syncs it, and resolves beta's name, qualified name and key for forgetting, including with a
reserved local prefix. Looking up copies only through their workspaces returns no match and
fails this regression. `machines_whose_workspaces_are_all_default_can_join` also runs the
real `musubi forget beta` command after beta removes its last workspace.

## Coverage reconnaissance

`just coverage` is opt-in diagnostic evidence, with no percentage gate. Install the tool and
Rust's matching LLVM tools once, alongside the normal test prerequisites:

```sh
cargo install cargo-llvm-cov --version 0.9.1 --locked
rustup component add llvm-tools-preview
just coverage
```

The recipe builds the Lean oracle, clears old coverage, instruments the workspace, and calls
`just test`, including its macOS RAM disk and nextest's default filters. It writes a source
report to `target/llvm-cov/html/index.html` and LLVM JSON to
`target/llvm-cov/coverage.json`. Profiles and reports stay under the ignored `target/` even
when `CARGO_TARGET_DIR` is set. It rebuilds the workspace's artifacts there; do not run it
concurrently with another build in the same workspace. Dependencies are not the subject of
the report, and the normal suite has no new dependency on the coverage tool.

Package, test, feature and nextest-profile selectors go to nextest just as with `just test`;
each invocation starts a fresh report. Alternate Cargo profiles, explicit targets, Cargo
configuration overrides and prebuilt test artifacts are refused, so collection and reporting
use the same build layout. Pass short options separately:

```sh
just coverage -p musubi-hub
just coverage -p musubi-jj -E 'test(/^join::/)'
just coverage --profile ci       # includes wrong-reply recovery with real repositories
```

Keep the revision, host target (`rustc -vV`), tool versions and exact command with any
conclusions. A focused run says nothing about tests it excluded. The default run excludes the
search and the longer wrong-reply recovery test; it does not run fuzzing, Kani, Lean proofs as
instrumented Rust, or doctests. The report includes test code, and generic instantiations can
have different coverage, so compare production source regions, not an aggregate percentage. See
the [cargo-llvm-cov documentation](https://github.com/taiki-e/cargo-llvm-cov) for report
formats.

`roots_find_each_history_and_stop_at_known_commits` protects the simple backend's contribution
to hive matching: all first commits in merged histories are found once, already indexed
commits stop the walk, and jj's synthetic root is excluded. The simple-backend sync examples
alone do not exercise this index walk.

`hub_join_sync_clone_and_list` also checks that agent-run creation defaults to `never`, an
explicit clone lease overrides a user default of `never`, and a rejoin lease replaces the
copy's repo policy and reaches another running daemon. Agent environment variables changing
the default, or preserving the old policy despite an explicit lease, breaks these checks.
`leases_are_explicit_durations_on_every_join_command` checks all three argument parsers and
rejects invalid or subsecond leases before setup. The CLI flow also refuses a lease shadowed
by workspace config, both in that workspace and when rejoining through a linked workspace,
without writing an operation.

`settings_stay_local_and_the_daemon_reloads_them` also changes `musubi.forget-after` in user
config while the daemon runs, waits for a sync, and checks that the other machine sees the new
expiry policy. Keeping the daemon's initial jj settings makes it fail.

`bracketed_ipv6_urls_name_one_repository` checks that scp-style and `ssh://` IPv6 remote URLs
match without conflating different hosts. `hub_join_sync_clone_and_list` joins real
repositories using those two forms; splitting at a colon inside the address makes its join
fail, saying that the repository and hive share history but not a remote.

`remote_configuration_stays_local` changes fetch and push URLs on one machine while the
other's config is locked, reopens it, and checks byte-for-byte preservation. It also keeps
an explicit reversion local. `repo_config_stays_local` checks the same boundary for rewrite
and push protections. Both fail with the removed settings reconciliation. Fetch, push,
tracking, conflicted-ref, and history tests still exercise replicated remote bookmarks with
remotes configured explicitly. `push_from_one_machine` has a copy with no remotes create work
that the other copy pushes, and verifies that the first still has no remotes. The search
configures each new copy's `origin` explicitly,
so its fetch and push rules continue reaching new and replacement machines.

`remote_bindings_are_checked_before_joining` retains approved name bindings through pending
expiry and a hub restart, rejects rebindings through `--hive` and rejoin, and checks push
mismatches and omitted names. `hub_join_sync_clone_and_list` reproduces a conflicting name
hidden by another matching remote, checks plain and explicit joins refuse without membership
or operation changes, and then joins equivalent IPv6 forms. The daemon/config binary test
also sends conflicting peer metadata and checks that clone creates no destination or parent.
`one_hub_many_hives` checks scoped join observations and index rebuilding. The envelope fuzzer
constructs nonempty join and clone binding maps and round-trips their plain operation
attributes. `inherited_destinations_match_git` compares the clone preview with Git for aliases,
longest-prefix ties, pushInsteadOf, multiple and explicit push URLs, and credentials.
`hub_join_sync_clone_and_list` refuses global and destination-conditional mismatches before
creating the clone's parent. `hub_survives_malformed_clone_preflights` checks the production
hub-wide handler with truncated and overlong requests and verifies that they reserve nothing.

`selected_defaults_fill_only_missing_values` checks default and custom clone selections,
TOML arrays, destination precedence, and opting out. `hub_join_sync_clone_and_list` clones
without an identity, checks the recorded name, email and selected alias are seeded, then
changes the source and verifies the clone keeps its seeded identity. The quick-start test
clones with a different existing identity and checks no repository identity override is
written. Disabling `clone_config::seed` makes the missing-name assertion fail in the binary
workflow. `remote_bindings_are_checked_before_joining` also pins creation defaults across
hub restart and a later join with different defaults. The envelope fuzzer includes nonempty
clone defaults in join requests.

Start with unexecuted recovery and refusal paths: reopening stored state, failed publication,
rollback, malformed input and platform adapters. Read the callers and existing assertions
before deciding a test is missing. An executed line does not show that its effects were
asserted: a recovery test must check the retained work and successful retry, not just an error
or absence of panic. A new test belongs at the narrowest existing layer that protects a
specific guarantee, and must fail when that guarantee is broken
([testing-philosophy.md](testing-philosophy.md#showing-that-a-test-works)). Do not add a test
merely to execute an uncovered line.

Coverage is local to the compiled platform: macOS cannot report uncompiled Linux or Windows
branches. Collect on those hosts before drawing conclusions about them. Hermetic test
commands preserve `LLVM_PROFILE_FILE` so instrumented musubi subprocesses contribute too;
a daemon or hub killed before it flushes its profile can still look unexecuted. Tests that
skip for missing prerequisites and processes that abort have the same limitation. Check test
output and process lifetimes before treating a blank region as a missing test.

## CI

CI runs clippy and the default suite on Linux, macOS and Windows, since each compiles code the
others don't, with the tests too slow for `just test` (nextest's `ci` profile); each first builds
the Lean oracle (the executable model, [conformance.md](conformance.md)) for the tests that check
the code against it. On Linux it also runs the rest of `just check`'s lints (formatting, rustdoc,
cargo-deny, cargo-machete, typos), checks the Lean model's proofs, and runs each benchmark script
once (`just bench-smoke`).

The Search workflow runs the search nightly on Linux, each shard on a runner of its own, with a
seed that changes from run to run. A failing shard uploads its example database; its output
gives the seed and a `reproduce_failure` attribute for replaying the failure locally.

The jj main workflow rebases `jj-next` onto the musubi revision under test, then builds it
against jj's main branch and runs the `ci` test profile, including its conformance timeouts
and wrong-reply tests.
[AGENTS.md](../../AGENTS.md#building-against-jjs-main-branch) says what belongs on `jj-next`.

To test against a checkout of jj outside this workspace, use a clean, disposable musubi
workspace with the appropriate `jj-next` changes:

1. Run `.github/scripts/use-jj-checkout.sh <jj checkout>`.
2. From this workspace, build the matching jj with `cargo build -p jj-cli --bin jj`, which the
   script has pointed at the checkout, and put `target/debug` on `PATH`.
3. Run `cargo nextest run --workspace --profile ci`.
4. Afterwards, discard only the script's edits and its `Cargo.lock` changes, or remove the
   disposable workspace.

## Protocol property tests

A Hegel state machine owns a hub and several nodes, all of them `musubi-core`'s sans-IO state
machines (they do no I/O themselves), joined by a simulated network that the test controls
completely. Operations are abstract: ids, parents and object sets, with no jj repository.
The rules, in the terms of [protocol.md](protocol.md):

- **Environment**: a node makes a local operation on some local parent, not necessarily a head.
- **Progress**: a node takes the next step of its policy ([protocol.md,
  "Policy"](protocol.md#policy)), merging if it has several heads; sends a poll's `Fetch`; or
  takes a policy step whose requests and replies go through at once.
- **Delivery**: deliver any message in flight, in any order, or deliver one again. A message
  never delivered is lost.
- **Misbehavior**: a node pushes without uploading; a hub replies with operations it never
  accepted; or a hub forgets everything outside `closure(head)` (the head's history and the
  objects it needs), including uploads it never accepted. In one test only, a node also takes
  false replies (`false_reply`): any made of what the hub stores, about any head, with a
  sequence number near the node's or the hub's, or the largest, as an answer to its own
  request or a late one.
- **Failure**: crash a node or the hub, keeping only persistent state, or crash a node partway
  through taking in a fetch. Send the hub back to an earlier head, as a power cut that loses
  the last heads it accepted would (`hubRegress` in the oracle), or make the hive again,
  empty, as the hub does one whose store is corrupt (`hubRegress` to 0, then `hubForget`). A
  node whose own request gets a reply with a head older than it knows, or another at the same
  sequence number, starts over from that reply (`loseKnown`, then `learn`).

Two tests run this machine: `protocol_invariants`, and `conformance`, which also checks every
step against the Lean model. A third, `nodes_recover_from_false_replies`, adds false replies,
which the model has no hub to send, so it runs without the oracle.

`storage_failures_preserve_operations` adds a deterministic countdown over actual fallible
`HubStorage` and `LocalRepo` calls to the generated protocol sequences. It fails before a
call, after selected complete logical effects, or after a nonempty proper prefix of an
operation/object import. The countdown, timing and surrounding actions are Hegel draws, so
failures shrink and replay. Immediately after an error, before recovery, the harness checks
closure, retained operations and objects, and reachability of the previously published heads.
It then follows the daemon: reopen the node's logical store and restart its core; a request
handling error keeps the hub adapter and reaches the requesting node as a failed sync.
Pruning upkeep errors keep the hub adapter without failing a node. Every case finishes with
faults disabled and the usual convergence/retention checks.

`storage_boundaries::every_storage_boundary_recovers` sweeps every countdown in a fixed
schedule of concurrent work, fetching, missing-object recovery, pruning and held-record
adoption. Its coverage assertion requires 39 reachable fallible trait methods, nine
complete-effect error boundaries and four proper import-prefix boundaries; none needs a real
repository fixture.
The sweep takes about a second on macOS. Both generated oracle tests use
`MUSUBI_CONFORMANCE_CASES`. The oracle checks prefixes it can represent; partial
merged uploads or partial bundle receipt explicitly retire it for that case while the Rust
checks continue. [Conformance and limits](conformance.md#storage-errors) lists the adapter
assumptions, recovery projection and error effects this abstraction cannot represent.

After every rule the test checks the model's safety invariants ([protocol.md,
"Properties"](protocol.md#properties)): HubClosed, HubMonotone, NodeClosed, Locality,
MergeOwnership, KnownIsHubHistory, and that a node stages only operations the hub accepted
(staged-is-accepted). Once the hub has gone back, Locality, staged-is-accepted and
KnownIsHubHistory are checked against its history together with the heads it lost, and
MergeOwnership no longer is: two nodes can then merge the same heads
(`formal/Musubi/RegressScenario.lean`). Once a node has taken a false reply, those four no
longer hold of it: it may have operations the hub offered it but never accepted, and nothing
else of other nodes', and its `known` may be anything. NodeClosed is still checked, with the
fake repository refusing to realize an operation without its parents or objects.

A final `quiesce` step stops environment actions, makes the network reliable, and runs every
node's policy until nothing changes. The test then checks liveness: every node's heads are
`{hub.head}`, and every operation created is in its ancestry, after false replies too. A bound
on quiescence steps turns livelock into a failure. While quiescing, `conformance` also asks the
Lean model for its liveness measures after each exchange, and requires them to fall whenever
the exchange changes the node, including its ordered applied records. The refined measure
appends the number of record mismatches to the eight set-based components.
`regrouped_records_conformance` reaches a remake and republication that preserves the dropped
union but changes record grouping, then checks the record-only adoption's strict decrease.
Every push the policy sends must upload what the
[liveness proofs assume](conformance.md#liveness).

## Example tests

These pin down jj-specific behavior with real repositories made by the `jj` CLI in
`musubi-testutil`'s hermetic environment.

`translation::failed_realization_writes_forget_the_batch` blocks one real op-store view or
operation destination with a directory, reaching a background write error rather than deleting
files after writes finish. A recorded fixture shares setup among the three failure/recovery
cases. [Conformance](conformance.md#storage-errors) describes the batch invalidation, recovery
and publication checks and their limits.

### The hub and the CLI

`failure_logs_read_operation_heads_without_changing_them` checks that CLI failure diagnostics
find a moved repository and read both concurrent operation heads without snapshotting or merging
them. No hub or daemon runs for this check.

`musubi-sync/tests/it/server.rs` runs one hub serving several hives over the in-memory
transport: a first copy creating a hive; a copy with the same remote spelled differently
joining it; a fork getting its own; an unrelated repository refused; requests for a hive the
hub lacks failing; and listing, renaming, removing, and an index rebuilt after a restart.
`musubi-hub`'s unit tests cover URL normalization, naming, and the matching rules case by
case.

`hub::request_tests` checks the command side of hub requests over the in-memory transport:
no responder, a hub's refusal, and a caller's deadline, with Tokio's clock paused. Missing
local hubs fail without waiting, both before a hub directory is made and after its server
stops. `a_hub_restarts_in_its_directory_and_keeps_its_advertised_name`, Unix only, starts a
real hub, checks both directory and per-user lock refusals, stops it with SIGTERM, checks
socket cleanup, then restarts it from its directory with its saved advertised name. It also
checks that a default symlink path too long for a Unix socket leaves usable explicit `--hub`
instructions. The clean stop lets an instrumented hub flush its coverage profile.

`musubi/tests/cli.rs` runs the binary as a user would: `musubi hub`; `musubi create` starting
a hive and `musubi join` matching it, over the hub's socket and over a stand-in for ssh whose
shell prints a banner first; `musubi clone` by a prefix of the hive's name; `musubi list` and
`leave`; and each machine's daemon. The first `create` or `join` starts the daemon in the
background, and it serves a repository added later without a restart, even when that `create`
ran with git's variables naming another repository, as in a git hook. Each test machine has
its own state directory and jj config, and so its own daemon and control socket; the tests stop
the daemons when they finish. One test, Unix only, turns on commit signing with `ssh-keygen`
as jj's signer and checks that the commits musubi rewrites are signed, which shows that the
binary loads jj's config as jj does. Another, Unix only too, puts a stand-in for a hub of a newer
release on a hub's socket, and checks that the daemon runs `musubi.upgrade-command`, starts
again in place once its binary is that release, and that `musubi status` shows an upgrade that
installed nothing; it can't run a real newer release, so the command installs a script that
only says it is one. A third, Unix only, runs `contrib/upgrade-from-source`, the example
upgrade command, against a stand-in for musubi's source that builds in a second, and checks
that it installs a release from its tag and a deployed build from its commit, not from `main`
or the edit in the working copy; that `--deploy` installs `main` as a build named for the time
in UTC, between the clock's readings before and after, and its commit; that it leaves the
repository's operation log as it was; and that it refuses, installing nothing, no release, a
release with `--deploy`, what isn't a release, a release or build the repository lacks, and,
once the repository has a remote, a deploy of a revision the remote lacks. The stand-in builds
with musubi's own build script, which names the build. It doesn't fetch a commit or tag from a
remote.

The existing `hub_join_sync_clone_and_list` fixture also checks `debug op-id` in both
directions, with odd-length prefixes, invalid hex, and an absent operation, and in a
repository in no hive, where it makes no machine key. Its snapshots
keep local and hive ids distinct. `debug_identifies_an_operation_received_but_not_realized`
transfers operations and views from a real repository through the canonical store's import
APIs, without realizing them, and checks the command's message. It starts no hub or daemon.

`upgrade::process_tests` in the binary's Unix unit tests runs the real upgrade worker in
separate disposable processes, without a repository, hub, service manager, or installed
daemon. A shell waits for an installer controlled through a local socket. The tests kill
one worker while its command runs, check that the inherited lock still excludes a new
worker, and let that same worker retry after the command exits. Other cases expire the
wait only after the installer has acknowledged starting, or have it exit unsuccessfully;
they check the failure reason, saved command output, once-per-lifetime attempt gate, and a
successful retry that removes the failure and requests a restart. The timeout test fails
before the Unix process-group fix: the shell stops but its foreground child keeps its
socket and lock. Socket handshakes bound synchronization; the wait callback is the only
production seam, and supplies an already-expired timeout instead of waiting an hour.
These tests cover ordinary foreground children preserving standard input, not detached
installers, children that close or redirect the lock, Windows processes, or login services.
The CLI test above still covers the command, daemon restart and status output.

`top::tests` renders the production `App::draw` into Ratatui's `TestBackend`, with inline
snapshots preserving screen rows and cell assertions checking warning colors and selection.
It covers loading, empty hubs, navigation and detail selection, resize, disappearing hives,
unreachable hubs, issue overflow, refresh speed limits and quit keys.
`a_silent_machine_is_an_issue_once` checks that continuing silence leaves room for new issues
while keeping the hive's count and red rows, including departed copies' retained reports. It
checks that contact between sparse polls rearms the warning even if the next poll is silent too.
Its timing tests run the production sampling loop with Tokio time paused. They advance across
refresh deadlines,
change intervals, release slow samples, and exercise shutdown. Rate calculations
read that same clock, including simultaneous samples and a restarted hub.
`top::sample::tests::a_failed_hub_is_retried_at_the_deadline` advances to either side of the
reconnect boundary; its only connection attempt is to a missing local hub. These tests start
no daemon or ssh process. `hub_join_sync_clone_and_list` reuses its hub and daemon for PTY
checks through `termlens`: the real binary handles speed keys and resize, and restores its
alternate screen and cursor after `q`, Escape and Ctrl-C. Screen predicates synchronize these
checks; they do not wait for a periodic refresh. PTY tests use real process deadlines to catch
hangs; they cannot control the child process's clock.

Tokio's `test-util` feature supplies the virtual clock for async timer tests; use
`#[tokio::test(start_paused = true)]` and `tokio::time::advance`, with `tokio::time::Instant`
for elapsed-time decisions. Pausing does not affect `std::time::Instant`, wall time, other
runtimes or child processes. Poll a timer-backed future before advancing to register its
deadline, and check its observable effect afterwards: `advance` alone does not run every
awakened task. Avoid waiting on an idle runtime when checking an unexpired timer, since Tokio
automatically advances paused time to the next timer when nothing can run.
`daemon::tests::retry_wait_expires_or_answers_commands` checks retry expiry, a sync interrupt
and command-channel closure with this clock. SSH's
`ssh_backoff_is_bounded_and_a_wake_retires_old_failures` crosses each exponential backoff
deadline, including the cap, then checks greeting and wake resets without rewriting private
deadlines. The sleep detector still compares real wall and monotonic clocks, since it detects
the operating system suspending; the supervisor tests inject its wake notification.

`copies_leave_a_removed_hive` checks that copies leave a hive removed from the hub, keeping their
work, and that `musubi leave` then takes such a copy out as any other. Before taking its final
listing snapshot, it waits for both the saved membership and the daemon's reported repository
count: the daemon saves membership before it finishes cleanup, so the membership file alone cannot
tell when its thread has stopped.

`recreating_hives_keeps_work_without_inheriting_remote_workspaces` follows the upgrade
guide with two copies and a real linked workspace whose name contains `/`, including the
first copy leaving before the other. It removes old remote workspace names, archives both
copies' musubi state and the hub, then creates and
joins a fresh hive. It checks that both copies retain their commits and show exactly the
local and remote workspaces expected. Omitting the workspace cleanup republishes old remote
names as new local workspaces. This exercises recreation with the current release, not
compatibility with an earlier release's files.

`the_quick_start_works_as_written` follows the README's quick start as a new user would:
`musubi hub` run in a repository rather than in the home directory, then the commands it
prints, pasted as printed, on the hub's machine and over the stand-in for ssh, the refusals a
new user meets first, and `musubi list` with no `--hub`. Its inline insta snapshot is
everything the user sees, so a change to what a new user meets shows in the diff. Change the
quick start and the test with it. `cargo insta review` accepts a new snapshot. No test reaches
a real machine over ssh: `musubi-testutil` points `MUSUBI_SSH` at a program that doesn't
exist, so a test that needs ssh must give a stand-in.

`login::process_tests` runs installation in disposable child processes with private home,
config and state directories and stand-ins for launchctl or systemctl. It checks failed
installation leaves no marker and no service file, successful installation records one, the
daemon and hub keep separate markers, only the intended environment reaches the service, and
uninstall works even after its service file was removed. On macOS it checks both GUI and
background launchd domains. These tests never reach the real service manager; they do not
check that it accepts the files or runs musubi.

Two CLI tests put a stand-in for launchctl and systemctl first on the `PATH` instead, one that
runs the hub an installed unit or agent names as the service manager would.
`daemon_install_and_uninstall_leave_the_daemon_as_they_say` checks that a daemon install the
service manager refuses leaves the daemon running and nothing installed, and, first, that the
daemon starts under a umask that lets the group write.
`a_refused_hub_install_leaves_the_installed_hub_running` checks that installing a hub for a
directory another hub serves refuses before it stops the installed one.
`one_daemon_serves_a_machine_wherever_it_listens`, without a service manager, checks the
daemon's socket: a setting's `~/` and refusal of relative paths, commands finding the daemon
where it listens, the refusal of a second daemon on another socket, and stopping and listening
again after the socket is deleted.

Two CLI tests install real login services, and so run only with
`MUSUBI_TEST_LOGIN_SERVICE=1`, which CI sets on its throwaway runners: never set it where
musubi is installed for real. One installs the daemon with launchd or systemd and checks that
the service manager starts it, restarts it after it is killed but not after
`musubi daemon stop`, and starts it for a command that needs it; on Windows it runs the `Run`
registry entry's command as a login would. The other installs the hub, and checks that a
repository syncs through it, that the service manager restarts it after it is killed, that
installing it again for another directory replaces it, and that `musubi hub uninstall` stops
it; on Windows, which runs no hub at login, it checks the refusal, which changes nothing, and
so runs always. CI's Linux runners have no systemd user manager without a login session, so
the workflow enables lingering and starts one first. Logging in itself is the one step no test
exercises.

## Faults

The protocol tests lose, duplicate or delay whole messages but never corrupt one, as
[protocol.md](protocol.md) assumes. `musubi-sync/tests/it/faults.rs` and `lies.rs` test the
implementation where that doesn't hold, and `faults.rs` where a link fails partway through a
call.

It records a real session over the in-memory transport: one machine pushes a commit, another
fetches it and pushes its own, and the first fetches that. The payload limit is small enough that
each commit's objects travel as a blob in several windows of chunks ([design.md, "Size limits and
chunking"](design.md#size-limits-and-chunking)). A case can start at the start of any call in the
session, from a snapshot of the hub's directory taken then. The session is recorded once per build
of the test binary, under `target/tmp`, as is the hive most race tests start from
([efficient-tests.md, "Make an expensive fixture once per
build"](efficient-tests.md#make-an-expensive-fixture-once-per-build)).

- `hub_survives_malformed_requests` sends the hub requests no honest node sends: the session's
  requests and bundles cut short, corrupted or spliced; chunks at extreme offsets; malformed
  requests sent as blobs; made-up ids, some as long as a commit's, an operation's or a SHA-256
  hash, and attachments; and envelopes from another protocol version. The hub must answer each
  without panicking; its head must move only forward, to operations whose closure it has
  (HubMonotone and HubClosed); and afterwards it must still answer a fetch from the root.
- `calls_survive_malformed_replies` gives a node, partway through one of the session's calls,
  replies no honest hub sends in place of the hub's. Half are the real reply with its numbers
  wrong: acknowledgements of any amount, chunks of any total or with the wrong data, indirect
  replies and attachments of any length. The rest are the real reply corrupted, another
  request's reply, a reply of another kind, garbage, or a reply from another version. Requests
  are picked by kind, so that a call's one protocol request is as likely to get one as its
  dozens of chunks. The call must end without panicking or sending requests forever, and,
  once the hub answers honestly again, get the reply it got in the session.
- `calls_finish_once_the_link_is_back` makes one of the session's calls through a link that
  fails at a chosen request, in one of three ways: the request and everything after it are
  lost, as when the wifi goes off; the request arrives but its reply and everything after it
  are lost, as when a lid closes just after it went; or it arrives an hour late, after the hub
  has swept away transfers in progress. Meanwhile the hub may receive malformed requests made
  from what the node sent. Once the link is back, the call, made again, must get the reply it
  got in the session (unless a malformed request happened to be a valid push that moved the
  head), within a bound on the number of requests.
- `node_recovers_when_its_link_fails_partway` fails the link the same ways with real
  repositories and the node's driver, retrying as the daemon does, while another machine
  syncs. Afterwards both machines must see the same commits. It is slow, so it runs few cases.

`server::tests::a_worker_reopens_its_service_after_a_panic` runs the production hive worker
with real jj repositories and storage. Its per-worker, test-only hook panics once after a push
has accepted a head, before the server prunes records, counts the request, updates the hive index,
or sends the reply and notice. The error leaves the accepted head in place: a fetch to the same
thread must reopen its service and find that head with its closure intact. Counting successful
service opens makes removing the panic path's reset fail even if retaining the service happens to
work. Honest
syncs then copy both earlier and later work to another repository, all subsequent published heads
have their closure, and another hive sharing the hub directory and activity still syncs. This
boundary does not interrupt an import or a write, poison a lock held inside jj, or exercise the
separate catch around activity summarization. It promises neither rollback nor power-cut
durability.
`server::tests::a_hub_slower_than_the_timeout_still_syncs` uses the same hook to count the
protocol requests the hub works out an answer to, and a link that turns each such reply into a
timeout, as when the hub takes longer than the node's timeout to prepare it. Two machines must
still push and fetch, over messages small enough that requests, replies and bundles travel as
blobs. It fails if the node doesn't send a request again after a timeout, or if the hub works
out the answer to the repeat again rather than repeating its reply. The hub is never actually
busy, so a repeat never waits behind the first. What the thread does with a request that
waited behind others past its sender's deadline is
`server::tests::requests_their_senders_gave_up_on_go_unanswered`'s: it holds a hive's thread on
one request while two time out behind it, a chunk of an upload and another, then checks that the
thread stored the chunk, and, in the hub's activity, that it answered the requests before and
after but not the other one. It fails if the thread works out every request it takes, as it
did, or lets go of the chunk too.

The existing `a_request_that_panics_the_hub_gets_an_error` separately reaches a real jj decoder
panic from malformed peer input; the protocol storage-call fault tests cover their own boundaries.

Smaller tests cover how long blobs live: a blob the hub prepares again for a second fetch lasts
as long as a new one (`blobs_prepared_again_last_as_long_as_new_ones`); uploading the same
content leaves a prepared blob alone (`uploads_leave_prepared_blobs_alone`); and a call that
fails or is dropped partway leaves no uploads behind, and no downloads but a partial one, kept
for a later call to resume (`calls_leave_no_uploads_behind`, `calls_leave_no_downloads_behind`).
A push and a fetch slow enough that the hub sweeps old blobs as they go still get their replies,
moving no chunk twice: the hub renews a blob a chunk moves to or from, and the node keeps the
call's other blobs at the hub while one moves (`blobs_last_while_chunks_of_them_move`). Over a
link that carries back in time only the first chunk of each window, a push and a fetch time out
again and again but finish, never asking again for a chunk whose reply came
(`calls_finish_on_a_link_that_cuts_every_window_short`); a push the hub never answers in
time gives up, though it uploads its request again each time it asks
(`calls_give_up_on_a_request_never_answered`); and a push and a fetch of more than a window of
chunks finish over a link that carries each chunk in 80 seconds, one message after another each
way, on Tokio's paused clock, with the production deadline, no chunk crossing the link twice
(`calls_finish_on_a_slow_link`). With one deadline for a whole window, its later chunks are cut
short, still cross the link, and cross it again behind the next attempt's, which then times out
too, until the fetch gives up; with the 30-second deadline musubi had, no chunk comes back in
time at all. Only the node's clock is paused: the hub's lifetimes run on the real one, so the
test never ages a blob, and no window is cut short, so it never asks again for a chunk of the
last window, which is what the hub keeps a served blob 18 minutes for. Nor does any test pin
ssh's keepalive settings, which were measured by hand over a throttled link.

`musubi-sync/tests/it/lies.rs` goes past the code that reads replies off the wire. Its
`nodes_recover_from_wrong_replies` gives a node, partway through a sync with real repositories,
replies that decode but are wrong: a head of any kind, sequence number and operation; a fetch
with its head another, its operations dropped, repeated, reordered or with other parents, or
its bundles others from the sync; objects for other operations; or another request's reply.
They are made of what the node has sent and been sent, and of its own head, which the hub
doesn't have yet. The sync must end without panicking, and once the hub is honest again, both
machines must show the same commits, everyone's among them, a node whose sync failed
restarting as the daemon does. The hive runs in process (`Hive::sync_through`), without the
transport or the daemon's driver, from a hive recorded once per build. It takes half a minute,
so it runs on CI but not in `just test` (`cargo nextest run --profile ci` runs it locally).

The truncated messages stand for a buggy or mismatched peer, not a dropped connection: the
stream transport frames each message with its length and drops one whose connection ends
partway through, so a dropped connection looks like a lost request or reply, which the link
faults cover.

The async stream boundary has generated tests in
`musubi-transport/src/stream/io_tests.rs`. One-byte pipes run the real client through
cancellation before, during and after transmission, timeout, disconnect, late replies and
bounded writer-queue pressure. Scripted I/O splits consecutive frames, inserts `Pending`,
and ends or fails reads and writes at generated offsets; writes also cross the buffer size.
The real hub relay forwards a complete request, then loses the next frame partway through:
that frame is never published, and the outstanding request future is dropped. Hegel shrinks
and saves failures; a paused Tokio clock makes waits deterministic. These tests do not run
ssh, socket readiness, the daemon supervisor or a repository sync; the transport contracts
cover reconnection and subscription reuse, and the sync fault tests cover lost calls.

Focused stream examples also reject excess silent subscriptions, unanswered requests and
duplicate live ids, and check that an answered request frees its id and slot. Client examples
keep subject sharing available at the subscription limit and refuse excess subjects and calls.
The CLI's existing clone scenario refuses both an occupied directory and an existing Git
directory before either gains jj state or joins the hive. The ssh scenario also fills the
destination while a clone contacts the hub, which must refuse it on returning. A relay example
finishes a request while reading part of the next frame: its reply goes out and the partial
frame retains its bytes.

The Unix process tests in `crates/musubi/src/ssh/supervisor_tests.rs` exercise the shipping
ssh supervisor, stderr reader, output wrapper and health tracking with controlled children
of the test binary. Pipe messages signal readiness and EOF; no test sleeps to arrange a
race. A child that ignores EOF is killed and reaped, and an explanation of the failure waits
for the supervisor to record why it didn't connect; a descendant holding stderr open
cannot hold up failure reporting. A megabyte of stderr must drain without blocking the
child, retain a bounded tail and preserve its final diagnostic. Wake notifications during
both cleanup waits must retire the old connection without restoring a stale failure; a
separate health test checks the same exclusion after a wake has already been published.
The greeting test distinguishes shell output from the hub answering, and a settled
connection must preserve the transport's diagnostic without counting it twice.
`a_wake_reconnects_the_real_transport_and_notifies_its_users` runs the real stream client
and relay through those process pipes, forces a wake, awaits the reconnection notification,
and exchanges requests before and after it. These tests inject the notification; they do
not suspend the machine, detect real sleep, run ssh, authenticate, or reach a remote host.
The bounded cleanup tests use the production one-second limits and run concurrently.

## Fuzzing

The fuzz targets in `fuzz/` make malformed input from nothing, where the fault tests make it
from a real session. They are coverage-guided, run by libFuzzer through cargo-fuzz, one for
each decoder of what a peer sends, and each checks more than that nothing panics:

- `frames`: frames read from a byte stream. Each encodes to exactly the bytes it was read from,
  since a frame has only one encoding.
- `greeting`: what the hub's machine prints before the hub greets. The greeting is found only
  at the end of a line, within the noise allowed before it.
- `envelope`: messages of each kind, most behind this release's versions, which the fuzzer
  would otherwise have to find first. A message that decodes re-encodes to one that decodes
  the same, and that encoding with a byte after it is refused. (postcard accepts varints
  longer than they need be, so a message can have more than one encoding.)
- `bundle`: bundles, most behind the header. The records of one that reads, written to a
  bundle of their own, compressed or not, read back the same.
- `canonical`: operations and views imported into a canonical store, under an id they don't
  hash to and then under the one they do, which reaches the checks past the hash. One admitted
  reads back as what it hashes to, and none, admitted or refused, leaves the store holding
  anything that isn't what its name says. jj-lib, and jj-core beneath it, panic on some
  malformed input, so a panic in them counts as a refusal, as it does on the hub; a panic
  anywhere else fails.
- `import`: bundles of a small history imported into a canonical store. Each view comes in one
  of three encodings that decode to it, or as bytes of the fuzzer's, whole or as a delta against
  any encoding of any view before it; some are sent twice or with a byte changed, some without
  their operation. Whatever the store makes of a bundle, it holds nothing that isn't what its
  id says, in normal form. A whole bundle such as musubi makes is stored byte for byte as sent;
  the fuzzer's empty first input is one. Panics in jj-lib and jj-core count as refusals, as for
  `canonical`.

`just fuzz` builds all targets once, then spreads workers across them, using the available
CPUs. Each worker runs for 300 seconds; `just fuzz all -max_total_time=3600` gives each an
hour. With fewer workers than targets, targets run in batches so that each gets a turn.
`just fuzz bundle` puts all workers on one target until stopped, and takes libFuzzer's
options after the target, as in `just fuzz bundle -max_total_time=300`. Set the total worker
budget with `--jobs N` or `MUSUBI_FUZZ_JOBS`; for example, `just fuzz all --jobs 4`.
Workers on the same target share its corpus, reloading each other's discoveries. A worker
failure stops the run and the other workers, prints the end of its log, and exits nonzero.
Each run keeps separate worker logs under `fuzz/target/fuzz-logs/`; crashes stay in
`fuzz/artifacts/<target>/`. Replay one with
`cargo +nightly fuzz run <target> fuzz/artifacts/<target>/<crash-file>`. Ctrl-C stops all
workers too. Use the runner's `--jobs` to set parallelism; libFuzzer options that start
subprocesses and positional replay inputs belong in `cargo fuzz run` instead.

`just fuzz-smoke` builds once and runs each target for 2,000 inputs, with one worker per
target up to the same CPU budget, to check that they still build and run. The runner needs
Python 3.9 or newer, `cargo-fuzz` and a nightly toolchain from rustup, on Linux or macOS.
`fuzz/` is a workspace of its own, so that `just check` neither builds nor lints it.
Its targets reach private code only through `cfg(fuzzing)` modules, which cargo-fuzz sets and
the tests build too, so that `just check` checks them. Corpora and crashes stay in `fuzz/`,
unversioned, and the files the targets write go in `/dev/shm`.

The files musubi appends lines to have Hegel properties beside their parsers instead:

- the translation map, the joins and local original evidence: among whole lines, a line
  torn anywhere names nothing,
  and the whole ones are read;
- a node's logs of renamings and of how records renamed the hub's history: with more appended
  after, a line torn anywhere names nothing, and a block counts as far as its whole lines go;
- the hub's log of heads: cut where a line ends, it reads as the heads before the cut; cut
  anywhere else, it is corrupt;
- a hub store whose `heads` or `backend` a crash or a disk damaged opens as it was, or is
  corrupt and made again, and never fails as if the damage were temporary;
- the canonical store's log, damaged from any point on (cut short, zero-filled, garbled, or
  grown with zeros), reads each operation and view back as written or not at all, loses only
  what was written after the damage, and is whole again once the next record is appended; two
  writers sharing one log each find what the other appended.

## Kani proofs

[Kani](https://model-checking.github.io/kani/) checks a Rust function for every value of its
inputs at once, rather than for those a test or a fuzzer happens to try, and gives a failing
input when it finds one. It suits small, pure arithmetic on numbers a peer sends or a hub
offers, where the case that goes wrong is one no test would pick. A small finite storage
adapter also makes bounded retries tractable:

- `blobs::proofs`: where the bytes of a chunk that extend what a blob's receiver has start,
  for any length so far, offset and chunk length, including offsets near `u64::MAX`.
- `wire::proofs`: a chunk leaves at least as much room for its envelope at every payload a
  hub may offer as at the smallest, where the unit test `a_full_chunk_fits` shows that it is
  enough.
- `service::proofs`: the hub's check for the last chunk of a download can't overflow, for any
  offset and length a node asks for, and holds exactly when the read reached the end.
- `remote::proofs`: each window of chunks an upload or download sends starts at its offset,
  goes up a chunk at a time without overflowing, and either reaches the end or is a full
  window, of any size up to eight.
- `musubi-core::storage_proofs`: the production push handler over a three-operation graph,
  with two independently faulty pushes, retained import subsets, a complete honest retry
  and an idempotent replay. It checks closed monotone heads and truthful replies, in about
  11 seconds of solver time. [Bounds, adapter assumptions and mutation
  evidence](bounded-verification.md) distinguish this opt-in check from unbounded liveness
  or verification of the real storage adapters.

It is slow on code that handles strings or long buffers: a proof that `fit_error` cuts a
message to fit, which takes more than 1 KiB of message to reach the cut, ran for 15 minutes
without finishing. Keep that to the fuzz targets and Hegel. A harness that collects into a
`Vec` can run out of memory where one that walks the same iterator takes a second.

`just kani` runs every proof, and takes cargo-kani's options, as in `just kani --harness
window`. It needs `cargo install --locked kani-verifier` and then `cargo kani setup`, once.
The proofs build only under `cargo kani`, so `just check` doesn't build them. CBMC, which Kani
runs, can take all a machine's memory on a proof it can't finish, and macOS enforces no
`ulimit` on memory, so `just kani` stops the run once it holds more than `KANI_MEMORY_MB`
(4096 unless set). Run Kani only through it.

## Generated end-to-end tests

A Hegel state machine drives two or three real colocated repositories, each served by a musubi
node, through an in-process hub. `musubi_sync::hive::Hive` delivers their requests to the hub
directly, one step at a time, so that a failing case replays exactly, and has the hub prune its
records after each request, as a hub does. The rules fall into groups, kept separate so that the
inconsistent states between them get explored: a machine can work on a stale view, git can move a
branch jj hasn't imported, a node can stop halfway through a sync.

- **Local work**, through the `jj` CLI on a chosen machine: commit, edit without snapshotting,
  describe, new (including merges), rebase, squash, abandon, resolve, bookmark and tag changes,
  undo, `jj op abandon`, and commands at an older operation (`--at-op`), which create
  concurrent operations. `trim_below_accepted_push` publishes a new child, pauses before
  advancing the saved base, and trims the earlier history, including the joins: this reaches
  accepted-frontier discovery and loss of all local parents without waiting for a sequence
  of independent rules to line up. `e2e_trim_below_accepted_push` exercises that rule with
  the independent import and history checks. `trim_below_accepted_forget` instead leaves
  unpublished work above an accepted forget and trims both watched accepted frontiers;
  `e2e_trim_below_accepted_forget` runs that rule through the same independent checks.
  The reference captures recipient merges before
  receipt, including setup and pre-sync local merges: a trim published elsewhere may
  reparent them while keeping their views. Only an independently captured operation with
  unchanged nonparent content qualifies; a replacement copy starts its capture afresh.
- **Workspaces**: add, rename and forget them; forget another machine's; and rewrite or abandon
  another machine's working-copy commit.
- **Copies**: forget another machine's copy, with `musubi forget` or once it has gone unused
  past its `musubi.forget-after`; forget one, abandon an operation, and sync the rest of the
  hive while the forgotten copy is away, so that the hub prunes the record it never took, as
  one rule, which a sequence would rarely do by itself; or, with two machines, have a third
  join, with an empty copy made as `musubi clone` makes one.
- **The remote**: someone outside the hive advances `origin`; a machine fetches or pushes.
- **Git-side work**: move or delete a branch with `git`.
- **Sync**: one node syncs until it is idle, or takes only a few steps of a sync, which may stop
  partway through an upload.
- **Faults**: restart or crash a node, with or without its translation cache, or while it is
  still writing realizations; restart the hub, or send it back by dropping the last one to
  three lines of its `heads` before it restarts, as a power cut would; have it lose the `heads`
  log its latest prune wrote, going back to the one before, as a power cut just after the
  prune would; have it make the hive again, empty, as it does when its store is corrupt; or lose
  a reply the hub sent. Faults are capped per sequence, so that a short sequence still reaches
  recovery.

Every sync step must succeed, but for two stops a user recovers from as the error says. One is jj
failing to merge a machine's operations with the hive's ([races.md, "Known jj
limitations"](races.md#known-jj-limitations)), which the test gets past by reverting the operation
named. The other is a copy that lacks the exact chain the hub pruned, identified by count and
digest. The test records presence, known copies and reports at the actual prune. A refusal is
expected only if the hub did not wait for that copy then and the copy lacks that exact prefix.
Holding another chain with the same count does not suffice. A later indirect push can make the
copy present again, so current presence cannot decide this check. Anywhere else the refusal
fails the case. The user then
makes a new copy with `musubi clone`, bringing nothing across, and runs `musubi leave --force` in
the old one, which tells the hive nothing: the new copy takes the old one's place in the rest of
the sequence, and the old one, out of the hive, is out of the checks.

After each rule, every repository must still load, and no import of git refs or of git's HEAD
may revert anything (`e2e_search/imports.rs`; for refs, `noSpuriousRevert` in
`formal/Musubi/Refs.lean`). Every `jj` command imports any difference between its record of
`.git` and `.git` itself as a change made with git, so a record musubi gets wrong moves a
bookmark back with no git command run. The search makes every move git makes of a machine's refs
outside `jj` itself, so it records, per machine, which refs git moved since jj last imported
there, and what `.git` had before. Each operation that imports (jj's "import git refs") may
change a bookmark, remote bookmark or tag only through a ref git moved in that time, from the
value `git_refs` had, or where jj's merge of two op heads that both changed `git_refs`
left the record different from the physical ref (`concurrent_records_revert`). A conflicted
remote bookmark or a restored bookmark alone is not an explanation: jj 0.47 imports only
physical refs that differ from `git_refs`. Otherwise the check walks back from the import to
the operation that left the record differing from `.git`, and the failure names it. Imports of
git's HEAD
("import git head"), which move a workspace's working copy onto what HEAD has, are checked the
same way against jj's record of each workspace's HEAD (`git_heads`). git moves HEAD only where
it is still a symbolic ref to the branch git moves, as in a new repository until jj first writes
HEAD, and jj writes HEAD only as it records it, so such an import may change the record only
after such a move, or where jj's merge of two op heads that both changed the record left it
differing from `.git`, as after a command at an older operation (`--at-op`), which still writes
HEAD ([races.md, "Known jj limitations"](races.md#known-jj-limitations)).

At the end of a sequence, and at most once in the middle, the hive syncs to a fixed point,
and the test checks that:

- every node's canonical head equals the hub's;
- translation does what the protocol's model assumes of it ([protocol.md, "Translation
  layer"](protocol.md#translation-layer)): in a copy of each repository that has lost its
  translation cache, translating again from nothing gives what the machine remembered, makes no
  canonical operation, gives distinct local operations reachable from the op heads distinct
  canonical forms, with the parents' forms as their parents but at a join point, and gives every
  operation of the hive's history a realization that translates back to it;
- all repositories agree on visible commits, change ids, bookmarks, tags, and remote bookmarks;
- in every colocated repository, `refs/heads` matches the local bookmarks that are neither
  conflicted nor on the root commit (which git can't hold), and a further `jj status` imports
  nothing;
- every operation made on any machine appears in every machine's `jj op log`, but for a copy's
  join, which on the copy itself is the last operation it made before joining, and for those
  `jj op abandon` dropped, which appear in none, unless jj brought one back on the machine that
  abandoned it, through a stale working copy ([races.md, "Known jj
  limitations"](races.md#known-jj-limitations));
- no change diverges, and no bookmark or tag conflicts, unless jj makes the same of the same
  operations in one repository (the reference, below);
- no change has two commits with the same parents and contents that two merges rewrote from
  one commit: the same rebase done twice, which the hub's sequencing exists to prevent. A
  ledger (`e2e_search/ledger.rs`) of which machine's commands rewrote what tells this apart
  from rewrites that commands make alike.

Workspace names have a separate logical ledger from the directories used for edits. Native
merges can restore a name whose directory was renamed or forgotten. The checker certifies a
name only from independently recorded workspace births, the actual native command's before
and after views, or jj's replay of authenticated source parents. A forgotten copy's private
bindings require matching source views and an independent native merge witness; shared
metadata naming a workspace is never its own certificate. Rewriting a dormant binding's
commit revokes opaque inheritance unless independent replay certifies its result.
`e2e_workspace_names_after_trim_match_native_jj` exercises a realized merge whose authenticated
parents and local base let native jj witness a restored name. A realization's marker neither
certifies that name nor disqualifies its independently checked replay.

Native trim fix-ups have a separate source witness: the accepted history observed before the
trim. Only unchanged foreign bindings already certified there can be inherited.
`workspace_fixup_witnesses_require_the_native_source` pairs an offline rename with a foreign
workspace forget and a full trim, then checks the resulting native merge certificate. It also
loses the sender's evidence deliberately: reparenting an old native fix-up or receiving a marked
realization cannot create new evidence, and a replacement copy cannot inherit its predecessor's
pending trim context. Removing either source guard fails the negative control.

The reference (`e2e_search/reference.rs`) is a jj repository of the test's own that replays
the hub's history, operation by operation, with the same parents:

1. Each machine's commands, and the operations musubi writes for it such as a forget, go in as
   the hive has them. Each merge goes in as jj's own merge of the same parents, in the same
   order, as jj merges concurrent processes on one machine, but for a merge whose parents `jj
   op abandon` changed, as it does for every operation above what it abandoned and above the
   operations beside it, which it moves onto the abandoned operation's parent: jj keeps its
   view, as it keeps every operation's, so the hive's must be the view of the merge it
   replaced, as the realizations are held to theirs, and it goes in as the hive has it.
   A command's one local parent can expand to several canonical parents or contract to the root
   when its former parent was dropped. It remains a command: the harness records each new
   operation of a jj invocation, including intermediate snapshots and imports, with its source
   input and output. The reference checks its shared payload against that output and checks
   unexplained divergence and conflicts against its input. Genuine reconciliations still take the
   merge path. `e2e_command_above_dropped_merge` pairs such a bookmark command with a concurrent
   one and checks the resulting genuine merge, then trims to the root while preserving the
   inherited conflict. Source witnesses cover reparented single-parent fix-ups as well as merges;
   their shared payload must still match, with no newly introduced divergence. A retained internal
   operation is also checked against its original single-parent input.
2. Where jj's merge gives what the hive's did, comparing commits by contents, change ids and
   parents, the reference goes on from the hive's operation. Where it doesn't, it goes on from
   its own, applying later operations three-way as jj applies a concurrent one, until the two
   agree again past every point where they parted.
3. A merge that makes a change diverge into more commits than jj's merge of the same parents
   does, or a name conflict with terms jj's lacks, is musubi's doing, and so is any such excess
   at the hive's head over the reference's. The failure lists where the merges parted.

Merges staged through the hub are judged as staged: a node that merges part of another
machine's work and later the rest makes what jj makes of the same two merges. A merge made on a
machine, rather than realized there, is judged against the parents as that machine had them
too, where they lack only the working-copy commit of another machine's workspace it forgot,
which the hive keeps: jj there merges as if the forget abandoned it ([races.md, "Known jj
limitations"](races.md#known-jj-limitations)).

The test also checks that the hive's history can stand for one repository's: every machine's
realization of each operation has the hive's view of it, and no operation but a merge makes
anything diverge or conflict unless what it did explains it: a fetch, an undo or restore, or an
import of git refs or of git's HEAD.

To keep the search effective:

- a rule is eligible only when it has work to do, and its candidates come from a helper that
  its precondition shares;
- each search shard has its own Hegel example database;
- a case replays exactly, so that Hegel can shrink a failure and a stored example finds it again
  ([efficient-tests.md, "Make generated cases replay
  exactly"](efficient-tests.md#make-generated-cases-replay-exactly)). A failure that doesn't
  replay exactly fails the run at once, saying where the replay diverged.
  `MUSUBI_SEARCH_FINGERPRINTS` writes each case's trace without the ids that differ between runs,
  for checking that two runs of a case did the same;
- the run ends by listing rules that never fired. An unreached rule is a search problem: give
  it a richer starting state or fix its precondition.

## Testing the tests

`just mutants` runs `cargo-mutants` over the protocol core's hub and node logic: each surviving
mutant is a change to the protocol that the property and conformance tests fail to notice.
[conformance.md](conformance.md) lists hand-made mutants and which check catches each.

### Native adapter campaigns

`just mutants-stream` and `just mutants-adapter` extend the core campaign to selected native
boundaries. They need `cargo-mutants` and `cargo-nextest`, build the Lean oracle once before
mutating, and leave `just mutants` and the routine checks unchanged. Neither mutates the whole
workspace:

- `mutants-stream` selects `Shared::attach`, `detach`, `receive` and the stream transport's
  `request`: pending-call completion, failure reasons, reconnect subscriptions and request ids.
  It runs the transport crate's unit and public contract tests.
- `mutants-adapter` selects the repository adapter's ancestry, missing-object, accepted-base,
  record-preparation and permanent-history-loss decisions. It runs focused native tests of
  missing objects, gc of an abandoned base, pruned records and rollback across a cached fix-up,
  together with the adapter's unit tests. These use real repositories where the core's model
  uses an abstract `LocalRepo`.

Both accept cargo-mutants options before their fixed test selection:

```sh
just mutants-stream --list
just mutants-adapter --list
just mutants-stream
just mutants-adapter
```

Each build is limited to 600 seconds and each test run to 120 seconds. Tests stop on the first
failure, terminating other tests still running. Runs are serial by default; `--jobs 2` is
available when memory allows. Output goes to
`mutants.out-stream/mutants.out` or `mutants.out-adapter/mutants.out`, including each mutant's
patch and test log. The default runs in a scratch copy. `--in-place` avoids rebuilding
unchanged dependencies in an isolated workspace, but edits that workspace during the campaign:
keep editors, reviews and source-control commands away from the mutated files, and run no
other builds or tests there meanwhile. Do not combine `--in-place` with parallel jobs.

A survivor means the selected tests missed a change, not necessarily that all tests missed it
or that production is wrong. Inspect each patch and its executed tests. A timeout shows only
that the mutant did not finish within the budget; prefer a failing assertion as evidence.
An unviable mutant did not compile. Keep equivalent mutations visible and explain why they
cannot change an observable result rather than adding implementation-shaped assertions to
kill them. These campaigns sample particular assumptions; they do not replace the proofs,
conformance tests, faults, fuzzing or generated search.

#### Interpreting the adapter survivor

The selected adapter campaign has a known survivor: inverting the cached-base equality filter
in `accepted_base`. The adapter clears the cache when polling or changing the saved base, so
in its supported lifecycle the entry is absent or tagged with that base. Inverting the filter
recomputes completeness. With stable repository contents it gives the same answer; extra I/O
can fail or notice concurrent collection sooner. This loses an optimization without returning
an incorrect cached answer. With this generator the adapter recipe exits 2 for that survivor;
inspect any other survivor separately.

Two hand-made controls check assumptions the generator does not mutate:

- Limiting `history_lost` to the outermost error must fail
  `node::tests::permanent_history_loss_survives_error_context` on a wrapped error.
- Replacing the object-store completeness check in `accepted_base` with `true` must fail
  `fetch_base::collected_objects_of_an_abandoned_fetch_base_are_fetched_again` on the poll
  that would omit collected objects.

Make one mutation at a time in a disposable workspace, then run its selected test:

```sh
cargo nextest run -p musubi-sync --lib \
    -E 'test(=node::tests::permanent_history_loss_survives_error_context)'
cargo nextest run -p musubi-sync --test races \
    -E 'test(=fetch_base::collected_objects_of_an_abandoned_fetch_base_are_fetched_again)'
```

Restore the source before running normal checks. The native advance campaign's coverage and
failure-path controls are recorded with its
[conformance boundary](conformance.md#a-repository-advance-that-also-merges).

## Measuring assurance

[The assurance network](assurance.md) records per-test Rust execution, oracle calls, fuzz
checkpoints and mutation results, and rebuilds the code graph with a deterministic layout.
Its collector passes `LLVM_PROFILE_FILE` through test subprocess environments; normal test
runs stay hermetic.
