# Testing

musubi's correctness rests on three layers of evidence. Each guards a different risk, so a
test belongs at the narrowest layer that can catch its bug.

| Layer | Where | Guards against | Cost |
| --- | --- | --- | --- |
| Formal model | `formal/` (Lean) | Protocol design errors: lost operations, dangling references, duplicate merges, livelock | Proof effort, no runtime |
| Protocol property tests | `crates/musubi-core/tests` | The Rust state machines departing from the model | Milliseconds per case |
| Race catalogue | `crates/musubi-sync/tests/races` | Concurrent changes on different machines resolving differently from jj's local behavior (docs/races.md) | ~2 s per test |
| Unit tests | `#[cfg(test)]` modules | Pure logic: URL normalization and hive names across forges, matching joining repositories to hives | Microseconds |
| Example tests | each crate's `tests/` | jj integration details: translation, git refs, objects, joins, transports, the hub's hives, the CLI | ~1 s per test |
| Fault tests | `crates/musubi-sync/tests/faults.rs` | Malformed requests reaching the hub's decoders, and links that die or stall partway through a sync | ~10–20 s per test |
| Generated end-to-end tests | `crates/musubi-sync/tests/e2e_search` | Everything interacting: real `jj` commands, real repositories, faults | Seconds per case; opt-in |

Run the default suite with `cargo nextest run`, or everything with `just check`. It needs `jj` 0.46.0, `git`, and `nats-server`
on `PATH`. Run the generated end-to-end search with `cargo nextest run --profile search`. Check
the formal model with `lake build` in `formal/`.

CI runs the default suite on Linux, macOS and Windows, and checks the Lean model and runs
the conformance test against its oracle on Linux. It doesn't run the end-to-end search.

## Protocol property tests

A Hegel state machine owns a hub and several nodes, all of them sans-IO state machines from
`musubi-core`, joined by a simulated network that the test controls completely. Its rules:

- environment: a node makes a local operation on some local parent, not necessarily a head;
  a node merges its heads;
- delivery: deliver, drop, duplicate, or delay a chosen in-flight message;
- failure: crash a node or the hub, keeping only persistent state;
- progress: let a node take its next policy step.

After every rule the test checks the model's safety invariants: HubClosed, HubMonotone,
NodeClosed, Locality, and MergeOwnership. A final `quiesce` step stops environment actions,
makes the network reliable, and runs every node's policy until nothing changes. The test then
checks liveness: every node's heads are `{hub.head}`, and every created operation is in its
ancestry. A bound on quiescence steps turns livelock into a failure.

Operations here are abstract: ids, parents, and object sets. No jj repository is involved.

## Example tests

These pin down jj-specific behavior with real repositories created by the `jj` CLI, using
`musubi-testutil`'s hermetic environment. Each one names the hazard it guards against. Some
tests are deliberately negative controls. `verbatim_replication_reverts_bookmarks` shows that
copying operations without translation loses bookmark moves; if it ever starts failing, jj
has changed and the design needs revisiting, not the test.

### The hub and the CLI

`musubi-sync/tests/server.rs` runs one hub serving several hives over the in-memory
transport: a first copy creating a hive, a copy with the same remote spelled differently
joining it, a fork getting its own, an unrelated repository refused, requests for a hive the
hub lacks failing, and listing, renaming, removing, and an index rebuilt after a restart.
`musubi-hub`'s unit tests cover URL normalization, naming, and the matching rules case by
case.

`musubi/tests/cli.rs` runs the binary as a user would: `musubi hub` starting its own
`nats-server`, `musubi create` starting a hive and `musubi join` matching it, `musubi
clone` by a prefix of the hive's name, `musubi list`, `leave`, and each machine's daemon,
which the first `create` or `join` starts in the background, serving a repository added
later without a restart. Each test machine has its own config directory, and so its own
daemon and control socket; the tests stop the daemons, and kill the NATS server a killed
hub leaves behind, when they finish.

One CLI test installs a real login service, and so runs only with
`MUSUBI_TEST_LOGIN_SERVICE=1`, which CI sets on its throwaway runners: never set it where
musubi is installed for real. It installs the daemon with launchd or systemd and checks
that the service manager starts it, restarts it after it is killed but not after `musubi
daemon stop`, and starts it for a command that needs it; on Windows it runs the `Run`
entry's command as a login would. CI's Linux runners have no systemd user manager without
a login session, so the workflow enables lingering and starts one first. Logging in itself
is the one step no test exercises.

## Faults

The protocol tests deliver well-formed messages, and lose, duplicate, or delay whole ones;
docs/protocol.md assumes no message is corrupted. `musubi-sync/tests/faults.rs` tests the
implementation where that doesn't hold. It records a real session over the in-memory
transport, with a payload limit small enough that each commit's objects travel as a blob of
several windows of chunks: one machine pushes a commit, another fetches it and pushes its
own, and the first fetches that. It snapshots the hub's directory after each request, so
that a case can start from any point in the session. Two Hegel tests use the session:

- `hub_survives_malformed_requests` sends a hub requests no honest node sends: the session's
  requests and bundles cut short, corrupted, or spliced; chunks at extreme offsets; requests
  that arrive as blobs, and are themselves malformed or indirect; protocol requests with ids
  and attachments taken from the session or made up; and envelopes from another version. The
  hub answers each without panicking, with a reply, or an error, that fits the transport, and
  its head moves only forward, to an operation whose closure it has (HubMonotone and
  HubClosed). Afterwards it still answers a fetch from the root, which reads everything up to
  its head.
- `calls_finish_once_the_link_is_back` makes one of the session's calls, a push and its
  uploads or a fetch and its downloads, through a link that fails at a chosen request. The
  request and all later ones may be lost, as when the wifi goes off. The request may arrive
  but its reply and all later requests be lost, as when a lid closes just after it went. Or
  an hour may pass before it arrives, in which the hub sweeps away transfers in progress,
  and then the link carries on, as when the lid opens. Meanwhile the hub may hear malformed
  requests made from what the node sent, and an hour may pass. Once the link is back, the
  call, made again, gets the reply it got in the session, unless a malformed request was a
  valid push that moved the head, within a bound on requests that catches a node that never
  starts over.

A third, `node_recovers_when_its_link_fails_partway`, fails the link the same ways with real
repositories and the node's driver, retrying as the daemon does, while another machine
syncs. Afterwards both machines see the same commits. It is slow, so it runs few cases.

A connection that dies partway through a message never delivers part of it: NATS and the
stream transport both frame each message with its length and drop an incomplete one. A killed connection reaches
musubi as a lost request or reply, which the link faults model. The truncated messages
stand for a buggy or mismatched peer.

## Generated end-to-end tests

Modeled on jj-stack's generated integration tests. A Hegel state machine drives two or three
real colocated repositories, each served by a real musubi node, through an in-process hub
over the in-memory transport. A smaller set of scenarios also runs across processes against
`nats-server`.

Rules fall into separate groups, and are kept separate so that the inconsistent states
between them get explored:

- **Local work**, through the `jj` CLI on a chosen machine: write files and commit, describe,
  new on a random commit, rebase, squash, abandon, bookmark create, move, and delete, undo,
  and commands at an older operation (`--at-op`), which create concurrent operations.
- **Git-side work** in a colocated repository: move or delete a branch with `git`.
- **Sync**: let one node take a single sync step, which may stop partway through an upload.
- **Faults**: partition and heal a node, drop or delay messages, crash a node or the hub.
  Faults are capped per sequence, so that a short walk still reaches recovery.

After each rule, every repository must still load, and `jj status` must succeed. At the end,
`quiesce` heals everything and syncs to a fixed point, then checks:

- every node's canonical head equals the hub's;
- all repositories agree on visible commits, change ids, bookmarks, tags, and remote
  bookmarks;
- in every colocated repository, `refs/heads` matches the local bookmarks that are not
  conflicted, and a further `jj status` imports nothing;
- every operation made on any machine appears in every machine's `jj op log`;
- no change diverges, and no bookmark or tag conflicts, unless jj would do the same with
  the same concurrent operations on one machine. A ledger of which machine's commands
  rewrote what explains each: two machines rewrote it, or a command at an older operation
  or a git-side move did; or a commit holds it visible that jj can't move, such as a
  descendant of a commit rewritten two ways, a target of a conflicted bookmark, or a branch
  imported from git. A bookmark on a merge commit that is abandoned conflicts between the
  merge's parents. Two commits of a change with the same parents and contents are the same
  rebase done twice, which the hub's sequencing exists to prevent.

As in jj-stack:

- a rule is eligible only when it has work to do, and its candidates are computed by a helper
  that its precondition shares;
- each seeded search shard has its own Hegel example database;
- a case replays exactly, so that Hegel can shrink a failure and a stored example finds it
  again: jj's change ids, random otherwise, come from a counter that each test
  environment's repositories share (musubi-testutil), origin's upstream commits carry
  change ids of their own, and rules choose among commits in change-id order, since commit
  ids and `jj log`'s order depend on when jj made the commits.
  `MUSUBI_SEARCH_FINGERPRINTS` writes each case's trace without the ids that differ between
  runs, for checking that two runs of a case did the same;
- the search run ends by listing rules that never fired. An unreached rule is a search
  problem: give it a richer starting state or fix its precondition.

## Testing the tests

`just mutants` runs `cargo-mutants` over the protocol core's hub and node logic: each
surviving mutant is a change to the protocol the property tests and the Lean conformance
check fail to notice. docs/conformance.md lists hand-made mutants and which check catches
each.
