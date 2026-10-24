# Testing philosophy

What musubi's tests and proofs must cover, and what evidence each kind of change needs.
[testing.md](testing.md) describes each layer of tests and what a test of each costs, and
[efficient-tests.md](efficient-tests.md) how to keep a test cheap.

Terms are those of [design.md](design.md), "Vocabulary"; testing.md describes Hegel, and
"the search", the generated end-to-end tests.

## What a test must protect

A user-visible behavior; a property of the protocol ([protocol.md](protocol.md),
"Properties"); a rule of the design, above all that replicated concurrency resolves as jj
resolves local concurrency ([races.md](races.md)); a behavior of jj, git or the operating
system that musubi relies on; or a failure in scope, below. Before adding a test, look for
what covers it already at every layer, from the theorems to the search, and put it at the
narrowest layer that catches what they don't.

## What is in scope

A state belongs in a test if musubi can reach it, however unlikely: across enough machines and
time, networks and crashes produce every interleaving. musubi can reach:

- messages lost, duplicated, delayed or reordered, links failing partway through a call, and
  any process crashing at any point ([protocol.md](protocol.md), "Network and failures");
- what a power cut leaves, since musubi makes no synchronous fsyncs: recent writes lost, a
  line torn as it was appended, a new file left empty, and so a hub back at an older head or
  with a store it must make again;
- whatever a buggy peer, or a peer of another release, sends;
- any jj command on any machine, concurrently, at an older operation or in a stale workspace,
  and git moving refs that jj hasn't imported;
- every supported kind of repository: colocated or not, on jj's simple backend, with
  submodules, signed commits, or remotes spelled through `insteadOf`.

These need no test:

- a corrupted message taken as valid: content hashes are checked on receipt;
- running any jj but the one musubi pins (the nightly run against jj's main branch aside),
  though what an older jj wrote into a repository's history is in scope; and shallow or
  partial clones, beyond their refusal;
- data from earlier releases, until 1.0 (AGENTS.md, "Compatibility"), beyond a message from
  another release being refused as such;
- not losing recent writes to a power cut. Test that damage is detected, and what follows.

## Proof or test

A Lean proof covers every interleaving, but of the model; a test runs the real code, but on the
cases it tries. Model a rule that must hold over every history or interleaving and whose state
can be made small: the protocol, which copies a hive shows (`Presence.lean`), what imports and
exports do to per-machine refs (`Refs.lean`), receiving chunked blobs (`Chunks.lean`). Design
it in the model first where you can, and keep the code's core a pure function that a test can
check against the model.

Don't model jj's behavior, which musubi matches rather than designs: test it against jj, and
test what a model assumes of jj as laws, as `ref_laws` does.

## What each kind of change needs

- **A Lean model, added or changed,** is tied to the code in the same change: an executable
  version proved sound and answered by the oracle, or, where its state is small, a Rust copy
  of it in the test; a test checking the implementation against that, step by step; and the
  correspondence in conformance.md and formal/README.md. A model no test refers to is a gap.
- **A change to the protocol** changes the model with it: the new step, its case in each
  invariant proof, its executable version and soundness proof, and its JSON in the oracle.
  The conformance test must reach the step, and the model's preconditions must be tight enough
  that a core taking the wrong step fails.
- **A change to the wire format** needs no model change where the model abstracts it away, but
  the fuzz targets for what it changes (`frames`, `envelope`, `bundle`, `import`) must reach
  the new form, as must `hub_survives_malformed_requests` for a message or a bundle. AGENTS.md
  says when `PROTOCOL_VERSION` changes.
- **A change to how concurrent changes resolve** gets a row in races.md, the race test it
  names, and a rule in the search if the search can't yet produce the situation.
- **A change to how a node translates, realizes or moves objects** gets an example test with
  real repositories in its crate's `tests/it`.
- **A change to a command** gets a test in `crates/musubi/tests/cli.rs` only where running the
  binary is what's at risk. Assert the command or reason a message gives, and the exit code,
  not the wording around them.
- **A new decoder of what a peer sends** gets a fuzz target. Fuzz targets are for decoders that
  run in process at hundreds of inputs a second or more; stateful behavior belongs in the
  fault tests.
- **A file musubi appends to** gets a Hegel property beside its parser: however its tail is
  torn or damaged, nothing is misread (testing.md, "Fuzzing", gives each file's).
- **An encoding that ids are hashes of** is pinned byte for byte, and a constant that must
  match another, as `JJ_LIB_VERSION` must match the pinned jj, is tested against it.
- **A design that relies on a behavior of jj** pins it with an example test, sometimes a
  negative control: `verbatim_replication_reverts_bookmarks` fails if jj changes enough that
  the design needs revisiting.
- **A known limitation,** musubi's or jj's, gets a row in races.md and, where possible, a test
  that fails once it goes away, so that the fix is noticed and the workaround removed.
- **Removing a guarantee or mechanism** removes the tests that exist only for it, and code
  whose only user is its own test goes with that test.

## What to check against

Check musubi against something independent of it:

- the Lean models, through the conformance tests ([conformance.md](conformance.md));
- jj itself, since a race must resolve as it would on one machine: `workspace_merge_matches_jj`
  compares musubi's merge of workspaces with jj's, debug builds compare musubi's faster merge
  of per-machine fields with jj's merge, and the search judges divergence and conflicts
  against a jj repository that replays the hub's history (testing.md);
- laws and round trips: `ref_laws`, and the fuzz targets.

When musubi and a model disagree, either may be wrong: a model can be as mistaken about jj as
the code.

## Showing that a test works

Say in the commit what breaking makes the test fail, so that a reviewer can read that rather
than repeat it, and say what it can't reach, as testing.md does for logging in.

## Realistic tests

Pin internal state only where a model defines it, as conformance does. Faults must look like
real ones: a crash leaves what a real crash leaves, such as realizations written but not yet
recorded, and the conformance test's fakes lose in a crash exactly what the model is told
they lose. Build fixtures with jj, git and musubi, or record them from a real session; write
musubi's files by hand only to test their parsers or to make the damage a fault would leave.

The harness runs the code that ships. Where a test needs a way in, share the code rather than
copy it, as `Hive`, which runs the tests' syncs, shares the work around a sync with the
daemon's `NodeDriver`; a rule every caller needs goes in the core, as `NodeCore` holds the rule
for following a hub that went back. Settings that speed tests up go to the jj commands tests
run, never to the musubi under test.

Tests run jj and git through `musubi-testutil`, which is hermetic and seeds jj's randomness so
that cases replay. A test that needs what isn't there skips itself, saying why, as tests of gc
do on battery, where musubi defers gc. A test that changes the machine, such as installing a
login service, runs only when an environment variable allows it.

## Cost

The suite runs real jj and git thousands of times and every change waits for it, so cost is
part of whether a test earns its place: testing.md's costs per layer are the budget for a new
test, and efficient-tests.md says how to stay within it.

## Beyond `just check`

- `just mutants`, after changing the protocol core: the tests should kill every mutant it makes.
  A mutant that survives, there or where cargo-mutants runs on other code, gets a test, and
  conformance.md's table of hand-made mutants gets a row when a new check catches one it lacks.
- `just fuzz-smoke`, after changing a decoder or a fuzz target.
- The search (`just property`), nightly. When it fails, find out why first:
  - a failure that doesn't replay exactly is a bug in determinism;
  - one the harness causes, doing what no user or fault could, or a check that is wrong, is
    fixed in the harness, never by dropping the check;
  - a bug in jj gets a row in races.md, "Known jj limitations";
  - anything else is a bug in musubi.

  A state the search rarely reaches gets a rule of its own that goes there.

Try, too, what no test sets up: other kinds of repository, the user guide's steps against the
real binary, real machines over real ssh. What works becomes a test that keeps it working.

## Keeping docs in step

testing.md, races.md, conformance.md and formal/README.md name tests and say what each checks,
and `crates/musubi-sync/tests/e2e_search/coverage.rs` lists the race catalogue's tests. A change
to a test updates them.
