# Assurance snapshot, November 7, 2026

Saved measurements for source commit `3a8ed3d119cd55e4d2c4b224b19626dcffd4f0c8`, using jj 0.47.1.
Each capture ran in an empty child of that commit. `sourceCommit` identifies the source tree to
check out; the capture revisions and source hashes remain in the dataset.

## Render the snapshot

From the repository root:

```sh
python3 contrib/assurance/assurance.py render \
    contrib/assurance/data/2026-11-07/snapshot.json \
    --out target/assurance/index.html --standalone
```

Open `target/assurance/index.html`. Rendering uses the saved data and current renderer, including
its labels and tooltips. It runs no tests, fuzzers, solvers or mutation campaigns.

## Files

- `snapshot.json`: the source graph, layout, per-technique coverage timeline, mutation results,
  and collection provenance. It contains 590 passing tests, 24 fuzz checkpoints and 126 mutation
  results: 90 caught by tests, 1 survivor, and 35 compilation failures.
- `observations.tar.zst`: per-test and per-checkpoint line observations, test identities,
  observed oracle operations, fuzz logs and corpora, and collection manifests. Each mutation
  shard's directory contains its outcomes and diffs, plus `normalized-results.json` with the
  classifications used in the snapshot.
- `SHA256SUMS`: checksums for both data files.

The archive supports analysis of individual runs. LLVM profiles, binaries, build outputs and
verbose mutation logs remain in the raw captures outside the repository. The normalized archive
is not an input to `assurance.py export`; rendering needs only `snapshot.json`.

Extract the observations with Zstandard and tar:

```sh
mkdir -p target/assurance/saved-2026-11-07
zstd -dc contrib/assurance/data/2026-11-07/observations.tar.zst |
    tar -xf - -C target/assurance/saved-2026-11-07
```

## Collection

The manifests preserve the commands, compiler versions, platform, seeds, budgets and source
hashes. The captures ran on Linux, on 32-CPU EC2 devboxes, in parallel:

- Tests: the `default` profile, with 50 conformance cases, Hegel seed 42 and 16 test threads,
  using Rust 1.99.1 and cargo-nextest 0.9.148.
- Fuzzing: a 60-second budget per target, four checkpoints and seed 42, using Rust nightly
  1.101.0 (2026-11-06) and cargo-fuzz 0.13.2.
- Mutation testing: 150 conformance cases and seed 42, using Rust 1.99.1 and cargo-mutants
  27.1.0, as four shards on four devboxes, each with four campaign workers, four test threads
  per worker and six compiler jobs. Each shard was collected as
  `assurance.py mutation --shard K/4` collects one, except that it was a contiguous slice of
  the campaign: that option has since taken mutants round-robin. `build` joined them.

Archive paths retain the capture names: `tests-3a8ed3d`, `fuzz-3a8ed3d` and
`mutation-3a8ed3d-shard-0` to `-3`. Their source fingerprints match. These measurements
describe the recorded source commit, independently of later changes.

[Reproducing the assurance network](../../../../docs/internals/assurance.md) describes fresh
collection and its prerequisites.
