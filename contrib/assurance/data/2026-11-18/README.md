# Assurance snapshot, November 18, 2026

Saved measurements for source commit `f1b4774a0e99df4d1cb9af46598d5398f3261864`, using jj 0.47.1.
Each capture ran in an empty child of that commit. `sourceCommit` identifies the source tree to
check out; the capture revisions and source hashes remain in the dataset.

## Render the snapshot

From the repository root:

```sh
python3 contrib/assurance/assurance.py render \
    contrib/assurance/data/2026-11-18/snapshot.json.zst \
    --out target/assurance/index.html --standalone
```

Open `target/assurance/index.html`. Rendering uses the saved data and current renderer, including
its labels and tooltips. It runs no tests, fuzzers, solvers or mutation campaigns.

## Files

- `snapshot.json.zst`: the source graph, layout, per-technique coverage timeline, mutation
  results, and collection provenance, compressed with Zstandard. It contains 715 passing tests,
  24 fuzz checkpoints and 127 mutation results: 90 caught by tests, no survivors, and 37
  compilation failures.
- `observations.tar.zst`: per-test and per-checkpoint line observations, test identities,
  observed oracle operations, fuzz logs and corpora, and collection manifests. The mutation
  capture's directory contains its outcomes and diffs, plus `normalized-results.json` with the
  classifications used in the snapshot.
- `SHA256SUMS`: checksums for both data files.

The archive supports analysis of individual runs. LLVM profiles, binaries, build outputs and
verbose mutation logs remain in the raw captures outside the repository. The normalized archive
is not an input to `assurance.py export`; rendering needs only `snapshot.json.zst`.

Extract the observations with Zstandard and tar:

```sh
mkdir -p target/assurance/saved-2026-11-18
zstd -dc contrib/assurance/data/2026-11-18/observations.tar.zst |
    tar -xf - -C target/assurance/saved-2026-11-18
```

## Collection

The manifests preserve the commands, compiler versions, platform, seeds, budgets and source
hashes. The captures ran one after another on Linux, on one 32-CPU EC2 devbox:

- Tests: the `default` profile, with 50 conformance cases, Hegel seed 42 and 16 test threads,
  using Rust 1.100.0 and cargo-nextest 0.9.152.
- Fuzzing: a 60-second budget per target, four checkpoints and seed 42, using Rust nightly
  1.102.0 (2026-11-16) and cargo-fuzz 0.13.2.
- Mutation testing: 150 conformance cases and seed 42, using Rust 1.100.0 and cargo-mutants
  27.1.0, as a single unsharded campaign with six workers.

Archive paths retain the capture names: `tests-f1b4774`, `fuzz-f1b4774` and `mutation-f1b4774`.
Their source fingerprints match. These measurements describe the recorded source commit,
independently of later changes.

[Reproducing the assurance network](../../../../docs/internals/assurance.md) describes fresh
collection and its prerequisites.
