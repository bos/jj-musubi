# Assurance snapshot, November 5, 2026

Saved measurements for source commit `170151a85381411b9d056f96046a10b7a39dd051`, using jj 0.47.1.
The capture workspace was an empty child of that commit. `sourceCommit` identifies the source
tree to check out; the original capture revisions and source hashes remain in the dataset.

## Render the snapshot

From the repository root:

```sh
python3 contrib/assurance/assurance.py render \
    contrib/assurance/data/2026-11-05/snapshot.json \
    --out target/assurance/index.html --standalone
```

Open `target/assurance/index.html`. Rendering uses the saved data and current renderer, including
its labels and tooltips. It runs no tests, fuzzers, solvers or mutation campaigns.

## Files

- `snapshot.json`: the source graph, layout, per-technique coverage timeline, mutation results,
  and collection provenance. It contains 533 passing tests, 24 fuzz checkpoints and 126 mutation
  results: 90 caught by tests, 1 survivor, and 35 compilation failures.
- `observations.tar.zst`: per-test and per-checkpoint line observations, test identities,
  observed oracle operations, fuzz logs and corpora, and collection manifests. The mutation
  directory contains the original outcomes and diffs, plus `normalized-results.json` with the
  classifications used in the snapshot.
- `SHA256SUMS`: checksums for both data files.

The archive supports analysis of individual runs. LLVM profiles, binaries, build outputs and
verbose mutation logs remain in the raw captures outside the repository. The normalized archive
is not an input to `assurance.py export`; rendering needs only `snapshot.json`.

Extract the observations with Zstandard and tar:

```sh
mkdir -p target/assurance/saved-2026-11-05
zstd -dc contrib/assurance/data/2026-11-05/observations.tar.zst |
    tar -xf - -C target/assurance/saved-2026-11-05
```

## Collection

The manifests preserve the commands, compiler versions, platform, seeds, budgets and source
hashes. The selected test profile was `default`, with 50 conformance cases and Hegel seed 42.
Fuzzing used a 60-second budget per target, four checkpoints and seed 42. Mutation testing used
150 conformance cases and seed 42 on a 32-CPU EC2 devbox, with four campaign workers, four test
threads per worker and six compiler jobs.

Archive paths retain the capture names: `tests-0471`, `fuzz-0471` and `mutation-0471-ec2-32`.
The mutation capture ran on Linux; tests and fuzzing ran on macOS. Their source fingerprints
match. These measurements describe the recorded source commit, independently of later changes.

[Reproducing the assurance network](../../../../docs/internals/assurance.md) describes fresh
collection and its prerequisites.
