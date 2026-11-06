# Reproducing the assurance network

The network shows source dependencies and measured execution of production Rust. Its pies
show which selected tests reached each executable line; they do not measure proof strength,
assertions, branches, runtime calls or data flowing between modules.

The collector, source inventory, layout, renderer and offline browser assets live in
`contrib/assurance/`. Nothing needs a chat transcript, a personal directory or a web service.
[The assurance renderer](assurance-renderer.md) describes the design and browser implementation.
Python 3.11 or later runs the tools. Collection and coverage export run on macOS or Linux
and need the project's normal test tools,
`llvm-tools-preview`, and, for the optional campaigns, cargo-fuzz with nightly Rust and
cargo-mutants. The run manifests record the exact compiler and tool versions used.

## Render the saved snapshot

The repository includes a
[November 5, 2026 snapshot](../../contrib/assurance/data/2026-11-05/README.md)
and a Zstandard archive of its normalized observations. To view it without collecting data:

```sh
python3 contrib/assurance/assurance.py render \
    contrib/assurance/data/2026-11-05/snapshot.json \
    --out target/assurance/index.html --standalone
```

Open `target/assurance/index.html`. The renderer uses current labels and tooltips with the saved
measurements. The snapshot records its source commit and collection provenance. Generated HTML
stays under ignored `target/assurance/`; renderer code stays in `contrib/assurance/`.

## Collect data

Run from the repository root, choosing a new output directory for each capture:

```sh
just assurance-tests target/assurance/tests
just assurance-fuzz target/assurance/fuzz
just assurance-mutation target/assurance/mutation
```

The default test profile runs once with 50 conformance cases per test, a fixed Hegel seed and
its example database disabled. Instrumented collection allows four times the normal timeout
periods, retaining each profile's selected tests and case counts. `tests --cases` changes the
case budget. Collection defaults to Rust
`stable` for tests and mutation runs, and `nightly` for fuzzing. Each accepts `--toolchain`
to select an exact installed version.
An oracle relay records the actual Lean requests made by each test, identifying conformance
checks independently of names. The test wrapper associates profiles from each test and its
child processes with that test. The harness passes `LLVM_PROFILE_FILE` through its otherwise
hermetic command environments solely for this collection.

The fuzz collector runs all targets listed in `fuzz/Cargo.toml`, with a 60-second budget per
target, four coverage checkpoints and recorded seeds. This coverage capture uses the dev
build with sanitizers disabled; the normal fuzz workflow keeps its usual sanitizer checks.
It retains the corpus, raw profiles, commands, logs and normalized line observations.
LibFuzzer's reported runtime excludes compilation and coverage export from the chart's timeline.

Mutation testing follows `just mutants`: it changes the protocol core, runs its tests against
the real Lean oracle, and records whether those tests fail. A change that does not compile
is not evidence that the tests noticed a bug; timeouts are separate too, including a test
stopped by nextest before the campaign’s outer timeout. A change the tests accept needs
inspection: it may reveal a missing check, or make no observable difference.
Mutation results describe the places changed, not a fraction of executed Rust lines.

For other budgets or profiles, use the Python entry point:

```sh
python3 contrib/assurance/assurance.py fuzz --out target/assurance/fuzz-long \
    --seconds 300 --checkpoints 10 --seed 42 --toolchain nightly --jobs 4
python3 contrib/assurance/assurance.py tests --out target/assurance/search \
    --profile search --seed 42 --jobs 4
```

The long search is a separate capture; a normal test capture contains only its smoke test.
The nightly jj compatibility job is deliberately absent from this figure.

Raw output stays under ignored `target/assurance/` directories. A manifest records the source
revision, production/model source hashes, platform, compiler, commands and run settings.
Keep the complete capture when auditing or re-exporting coverage. Tests that kill child
processes can leave truncated profiles: export retains usable profiles and records LLVM's
warnings, so missing flushes remain a limitation rather than an invented coverage result.
Completed test binaries are preserved alongside their profiles, before later builds can
replace them. Export requires the recorded compiler/LLVM version; `export --toolchain` selects
a matching installed toolchain. If export is interrupted after tests pass, resume it without
running tests again:

```sh
python3 contrib/assurance/assurance.py export --run target/assurance/tests
```

A fresh campaign is not promised to have identical timing or results on another machine.
Fixing seeds and recording budgets makes the procedure repeatable; retaining a capture makes
its data and chart reproducible. Use the compiler and tool versions in its manifest when
repeating collection, rather than assuming that a later `stable` or `nightly` is equivalent.
For example, `tests --toolchain 1.98.1` selects that compiler after installing it and its
`llvm-tools-preview` component with rustup.

## Build and render

```sh
python3 contrib/assurance/assurance.py build \
    --run target/assurance/tests --run target/assurance/fuzz \
    --run target/assurance/mutation --out target/assurance/data.json
python3 contrib/assurance/assurance.py render target/assurance/data.json \
    --out target/assurance/index.html --standalone
```

Open `target/assurance/index.html` in a browser. It includes its data, styles and the three
Lucide icons it uses, and needs no network access. Omit `--standalone` to render an inline
fragment. Rendering a saved dataset does not read or rebuild the source checkout.

Use **All** or **None** beside Techniques to select the assurance methods together.
**Expand all** and **Collapse all** below the graph change the detail of every component;
individual components can still be expanded or collapsed independently under **Explore the code**.
Replay takes eight seconds from beginning to end and advances evenly in the selected clock.
The clock offers **Elapsed run time**, which follows recorded completion times, and
**Sum of run durations**, which adds each test and fuzz run's duration, including overlapping
runs. Clock definitions and disabled-replay reasons appear in tooltips. The graph's **Explore
the code** section contains its interaction instructions.

The builder refuses captures whose production/model source fingerprint differs from the
checkout. It discovers production modules and import dependencies again, so new files and
crates participate automatically. `catalog.json` contains the explicitly curated proof scopes
and role overrides; missing referenced files or symbols fail with a request to update the
catalog rather than silently retaining stale claims. New unclassified modules stay visible
with an unclassified role.

Lean has one chain in this view: **proofs → Rust conformance tests → measured Rust coverage**.
Conformance tests are those observed calling the oracle. The proof sources are attached by
oracle operation, and each successful Rust execution contributes its coverage once. Hegel,
fault injection and the other techniques can overlap those executions; line unions count
shared lines once. Kani's Rust execution overlay remains the explicitly related ordinary tests,
not a solver result.

Layout uses sorted node and edge identities, a fixed seed, per-node SHA-256 initialization,
and 520 force iterations. The resulting positions are saved in the dataset; the browser never
runs a force simulation. The same inputs and seed produce the same layout, independent of file
enumeration order. Changing source structure recomputes it. `build --seed` is an explicit
layout input, and the dataset records the algorithm version and generator file hashes.

Run the collector and layout regression checks with `just assurance-check`.
