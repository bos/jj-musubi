# The full local check. AGENTS.md says when to run it.
check: fmt-check lint oracle _test-ready docs deny machete typos fuzz-runner-test assurance-check antithesis-driver

# Build musubi: target/debug/musubi.
dev:
    cargo build --locked -p jj-musubi

# Install the workspace-cache tool at the version Dependabot tracks.
workspace-cache-install:
    #!/usr/bin/env python3
    import pathlib, subprocess, tomllib
    manifest = pathlib.Path("contrib/tool-versions/Cargo.toml")
    version = tomllib.loads(manifest.read_text())["dependencies"]["cargo-shared-target"]
    subprocess.run(["cargo", "install", "cargo-shared-target", "--version", version, "--locked"], check=True)

# Optional workspace-cache integration checks; run workspace-cache-install first.
workspace-cache-test:
    python3 -m unittest discover -s contrib -p test_seed_target.py

# Build musubi optimized: target/release/musubi.
release:
    cargo build --locked -p jj-musubi --release

# Show the balance of production, proof/model, test and miscellaneous code (needs tokei).
loc:
    @python3 contrib/loc.py

# Install musubi (`just install dev` for a dev build) and restart a running daemon.
install profile="release":
    #!/usr/bin/env bash
    set -euo pipefail
    root="${CARGO_INSTALL_ROOT:-${CARGO_HOME:-$HOME/.cargo}}"
    musubi="$root/bin/musubi"
    cargo build --locked -p jj-musubi --profile {{ profile }}
    # A running daemon keeps the old binary (and on Windows locks it): stop it, install, and
    # start the new one.
    running=false
    if [[ -x $musubi ]]; then
        out=$("$musubi" daemon stop)
        echo "$out"
        if [[ $out == Stopped* ]]; then running=true; fi
    fi
    cargo install --locked --path crates/musubi --profile {{ profile }} --root "$root"
    if $running; then "$musubi" daemon start; fi

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all --check

lint:
    cargo clippy --workspace --all-targets -- -D warnings
    # The Antithesis build (antithesis/README.md), which no other check compiles.
    cargo clippy -p jj-musubi --features antithesis -- -D warnings

# On macOS the tests' directories go on a RAM disk made for the run, unless
# MUSUBI_KEEP_TEST_DIRS keeps them: jj syncs what it writes, and on the SSD the suite takes
# three times as long.
# A targeted run needs the executable oracle, not every proof and smoke check.
[positional-arguments]
test *args: _test-oracle
    just _test-ready "$@"

# A supplied oracle may be an assurance relay; its caller already prepared the real one.
[private]
_test-oracle:
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ -z ${MUSUBI_ORACLE+x} ]]; then
        python3 contrib/build-oracle.py
    fi

# The caller prepared the oracle: check/coverage run every proof and smoke check first;
# targeted test runs build only the executable. Keep their filesystem and runner setup shared.
[positional-arguments]
[private]
_test-ready *args:
    #!/usr/bin/env bash
    set -euo pipefail
    export MUSUBI_ORACLE="${MUSUBI_ORACLE-$PWD/formal/.lake/build/bin/oracle}"
    if [[ $OSTYPE == darwin* && -z ${MUSUBI_KEEP_TEST_DIRS+x} ]]; then
        # 512 MiB, in 512-byte sectors, shared by active test directories and recordings.
        # Leave room for concurrent repository cases; four workers alone have used 76 MiB.
        # Before macOS 26, only hdiutil attaches one.
        ram=ram://1048576
        dev=$(diskutil image attach --noMount $ram 2>/dev/null || hdiutil attach -nomount $ram)
        dev=${dev%%[[:space:]]*}
        trap 'diskutil eject "$dev" > /dev/null' EXIT
        diskutil erasevolume APFS "musubi-test-$$" "$dev" > /dev/null
        export TMPDIR="/Volumes/musubi-test-$$/"
        # Directory cloning needs the recordings and their restored copies on one filesystem.
        export MUSUBI_TEST_CACHE_DIR="${MUSUBI_TEST_CACHE_DIR-${TMPDIR}fixtures}"
    fi
    # The virtual workspace defaults to all members; let -p narrow that selection.
    cargo nextest run "$@"

# Collect diagnostic coverage with the same nextest filters and RAM disk as `test`.
[positional-arguments]
coverage *args:
    #!/usr/bin/env bash
    set -euo pipefail
    # Collection and reporting must use the same build layout. Support test selection,
    # not alternate builds or prebuilt nextest archives.
    for arg in "$@"; do
        case "$arg" in
            --) break ;;
            -r*|--release|--cargo-profile*|--target*|--manifest-path*|--config|--config=*|--archive-file*|--binaries-metadata*|--cargo-metadata*|--workspace-remap*|--build-dir-remap*)
                echo "coverage: alternate build layouts and prebuilt test artifacts are not supported" >&2
                exit 2 ;;
            --*|-p*|-E*|-P*|-F*|-j*) ;;
            -??*)
                echo "coverage: pass short options separately, not in a group" >&2
                exit 2 ;;
        esac
    done
    just oracle
    # Keep reports and profiles local and ignored, even with CARGO_TARGET_DIR set.
    export CARGO_TARGET_DIR="$PWD/target"
    export CARGO_LLVM_COV_TARGET_DIR="$CARGO_TARGET_DIR"
    coverage_env=$(cargo llvm-cov show-env --sh --no-cfg-coverage)
    eval "$coverage_env"
    cargo llvm-cov clean --workspace
    rm -f target/llvm-cov/coverage.json
    just _test-ready "$@"
    cargo llvm-cov report --html --output-dir target/llvm-cov
    cargo llvm-cov report --json --output-path target/llvm-cov/coverage.json

docs:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps --quiet

# Copy the user guide to the sibling website checkout.
alias web := website-docs

website-docs:
    JJ_MUSUBI_SOURCE={{ quote(justfile_directory()) }} python3 ../website/scripts/sync-jj-musubi-docs.py

# The Antithesis workload's driver, a workspace of its own (antithesis/README.md).
antithesis-driver:
    cargo fmt --check --manifest-path antithesis/musubi/driver/Cargo.toml
    cargo clippy --locked --manifest-path antithesis/musubi/driver/Cargo.toml -- -D warnings
    cargo deny --log-level error --manifest-path antithesis/musubi/driver/Cargo.toml check

deny:
    cargo deny --log-level error check

machete:
    cargo machete --skip-target-dir

typos:
    typos

# Check the Lean proofs and build the oracle the conformance tests run against.
oracle:
    python3 contrib/build-oracle.py --full

# Run every benchmark script once, as briefly as each allows, against a debug build, so that
# they keep up with the CLI (see bench/README.md). It measures nothing.
bench-smoke: dev
    #!/usr/bin/env bash
    set -euo pipefail
    # Short, for the hubs' sockets.
    work=$(mktemp -d /tmp/musubi-bench.XXXXXX)
    cleanup() {
        # On failure, what the services and daemons said, before it goes.
        if [ $? != 0 ]; then
            tail -n 30 "$work"/runs/*/*.log "$work"/runs/*/cfg*/daemon.log || true
        fi
        rm -rf "$work" || true
    }
    trap cleanup EXIT
    export MUSUBI=$PWD/target/debug/musubi MUSUBI_BENCH_DIR=$work
    py="/usr/bin/python3 -I"
    bench/setup_sources.sh
    $py bench/bench.py small 1 --clones 1 --week-commits 1 --week-describes 1 \
        --latency-reps 1 --idle-seconds 1 --oplog-ops 2
    $py bench/stalebase.py small 1 1
    $py bench/oplog.py small 1
    $py bench/daemonslots.py small 1
    $py bench/report.py
    $py bench/tracestats.py "$work"/runs/small/trace-*.json > /dev/null
    $py bench/tracelist.py "$work"/runs/small/trace-*.json > /dev/null

# The generated end-to-end search (expensive; not part of `check`).
property:
    just test --workspace --profile search

# Explore, replay, or branch real Linux op-head schedules.
[positional-arguments]
head-schedule *args:
    @python3 contrib/head_schedule.py "$@"

# Fuzz all targets or one across available CPUs (see docs/internals/testing.md).
[positional-arguments]
fuzz target="all" *args:
    @python3 contrib/fuzz.py "$@"

# Run every fuzz target briefly, so that they keep up with the code. It finds little.
fuzz-smoke:
    @python3 contrib/fuzz.py --smoke

# Check the fuzz runner's process budget, failure reporting and cancellation.
fuzz-runner-test:
    python3 -m unittest discover -s contrib -p test_fuzz.py

# Run every Kani proof, or as cargo-kani's options say: `just kani --harness window`. See
# "Kani proofs" in docs/internals/testing.md.
kani *args:
    #!/usr/bin/env bash
    set -euo pipefail
    # CBMC can take all a machine's memory on a proof it can't finish, and macOS enforces no
    # ulimit on memory, so stop the run once it holds more than KANI_MEMORY_MB.
    limit=${KANI_MEMORY_MB:-4096}
    set -m # The run in a process group of its own, to add up and stop.
    cargo kani --workspace {{ args }} &
    run=$!
    # Out of the terminal's foreground group, the run misses its Ctrl-C: pass it on, and stop
    # the run however this ends.
    trap 'kill -TERM -- "-$run" 2> /dev/null || true' EXIT
    trap 'exit 130' INT TERM HUP
    while kill -0 "$run" 2> /dev/null; do
        kb=$(ps -o rss= -p "$(pgrep -d, -g "$run")" 2> /dev/null | awk '{ n += $1 } END { print n + 0 }' || true)
        if (( ${kb:-0} > limit * 1024 )); then
            kill -TERM -- "-$run" 2> /dev/null || true
            wait "$run" 2> /dev/null || true
            echo "kani: stopped at over $limit MB (KANI_MEMORY_MB)" >&2
            exit 1
        fi
        sleep 0.2
    done
    wait "$run"

# Mutation testing of the protocol core against its property and conformance tests. Each
# mutant runs against the oracle built here, not one it builds for itself, and the conformance
# tests make as many cases as on CI.
mutants: oracle
    MUSUBI_ORACLE=$PWD/formal/.lake/build/bin/oracle HEGEL_TEST_CASES=150 \
        cargo mutants --package musubi-core \
        --file crates/musubi-core/src/hub.rs --file crates/musubi-core/src/node.rs \
        --test-tool nextest --timeout 600

# Stream request correlation and reconnect bookkeeping; opt-in, with bounded per-mutant time.
[positional-arguments]
mutants-stream *args: oracle
    MUSUBI_ORACLE=$PWD/formal/.lake/build/bin/oracle cargo mutants \
        --package musubi-transport --file crates/musubi-transport/src/stream.rs \
        --re 'Shared::(attach|detach|receive)|StreamTransport>::request' \
        --test-tool nextest --build-timeout 600 --timeout 120 \
        --output mutants.out-stream "$@" -- --max-fail 1:immediate

# Repository decisions the protocol model assumes; only the focused native regressions run.
[positional-arguments]
mutants-adapter *args: oracle
    #!/usr/bin/env bash
    set -euo pipefail
    filter='test(/^node::tests::/) | test(/^adapter::/) | test(/^objects::/)'
    filter+=' | test(/^fetch_base::/)'
    filter+=' | test(=history::a_forgotten_copy_behind_pruned_records_stops)'
    filter+=' | test(=history::a_receiver_takes_records_that_drop_its_head_above_a_cached_fixup)'
    # The LocalRepo state only the jj repository keeps, which the core's model leaves out.
    filter+=' | test(=history::lost_records_follow_an_older_name_the_receiver_never_held)'
    filter+=' | test(=history::record_bodies_keep_pending_drops_named_after_hub_rollback)'
    filter+=' | test(=history::records_fetched_without_operations_keep_their_bodies)'
    filter+=' | test(=history::received_records_survive_departure_and_drop_local_aliases)'
    filter+=' | test(=history::lost_received_records_preserve_work_before_the_fixup_arrives)'
    filter+=' | test(=history::abandoning_a_push_the_hub_just_accepted_drops_it)'
    filter+=' | test(=history::abandoning_a_push_whose_acceptance_was_lost_drops_it)'
    filter+=' | test(/^publication::/)'
    hooks='heads_for|store_record_ops|has_record_receipts|pushing|permit_publication|learned'
    MUSUBI_ORACLE=$PWD/formal/.lake/build/bin/oracle cargo mutants \
        --package musubi-sync --file crates/musubi-sync/src/node.rs \
        --re "history_lost|>::(accepted_base|is_ancestor|prepare_records|objects_missing|$hooks)" \
        --test-tool nextest --build-timeout 600 --timeout 120 \
        --output mutants.out-adapter "$@" \
        -- --max-fail 1:immediate --lib --test races --test it -E "$filter"

# Collect a new assurance capture; output directories must not contain an earlier run.
assurance-tests out:
    python3 contrib/assurance/assurance.py tests --out {{ quote(out) }}

assurance-fuzz out:
    python3 contrib/assurance/assurance.py fuzz --out {{ quote(out) }}

assurance-mutation out:
    python3 contrib/assurance/assurance.py mutation --out {{ quote(out) }}

# Check the assurance graph, evidence and renderer; see docs/internals/assurance.md.
assurance-check:
    python3 -m unittest discover -s contrib/assurance -p 'test_*.py'
