# The full local check. Run before finishing any change.
check: fmt-check lint oracle test docs deny machete typos

# Build musubi: target/debug/musubi.
dev:
    cargo build --locked -p musubi

# Build musubi optimized: target/release/musubi.
release:
    cargo build --locked -p musubi --release

# Install musubi (`just install dev` for a dev build) and restart a running daemon.
install profile="release":
    #!/usr/bin/env bash
    set -euo pipefail
    root="${CARGO_INSTALL_ROOT:-${CARGO_HOME:-$HOME/.cargo}}"
    musubi="$root/bin/musubi"
    cargo build --locked -p musubi --profile {{profile}}
    # A running daemon keeps the old binary (and on Windows locks it): stop it, install, and
    # start the new one.
    running=false
    if [[ -x $musubi ]]; then
        out=$("$musubi" daemon stop)
        echo "$out"
        if [[ $out == Stopped* ]]; then running=true; fi
    fi
    cargo install --locked --path crates/musubi --profile {{profile}} --root "$root"
    if $running; then "$musubi" daemon start; fi

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all --check

lint:
    cargo clippy --workspace --all-targets -- -D warnings

test *args:
    cargo nextest run --workspace {{args}}

docs:
    RUSTDOCFLAGS="-D warnings" cargo doc --workspace --no-deps --quiet

deny:
    cargo deny --log-level error check

machete:
    cargo machete

typos:
    typos

# Check the Lean proofs and build the oracle the conformance tests run against.
oracle:
    cd formal && ~/.elan/bin/lake build && test/run_smoke.sh

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
    cargo nextest run --workspace --profile search

# Mutation testing of the protocol core against its property and conformance tests. Each
# mutant runs against the oracle built here, not one it builds for itself.
mutants: oracle
    MUSUBI_ORACLE=$PWD/formal/.lake/build/bin/oracle cargo mutants --package musubi-core \
        --file crates/musubi-core/src/hub.rs --file crates/musubi-core/src/node.rs \
        --test-tool nextest --timeout 600
