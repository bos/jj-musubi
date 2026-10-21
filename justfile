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

# The generated end-to-end search (expensive; not part of `check`).
property:
    cargo nextest run --workspace --profile search

# Mutation testing of the protocol core against its property and conformance tests. Each
# mutant runs against the oracle built here, not one it builds for itself.
mutants: oracle
    MUSUBI_ORACLE=$PWD/formal/.lake/build/bin/oracle cargo mutants --package musubi-core \
        --file crates/musubi-core/src/hub.rs --file crates/musubi-core/src/node.rs \
        --test-tool nextest --timeout 600
