# The full local check. Run before finishing any change.
check: fmt-check lint oracle test docs deny machete typos

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

# Mutation testing of the protocol core against its property and conformance tests.
mutants:
    MUSUBI_ORACLE=$PWD/formal/.lake/build/bin/oracle cargo mutants --package musubi-core \
        --file crates/musubi-core/src/hub.rs --file crates/musubi-core/src/node.rs \
        --test-tool nextest --timeout 600
