# Contributing

## Before you start

Open an issue before writing a substantial change. musubi's correctness rests on a protocol
proved in Lean and on matching jj's own behaviour exactly, so a change to what it replicates
or how machines agree needs discussing first. [The design](docs/internals/design.md) explains
the choices and the reasons for them.

Bug reports, documentation fixes, and small focused fixes are welcome without discussion.
For a security problem, see [SECURITY.md](SECURITY.md).

Read [AGENTS.md](AGENTS.md), the working agreement for people and coding agents alike, before your
first change: it says how to check, test and review a change, and what the hub, the wire format
and the docs may and may not do. The [contributor docs](docs/internals/README.md) cover the
design, the protocol, testing, and releasing.

## Development setup

You need:

- Rust 1.97.1 or later, and `just`.
- `jj` 0.46.0 and `git` on `PATH`: the tests run them.
- `cargo-nextest`, `cargo-deny`, `cargo-machete`, and `typos`, for `just check`.
- Lean, with `lake`, on `PATH`, for the proofs and the conformance oracle. `elan` installs
  the version `formal/lean-toolchain` names.

Run `just --list` to see every recipe. `just dev` builds `target/debug/musubi`, and
`just install` installs it and restarts a running daemon.

## Checks

```sh
just check      # fmt, clippy, Lean proofs and oracle, tests, docs, cargo-deny, machete, typos
```

The test suite alone takes a couple of minutes, so while working run only what your change
touches, then `just check` once before asking for review, saying which checks passed
([AGENTS.md, "Checks"](AGENTS.md#checks)):

```sh
cargo nextest run -p musubi-jj -E 'test(/^join::/)'    # one test file
cargo nextest run -p musubi-jj                         # one crate
```

Some runs are slow, and not part of `just check`:

```sh
just property       # the generated end-to-end search
just fuzz bundle    # one fuzz target, until stopped (needs cargo-fuzz and nightly Rust)
just mutants        # mutation testing of the protocol core (needs cargo-mutants)
just bench-smoke    # every benchmark script, once (see bench/README.md)
```

[docs/internals/testing.md](docs/internals/testing.md) explains every layer of tests, and what
CI and the nightly workflows run.
[docs/internals/testing-philosophy.md](docs/internals/testing-philosophy.md) says what a test
must protect, which layer it belongs in, and what evidence each kind of change needs, and
[docs/internals/efficient-tests.md](docs/internals/efficient-tests.md) how to keep a new test
fast.

When a change alters what users see, update the [user guide](docs/README.md) and the built-in
help too: see [docs/AGENTS.md](docs/AGENTS.md).

## Submitting

Pull requests go to `main`.

By contributing, you agree that your contributions are licensed under the
[Apache License 2.0](LICENSE).
