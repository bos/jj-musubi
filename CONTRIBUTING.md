# Contributing

Thanks for your interest in musubi.

## Before you start

Open an issue before writing a substantial change. musubi's correctness rests on a protocol
proved in Lean and on matching jj's own behaviour exactly, so a change to what it replicates
or how machines agree needs discussing first. [The design](docs/internals/design.md) explains
the choices and the reasons for them.

Bug reports, documentation fixes, and small focused fixes are welcome without discussion.
For a security problem, see [SECURITY.md](SECURITY.md).

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
touches: one test, one file, or one crate:

```sh
cargo nextest run -p musubi-jj -E 'test(/^join::/)'
cargo nextest run -p musubi-jj
```

Before asking for review, run `just check` once, and say which checks passed.

Some runs are slow, and not part of `just check`:

```sh
just property       # the generated end-to-end search
just fuzz bundle    # one fuzz target, until stopped (needs cargo-fuzz and nightly Rust)
just mutants        # mutation testing of the protocol core
just bench-smoke    # every benchmark script, once (see bench/README.md)
```

CI (`.github/workflows/ci.yml`) runs the lints on Linux, the tests on Linux, macOS, and
Windows, and the Lean proofs and conformance tests on Linux. The Search workflow runs the
end-to-end search nightly. [docs/internals/testing.md](docs/internals/testing.md) explains
every layer of tests, and which a change belongs in, and
[docs/internals/efficient-tests.md](docs/internals/efficient-tests.md) how to write a new test
so that the suite stays fast.

## Conventions

[AGENTS.md](AGENTS.md) is the working agreement for this repository, for people as much as
for coding agents. In short:

- This is a jj repository: use jj, not git.
- Until 1.0, musubi keeps no compatibility with earlier releases. A change to the wire format
  bumps `PROTOCOL_VERSION` once per release, and anything that breaks goes in
  `CHANGELOG.md`, with what a user must do on upgrading.
- The hub needn't be durable, and musubi makes no synchronous fsyncs: don't add either.
- Code and Markdown wrap at 98 columns.
- A commit's subject says what it does in plain words, as an imperative sentence with no
  trailing period: "Refuse bytes after the end of a frame or a message". Its body, if it
  needs one, says why.

The [contributor docs](docs/internals/README.md) cover the design, the protocol, testing, and
releasing. When a change alters what users see, update the [user guide](docs/README.md) and
the built-in help too: see [docs/AGENTS.md](docs/AGENTS.md).

## Submitting

Pull requests go to `main`.

By contributing, you agree that your contributions are licensed under the
[Apache License 2.0](LICENSE).
