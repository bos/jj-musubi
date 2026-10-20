# jj-musubi

Keeps a [jj](https://jj-vcs.dev) repository in sync across your machines. Commit, rebase,
or abandon on one machine and the same operation appears in `jj op log` on the others
within a second or so. A machine that was offline catches up when it reconnects.

musubi replicates jj's operation log, not just branches, so `jj undo`, `jj op log`, and
divergence all behave across machines as they do between workspaces on one machine. It
never touches working copies: when another machine rewrites the commit under your `@`, jj
updates your files on your next command (set `snapshot.auto-update-stale = true`).

Status: early. The protocol is verified in Lean (`formal/`), and the implementation is
tested against that model and against real repositories, but musubi has not yet been used
in anger.

## Quick start

You need `jj` 0.46.0 and `git` on every machine, and a [NATS](https://nats.io) server they
can all reach.

On the machine that will hold the hive (any always-on machine):

```sh
musubi hub --dir ~/musubi-hub --nats nats://nats.example.com:4222
```

The first run creates the hive and prints its id. Then, in each machine's copy of the
repository:

```sh
musubi join <hive-id> --nats nats://nats.example.com:4222
musubi daemon
```

Workspaces stay per-machine: each machine keeps its own `default@`, and `jj log` labels
the other machines' working copies `default@laptop` and so on. A machine's name defaults
to jj's `operation.hostname`; choose another with `musubi join --machine <name>`.

Or start a new machine from the hive:

```sh
musubi clone <hive-id> ~/src/project --nats nats://nats.example.com:4222
```

`musubi status` shows a repository's replication state. `musubi op-id <id>` translates an
operation id between this machine's op log and the hive's: each machine records its own
git refs and workspaces in its operations, so the ids differ.

## How it works

- [docs/design.md](docs/design.md): the design, and why.
- [docs/protocol.md](docs/protocol.md): the sync protocol, precisely.
- [docs/races.md](docs/races.md): what happens when machines change the same thing at once.
- [docs/conformance.md](docs/conformance.md): how the Rust code is checked against the Lean
  model.
- [docs/testing.md](docs/testing.md): the test layers.

## Development

```sh
just check      # fmt, clippy, Lean proofs and oracle, tests, docs, cargo-deny, machete, typos
just property   # the generated end-to-end search (slow)
```

Needs `cargo-nextest`, `nats-server`, `cargo-deny`, `cargo-machete`, `typos`, and Lean via
`elan` (`~/.elan/bin`).

CI (`.github/workflows/ci.yml`) runs the same lints on Linux, the tests on Linux, macOS and
Windows, and the Lean proofs and conformance test on Linux.

## Releasing

Set the version in `Cargo.toml`, then push a matching tag:

```sh
jj tag set v0.1.0 -r main
jj git push --remote origin --tag v0.1.0
```

`.github/workflows/release.yml` builds `musubi` for Linux (static, x86_64 and aarch64),
macOS (x86_64 and aarch64), and Windows (x86_64 and aarch64), with build provenance
attestations, and attaches the archives and their checksums to a draft GitHub release.
Review the draft and publish it. Running the workflow by hand from the Actions tab builds
the same archives without releasing anything.
