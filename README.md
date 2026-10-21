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

You need:

- `jj` 0.46.0 and `git` on every machine;
- [`nats-server`](https://docs.nats.io/running-a-nats-service/introduction/installation) on
  the machine that runs the hub (`brew install nats-server`, or a release binary);
- a repository with at least one commit;
- every machine able to reach the hub's machine. On macOS, allow incoming connections when
  the firewall asks about `nats-server`.

On the machine that will run the hub (any machine that is usually on):

```sh
musubi hub
```

It creates `./musubi-hub` the first time, starts a NATS server for it, and prints what to
run on the other machines:

```text
Created a new hub in /home/you/musubi-hub
To add a repository on any machine: musubi join --nats nats://myhost:41234
To make a new copy of a hive:       musubi clone <name> <dir> --nats nats://myhost:41234
```

Then, in each machine's copy of the repository, run the join command it printed:

```sh
musubi join --nats nats://myhost:41234
```

That's all. The first copy to join creates a hive, named after its `origin` remote
(`jj-musubi`, say); copies on other machines that share its history and a remote join that
hive. Joining starts a daemon in the background that keeps every joined repository on the
machine in sync, and remembers the hub, so later commands need no `--nats`.

Anyone who can reach the hub's port can read and write every hive on it, so run it on a
network you trust. `musubi hub --token` has its NATS server require a random token, which
the URLs it prints then carry (`nats://<token>@myhost:41234`).

A hub serves any number of repositories, each its own hive. A fork, which shares history
but has a remote of its own, gets a hive of its own; `musubi join --hive <name>` joins a
chosen hive instead, and `musubi join --new <name>` starts one. Run `musubi hub`
again in the same place after a restart: it keeps its port (and token).

Workspaces stay per-machine: each machine keeps its own `default@`, and shows the other
machines' working copies as workspaces named after them, so `jj log` shows
`laptop/default@` and so on. A machine's name defaults to jj's `operation.hostname`;
choose another with `musubi join --machine <name>`.

Or start a new machine from a hive:

```sh
musubi clone jj-musubi ~/src/jj-musubi
```

Day to day:

- `musubi` (or `musubi list`) shows the hub's hives, this machine's copies of them, and how
  their syncing goes, and in a hive's repository, its details.
- `musubi sync` syncs the current repository now; `musubi leave` stops syncing it.
- `musubi daemon stop` and `musubi daemon restart` control the daemon. It doesn't start at
  login yet: after a reboot, run `musubi daemon restart`.
- `musubi hub rename <name> <new-name>` and `musubi hub rm <name>` manage the hub's hives.
- Each machine records its own git refs and workspaces in its operations, so the same
  operation has a different id on each machine and in the hive; `musubi debug op-id <id>`
  translates between them. (`musubi debug` holds tools for investigating a hive, and is
  left out of `musubi --help`.)

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
