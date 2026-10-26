# jj-musubi

Keeps a [jj](https://jj-vcs.dev) repository in sync across your machines. Commit, rebase, or
abandon on one machine, and the operation appears in `jj op log` on the others within a second
or so. A machine that was offline catches up when it reconnects.

musubi replicates jj's operation log, not just branches, so `jj op log`, `jj undo`, and
divergence work across machines as they do across workspaces on one machine. It never touches
your files: when another machine rewrites the commit your working copy is on, jj reports the
working copy stale, and `jj workspace update-stale` updates it, or [jj can do that
itself][stale].

[stale]: docs/guides/working-across-machines.md#when-another-machine-rewrites-your-working-copy

Status: early. The protocol is proved correct in the Lean theorem prover (`formal/`), and the
implementation is tested against that model and against real repositories, but musubi hasn't
yet been used in earnest.

## Install

Install musubi on every machine, the hub's included. Download the archive for your platform
from the [latest release](https://github.com/bos/jj-musubi/releases/latest) and put the
`musubi` in it on your `PATH`. There are builds for Linux (static), macOS, and Windows, each
for x86_64 and aarch64. The release's `SHA256SUMS` lists each archive's checksum, and
`gh attestation verify <archive> --repo bos/jj-musubi` checks that this repository's release
workflow built it.

On macOS, `musubi` isn't notarized, so macOS refuses to run it if a browser downloaded it.
Download it with `curl -LO` instead, or clear the browser's mark with
`xattr -d com.apple.quarantine musubi`.

Or build it from source, with Rust 1.97.1 or later:

```sh
cargo install --locked jj-musubi
```

Or build the latest code, which may not talk to a hub running a release:

```sh
cargo install --locked --git https://github.com/bos/jj-musubi jj-musubi
```

To complete musubi's commands and hive names in your shell, see
[Complete commands in your shell](docs/reference/commands.md#complete-commands-in-your-shell).

## Quick start

One machine that is usually on runs a **hub**. Each repository it shares is a **hive**, and
every machine's copy of the repository joins it. A **daemon** on each machine keeps its copies
in sync with the hub.

You need:

- `jj` 0.46.0 and `git` on every machine;
- a repository with at least one commit and all of its history: not a shallow or partial
  clone;
- ssh access to the hub's machine from every other machine: if `ssh devbox` works, so does
  musubi;
- `musubi` on the `PATH` of non-interactive shells on the hub's machine, since other machines
  run it over ssh: check with `ssh devbox musubi --version`.

On the hub's machine:

```sh
musubi hub
```

It creates `./musubi-hub` the first time, and prints what to run on the other machines:

```text
Created a new hub in /home/you/musubi-hub
Saved this hub as this machine's default.
To share a repository:               musubi create --hub devbox
To add another machine's copy of it: musubi join --hub devbox
To make a new copy of a hive:        musubi clone <name> <dir> --hub devbox
Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't devbox.
On this machine, leave out --hub.
```

In one machine's copy of the repository, start a hive from it:

```sh
musubi create --hub devbox
```

The hive is named after the repository's `origin` remote (`jj-musubi`, say), or its
directory. In each other machine's copy, join it:

```sh
musubi join --hub devbox
```

The hub works out which hive a copy belongs in from its history and remotes. `create` and
`join` start the daemon and remember the hub, so later commands need no `--hub`. The first
time a machine uses a hub, musubi adds an ssh key of its own to `~/.ssh/authorized_keys` on
the hub's machine, allowed only to reach the hub; ssh may ask for your password that once.

To start a new machine from a hive instead:

```sh
musubi clone jj-musubi ~/src/jj-musubi --hub devbox
```

To keep the daemon running across reboots, run `musubi daemon install` on each machine.
[Set up a hub and machines](docs/guides/set-up.md) covers each step in more depth.

## Day to day

Keep using jj. `jj log` shows each other machine's working copy as a workspace named after
it, such as `laptop/default@`, and `jj op log` shows what every machine did.

- `musubi` (or `musubi list`) shows the hub's hives, this machine's copies of them, and
  whether each is syncing.
- `musubi status` shows the current repository's hive, whether it syncs and whether the hub
  has its latest work, every machine's working copies, and the daemon, and warns of what's
  wrong. It answers at once, for scripts and agents to ask.
- `musubi sync` syncs the current repository now; `musubi leave` takes it out of its hive.
- `musubi forget <machine>` forgets a machine that went away without leaving. A copy that a
  coding agent (Claude Code or Codex) joined is forgotten by itself after 6 hours unused
  (`musubi.forget-after`).
- `musubi daemon install` starts the daemon at login; `musubi daemon start`, `stop` and
  `restart` control it.
- `musubi hub install` runs the hub at login; `musubi hub rename` and `musubi hub remove`
  manage the hub's hives.

The daemon logs to `daemon.log` in musubi's state directory (`~/.local/state/musubi` on Linux
and macOS), or under systemd, to `journalctl --user -u musubi`. See
[Logging](docs/reference/configuration.md#logging).

## Learn more

- [How musubi works](docs/how-it-works.md): what replicates, and what stays on each machine.
- [Set up a hub and machines](docs/guides/set-up.md): ssh, keeping the hub running, forks,
  machine names, and more than one repository.
- [Work across machines](docs/guides/working-across-machines.md): stale working copies, undo,
  concurrent changes, and shared remotes and config.
- [Manage hives, machines, and hubs](docs/guides/manage.md): leaving, renaming, upgrading, and
  replacing a hub.
- [Troubleshooting](docs/troubleshooting.md)
- [Command reference](docs/reference/commands.md) and
  [configuration](docs/reference/configuration.md)
- [How musubi compares with other approaches](docs/comparison.md)

The [user guide](docs/README.md) lists every page, and `musubi <command> --help` every flag.

## Upgrading

Upgrade the hub's machine and every other machine together: until 1.0, a release may change
the protocol, and a machine and a hub whose protocols differ refuse to sync, saying so.
[Upgrade musubi](docs/guides/manage.md#upgrade-musubi) gives the steps, and
[CHANGELOG.md](CHANGELOG.md) what each release changes.

## Development

See [CONTRIBUTING.md](CONTRIBUTING.md) for setup and checks, and the
[contributor docs](docs/internals/README.md) for the design, the protocol and its proofs, and
testing.

## License

Copyright 2026 Voxel Labs, Inc. Licensed under the [Apache License, Version 2.0](LICENSE).
