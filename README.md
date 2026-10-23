# jj-musubi

Keeps a [jj](https://jj-vcs.dev) repository in sync across your machines. Commit, rebase,
or abandon on one machine and the same operation appears in `jj op log` on the others
within a second or so. A machine that was offline catches up when it reconnects.

musubi replicates jj's operation log, not just branches, so `jj undo`, `jj op log`, and
divergence all behave across machines as they do between workspaces on one machine. It
never touches working copies: when another machine rewrites the commit under your `@`, your
next `jj` command stops and suggests `jj workspace update-stale`, which updates your files.
With `snapshot.auto-update-stale = true`, the next command updates them itself. To set that
on every machine at once, set it in the repo config and share it:

```sh
jj config set --repo snapshot.auto-update-stale true
jj config set --repo musubi.shared-config '["snapshot.auto-update-stale"]'
```

Status: early. The protocol is proved correct in the Lean theorem prover (`formal/`), and
the implementation is tested against that model and against real repositories, but musubi
has not yet been used in anger.

## Install

Install musubi on every machine, the hub's included. Download the archive for your platform
from the [latest release](https://github.com/bos/jj-musubi/releases/latest), and put the
`musubi` in it on your `PATH`: on the hub's machine, the `PATH` of non-interactive shells too
(see [Quick start](#quick-start)). There are builds for Linux (static, x86_64 and aarch64), macOS
(x86_64 and aarch64), and Windows (x86_64 and aarch64). The release's `SHA256SUMS` lists each
archive's checksum, and `gh attestation verify <archive> --repo bos/jj-musubi` checks that
this repository's release workflow built it.

On macOS, a browser marks what it downloads as quarantined, and macOS then refuses to run
`musubi`, which isn't notarized. Download it with `curl -LO` instead, or clear the mark with
`xattr -d com.apple.quarantine musubi`.

Or build it from source, with Rust 1.97.1 or later:

```sh
cargo install --locked jj-musubi
```

Or build the latest code, which may not talk to a hub running a release:

```sh
cargo install --locked --git https://github.com/bos/jj-musubi jj-musubi
```

To have your shell complete musubi's commands and hive names, see
[Complete commands in your shell](docs/reference/commands.md#complete-commands-in-your-shell).

## Quick start

You need:

- `jj` 0.46.0 and `git` on every machine;
- a repository with at least one commit, and all of its history: not a shallow or partial
  clone;
- ssh access to the hub's machine from every other machine: if `ssh devbox` works, so does
  musubi;
- `musubi` on the hub machine's `PATH` for non-interactive shells, which other machines run
  it in: check with `ssh devbox musubi --version`.

On the machine that will run the hub (any machine that is usually on):

```sh
musubi hub
```

It creates `./musubi-hub` the first time, and prints what to run on the other machines:

```text
Created a new hub in /home/you/musubi-hub
Saved this hub as this machine's default (/home/you/.config/musubi/config.toml).
To share a repository:               musubi create --hub devbox
To add another machine's copy of it: musubi join --hub devbox
To make a new copy of a hive:        musubi clone <name> <dir> --hub devbox
Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't devbox.
On this machine, leave out --hub.
```

Then, in one machine's copy of the repository, start a hive from it:

```sh
musubi create --hub devbox
```

The hive is named after the repository's `origin` remote (`jj-musubi`, say), or its
directory. In each other machine's copy, join it:

```sh
musubi join --hub devbox
```

That's all. The hub works out which hive a copy belongs in from its history and remotes.
`create` and `join` start a daemon in the background that keeps every repository on the
machine in sync, and remember the hub, so later commands need no `--hub`. The first time a
machine uses a hub, musubi adds an ssh key of its own to `~/.ssh/authorized_keys` there,
allowed only to reach the hub; ssh may ask for your password that once.

To start a new machine from a hive instead:

```sh
musubi clone jj-musubi ~/src/jj-musubi --hub devbox
```

To keep the daemon running across reboots, run `musubi daemon install` on each machine.

## Day to day

Keep using jj. Each other machine's working copy shows in `jj log` as a workspace named after
it, such as `laptop/default@`, and `jj op log` shows what every machine did.

- `musubi` (or `musubi list`) shows the hub's hives, this machine's copies of them, and how
  their syncing goes, and in a hive's repository, its details.
- `musubi sync` syncs the current repository now; `musubi leave` stops syncing it.
- `musubi daemon install` starts the daemon at login; `musubi daemon start`, `stop` and
  `restart` control it.
- `musubi hub rename` and `musubi hub rm` manage the hub's hives.

The hub and the daemon log what they do: the daemon to `daemon.log` in musubi's state
directory (`~/.local/state/musubi` on Linux and macOS), or, when systemd starts it at login,
to `journalctl --user -u musubi`.

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

The [user guide](docs/README.md) lists every page. For every flag, run
`musubi <command> --help`.

## Upgrading

Upgrade the hub's machine and every other machine together: until 1.0, a release may change
the protocol, and a machine and a hub whose protocols differ refuse to sync, saying so.
[CHANGELOG.md](CHANGELOG.md) says what each release changes, and anything else to do on
upgrading. See [Upgrade musubi](docs/guides/manage.md#upgrade-musubi) for the steps.

## Development

See [CONTRIBUTING.md](CONTRIBUTING.md) for setup and checks, and the
[contributor docs](docs/internals/README.md) for the design, the protocol and its proofs, and
testing.

## License

Copyright 2026 Voxel Labs, Inc. Licensed under the [Apache License, Version 2.0](LICENSE).
