# jj-musubi

Your [jj](https://jj-vcs.dev) repositories on every machine you use, always up to date. Work
on your laptop, close the lid, and sit down at your desktop: the change you were working on is
already there. No pushing work in progress to GitHub, no fetching it back, no wondering which
machine is behind.

musubi is for jj, the git-compatible version control system, and all it needs is ssh to one
machine that's usually on.

Engineers at Meta get this from Sapling's Commit Cloud, which uploads every commit as soon as
it's made, and engineers at Google have something like it in an internal jj server that keeps
their repositories' history in the cloud. musubi brings that to your own repositories, on your
own machines, over plain ssh, with no service to sign up for.

## What you get

- **Agents on every machine, and their work everywhere.** Run Claude Code or Codex on your
  laptop, your desktop, and a couple of devboxes, all in one repository. Every agent's work
  shows up in `jj log` on every machine as it goes, as `devbox/default@` or `laptop/agent-2@`:
  that machine's working copy, which you can look at and build on like any commit. One
  `jj log` shows what every agent everywhere is doing. Review an agent's change from wherever
  you are, hand it to an agent on another machine with `jj new devbox/default@`, and never ask
  "which machine was that on?" again. A [skill for
  agents](skills/musubi/SKILL.md) keeps them from tripping over each other.
- **Every machine current, all the time.** Laptop, desktop, home server: each has every
  commit, bookmark and change you've made on any of them, within a second or so of the `jj`
  command that made it, and a machine that was asleep catches up within seconds of waking. You
  never have to remember which one is behind.
- **Close the lid, pick up anywhere.** Shut your laptop at work and go home. Your desktop
  already has everything up to your last `jj` command, as `laptop/default@`;
  `jj new laptop/default@` and carry on. Open the laptop again and it catches up with the
  evening's work within seconds of waking.
- **GitHub, everywhere at once.** `jj git fetch` on one machine and every machine has the new
  `main@origin`. `jj git push` from the desktop and the laptop shows it pushed. Fetch once,
  not once per machine.
- **Undo that follows you.** jj records every command you run, so that `jj undo` can take any
  of them back. musubi shares that record, so a mistake made on one machine can be put right
  from any other.
- **Your files stay yours.** musubi never writes to your working copy. When another machine
  rewrites the commit you're on, jj says so, and `jj workspace update-stale` brings your files
  up to date when you're ready.
- **Offline is fine.** jj never needs the hub. Work on a plane, and the laptop catches up when
  it lands.
- **Built to be trusted.** The sync protocol is modelled and proved correct in the Lean theorem
  prover, the Rust code is checked against that model step by step, and a search runs real jj
  commands on real repositories through crashes, lost connections and power cuts. [How musubi
  keeps your work safe](docs/safety.md) tells the story.

Here a change described on the laptop shows up on the desktop a second later:

```text
laptop:~/src/app$ jj describe -m "Add retry logic to the fetcher"
Working copy  (@) now at: kkmpptxz 8d0b4e11 Add retry logic to the fetcher
Parent commit (@-)      : zzzzzzzz 00000000 (empty) (no description set)

desktop:~/code/app$ jj log
@  vruxwmqv me@example.com 2026-10-23 10:14:02 default@ 3f2a1c9e
│  (empty) (no description set)
│ ○  kkmpptxz me@example.com 2026-10-23 10:14:01 laptop/default@ 8d0b4e11
├─╯  Add retry logic to the fetcher
◆  zzzzzzzz root() 00000000
```

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

It creates `~/musubi-hub` the first time, and prints what to run on the other machines:

```text
Created a new hub in /home/you/musubi-hub
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
[Set up a hub and machines](docs/guides/setup.md) covers each step in more depth.

## Day to day

Keep using jj as you always have; there's nothing to push, fetch or remember. `jj log` shows
each other machine's working copy as a workspace named after it, such as `laptop/default@`,
which you can diff, build on, or rebase like any other revision. musubi's own commands are for
checking on it:

- `musubi` (or `musubi list`) shows the hub's hives, this machine's copies of them, and
  whether each is syncing.
- `musubi status` shows the current repository's hive, whether it syncs and whether the hub
  has its latest work, every machine's working copies, and the daemon, and warns of what's
  wrong. It answers at once, for scripts and agents to ask.
- `musubi top` shows the hub's traffic and every machine's syncing, live.
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
- [How musubi keeps your work safe](docs/safety.md): the proofs, the tests, and the design
  choices that keep every machine's work intact.
- [Set up a hub and machines](docs/guides/setup.md): ssh, keeping the hub running, forks,
  machine names, and more than one repository.
- [Work across machines](docs/guides/working-across-machines.md): picking up on another
  machine, coding agents, stale working copies, undo, and shared remotes and config.
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
