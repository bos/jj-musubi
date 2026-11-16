# jj-musubi: live sync for jujutsu

jj-musubi keeps your [jujutsu (jj)](https://jj-vcs.dev) repositories in sync across machines,
including unfinished work. Work on your laptop, then pick up on another machine where you
left off. Syncing runs in the background.

A machine that stays on runs the **hub**, which stores shared history and coordinates updates.
A **daemon** on each machine talks to it over ssh to sync local repos. Copies of one project
form a **hive**; a hub can serve many hives.

Engineers at Meta get similar workflows from Sapling's Commit Cloud, and engineers at Google
from an internal jj server. jj-musubi brings these workflows to your own machines.

## What jj-musubi makes possible

Each checkout is a jj workspace, like a git worktree.

- **Share in-progress work between machines.** Recorded edits normally arrive within a second
  or so of jj taking a snapshot. Other machines show the laptop's working-copy commit as
  `laptop/default@` in `jj log`, ready to check out.
- **Run coding agents in parallel.** Give agents on multiple machines their own workspaces, then
  review, build, or extend that work from any machine. A [skill for
  agents](skills/jj-musubi/SKILL.md) helps agents coordinate.
- **Fetch or push once.** Run `jj git fetch` on one machine, and every machine gets the new
  `main@origin`. Push from your devbox and your laptop shows it pushed.
- **Work offline.** Keep working while disconnected. Your laptop and other machines catch up
  once you're back online.

```text
laptop:~/src/app$ jj describe -m "Add retry logic to the fetcher"
Working copy  (@) now at: kkmpptxz 8d0b4e11 Add retry logic to the fetcher
Parent commit (@-)      : zzzzzzzz 00000000 (empty) (no description set)

devbox:~/src/app$ jj log
@  vruxwmqv me@example.com 2026-10-23 10:14:02 default@ 3f2a1c9e
│  (empty) (no description set)
│ ○  kkmpptxz me@example.com 2026-10-23 10:14:01 laptop/default@ 8d0b4e11
├─╯  Add retry logic to the fetcher
◆  zzzzzzzz root() 00000000
```

Run `jj new laptop/default@` on the devbox to check out a new change based on that work.
The [handoff guide](docs/guides/working-across-machines.md#pick-up-on-another-machine) covers
switching back.

Machine-checked proofs model the sync protocol. Tests compare the implementation with those
models and inject failures into syncs between jj repos. [Understanding jj-musubi
safety](docs/safety.md) covers what sync does, how to pause or leave, and the checks' limits.

## Install

Install jj-musubi, jj, and git on every machine. Download a build from the
[latest release](https://github.com/bos/jj-musubi/releases/latest) and put its `musubi`
executable on your `PATH`. Builds cover Linux, macOS and Windows, on x86_64 and aarch64.

Or install from source with Rust 1.97.1 or later:

```sh
cargo install --locked jj-musubi
```

[Installation details](docs/guides/setup.md#install-jj-musubi) cover archive checksums,
release attestations and macOS download restrictions. For an existing installation, follow the
[upgrade guide](docs/guides/upgrading.md); it also covers deploying builds from source.

## Quick start

Start with two machines and a jj repo containing at least one commit and its complete history;
shallow and partial clones cannot sync. You can use a disposable project first. Choose one
machine as the hub.

From the other machine, check that ssh can find `musubi` on the hub's `$PATH`:

```sh
ssh my_hub_machine musubi --version
```

On the hub's machine, start the hub and leave its terminal open. Use another terminal for
any repo commands there:

```sh
musubi hub
```

On your laptop, inside the repo you want to share:

```sh
musubi create --hub my_hub_machine
```

This creates a hive named after your repo. In each other machine's copy of that repo, join the
hive:

```sh
musubi join --hub my_hub_machine
```

The hub matches the copy by its history and remotes, so you don't need to name the hive.

Both commands start the daemon and remember the hub. The first connection installs an ssh key
restricted to reaching it. Sharing starts from the repo's current state; the
[setup guide](docs/guides/setup.md) covers history options and clone settings.

If you don't have a copy of the repo on some machine, you can clone one:

```sh
musubi clone my-repo ~/src/my-repo --hub my_hub_machine
```

Run `musubi status` in each copy. Check for a running daemon, a recent sync and
`the hub has all its work`. The [first-sync check](docs/guides/setup.md#your-first-sync)
walks through recording work and checking the other copy's `jj log`.

Run `musubi daemon install` on each working machine to sync at login. [Keep the hub
running](docs/guides/setup.md#keep-the-hub-running) covers hub startup, platform support and
login requirements.

## Day to day

Keep using jj; `musubi status` reports on the current copy and `musubi top` shows activity
across machines. The [working guide](docs/guides/working-across-machines.md) covers handoffs,
stale working copies and undo. [Monitoring](docs/guides/manage.md#check-syncing) explains sync reports
and where to look when work hasn't arrived. You can [pause syncing or
leave](docs/guides/manage.md#pause-syncing-or-leave) while keeping your repos and files.

## Learn more

- [How jj-musubi works](docs/how-it-works.md): what replicates and what stays on each machine.
- [Work across machines](docs/guides/working-across-machines.md): handoffs, coding agents,
  stale working copies and undo.
- [Manage hives, machines and hubs](docs/guides/manage.md): membership, leaving and replacing
  a hub.
- [Snapshot limits and cleanup](docs/guides/snapshots.md): inspect and resolve held work.
- [Command reference](docs/reference/commands.md),
  [configuration and logging](docs/reference/configuration.md), and
  [shell completion](docs/reference/commands.md#complete-commands-in-your-shell)
- [Other approaches](docs/comparison.md): Git remotes, file syncing and working over ssh.

The [user guide](docs/README.md) lists every page; `musubi <command> --help` lists every flag.

## License

Copyright 2026 Voxel Labs, Inc. Licensed under the [Apache License, Version 2.0](LICENSE).
