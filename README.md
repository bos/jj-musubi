# jj-musubi: live sync for jj repos

jj-musubi keeps your [jj](https://jj-vcs.dev) repositories in sync across machines. Work on your
laptop, then pick up on a development machine: your unfinished work is already in its
repository, ready for you to check out. Your files on that machine stay put until you choose
what to work on.

jj is a git-compatible version control system. A `jj` command snapshots your files, recording
unfinished edits in a working-copy commit. musubi shares those commits too, so you can switch
machines without first committing and pushing a branch. You keep using GitHub or another Git
remote to share work with other people.

One machine that's usually on runs the **hub**, a musubi process that stores shared history
and passes updates between your machines. Each machine you work on runs a **daemon**, a
background process that sends and receives updates. The copies of one project form a
**hive**: your laptop's and devbox's copies of `app`, for example. A hub can serve many hives.
Your machines reach it over ssh; there's no service to sign up for.

Engineers at Meta get similar workflows from Sapling's Commit Cloud, and engineers at Google
from an internal jj server. musubi brings them to repositories on your own machines.

## Things you can do

In jj, a workspace is a checkout with its own files, and a bookmark names a commit, much like
a Git branch. musubi shows each other machine's workspace as a name you can use in jj commands;
it doesn't create another checkout directory here.

- Run your coding agent on your laptop and a couple of devboxes, each in its own jj workspace.
  `jj log` shows each agent's working-copy commit as `devbox/default@` or `laptop/agent-2@`,
  updated after its latest `jj` command. You can review or build on that commit from any
  machine, or hand it to another agent with `jj new devbox/default@`. A [skill for
  agents](skills/jj-musubi/SKILL.md) helps them work alongside each other.
- Each machine normally receives every commit, bookmark and edit within a second or so of the
  `jj` command that made it. Shut your laptop halfway through something you're working on, and
  the devbox has your work as `laptop/default@`. Run `jj new laptop/default@` there to carry on.
  The laptop catches up within seconds of waking.
- `jj git fetch` on one machine and every machine has the new `main@origin`. `jj git push` from
  the devbox and the laptop shows it pushed.
- musubi shares jj's record of repository changes, so you can inspect and revert a mistake
  from another machine. [Undo across
  machines](docs/guides/working-across-machines.md#undo-across-machines)
  explains the commands and which changes their results affect.
- Background sync leaves your working-copy files alone. When another machine rewrites your
  commit, jj says so. Run `jj workspace update-stale` to update the files when you're ready.
- jj never needs the hub. Work on a plane, and the laptop catches up when it lands.

Here a change described on the laptop shows up in the devbox's repository a second later:

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

`jj new laptop/default@` on the devbox checks out a new change based on that recorded work.
It leaves the laptop's change available as its parent. The [handoff
guide](docs/guides/working-across-machines.md#pick-up-on-another-machine) also covers switching
back.

## Try it and keep control

Background sync changes repository history and Git refs, while leaving checked-out files alone.
Concurrent work combines as jj combines commands in separate workspaces; conflicts remain
visible for you to resolve. You can keep working offline.

The protocol has machine-checked proofs, tests comparing the Rust implementation with those
models, and tests against real jj repositories under injected failures. [Trying musubi
safely](docs/safety.md) explains the checks, their limits, and a way to try a disposable project.

`musubi daemon stop` stops background syncing for all this machine's copies. `musubi leave`
takes one repository out after attempting to send its latest work, and keeps the repository
and files. See [Pause syncing or leave](docs/guides/manage.md#pause-syncing-or-leave).

## Install

Install musubi on the machines you work on and on the machine that will run the hub.

Download the archive for your platform from the
[latest release](https://github.com/bos/jj-musubi/releases/latest) and put the
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

These steps connect your laptop and a development machine called `devbox`. Replace `devbox`
with the name you use for ssh. You can try them with a disposable project first.

You need:

- `jj` 0.47.1 and `git` on every machine;
- a jj repository with at least one commit and all of its history (musubi refuses shallow and
  partial clones);
- ssh access to the hub's machine from every other machine: if `ssh devbox` works, so does
  musubi;
- `musubi` on the `PATH` of non-interactive shells on the hub's machine, since other machines
  run it over ssh: check with `ssh devbox musubi --version`.

If you have no jj repository yet, start with `jj git clone <url> <dir>` and run the repository
commands below inside `<dir>`. For an existing Git checkout, see jj's
[Git compatibility guide](https://docs.jj-vcs.dev/latest/git-compatibility/).

On the hub's machine:

```sh
musubi hub
```

Leave this terminal running: the hub stays in the foreground. Use another terminal for the
remaining commands, even if you work on the devbox too.

It creates `~/musubi-hub` the first time, and prints what to run on the other machines:

```text
Created a new hub in /home/you/musubi-hub
To share a repository:               musubi create --hub devbox
To add another machine's copy of it: musubi join --hub devbox
To make a new copy of a hive:        musubi clone <name> [<dir>] --hub devbox
Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't devbox.
On this machine, leave out --hub.
```

In one machine's copy of the repository, start a hive from it:

```sh
musubi create --hub devbox
```

The hive is named after the repository's `origin` remote (`jj-musubi`, say), or its
directory. By default, sharing starts with the repository's current state; older undo history
stays local. Add `--full-history` to `musubi create` or `musubi join` if you want to share that
older history too. In each other machine's copy, join it:

```sh
musubi join --hub devbox
```

The hub works out which hive a copy belongs in from its history and remotes. `create` and
`join` start the daemon and remember the hub, so later commands need no `--hub`. The first
time a machine uses a hub, musubi adds an ssh key of its own to `~/.ssh/authorized_keys` on
the hub's machine, allowed only to reach the hub; ssh may ask for your password that once.

To start a new machine from a hive instead, use the name `musubi create` printed. In this
example it is `jj-musubi`:

```sh
musubi clone jj-musubi ~/src/jj-musubi --hub devbox
```

Run `musubi status` inside each copy. Look for a running daemon serving the repository, a
recent sync, and `the hub has all its work`. This means all work jj has recorded, not edits
since your last `jj` command. The [setup verification](docs/guides/setup.md#check-your-first-sync)
walks through checking work arriving on the other machine.

To start the daemon at login, run `musubi daemon install` on each machine you work on.
On the hub's machine, stop the foreground hub with Ctrl-C and run `musubi hub install`
(macOS or Linux). Linux servers also need `loginctl enable-linger` to keep user services
running after logout. [Keep the hub running](docs/guides/setup.md#keep-the-hub-running)
explains platform support and login requirements.

## Day to day

Keep using jj as you always have; the daemon syncs your work in the background. `jj log` shows
the change each other machine's workspace is on, named after the machine and workspace, such
as `laptop/default@`, which you can diff, build on, or rebase like any other revision.
musubi's own commands are for checking on it:

- `musubi` (or `musubi list`) shows the hub's hives, this machine's copies of them, and
  whether each is syncing.
- `musubi status` reports the current repository's sync state, whether the hub has its latest
  recorded work, every machine's working copies, and the daemon's status. It returns
  immediately and includes warnings when something needs attention.
- `musubi top` shows the hub's traffic and every machine's syncing, live.
- `musubi sync` syncs the current repository now; `musubi leave` takes it out of its hive.
- `musubi forget <machine>` forgets a machine that went away without leaving. A temporary
  copy joined with `--lease 6h` is forgotten after six hours without a local
  operation (`musubi.forget-after`); other copies are kept by default.
- `musubi daemon install` starts the daemon at login; `musubi daemon start`, `stop` and
  `restart` control it.
- `musubi hub install` runs the hub at login; `musubi hub rename` and `musubi hub remove`
  manage the hub's hives.

Automatic snapshots can keep accidental files even after you delete them. To limit how much
of that content spreads, musubi pauses sending when snapshots retain more than **100 extra
file paths or 8 MiB**. Receiving continues. The limits add up across snapshots. Content needed
by changes you've deliberately committed or rewritten, and content already shared with the
hive, doesn't count against them.

If work hasn't arrived, start with `musubi status` on the sending machine. A snapshot hold
names `musubi sync --outgoing`, which lists what's waiting. [Accidental files and stopped
sending](docs/troubleshooting.md#accidentally-added-files-and-sending-stopped) walks through
checking the hold, keeping files locally, and cleaning up or approving the recorded work.

The daemon logs to `daemon.log` in musubi's state directory (`~/.local/state/musubi` on Linux
and macOS), or under systemd, to `journalctl --user -u musubi`. See
[Logging](docs/reference/configuration.md#logging).

## Learn more

- [How musubi works](docs/how-it-works.md): what replicates, and what stays on each machine.
- [Trying musubi safely](docs/safety.md): what sync changes, how to stop it, and the evidence
  behind its safety properties.
- [Set up a hub and machines](docs/guides/setup.md): ssh, keeping the hub running, forks,
  machine names, and more than one repository.
- [Work across machines](docs/guides/working-across-machines.md): picking up on another
  machine, coding agents, stale working copies, undo, and configuring each machine.
- [Manage hives, machines, and hubs](docs/guides/manage.md): leaving, renaming, upgrading, and
  replacing a hub.
- [Troubleshooting](docs/troubleshooting.md)
- [Command reference](docs/reference/commands.md) and
  [configuration](docs/reference/configuration.md)
- [How musubi compares with other approaches](docs/comparison.md)

The [user guide](docs/README.md) lists every page, and `musubi <command> --help` every flag.

## Upgrading

Upgrade the hub's machine and every other machine together: until 1.0, a release may change
the protocol, and a machine and a hub whose protocols differ refuse to sync, saying so. Give
each machine a command to install a release, and it follows its hub by itself.
[Upgrade musubi](docs/guides/manage.md#upgrade-musubi) gives the steps, and
[CHANGELOG.md](CHANGELOG.md) what each release changes.

## Development

See [CONTRIBUTING.md](CONTRIBUTING.md) for setup and checks, and the
[contributor docs](docs/internals/README.md) for the design, the protocol and its proofs, and
testing.

## License

Copyright 2026 Voxel Labs, Inc. Licensed under the [Apache License, Version 2.0](LICENSE).
