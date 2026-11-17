# Get started

Connect two machines so that work recorded by jj on one arrives on the other. One machine
runs a **hub**, which stores shared history and passes updates over ssh. A background **daemon**
on each working machine syncs its repositories with the hub. Copies of one repo form a **hive**.

## Install

Install jj-musubi, jj, and git on every machine. Download a build from the
[releases page](https://github.com/bos/jj-musubi/releases) and put its `musubi`
executable on your `PATH`. Builds cover Linux, macOS and Windows, on x86_64 and aarch64.

Read the [installation details](guides/setup.md#install-jj-musubi) for more details. For an
existing installation, follow the [upgrade guide](guides/upgrading.md).

## Quick start

To try out jj-musubi, you'll need two machines (or VMs, or containers) and a jj repo that has at
least one commit and complete history (shallow and partial clones are not supported). You can
use a disposable clone of a project for experimenting.

Choose one machine as the hub. From the other machine, check that ssh can find `musubi` on the
hub's `$PATH`:

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

This creates a hive named after your repo. In each other machine's copy of that repo, join that
hive:

```sh
musubi join --hub my_hub_machine
```

The hub finds the right hive by history and remotes, so you don't need to name it.

These commands start the daemon and remember which hub it talks to. The first connection
installs an ssh key restricted to talking only to that hub.

If you don't have a copy of the repo on some machine, you can clone one:

```sh
musubi clone my-repo ~/src/my-repo --hub my_hub_machine
```

Run `musubi status` in each copy. Check for a running daemon, a recent sync and
`the hub has all its work`. The [first-sync check](guides/setup.md#your-first-sync)
walks through recording work and checking the other copy's `jj log`.

Run `musubi daemon install` on each working machine to start its daemon at login, and read [Keep
the hub running](guides/setup.md#keep-the-hub-running) for managing the hub.

## Day to day

Simply use jj as usual; `musubi status` and `musubi top` will tell you what's going on if you're
curious. The [working guide](guides/working-across-machines.md) covers handoffs, stale
working copies and undo. [Monitoring](guides/manage.md#check-syncing) explains sync reports
and where to look if work isn't syncing. You can [pause syncing or
leave](guides/manage.md#pause-syncing-or-leave) without affecting your repos or files.

