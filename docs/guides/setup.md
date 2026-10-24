# Set up a hub and machines

This guide sets up musubi from nothing. One machine runs a **hub**, which every other machine
reaches over ssh. Each repository you share becomes a **hive** on the hub, and a **daemon**
on each machine keeps that machine's copies in sync with it. [How musubi
works](../how-it-works.md) says more, and the [README](../../README.md#quick-start) has the
short version of this guide.

## Before you start

You need, on every machine:

- `musubi`. See [Install](../../README.md#install).
- `jj` 0.46.0, and `git`. musubi runs the `git` that jj's `git.executable-path` names; the
  hub runs the `git` on its `PATH`.
- ssh access to the hub's machine: if `ssh devbox` works, so does musubi. Your
  `~/.ssh/config` applies, with its aliases, `ProxyCommand` and `ProxyJump`.

You also need a repository with at least one commit and all of its history. musubi refuses a
shallow or partial clone, since it couldn't send other machines everything they need. A
`jj git clone` without `--depth` is fine.

## Choose the hub's machine

Run the hub on a machine that is usually on and that every other machine can reach over ssh:
a devbox, a home server, or a desktop that never sleeps. A laptop is a poor choice, since the
others can't sync while it sleeps. The hub's machine can have copies of the repositories
too: a devbox you work on is a fine hub.

## Start the hub

Other machines run `musubi` on the hub's machine over ssh, so it must be on the `PATH` of
non-interactive shells there. Check from another machine:

```sh
ssh devbox musubi --version
```

If that says `musubi: command not found`, put its directory on the `PATH` in `~/.zshenv`, or
near the top of `~/.bashrc`, before any line that returns early for non-interactive shells.

Then, on the hub's machine:

```sh
musubi hub
```

The first time, it creates `~/musubi-hub` and prints what to run elsewhere:

```text
Created a new hub in /home/you/musubi-hub
To share a repository:               musubi create --hub devbox
To add another machine's copy of it: musubi join --hub devbox
To make a new copy of a hive:        musubi clone <name> <dir> --hub devbox
Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't devbox.
On this machine, leave out --hub.
```

The `--hub` it suggests is this machine's host name. If other machines reach it by another
name, such as an alias in their `~/.ssh/config`, use that instead; `musubi hub --advertise
<name>` makes the hub print that name from then on.

To serve the same hives later, run `musubi hub` again, with the same `--dir` if you gave one.
Machines reconnect by themselves.

`--dir` keeps the hub's directory somewhere else. Leave it out unless you run more than one
hub on the machine: other machines' ssh connections reach only the hub last started without
it.

### Keep the hub running

`musubi hub` runs in the foreground until you stop it. To run the hub at login from now on,
and now, stop it and run instead:

```sh
musubi hub install
```

This installs a launchd agent on macOS, or a systemd user unit on Linux, which runs `musubi
hub` in the hub's directory, and again if it fails. It serves the directory `musubi hub`
would, taking `--dir` and `--advertise` as `musubi hub` does, and prints what to run
elsewhere. On Linux, the hub stops when you log out unless you also run `loginctl
enable-linger`; a server you reach only over ssh needs it. Windows has no `hub install`.

The service runs the `musubi` that `hub install` found, with the `PATH` you ran it with. If
you move `musubi`, or the `git` it runs, or want the hub to serve another directory, run
`musubi hub install` again. `musubi hub uninstall` stops the hub, and stops it running at
login.

The hub logs to `hub.log` in musubi's state directory on macOS, and to the journal on Linux:
`journalctl --user -u musubi-hub`.

## Share a repository

In the repository on one machine, start a hive from it (on the hub's machine, leave out
`--hub`):

```sh
musubi create --hub devbox
```

The hive is named after the repository's `origin` remote (`app` for `github.com/you/app`), or
its directory if it has no remotes. To choose another name, pass it: `musubi create work-app`.

`create` starts the daemon if it isn't running, and returns once the repository has synced:

```text
Created an ssh key for musubi: /home/you/.local/state/musubi/hub_key
Adding it to ~/.ssh/authorized_keys on devbox, allowed only to run `musubi hub connect`. ssh may ask for your password.
Created hive app
Syncing...
Synced with the hub (hive at #1).
```

The first hub a machine uses becomes its default, so later commands need no `--hub`. The
ssh key is explained [below](#the-ssh-key-musubi-adds).

## Add other machines

On each other machine, in its copy of the repository:

```sh
musubi join --hub devbox
```

You don't need to name the hive: the hub picks the one that has some of the copy's history
and one of its remotes' URLs.

```text
Joined hive app (matched remote origin), 2 machines
Syncing...
Synced with the hub (hive at #3).
```

The copies' histories are merged as jj merges concurrent operations: commits both copies have
are sent only once, and a bookmark that points to different commits in the two copies is
conflicted until you move it.

If the copy matches no hive, or more than one, `join` refuses and says why. See [Joining is
refused](../troubleshooting.md#joining-is-refused).

For a machine with no copy yet, clone the hive instead. This makes a new colocated
repository, joins it to the hive, syncs it, and checks out the hive's trunk, as `jj git clone`
checks out a remote's default branch:

```sh
musubi clone app ~/src/app --hub devbox
```

## The ssh key musubi adds

The first time a machine uses a hub over ssh, musubi creates an ssh key for itself, `hub_key`
in its state directory (`~/.local/state/musubi` on Linux and macOS), and adds it to
`~/.ssh/authorized_keys` on the hub's machine:

```text
restrict,command="musubi hub connect" ssh-ed25519 AAAA... musubi@laptop
```

`command=` means the key can reach the hub and nothing else on that machine. musubi adds it
through your own ssh, so ssh may ask for your password that once. After that, the daemon uses
this key and never prompts. It needs an ssh agent only for a `ProxyJump` host, or to sign
commits with a key the agent holds; it uses the agent of the latest session that ran a musubi
command.

Anyone who can reach a hub can read and write every hive on it, so other machines reach it
only over ssh, with keys that can do nothing else ([SECURITY.md](../../SECURITY.md)).

If `musubi` isn't on the `PATH` of non-interactive shells on the hub's machine, you can give
its absolute path in that line instead: `command="/opt/musubi/bin/musubi hub connect"`.

## Start the daemon at login

`create`, `join` and `clone` start the daemon, but it doesn't survive a reboot. To start it
at login from now on:

```sh
musubi daemon install
```

This installs a launchd agent on macOS, a systemd user unit on Linux, or an entry under the
`Run` registry key on Windows, and starts the daemon. On Linux, the daemon stops when you log
out unless you also run `loginctl enable-linger`; a server you reach only over ssh needs it.

On macOS and Linux, the service runs the `musubi` that `daemon install` found, with the
`PATH` you ran it with. If you move `musubi`, or the `git` it runs, run `musubi daemon
install` again.

## Name machines

Other machines show each machine's working copy as a workspace named after it, such as
`laptop/default@`. The name defaults to jj's `operation.hostname`, usually the host name. To
choose another, pass `--machine` to `create`, `join` or `clone`:

```sh
musubi join --machine work-laptop
```

Two machines may share a name: musubi tells them apart by an id of its own, and shows them as
`laptop-1a2b/default@` and `laptop-3c4d/default@` from then on, even once one has left.

## Bring the operation history

By default, a machine that creates or joins a hive shares its repository's current state, not
its past operations, so other machines' `jj op log` starts from the join. This keeps old
operations out of the hive: a repository used for years can have tens of thousands, whose
views keep alive commits nothing else needs, such as old working-copy snapshots.

To share the whole operation history instead, pass `--full-history` to `create` or `join`.

## More repositories, forks, and hubs

One hub serves any number of repositories, each its own hive, and one daemon per machine
serves them all. Run `musubi create` in each repository you want to share, and `musubi join`
in its other copies.

A fork shares history with the original but has remotes of its own, so `musubi join` won't
put it in the original's hive. Run `musubi create` in it to give it a hive of its own, or
`musubi join --hive <name>` to join a particular hive whatever its remotes.

A machine can use more than one hub. Pass `--hub` to `create`, `join` or `clone` to use one
other than the default. Each repository remembers its own hub.
