# Set up a hub and machines

Choose the hub's machine, share a repository, and add the other machines over ssh.

The **hub** is a musubi process on a machine that's usually on. It stores shared repository
history and passes updates between machines over ssh. Each machine you work on runs a
**daemon**, a background process that syncs its repositories with the hub. The copies of one
repository form a **hive**; a hub can serve several hives, one per project.

The examples use `devbox` for the hub's ssh name and `app` for the project. Replace them with
yours. Start on the machine with your existing jj repository, and keep a terminal available
on the devbox too. The [quick start](../../README.md#quick-start) has the shorter route.

## Before you start

You need, on every machine:

- `musubi`. See [Install](../../README.md#install).
- `jj` 0.47.1, and `git`. musubi runs the `git` that jj's `git.executable-path` names; the
  hub runs the `git` on its `PATH`.
- ssh access to the hub's machine: if `ssh devbox` works, so does musubi. Your
  `~/.ssh/config` applies, with its aliases, `ProxyCommand` and `ProxyJump`.

You also need a jj repository with at least one commit and all of its history. musubi refuses a
shallow or partial clone, since it couldn't send other machines everything they need. A
`jj git clone <url> <dir>` without `--depth` is fine. For a first trial, use a disposable project
whose history and files you're comfortable sharing. Check its ignore rules before joining:
new files normally enter jj's next snapshot too.

## Choose the hub's machine

Run the hub on a machine that is usually on and that every other machine can reach over ssh: a
devbox, a home server, or anything else that never sleeps. A laptop is a poor choice, since the
others can't sync while it sleeps. The hub's machine can have copies of the repositories too: a
devbox you work on is a fine hub.

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

Leave this terminal open. The command runs until you stop it; use another terminal for
repository commands on the same machine.

The first time, it creates `~/musubi-hub` and prints what to run elsewhere:

```text
Created a new hub in /home/you/musubi-hub
To share a repository:               musubi create --hub devbox
To add another machine's copy of it: musubi join --hub devbox
To make a new copy of a hive:        musubi clone <name> [<dir>] --hub devbox
Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't devbox.
On this machine, leave out --hub.
```

The `--hub` it suggests is this machine's host name. If other machines reach it by another
name, such as an alias in their `~/.ssh/config`, use that instead; `musubi hub --advertise
<name>` makes the hub print that name from then on. On the hub's own machine, use that name
or `localhost`. Commands reach the default hub through its local directory, without ssh.

To serve the same hives later, run `musubi hub` again, with the same `--dir` if you gave one.
Machines reconnect by themselves.

`--dir` keeps the hub's directory somewhere else. Leave it out unless you run more than one
hub on the machine: other machines' ssh connections reach only the hub last started without
it.

### Keep the hub running

`musubi hub` runs in the foreground until you stop it. To start it now and at each login,
stop it and run:

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

These are user services. On Linux, `loginctl enable-linger` lets them start without an
interactive login and survive logout. On macOS they need a logged-in user session; installing
one does not make a system service that starts before login. Windows starts the daemon at
user login and has no built-in hub service installer. After reboot, check that the expected
user session or Linux lingering is in place before relying on sync.

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

By default, the hive starts with this copy's current repository state. Earlier operations,
which jj uses for undo, stay local. Use `musubi create --full-history --hub devbox` if you want
to share that earlier operation history too; `musubi join` accepts `--full-history` as well.

`create` starts the daemon if it isn't running, and returns once the repository has synced:

```text
Created an ssh key for musubi: /home/you/.local/state/musubi/hub_key
Adding it to ~/.ssh/authorized_keys on devbox, allowed only to run `musubi hub connect`. ssh may ask for your password.
Created hive app
```

The first hub a machine uses becomes its default, so later commands need no `--hub`. The
ssh key is explained [below](#the-ssh-key-musubi-adds). Concurrent joins on this machine reuse
the same completed key pair; each hub may still ask you to authorize it.

## Add other machines

On each other machine, in its copy of the repository:

```sh
musubi join --hub devbox
```

You don't need to name the hive: the hub picks the one that has some of the copy's history
and one of its remotes' URLs.

```text
Joined hive app (matched remote origin), 2 machines
```

The copies' histories are merged as jj merges concurrent operations: commits both copies have
are sent only once, and a bookmark that points to different commits in the two copies is
conflicted until you move it.

If the copy matches no hive, or more than one, `join` refuses and says why. See [Joining is
refused](../troubleshooting.md#joining-is-refused).

For a machine with no copy yet, clone the hive instead. This makes a new colocated
repository, joins it to the hive, syncs it, and checks out `trunk()` using this machine's jj
config:

```sh
musubi clone app ~/src/app --hub devbox
```

Without a directory, as in `musubi clone app --hub devbox`, it makes the copy in a new directory
named after the hive, in the current directory: `app`, or `dotfiles` for a hive named
`bos/dotfiles`.

The new copy uses this machine's jj configuration. If its name or email is missing, musubi
fills it from defaults saved when the hive was created. Git remotes stay local: before fetching
or pushing from the new copy, configure one if this machine's Git config doesn't supply it:

```sh
jj git remote add origin https://github.com/you/app.git
```

The destination must be new or empty. To share a repository you already have, run
`musubi join` in it instead.

## Check your first sync

In each copy, run:

```sh
musubi status
```

Look for `Daemon: running`, `serving this repository`, a recent `synced ... ago`, and
`the hub has all its work`. The last phrase means the work jj has already recorded. Neither
`musubi status` nor `musubi sync --outgoing` records new edits on disk.

To check a handoff, first make sure ignored and generated files are excluded on the laptop.
Run `jj status` there to record saved edits, followed by `musubi sync`. On the devbox, run
`musubi sync` inside its copy, then `jj log`: the laptop's working-copy commit should appear
as `laptop/default@`, using the
machine name its `musubi status` reports. Compare it with `jj diff -r laptop/default@`.
Your checked-out files on the devbox stay put; [pick up that
work](working-across-machines.md#pick-up-on-another-machine) when you're ready.

`musubi status` reports the last known sync without contacting the hub and exits successfully
even when it reports a problem. `musubi sync` makes a fresh attempt and reports an error if
it fails. For a sending hold or any other warning, start with
[Troubleshooting](../troubleshooting.md#start-with-this-copy).

If this was a trial, you can [pause syncing or leave](manage.md#pause-syncing-or-leave) while
keeping the repository and files.

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

## Clone settings and remote checks

Clone fills missing selected settings once; it never keeps config in sync. Choose other
defaults with `musubi.clone-config` before creating the hive, and set local rewrite and push
protections on every machine where you need them. See
[Configure each machine](working-across-machines.md#configure-each-machine).

Joining checks that a configured remote name means the same fetch and push destinations as
it does in the hive. `--hive` chooses a hive but cannot bypass a mismatch. Cloning checks
inherited remotes before creating the destination. [Fetch and
push](working-across-machines.md#fetch-and-push) explains how to use distinct names for a fork.

git names objects with SHA-1 or SHA-256, chosen when a repository is made. musubi supports
either, but all copies in a hive must use the same one. `git rev-parse --show-object-format`
reports it; `musubi clone` makes the copy with the hive's format.

## The ssh key musubi adds

The first time a machine uses a hub over ssh, musubi creates an ssh key for itself, `hub_key`
in its state directory (`~/.local/state/musubi` on Linux and macOS), and adds it to
`~/.ssh/authorized_keys` on the hub's machine:

```text
restrict,command="musubi hub connect" ssh-ed25519 AAAA... musubi@laptop
```

If setup fails, retry the command once the reported problem is fixed. A new key becomes active
only when both key files are ready. Musubi preserves an existing private key and recreates its
public-key file if missing or empty.

`command=` means the key can reach the hub and nothing else on that machine. musubi adds it
through your own ssh, so ssh may ask for your password that once. After that, the daemon uses
this key and never prompts. It needs an ssh agent only for a `ProxyJump` host, or to sign
commits with a key the agent holds. On Unix, a daemon started by a command uses the latest
responsive agent supplied by a `musubi` command. Commands inheriting that agent keep using it,
including through symbolic links.

Anyone who can reach a hub can read and write every hive on it, so other machines reach it
only over ssh, with keys that can do nothing else ([SECURITY.md](../../SECURITY.md)).

If `musubi` isn't on the `PATH` of non-interactive shells on the hub's machine, you can give
its absolute path in that line instead: `command="/opt/musubi/bin/musubi hub connect"`.

## Name machines

Other machines show each machine's working copy as a workspace named after it, such as
`laptop/default@`. The name defaults to jj's `operation.hostname`, usually the host name. To
choose another, pass `--machine` to `create`, `join` or `clone`:

```sh
musubi join --machine work-laptop
```

Two machines may share a name: musubi tells them apart by an id of its own, and shows them as
`laptop-1a2b/default@` and `laptop-3c4d/default@` from then on, even once one has left. So
may two copies on one machine, as when a copy deleted without `musubi leave` is cloned again:
`musubi list` and `musubi status` say which name a copy here has in the hive's list. A machine
where a workspace of your own has a name starting `laptop/` shows the laptop so too.

## Bring the operation history

By default, a machine that creates or joins a hive shares its repository's current state.
Other machines' `jj op log` starts from the join. A repository used for years can have tens of
thousands of past operations, keeping old working-copy snapshots and other unused commits
alive; leaving these out keeps the hive smaller.

To share the whole operation history instead, pass `--full-history` to `create` or `join`.

## More repositories, forks, and hubs

One hub serves any number of repositories, each its own hive, and one daemon per machine
serves them all. Run `musubi create` in each repository you want to share, and `musubi join`
in its other copies.

A fork shares history with the original but has remotes of its own, so `musubi join` won't
put it in the original's hive. Run `musubi create` in it to give it a hive of its own, or
`musubi join --hive <name>` to choose a particular hive. It still checks each configured
remote name against the hive's fetch and push destinations; use distinct remote names for
different destinations. See [Fetch and push](working-across-machines.md#fetch-and-push).

A machine can use more than one hub. Pass `--hub` to `create`, `join` or `clone` to use one
other than the default. Each repository remembers its own hub.
