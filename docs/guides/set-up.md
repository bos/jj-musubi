# Set up a hub and machines

This guide walks through setting up musubi from nothing: choosing and starting a hub, sharing
a repository through it, and adding machines. The [README](../../README.md#quick-start) has
the short version.

## Before you start

You need, on every machine:

- `musubi`. See [Install](../../README.md#install).
- `jj` 0.46.0, and `git`. musubi runs the `git` that jj's `git.executable-path` names, or on
  the hub's machine, the `git` on its `PATH`.
- ssh access to the hub's machine: if `ssh devbox` works, so does musubi. Your
  `~/.ssh/config` applies, aliases, `ProxyCommand`, `ProxyJump` and all.

And a repository with at least one commit and all of its history. musubi refuses a shallow or
partial clone, since it couldn't send other machines everything they need. A fresh
`jj git clone` without `--depth` is fine.

## Choose the hub's machine

The hub should run on a machine that is usually on and that every other machine can reach
over ssh: a devbox, a home server, or a desktop that never sleeps. A laptop is a poor
choice, since the others can't sync while it sleeps.

The hub's machine can also have copies of its hives, and usually does: a devbox you work on
is a fine hub.

## Start the hub

On the hub's machine, make sure `musubi` is on the `PATH` of non-interactive shells, since
other machines run it over ssh. Check from another machine:

```sh
ssh devbox musubi --version
```

If that says `musubi: command not found`, put its directory on the `PATH` in `~/.zshenv`, or
near the top of `~/.bashrc`, before any line that returns early for non-interactive shells.

Then start the hub:

```sh
musubi hub
```

The first time, it creates `./musubi-hub` and prints what to run elsewhere:

```text
Created a new hub in /home/you/musubi-hub
Saved this hub as this machine's default (/home/you/.config/musubi/config.toml).
To share a repository:               musubi create --hub devbox
To add another machine's copy of it: musubi join --hub devbox
To make a new copy of a hive:        musubi clone <name> <dir> --hub devbox
Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't devbox.
On this machine, leave out --hub.
```

The `--hub` it suggests is this machine's host name. If other machines reach it by another
name, such as an alias in their `~/.ssh/config`, use that instead. `musubi hub --advertise
<name>` makes the hub print that name from then on.

Later, run `musubi hub` again from the same directory, or from inside `musubi-hub`, to serve
the same hives. Machines reconnect by themselves.

### Keep the hub running

`musubi hub` runs in the foreground until you stop it. To keep it running after you log out,
run it under `tmux` or `screen`, or as a service. On Linux, a systemd user unit does it, in
`~/.config/systemd/user/musubi-hub.service`:

```ini
[Unit]
Description=musubi hub

[Service]
WorkingDirectory=%h
ExecStart=/usr/local/bin/musubi hub
Restart=on-failure

[Install]
WantedBy=default.target
```

Give `ExecStart` the path to your `musubi`, and if `git` isn't in `/usr/bin` or
`/usr/local/bin`, an `Environment=PATH=...` line that includes it. Then:

```sh
systemctl --user enable --now musubi-hub
loginctl enable-linger
```

`loginctl enable-linger` keeps your user's services running while you're logged out. The
hub logs to the journal: `journalctl --user -u musubi-hub`.

Run the hub without `--dir`, as above, unless you mean to run more than one. Other machines'
ssh connections run `musubi hub connect`, which finds the hub that `musubi hub` last served
without `--dir`.

## Share a repository

In the repository on one machine, start a hive from it:

```sh
musubi create --hub devbox
```

On the hub's machine itself, leave out `--hub`. The hive is named after the repository's
`origin` remote (`app` for `github.com/you/app`), or after its directory if it has no
remotes. To choose another name, pass it: `musubi create work-app`.

`create` starts the daemon, if it isn't running, and returns once the repository has synced:

```text
Created an ssh key for musubi: /home/you/.local/state/musubi/hub_key
Adding it to ~/.ssh/authorized_keys on devbox, allowed only to run `musubi hub connect`. ssh may ask for your password.
Saved devbox as this machine's default hub (/home/you/.config/musubi/config.toml).
Created hive app
Syncing...
Synced with the hub (hive at #1). The daemon keeps it in sync from now on.
To start the daemon at login too: musubi daemon install
```

The first time, it saves the hub as this machine's default, so later commands need no
`--hub`.

## Add other machines

On each other machine, in its copy of the repository:

```sh
musubi join --hub devbox
```

The hub works out which hive the copy belongs in: the one that has some of its history and
one of its remotes' URLs. You don't need to name it:

```text
Joined hive app (matched origin), 2 machines
Syncing...
Synced with the hub (hive at #3). The daemon keeps it in sync from now on.
```

The copies' histories are merged, as jj merges concurrent operations: commits both copies
have are sent only once, and a bookmark that points to different commits in the two copies
becomes conflicted until you move it.

If the copy belongs in no hive, or in more than one, `join` refuses and says why. See
[Joining is refused](../troubleshooting.md#joining-is-refused).

To start a new machine with no copy yet, clone the hive instead:

```sh
musubi clone app ~/src/app --hub devbox
```

This makes a new colocated repository, joins it to the hive, and syncs it.

## The first connection over ssh

The first time a machine uses a hub over ssh, musubi creates an ssh key for itself, at
`hub_key` in its state directory (`~/.local/state/musubi` on Linux and macOS), and adds it to
`~/.ssh/authorized_keys` on the hub's machine:

```text
restrict,command="musubi hub connect" ssh-ed25519 AAAA...
```

`command=` means that anyone holding the key can reach the hub and nothing else on that
machine. Adding it goes through your ordinary ssh, so ssh may ask for your password that
once. From then on, the daemon reaches the hub with this key alone, never prompting. It needs
an ssh agent only for what it needs anyway: a `ProxyJump` host, or signing commits with a key
an agent holds. It uses the agent of the latest session to run a musubi command.

Anyone who can reach a hub can read and write every hive on it. So the hub listens only on a
socket in its directory that only its own user can reach, and other machines come in over
ssh, as that user, with keys that can do nothing else.

If `musubi` isn't on the `PATH` of non-interactive shells there, you can instead give its
absolute path in that line: `command="/opt/musubi/bin/musubi hub connect"`.

## Start the daemon at login

`create`, `join`, and `clone` start the daemon for you, but it doesn't survive a reboot. To
start it at login from now on:

```sh
musubi daemon install
```

This installs a launchd agent on macOS, a systemd user unit on Linux, or an entry under the
`Run` registry key on Windows, and starts the daemon. On Linux, it stops when you log out
unless you also run `loginctl enable-linger`, which a server you reach only over ssh needs.

The service runs the `musubi` that `daemon install` found, and on macOS and Linux, with the
`PATH` you ran it with. If you move `musubi`, or the `git` it runs, run `musubi daemon
install` again.

## Name machines

Other machines show each machine's working copy as a workspace named after it, such as
`laptop/default@`. The name defaults to jj's `operation.hostname`, which is usually the host
name. To choose another, pass `--machine` to `create`, `join`, or `clone`:

```sh
musubi join --machine work-laptop
```

Two machines may share a name: musubi tells them apart by an id of its own, and shows them as
`laptop-1a2b/default@` and `laptop-3c4d/default@`.

## Bring the operation history

By default, a machine that creates or joins a hive shares its repository's current state,
not its past operations: other machines' `jj op log` starts from the join. A repository in
use for years can have tens of thousands of operations, each of whose views can keep alive
commits nothing else needs, such as old working-copy snapshots.

To share the whole operation history instead, pass `--full-history` to `create` or `join`.

## More repositories, forks, and hubs

One hub serves any number of repositories, each its own hive. Run `musubi create` in each
repository you want to share, and `musubi join` in the other copies. One daemon per machine
serves them all.

A fork shares history with the original but has remotes of its own, so `musubi join` won't
put it in the original's hive. Run `musubi create` in it to give it a hive of its own, or
`musubi join --hive <name>` to join a particular hive whatever its remotes.

A machine can use more than one hub. Its default is the first it joined; pass `--hub` to
`create`, `join`, or `clone` to use another. Each repository remembers its own hub.
