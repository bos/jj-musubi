# Set up a hub and machines

The **hub** stores shared history and passes updates over ssh. A background **daemon** on each
machine syncs its repositories with the hub. Copies of one repo form a **hive**; a hub
can serve several hives.

Choose what machine the hub will run on, share a repo, and add other machines. These
examples use `devbox` for the hub's ssh name and `app` for the project.
Replace them with yours.

## Before you start

You need, on every machine:

- jj-musubi, which provides the `musubi` command. See [Install jj-musubi](#install-jj-musubi).
- `jj` and `git`.
- [ssh access](#connect-over-ssh) from every machine to the hub machine.

Use a jj repo with at least one commit and complete history (shallow and partial clones
are not supported). For a trial, use a disposable clone of a project.

## Install jj-musubi

Install jj-musubi on every working machine and the hub machine. Download an archive from the
[latest release](https://github.com/bos/jj-musubi/releases/latest) and put its `musubi`
executable on your `PATH`. There are builds for Linux (static), macOS and Windows, each for
x86_64 and aarch64.

The release's `SHA256SUMS` lists each archive's checksum. To check that this repo's
release workflow built an archive, run `gh attestation verify <archive> --repo bos/jj-musubi`.

On macOS, downloads via browser will not run by default because `musubi` isn't notarized. Use
`curl -LO`, or clear the browser's mark with `xattr -d com.apple.quarantine musubi`.

To build a release from source, install Rust 1.97.1 or later, then run:

```sh
cargo install --locked jj-musubi
```

## Choose the hub machine

Choose a machine that's usually available and reachable over ssh, such as a devbox or home
server. When it's unavailable (e.g. sleeping, shut down), other machines can't sync.

The hub can coexist on a machine alongside the daemons.

## Connect over ssh

The hub may not know the hostname under which other machines can reach it, or you may have an
ssh alias for it. `musubi hub --advertise <name>` makes it use your preferred hostname.

On the hub machine, that name or `localhost` reaches the default hub through its local
directory, without ssh.

The hub's `musubi` must be on the `PATH` of non-interactive shells. Check from another machine:

```sh
ssh devbox musubi --version
```

If that says `musubi: command not found`, put its directory on the `PATH` in your shell's
startup file, before any line that returns early for non-interactive shells.

The first time a machine uses a hub over ssh, jj-musubi authorizes a key restricted to
reaching the hub. It adds the key through your own ssh, so ssh may ask for your password that
once. After that, the daemon uses this key and never prompts.

Anyone who can reach a hub can read and write every hive on it
([SECURITY.md](../../SECURITY.md)). See [SSH configuration](../reference/configuration.md#ssh)
for key files, agent access and an absolute-command-path workaround.

## Start the hub

Then, on the hub machine, start the hub:

```sh
musubi hub
```

The hub will keep running until you stop it. Leave this terminal open for now.
You can [install a service](#keep-the-hub-running) after checking your first sync.

The first time you start a hub, it creates `~/musubi-hub` for data, and prints what to run
elsewhere:

```text
Created a new hub in /home/you/musubi-hub
To share a repository:               musubi create --hub devbox
To add another machine's copy of it: musubi join --hub devbox
To make a new copy of a hive:        musubi clone <name> [<dir>] --hub devbox
Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't devbox.
On this machine, leave out --hub.
```

The `musubi-hub` directory contains jj-musubi's data. Use `--dir` to point at a different hub
directory (you can omit it unless you run several hubs).

## Share a repo

In the repo on one machine, start a hive from it (on the hub's machine, leave out
`--hub`). Choose any [clone defaults](#choose-clone-defaults) before creating the hive:

```sh
musubi create --hub devbox
```

The hive is named after the repo's `origin` remote (`app` for `github.com/you/app`), or
its directory if it has no remotes. If you'd prefer a different name, supply it:
`musubi create work-app`.

Sharing starts with the current repo state. To share earlier undo history too, see
[Bring the operation history](#bring-the-operation-history).

`create` starts the daemon if it isn't running, and returns once the repo has synced.

When you first join a hub, it becomes this machine's default; later commands need no `--hub`.

## Add other machines

On each other machine, in its copy of the repo:

```sh
musubi join --hub devbox
```

The hub matches the hive by the copy's history and remotes; you needn't name it.

```text
Joined hive app (matched remote origin), 2 machines
```

If the repo you're trying to join from doesn't match a hive, or matches more than one, `join`
stops and says why. See [Joining is refused](../troubleshooting.md#joining-is-refused).

On a machine that doesn't yet have a copy of the repo, clone the hive. This creates a colocated
repo, joins and syncs it, then checks out `trunk()` using this machine's jj config:

```sh
musubi clone app ~/src/app --hub devbox
```

A small amount of repo-local config is copied during a clone. For instance, if your machine
doesn't have name or email settings in its jj config, they'll come from the hive's creation
defaults. For Git remotes, see [Fetch and
push](working-across-machines.md#fetch-and-push).

## Your first sync

In each copy, run:

```sh
musubi status
```

Look for `Daemon: running`, `serving this repository`, a recent `synced ... ago`, and
`the hub has all its work`. `musubi status` doesn't contact the hub, so it should return
immediately even if e.g. your laptop isn't on a network.
Read the report: its exit status is 0 even when it warns.

To see a sync happen, edit some files, then run `jj status` to snapshot those edits. You can
then either wait a moment or run `musubi sync` (to be sure the send part of a sync
has completed). In the devbox's repo, again either wait a moment or run `musubi sync` (to ensure
that the receive side of the sync has completed), then `jj log`. The laptop's in-progress commit
should appear as `laptop/default@`, using the machine name from `musubi status`. You can inspect
its contents using `jj diff -r laptop/default@`. jj-musubi won't update your working
copy, so its files stay put until you [pick up the
work](working-across-machines.md#pick-up-on-another-machine).

I almost never run `musubi sync` by hand. It's occasionally convenient for debugging, because it
will report holds and failures. For a hold or other warning, see
[Troubleshooting](../troubleshooting.md#start-with-this-copy).

## Keep the hub running

Stop the foreground hub, then install a service that will start it now and at login:

```sh
musubi hub install
```

This installs a launchd agent on macOS or a systemd user unit on Linux, restarting the hub if
it fails. It uses the same directory, `--dir` and `--advertise` as `musubi hub`, and prints what
to run elsewhere. Windows has no `hub install`.

The service uses the `musubi` and `PATH` found during installation. Run `musubi hub install`
again if you move `musubi` or `git`, or change the hub directory.

To start the hub at boot and keep it running after logout, on macOS or Linux:

```sh
musubi hub install --at-boot
```

Run this as your normal user, without `sudo`. It will ask for administrator permission to
install and manage the service as you, using your home and state directory. On macOS this
installs a launchd daemon; on Linux, a systemd system unit.

Without `--at-boot`, macOS needs a logged-in user session. This is also the default on Linux,
but you can keep the login service running using `loginctl enable-linger` (this affects *all*
of your user services).

On macOS the hub logs to `hub.log` in jj-musubi's state directory. On Linux use
`journalctl --user -u musubi-hub` for a login service, or
`sudo journalctl -u musubi-hub-$(id -u).service` for a boot service.

`musubi hub uninstall` stops the hub and removes the service.

## Start the daemon at login

`create`, `join` and `clone` start the daemon. To start it at login too:

```sh
musubi daemon install
```

This starts the daemon and installs a launchd agent on macOS, a systemd user unit on Linux,
or a Windows `Run` registry entry. The [user-service requirements](#keep-the-hub-running) apply.

## Choose clone defaults

Before creating a hive, choose the settings future clones may inherit. Name and email are
the defaults; for example, add an alias:

```sh
jj config set --repo musubi.clone-config '["user.name", "user.email", "aliases.l"]'
```

Choose portable settings. Keep signing keys, tool paths and watchers local; include any
aliases or remote names your chosen settings depend on. See
[`musubi.clone-config`](../reference/configuration.md#each-repos) for override rules
and behavior when a hive is recreated.

## Name machines

Other machines show each machine's working copy as a workspace named after it, such as
`laptop/default@`. The name defaults to jj's `operation.hostname`, usually the host name. To
choose another, pass `--machine` to `create`, `join` or `clone`:

```sh
musubi join --machine work-laptop
```

Duplicate names get id suffixes, such as `laptop-1a2b/default@` and `laptop-3c4d/default@`,
even after one leaves. This includes a copy deleted without `musubi leave` and cloned again.
`musubi list` and `musubi status` identify the copy here. A workspace of your own starting
`laptop/` also makes this machine show the laptop with a suffix.

## Bring the operation history

By default, creating or joining shares the current state; other machines' `jj op log` starts
from the join. Leaving out older operations keeps unused snapshots and commits out of the hive.

To share the whole operation history, use `musubi create --full-history --hub devbox`, or pass
`--full-history` to `join`.

## More repos, forks, and hubs

One hub can serve several repos, with one daemon on each working machine. Run
`musubi create` in each repo, and `musubi join` in its other copies.

A fork's different remotes keep it out of the original hive. Give it a hive with `musubi create`,
or choose one with `musubi join --hive <name>`. Remote checks still apply; use distinct names
for different destinations ([Fetch and push](working-across-machines.md#fetch-and-push)).

A machine can use more than one hub. Pass `--hub` to `create`, `join` or `clone` to use one
other than the default. Each repo remembers its own hub.
