# Setup: hub and daemons

The **hub** stores shared history and passes updates over ssh. A background **daemon** on each
machine syncs its repositories with the hub. Copies of one repo form a **hive**; a hub can serve
several hives.

We'll walk you through choosing what machine the hub will run on, sharing a repo, and
adding other machines. These examples use `devbox` for the hub's ssh name and `app` for the
project. Replace them with yours.

## Before you start

You need a few prerequisites on every machine:

- jj-musubi, which provides the `musubi` command. See [Install jj-musubi](#install-jj-musubi).
- `jj` and `git`.
- [ssh access](#connect-over-ssh) from every machine to the hub machine.

Use a jj repo with at least one commit and complete history (shallow and partial clones are not
supported). To try things out, I recommend you use a disposable clone of some project.

## Install jj-musubi

Install jj-musubi on every working machine and the hub machine. The easiest way is to download
an archive from the [releases page](https://github.com/bos/jj-musubi/releases) and put
its `musubi` executable on your `PATH`. There are builds for Linux (static), macOS and Windows,
each for x86_64 and aarch64. On illumos, build it from source, with
[rustup](https://rustup.rs)'s Rust, a C compiler and git (`pkg install build-essential` on
OmniOS):

```sh
cargo install --locked jj-musubi
```

jj publishes no illumos build either: build it from source too, as [jj's installation
guide](https://docs.jj-vcs.dev/latest/install-and-setup/) says.

The release's `SHA256SUMS` lists each archive's checksum. To check that this repo's
release workflow built an archive, run `gh attestation verify <archive> --repo bos/jj-musubi`.

On macOS, downloads via browser will not run by default because `musubi` isn't notarized. Use
`curl -LO`, or clear the browser's mark with `xattr -d com.apple.quarantine musubi`.

## Choose the hub machine

Choose a machine that's usually available and reachable over ssh, such as a devbox or home
server. When it's unavailable (e.g. sleeping, shut down), other machines can't sync.

The hub can coexist on a machine alongside the daemons.

## Connect over ssh

The hub may not know the hostname under which other machines can reach it (e.g. if you're
connecting to it over Tailscale), or you may have an ssh alias for it. `musubi hub --advertise
<name>` tells jj-musubi your preferred hostname.

The hub's `musubi` must be on the `PATH` of non-interactive shells. Check from another machine:

```sh
ssh devbox musubi --version
```

If that says `musubi: command not found`, put its directory on `PATH` in your shell's startup
file, before any line that returns early for non-interactive shells.

The first time it contacts a hub over ssh, jj-musubi will authorize an ssh key that can only
talk to the hub. It will use ssh to set up that key, so ssh may ask for your password once.
After that, the daemon uses this key and should never prompt.

To be very clear, jj-musubi is intended for use by just one person (and their agents). Anyone
who can talk to a hub can read and write every hive on it ([SECURITY.md](../../SECURITY.md)).
See [SSH configuration](../reference/configuration.md#ssh) for more details.

## Start the hub

On the hub machine, start the hub interactively:

```sh
musubi hub
```

The hub will keep running until you stop it. Leave this terminal open for now. Once you're
satisfied that you want to continue using jj-musubi, you can [manage it through a
service](#keep-the-hub-running).

When you first start a hub, it creates `~/.local/share/musubi/hub` by default (see [the hub's
directory](../reference/configuration.md#on-the-hubs-machine) for other systems) and prints
what to run elsewhere:

```text
Created a new hub in /home/you/.local/share/musubi/hub
To share a repository:               musubi create --hub devbox
To add another machine's copy of it: musubi join --hub devbox
To make a new copy of a hive:        musubi clone <name> [<dir>] --hub devbox
Other machines reach this hub over ssh: use the name they ssh to this machine by, if it isn't devbox.
On this machine, leave out --hub.
```

To choose a different data directory for the default hub, set
[`musubi.hub-dir`](../reference/configuration.md#this-machines) on the hub's machine before
starting the hub:

```sh
jj config set --user musubi.hub-dir '~/data/musubi-hub'
```

## Share a repo

In your repo on one machine, create a jj-musubi hive from it:

```sh
musubi create --hub devbox
```

The hive is named after the repo's `origin` remote (`app` for `github.com/you/app`), or its
directory if it has no remotes. If you'd prefer a different name, just provide that: `musubi
create work-app`.

When you add a repo to a hive, by default it does not contain undo history from before that
point. To share earlier undo history too, see [Bring the operation
history](#sharing-complete-operation-history).

`create` starts the daemon if it isn't running, and returns once the repo has synced.

## Add other machines

On each other machine, in its copy of the repo:

```sh
musubi join --hub devbox
```

The hub figures out which hive from your repo's history and remotes; you don't need to name it.

```text
Joined hive app (matched remote origin), 2 machines
```

A newer descendant of `main` can come from either copy. If the copies have observed different
rewrites of upstream history, `join` tries fetching the conflicted bookmarks once, with a
30-second limit per remote, and syncs the result. `create` does the same if its starting repo
has conflicted remote bookmarks. Neither
command changes your checkout files. If a remote is unavailable, joining still succeeds and
prints how to [resolve the remaining conflict][join-conflict].
Local bookmark differences merge as they do in jj; a fetch can leave those conflicted.

[join-conflict]: ../troubleshooting.md#remote-bookmarks-remain-conflicted-after-joining

If the repo you're trying to join from doesn't match a hive, or matches more than one, `join`
stops and says why. (See [Joining is refused](../troubleshooting.md#joining-is-refused).)

On a machine that doesn't yet have a copy of the repo, clone the hive. This creates a
repo, joins the hive and syncs, then checks out `trunk()` using this machine's jj config:

```sh
musubi clone app ~/src/app --hub devbox
```

A small amount of repo-local config is copied during a clone. For instance, a machine might not
have name or email settings in its jj config, which is common in disposable environments used by
agents.

## Your first sync

If you want to see what's going on, run:

```sh
musubi status
```

Look for `Daemon: running`, `serving this repository`, a recent `synced ... ago`, and `the hub
has all its work`. `musubi status` doesn't contact the hub, so it should return immediately even
if e.g. your laptop isn't on a network.

Let's say you're on a laptop. To see a sync happen, edit some files, then run `jj status` to
snapshot those edits. You can then either wait a moment or run `musubi sync` to be sure the send
part of a sync has completed.

On another machine, either wait a moment or run `musubi sync` to ensure that the receive side of
the sync has completed, then run `jj log`. The laptop's in-progress commit should appear as
`laptop/default@`, using the machine name from `musubi status`. You can inspect its contents
using `jj diff -r laptop/default@`. jj-musubi won't update your working copy, so nothing changes
until you [pick up the work](working-across-machines.md#pick-up-on-another-machine).

I almost never run `musubi sync` by hand. It's occasionally convenient for debugging, because it
will report holds and failures. For a hold or other warning, see
[Troubleshooting](../troubleshooting.md#start-with-this-copy).

## Keep the hub running

So you've decided to use jj-musubi for real. Stop the foreground hub, then install a service
that will start it now and at login:

```sh
musubi hub install
```

This installs a launchd agent on macOS, a systemd user unit on Linux, or an SMF service on
illumos, and that will restart the hub if it fails. (Windows has no `hub install`.) On illumos,
the service starts at boot, whether or not you're logged in (see [illumos](#illumos)).

To start the hub at boot and keep it running after logout, on macOS or Linux:

```sh
musubi hub install --at-boot
```

Run this as your normal user, without `sudo`. It will ask for administrator permission to
install and manage the service as you, using your home and state directory. On macOS this
installs a launchd daemon; on Linux, a systemd system unit.

Without `--at-boot`, macOS needs a logged-in user session. This is also the default on Linux,
but you can keep the login service running using `loginctl enable-linger` (N.B. that command
will affect *all* of your user services).

On macOS, the hub logs to `hub.log` in jj-musubi's state directory. On Linux, use `journalctl
--user -u musubi-hub` for a login service, or `sudo journalctl -u musubi-hub-$(id -u).service`
for a boot service. On illumos, see [illumos](#illumos).

`musubi hub uninstall` stops the hub and removes the service.

## Start the daemon at login

`create`, `join` and `clone` start the daemon. To start it at login (at boot on illumos) too:

```sh
musubi daemon install
```

This starts the daemon and installs a launchd agent on macOS, a systemd user unit on Linux, an SMF
service on illumos, or a Windows `Run` registry entry. On macOS and Linux, the [user-service
requirements](#keep-the-hub-running) apply.

### illumos

On illumos, `daemon install` and `hub install` each set up an SMF instance for you:
`svc:/site/musubi/daemon:<you>` and `svc:/site/musubi/hub:<you>`. `<you>` is your user name, or
`uid` and your numeric user ID (`uid1000`, say) if that name isn't a valid SMF instance name;
`install` prints the full name, and `svcs '*musubi*'` lists them. SMF starts each at boot,
whether or not you're logged in, runs it as you, and starts it again if it exits, so `hub
install` needs no `--at-boot` there.

musubi runs `svccfg` and `svcadm` through `pfexec` to set the service up, and to start and
stop it afterwards, so your account needs the Service Management rights profile (Primary
Administrator includes it). `profiles` lists yours. The profile lets an account change how any
service on the machine runs, including as root, so granting it amounts to granting root on
that machine. pfexec uses your account's own profiles: one granted to a role you `su` to
doesn't count. Without it, `create`, `join` and `clone` still start the daemon, but nothing
starts it after a reboot.

An administrator adds the profile with `usermod -P`, which replaces the account's profiles, so
name the ones it has already too, comma-separated. `grep '^<you>:' /etc/user_attr` shows them,
as `profiles=` (none if there's no such line). For an account with Basic Solaris User, say:

```sh
usermod -P 'Basic Solaris User,Service Management' <you>
```

SMF writes the daemon's output to `/var/svc/log/site-musubi-daemon:<you>.log` and the hub's to
`/var/svc/log/site-musubi-hub:<you>.log`, which `logadm` rotates. If one isn't running, or SMF
has put it in maintenance, see [Troubleshooting](../troubleshooting.md#illumos).

`musubi daemon stop` stops the daemon until a musubi command starts it again (`musubi daemon
start`, or one that needs the daemon) or the next boot.

## Use musubi in a dev container

Add the jj-musubi [Dev Container Feature](https://containers.dev/features) to your project's
`.devcontainer/devcontainer.json`. It installs a Linux release of `musubi` on Debian and Ubuntu
images for x86_64 or aarch64, and starts the daemon as your development user each time the
container starts. Make sure the container also has `jj` and `git`.

```json
{
    "features": {
        "ghcr.io/bos/jj-musubi/musubi:1": {}
    }
}
```

The Feature installs the latest jj-musubi release by default. Set the Feature's `version`
option to select a specific release. For Codespaces, use a release newer than 0.47.1 so OpenSSH
can use the private key generated on the workspace mount.

In GitHub Codespaces, add `"remoteEnv": {"MUSUBI_STATE_DIR": "/workspaces/.musubi"}` to the
same configuration before joining a hive. Codespaces keeps `/workspaces` across rebuilds, so
the daemon can keep its hub key and remember which repos it syncs. This path is outside the
project checkout. If you configure SSH aliases or trust your hub's host key in the container,
restore that SSH configuration and host key verification after a rebuild.

Create or rebuild the container, then [connect to your hub over ssh](#connect-over-ssh) from
inside the container. If Codespaces cloned your project with Git, run `jj git init --colocate`
in that checkout before you [join the hive](#add-other-machines).

## Optional clone defaults

Depending on how you like to work, it can be convenient to choose which jj and jj-musubi
settings future clones can inherit. Name and email are the defaults.

```sh
jj config set --repo musubi.clone-config '["user.name", "user.email", "aliases.l"]'
```

I recommend auto-configuring only portable settings. For instance, signing keys, tool paths and
watchers shouldn't be shared because they'll probably cause you headaches. See
[`musubi.clone-config`](../reference/configuration.md#each-repos) for override rules and
behaviour when a hive is recreated.

## Naming machines

When a repo is managed by musubi, jj shows each machine's working copy as a workspace named
after the machine, such as `laptop/default@` (`@` = "the working copy", `default` = "the default
workspace", `laptop/` = "on the machine named `laptop`").

The machine name defaults to jj's `operation.hostname`, usually its hostname, and these are
often horrendously long and unfriendly. To choose a friendlier or shorter name, pass `--machine`
to `create`, `join` or `clone`:

```sh
musubi join --machine work-laptop
```

If you somehow set up multiple machines with the same name (but why?), they'll be given unique
suffixes, such as `laptop-1a2b/default@` and `laptop-3c4d/default@`. This also takes care of
such odd situations as you deciding to name a normal jj workspace `laptop/default`.

## Sharing complete operation history

By default, creating or joining doesn't share undo history from before that time. (If you speak
the jargon, each machine's `jj op log`, as shared to other machines, starts from the time it
joined). This keeps snapshots and commits that are unlikely to be helpful from cluttering the
hive.

If you want to share the whole operation history, use `musubi create --full-history --hub
devbox`, or pass `--full-history` to `join`.
