# Troubleshooting

Start with `musubi list`, run in the repository. It shows whether the daemon is running,
whether the hub is reachable, and for each copy on this machine, when it last synced or the
error its last sync failed with. `musubi sync` syncs at once and prints any error itself.

For more, look at the daemon's log: `daemon.log` in musubi's state directory
(`~/.local/state/musubi` on Linux and macOS), or under systemd, `journalctl --user -u
musubi`. On the hub's machine, the hub logs to its terminal. To log more, see
[Logging](reference/configuration.md#logging).

## Reaching the hub

### "no hub given; pass --hub <host>, ..."

This machine has no default hub yet: it gets one the first time it creates, joins, or clones
a hive. Pass `--hub` with the name you ssh to the hub's machine by, as `musubi hub` printed.

### "`musubi` is not on the PATH of non-interactive shells on devbox"

ssh to the hub's machine worked, but the shell there couldn't find `musubi`. ssh runs it in a
non-interactive shell, which reads less of your shell's startup files than a login does. Put
`musubi`'s directory on the `PATH` in `~/.zshenv`, or near the top of `~/.bashrc`, before any
line that returns early for non-interactive shells. Check with:

```sh
ssh devbox musubi --version
```

Or give `musubi`'s absolute path in the line musubi added to `~/.ssh/authorized_keys` on the
hub's machine: `command="/opt/musubi/bin/musubi hub connect"`.

### "`musubi hub connect` on devbox failed: ..." or "ssh to devbox worked, but ..."

ssh reached the hub's machine, but no hub of this release answered there. "no hub has run on
this machine" means `musubi hub` has never run there without `--dir`; start it, or for a hub
run with `--dir`, add `--dir <dir>` to the `command=` in the line musubi added to
`~/.ssh/authorized_keys` there. Otherwise the message says what answered instead, such as
another release of musubi.

### "ssh to devbox failed: ..."

ssh itself failed; the rest of the message is what ssh said. Check that `ssh devbox` works
from this machine. The daemon runs ssh with your `~/.ssh/config`, but with musubi's own key,
and never prompts, so a host that needs a password or a hardware key each time can't be
reached by the daemon.

If ssh refuses musubi's key, its line may have gone from `~/.ssh/authorized_keys` on the
hub's machine. Add it again, from this machine:

```sh
echo "restrict,command=\"musubi hub connect\" $(cat ~/.local/state/musubi/hub_key.pub)" |
  ssh devbox 'cat >> ~/.ssh/authorized_keys'
```

### "the hub at devbox is out of reach", "no hub is serving ...", or "request timed out"

No hub answered. Check that `musubi hub` is running on the hub's machine, and start it if
not. The daemons reconnect by themselves. A sync that goes through the daemon waits about
half a minute for the hub, then says only `request timed out`.

If the hub runs with `--dir`, other machines can't find it: `musubi hub connect`, which they
run over ssh, finds the hub that `musubi hub` last served without `--dir`. Add `--dir <dir>`
to the `command=` in the line musubi added to `~/.ssh/authorized_keys` on the hub's machine.

### "hub: this hub has no hive ..."

The hub doesn't have the hive this copy belongs to: someone removed it with `musubi hub rm`,
or the hub lost its state, or this machine now reaches a different hub. `musubi list` shows
the hive as "(no longer on the hub)". Nothing is lost: see [Replace or move a
hub](guides/manage.md#replace-or-move-a-hub) to make the hive again from the machines'
copies.

### "incompatible peer: protocol ... but this is protocol ..."

This machine and the hub run different releases of musubi, which can't talk to each other
before 1.0. Install the same release on the hub's machine and every other machine. See
[Upgrade musubi](guides/manage.md#upgrade-musubi).

### "the running daemon is musubi ..., but this is ...; restart it with `musubi daemon restart`"

You installed a new musubi, but the daemon still runs the old one. Run
`musubi daemon restart`.

## Joining a hive

### Joining is refused

The hub decides which hive a copy belongs in. It refuses when it can't tell, and says why:

- **"this repository has no commits to share yet; commit something first"**: an empty
  repository matches nothing. Commit something, or clone the hive with `musubi clone`.
- **"no hive on this hub shares history with this repository; `musubi create` starts one"**:
  the hub has no hive for this repository. Start one with `musubi create`, or check that
  `--hub` names the hub you meant.
- **"hive app shares history with this repository, but not a remote; ..."**, or **"hives
  app, web share history ..."**: the copy has history in common with a hive, but none of its
  remotes' URLs match the hive's. A fork, with
  `origin` pointing at your own fork, looks like this; so does a copy whose remote is spelled
  with an ssh host alias. To join that hive anyway, run `musubi join --hive app`. To give a
  fork a hive of its own, run `musubi create`.
- **"this repository matches several hives: app, web; ..."**: more than one hive matches.
  Choose one with `musubi join --hive <name>`.
- **"this repository shares no history with hive app; ..."**, from `musubi join --hive app`:
  `--hive` joins only a hive the copy has some history in common with. Check the name, or
  start a hive of its own with `musubi create`.
- **"this hub has no hive named app"**: no hive's name starts with that. `musubi list` shows
  the hub's hives.
- **"this repository belongs in hive app (...); `musubi join` joins it, ..."**, from
  `musubi create`: the hub already has a hive for this repository. Run `musubi join` to
  join it, or `musubi create <name>` to start another hive anyway.

### "this repository is already part of hive app; `musubi leave` first to join another"

The repository is already in a hive. To move it to another hive or hub, run `musubi leave`,
then `musubi join` or `musubi create`.

### "musubi needs all of a repository's history, and this one is a shallow clone ..."

The repository is a shallow or a partial clone, which can't send other machines everything
they need. Make a full copy with `musubi clone <hive> <dir>`, if a hive has it, or with
`jj git clone` without `--depth`.

## Syncing

### "jj cannot merge this machine's operations with the hive's (...)"

jj 0.46 can't merge some combinations of concurrent operations, such as rebases on two
machines that form a loop. Rather than leave every `jj` command here failing, musubi doesn't
apply the hive's latest operations on this machine, so jj keeps working. The message lists
this machine's operations that the hive doesn't have yet, newest first. Revert the one that
conflicts with the hive's, usually the newest:

```sh
jj op revert <id>
```

musubi then catches up. [docs/internals/races.md](internals/races.md#known-jj-limitations)
describes the cases jj can't merge.

### "jj cannot merge this machine's concurrent operations: ... merge commit on the root commit"

Two concurrent operations on this machine can't be merged, because of a bug in jj 0.46, and
every `jj` command fails. The message says how to find and revert the operation that made
the merge commit: run `jj --at-op <head> op log -n1` for each operation id in
`.jj/repo/op_heads/heads`, then `jj --at-op <head> op revert @` at the head that made it.

### Syncing paused after `jj op abandon`

```text
the operation history the hub accepted is no longer reachable from this repository's op
heads (was `jj op abandon` run?); musubi does not replicate op abandon yet, so replication
is paused for this repository
```

`jj op abandon` removed operations that the hub, and so other machines, already have. musubi
can't yet pass that on, and won't bring them back, so it stops syncing this repository.
Abandoning only the operations from before this machine first joined is fine.

A similar message, "operation ... realizes canonical operation ... but no longer has its
parents (was `jj op abandon` run?)", has the same cause and the same remedy.

musubi can't yet sync this copy again. The other machines keep the operations you abandoned.
To carry on here, run `musubi leave`, make a new copy with `musubi clone`, and bring across
any work this copy made since its last sync.

If `musubi join` or `musubi create` says this, the operations were abandoned while the copy
was out of its hive, and it isn't in one: skip `musubi leave`. A `musubi create` that failed
this way leaves an empty hive on the hub; remove it with `musubi hub rm`.

### "unknown field ... (written by a newer jj?)"

A `jj` newer than 0.46.0, the version musubi supports, wrote an operation with fields
musubi doesn't know. musubi won't drop them by syncing it. Use jj 0.46.0 with this release of
musubi, and upgrade the two together.

### Every machine's sync of a hive fails on the same object

If the hub's machine lost power, a file the hub wrote just before may be cut short, and
every sync that needs it fails. Make the hive again: stop the hub, delete the hive's `heads`
file, in its directory under the hub's (`musubi-hub/<hive id>/heads`), and start the hub
again. It finds the store corrupt, sets it aside under `removed/`, and makes the hive again,
empty, for the machines to fill.

### "the first sync failed: ..."

`create`, `join`, or `clone` set up the repository, but its first sync failed for the reason
given. The daemon keeps trying. Fix the cause, and `musubi list` shows when it succeeds.

### "Could not start the daemon (...); syncing once instead."

The command synced the repository itself, but there's no daemon to keep it in sync. The
message gives the reason. Start the daemon with `musubi daemon start` once it's fixed.

## The daemon

### The daemon isn't running after a reboot

`create`, `join`, and `clone` start the daemon, but nothing starts it again after a reboot
until you run `musubi daemon install`. On Linux, a daemon installed this way stops when you
log out, unless you run `loginctl enable-linger`.

### "the daemon exited (...) before it was ready" or "did not start listening"

The daemon failed as it started. The message includes the end of its log, or names the log.

### "... is not a private directory of this user's ..."

musubi only uses a socket in a directory that belongs to you and no one else can write to,
so that no one else can put a socket of their own in its place. Remove the directory, and
musubi makes it again, or choose another place for the daemon's socket with `MUSUBI_SOCKET`.

### "... would be ... bytes longer than this system allows" or "... is ... bytes longer ..."

Unix socket paths are limited to about 100 bytes. For the daemon, choose a shorter path with
`MUSUBI_SOCKET` or `socket` under `[daemon]` in `config.toml`. For a hub, serve it from a
directory with a shorter path.

### "a hub is already running, serving ...; use --dir to run another"

One hub per user runs without `--dir`. Use that one, or stop it first.

## Surprises

### Your working copy is stale

Another machine changed the commit your working copy is on. Run
`jj workspace update-stale`. See [When another machine rewrites your working
copy](guides/working-across-machines.md#when-another-machine-rewrites-your-working-copy).

### A remote or setting changed back

When two machines change the same remote or shared setting before either has synced, the
later change wins on every machine, by each machine's clock. The daemon on the machine whose
value was replaced logs the old and new values. A machine whose clock is wrong can win when
it shouldn't. Set the value again; the latest write wins.

### `jj log` shows `main*` after a sync

In a colocated repository, jj exports bookmarks to git only when a command changes
something, so after a `jj` command that merged other machines' work, git's branches can lag
jj's bookmarks. Any command that changes something exports them, as does `jj git export`.

### An annotated tag is lightweight on other machines

musubi moves the commits a tag points to, not git's tag objects, so an annotated tag fetched
on one machine is a lightweight tag at the same commit on the others: `git describe` without
`--tags` passes it over, and `git tag -v` has nothing to verify. Fetch the tag on a machine
that needs it.
