# Troubleshooting

Start with `musubi status` in the repository. It shows whether the daemon is running and
serving the repository, when it last synced or the error its last sync failed with, and
whether the hub has this machine's latest work. `musubi list` shows whether each hub is
reachable, and every copy on this machine. `musubi sync` syncs at once and prints any error
itself. `musubi top` shows every machine's syncing, as the hub hears of it.

For more, read the daemon's log: `daemon.log` in musubi's state directory
(`~/.local/state/musubi` on Linux and macOS), or under systemd, `journalctl --user -u
musubi`. The hub logs to its terminal. To log more, see
[Logging](reference/configuration.md#logging).

Messages below use `devbox` for the hub's machine, `app` for a hive, and `laptop` for a
machine.

## Reaching the hub

### "no hub given; pass --hub <host>, ..."

This machine has no default hub yet; it saves one the first time it creates, joins, or clones
a hive. Pass `--hub` with the name you ssh to the hub's machine by, as `musubi hub` printed,
or set a default with `jj config set --user musubi.hub <hub>`.

### "`musubi` is not on the PATH of non-interactive shells on devbox"

ssh reached the hub's machine, but the shell there couldn't find `musubi`. ssh runs commands
in a non-interactive shell, which reads less of your startup files than a login does. Put
`musubi`'s directory on the `PATH` in `~/.zshenv`, or near the top of `~/.bashrc`, before any
line that returns early for non-interactive shells. Check with:

```sh
ssh devbox musubi --version
```

Or give `musubi`'s absolute path in the line musubi added to `~/.ssh/authorized_keys` on the
hub's machine: `command="/opt/musubi/bin/musubi hub connect"`.

### "`musubi hub connect` on devbox failed: ..." or "ssh to devbox worked, but ..."

ssh reached the hub's machine, but no hub of this release answered there. If the message says
"no hub has run on this machine", `musubi hub` has never run there without `--dir`: start it,
or for a hub run with `--dir`, add `--dir <dir>` to the `command=` in the line musubi added
to `~/.ssh/authorized_keys` there. Otherwise the message says what answered instead, such as
another release of musubi.

### "ssh to devbox failed: ..."

ssh itself failed; the rest of the message is what ssh said. Check that `ssh devbox` works
from this machine. The daemon runs ssh with your `~/.ssh/config` but with musubi's own key,
and never prompts, so it can't reach a host that needs a password or a hardware key each time.

If ssh refuses musubi's key, its line may have gone from `~/.ssh/authorized_keys` on the
hub's machine. Add it again, from this machine:

```sh
echo "restrict,command=\"musubi hub connect\" $(cat ~/.local/state/musubi/hub_key.pub)" |
  ssh devbox 'cat >> ~/.ssh/authorized_keys'
```

### "ssh to devbox did not connect" or "ssh to devbox did not connect: ..."

musubi gave up waiting for the hub to answer: after half a minute, or a minute while joining.
ssh may be hanging, on a `ProxyCommand` say, or on a shell startup file on the hub's machine that
waits for input; the hub may be stuck; or, if the message goes on "cannot run ssh: ...", ssh
can't run at all. Check that `ssh devbox true` finishes at once from this machine, and see what
the hub logs: in its terminal, or under systemd in `journalctl --user -u musubi-hub`.

### "the hub on devbox ended the connection before greeting"

ssh reached the hub's machine, but the hub never answered: it closed the connection, as it does
when it stops, or didn't answer within half a minute, as when it's stuck. The daemon tries again
by itself. If this keeps happening, see what the hub logs, as above, and restart it if it's
stuck.

### "the hub at devbox is out of reach", "no hub is serving ...", or "request timed out"

No hub answered. Check that `musubi hub` is running on the hub's machine, and start it if not;
`musubi sync` and `musubi list` say why the hub is out of reach, and `musubi status` shows why
the last sync couldn't reach it. Where the message gives a reason after the colon, such as "ssh
to devbox failed: ...", that reason's own entry above says more.
Daemons reconnect by themselves: within a few seconds to a hub on the same machine, and within
about a minute over ssh, which waits longer between tries after each failure.

If the hub runs with `--dir`, other machines can't find it: the `musubi hub connect` they run
over ssh finds the hub that `musubi hub` last served without `--dir`. Add `--dir <dir>` to the
`command=` in the line musubi added to `~/.ssh/authorized_keys` on the hub's machine.

### "the hub has no record of this repository's hive ..."

The hub has lost this copy's hive, as when its directory was deleted, or this machine now
reaches a different hub. `musubi list` shows the hive as "(no longer on the hub)". Nothing is
lost: if this is the right hub, run `musubi join` in the copy to make the hive again from it,
and the other machines fill it. See
[Replace or move a hub](guides/manage.md#replace-or-move-a-hub).

### "this repository's hive was removed from the hub, ..."

Someone removed the hive with `musubi hub remove`, and this copy has left it, keeping
everything it has. To share the repository again, start a new hive with `musubi create`.

### "incompatible peer: protocol ... but this is protocol ..."

This machine and the hub run different releases of musubi, which can't talk to each other
before 1.0. Install the same release everywhere. See
[Upgrade musubi](guides/manage.md#upgrade-musubi).

### "the running daemon is musubi ..., but this is ...; restart it with `musubi daemon restart`"

You installed a new musubi, but the daemon still runs the old one. Run
`musubi daemon restart`.

## Joining a hive

### Joining is refused

The hub decides which hive a copy belongs in: one that shares some of its history and one of
its remotes' URLs. It refuses when it can't tell, and says why:

- **"this repository has no commits to share yet; commit something first"**: an empty
  repository matches nothing. Commit something, or clone the hive with `musubi clone`.
- **"no hive on this hub shares history with this repository; `musubi create` starts one"**:
  start a hive with `musubi create`, or check that `--hub` names the hub you meant.
- **"hive app shares history with this repository, but not a remote; ..."**, or **"hives
  app, web share history ..."**: none of the copy's remotes' URLs match the hive's. A fork
  whose `origin` is your own fork looks like this, and so does a remote spelled with an ssh
  host alias. To join anyway, run `musubi join --hive app`; to give a fork its own hive, run
  `musubi create`.
- **"this repository matches several hives: app, web; ..."**: choose one with
  `musubi join --hive <name>`.
- **"this repository shares no history with hive app; ..."**, from `musubi join --hive app`:
  `--hive` joins only a hive that shares some history with the copy. Check the name, or start
  a hive of its own with `musubi create`.
- **"this hub has no hive named app"**: no hive's name starts with that (for
  `musubi hub remove`, no hive has that whole name or id). `musubi list` shows the hub's
  hives.
- **"this repository belongs in hive app (...); `musubi join` joins it, ..."**, from
  `musubi create`: the hub already has a hive for this repository. Run `musubi join`, or
  `musubi create <name>` to start another hive anyway.

### "this repository is already part of hive app; `musubi leave` first to join another"

`musubi create` or `musubi join --hive` would put the repository in a second hive. Run
`musubi leave` first. To move it, hive and all, to another hub, run `musubi join --hub <hub>`
instead.

### "the hub lacks this repository's hive, but it belongs in hive app (...): ..."

`musubi join` would make this copy's hive again, but the hub has another hive the copy belongs
in, made meanwhile with `musubi create`, say. Run `musubi leave --force`, then `musubi join`,
to join that one. If the message says the copy belongs in several, run
`musubi join --hive <name>` after leaving.

### "musubi needs all of a repository's history, and this one is a shallow clone ..."

A shallow or partial clone can't send other machines everything they need. Make a full copy
with `musubi clone <hive> <dir>`, if a hive has it, or with `jj git clone` without `--depth`.

## Leaving a hive or forgetting a machine

### "couldn't tell hive app that this repository leaves (...), so this repository is still part of hive app; ..."

`musubi leave` couldn't reach the hub to send this copy's last work and its leaving, so the
repository is still part of the hive, and the daemon syncs it again. That sync takes the
forget `musubi leave` recorded to the hive, so the other machines stop showing this copy until
it's next used. Run `musubi leave` again
once the hub can be reached, or `musubi leave --force` to leave without telling the hive: the
other machines then go on showing this copy until one of them runs `musubi forget`.

If the parentheses say "work done in this repository while it left kept it in the hive", a
`jj` command ran in the repository during each of `musubi leave`'s three tries. Stop whatever
is running `jj` there, and run `musubi leave` again.

### "couldn't record what changed in the working copy (...), so this repository is still part of hive app; ..."

`musubi leave` first snapshots the working copy, as any `jj` command would, so that the
repository leaves with all of its work, and jj couldn't; the parentheses say why. Most often
the working copy is stale, as after another machine rewrote its commit: run
`jj workspace update-stale`, then `musubi leave` again.

### "Warning: Couldn't put back this repository's working copies (...)."

`musubi leave` takes this copy's working copies out of the view while it tells the hive, then
puts them back, and couldn't. jj then says a workspace has no working-copy commit. `jj op log`
lists the operation `musubi: leave`; `jj op restore` to the operation before it brings them
back.

### "Warning: Couldn't give this repository's working copies new commits (...)."

The repository has left its hive, but a working copy whose commit the hive abandoned didn't
get a new one. Run `jj new @-` in that workspace.

### "no machine laptop shows here in hive app; `jj workspace list` names those that do"

No machine with working copies here has that name: it was forgotten already, it left, or it
shows by another name, such as `laptop-1a2b` when another machine, even one long gone, shares
its name. `musubi forget` takes the name in its working copies' names (`laptop` for
`laptop/default@`), or the name `musubi list` gives it if no other machine has that name.

### "laptop is this machine; `musubi leave` takes this repository out of hive app"

`musubi forget` forgets other machines' copies. To take this one out, run `musubi leave`.

### "musubi.forget-after is neither `never` nor a duration such as `6h`; taking it for never"

The daemon logs this when it can't read the copy's `musubi.forget-after`, and then never has
the hive forget the copy. Set it to `never` or a duration
(see [Settings](reference/configuration.md#settings)):
`jj config set --repo musubi.forget-after 6h`.

### "musubi.forget-after in your user config is neither `never` nor a duration such as `6h`; fix it and run this again"

`musubi join`, `create`, or `clone` found a `musubi.forget-after` it can't read, in the config
the message names, and joined nothing. Fix it there, or unset it to have the command choose
(`jj config unset --user musubi.forget-after`, or `--repo` for the repo config), then run the
command again.

## Syncing

### "jj cannot merge this machine's operations with the hive's (...)"

jj 0.46 can't merge some combinations of concurrent operations, such as rebases on two
machines that form a loop. So that every `jj` command here doesn't fail, musubi holds back the
hive's latest operations on this machine. The message names the operation to revert, one of
this machine's that the hive doesn't have yet. Revert it, and musubi catches up:

```sh
jj op revert <id>
```

Work done since stays, rebased off what the reverted operation rewrote. A change rewritten
again since, say described, is left divergent, as `jj op revert` leaves it without musubi:
`jj abandon` the copy you don't want. If another of this machine's operations conflicts
too, the next sync names it. Where musubi can't find one to name, the message lists this
machine's operations that the hive doesn't have yet, newest first; revert the one that
conflicts with the hive's.

[Known jj limitations](internals/races.md#known-jj-limitations) describes the cases jj can't
merge.

### "jj cannot merge this machine's concurrent operations: ... merge commit on the root commit"

A bug in jj 0.46 keeps two concurrent operations on this machine from merging, and every `jj`
command fails. For each operation id in `.jj/repo/op_heads/heads`, run
`jj --at-op <head> op log -n1` to find the one that made the merge commit, then run
`jj --at-op <head> op revert @` at that head.

### Syncing paused after `jj op abandon`

```text
the operation history the hub accepted is no longer reachable from this repository's op
heads (was `jj op abandon` run?); musubi does not replicate op abandon yet, so replication
is paused for this repository
```

musubi may print instead: "operation ... realizes canonical operation ... but no longer has
its parents (was `jj op abandon` run?) ...".

`jj op abandon` removed operations that the hub, and so other machines, already have. musubi
can't pass that on yet, and won't bring them back, so it stops syncing this copy, and can't
sync it again. (Abandoning only operations from before this machine first joined is fine.)
The other machines keep the operations you abandoned. To carry on here, run
`musubi leave --force`, make a new copy with `musubi clone`, and bring across any work this
copy made since its last sync.

If `musubi join` or `musubi create` says this, the operations were abandoned while the copy
was out of its hive: skip `musubi leave --force`. A `musubi create` that failed this way
leaves an empty hive on the hub; remove it with `musubi hub remove`.

### "unknown field ... (written by a newer jj?)"

A `jj` newer than 0.46.0, the version musubi supports, wrote an operation with fields musubi
doesn't know, and musubi won't drop them by syncing it. Use jj 0.46.0 with this release of
musubi, and upgrade the two together.

### Every machine's sync of a hive fails on the same object

If the hub's machine lost power, a file the hub wrote just before may be cut short, and every
sync that needs it fails. Stop the hub, delete the hive's `heads` file
(`musubi-hub/<hive id>/heads`), and start the hub again. It finds the store corrupt, sets it
aside under `removed/`, and makes the hive again, empty, for the machines to fill.

### "the first sync failed: ..."

`create`, `join`, or `clone` set up the repository, but its first sync failed for the reason
given. The daemon keeps trying: fix the cause, and `musubi status` shows when it succeeds.

### "Warning: Could not start the daemon (...); syncing once instead."

The command synced the repository itself, but no daemon keeps it in sync. Fix the reason
given, then run `musubi daemon start`.

### "Warning: The daemon isn't running, so this synced in its own process, ..."

`musubi sync` synced the repository itself, since the daemon that serves it isn't running, as
after `musubi daemon stop`; nothing syncs it otherwise. Run `musubi daemon start`.

## What `musubi status` reports

### "Warning: Syncing fails: ..."

The repository's last sync failed, for the reason quoted: find that message on this page. If
the daemon serves the repository, it keeps trying, and its log, which the hint names, says
more. Otherwise `musubi sync` tries again.

### "Warning: The daemon isn't running, so this repository syncs only when you run `musubi sync`."

Start it with `musubi daemon start`, and to have it start at login from now on, run `musubi
daemon install`. Until then, "the hub lacks its latest work" means just that: other machines
see this machine's work once you run `musubi sync`.

### "Warning: The daemon doesn't serve this repository."

The daemon runs, but doesn't know of this repository, as when musubi's state directory was
deleted or `MUSUBI_STATE_DIR` changed. `musubi join` in the repository has it serve the
repository again.

## What `musubi top` reports

### "... not heard from in 6m: offline, or its daemon isn't running"

A machine's daemon reports to the hub after every sync, at least every half minute, and the
hub has heard nothing for over two minutes. The machine is asleep or off the network, its
daemon has stopped, or it can't reach the hub: `musubi status` there says which. It catches up
when it reconnects. A machine in the middle of a long first sync shows like this too, since it
reports only once a sync ends, and so, for a day, does one that left the hive or whose copy
was deleted.

### "... 3 heads behind for 2m"

The machine reports to the hub, but hasn't caught up with what the hub accepted over a minute
ago, though it syncs as soon as it hears of a new head. Its daemon's log (see the top of this
page) says why.

### "... sync failing: ..."

The machine's last sync failed, for the reason quoted. Find that message on this page.

### "... the hub failed a request 5m ago: ..."

In the last ten minutes, the hub couldn't answer a request for the hive, for the reason
quoted; the hub's log says more. The machine that asked retries, and if it keeps failing, it
shows as failing too.

### "... the hub had trouble 5m ago: its store was damaged, so the hub made it again: ..."

The hub found the hive's store corrupt, as after a power cut, and made it again, empty. The
machines fill it as they sync, and nothing is lost.

### "not heard from since the hub started" or "not heard from in a day: it may have left the hive"

The hive shows a working copy of this machine, but the hub hasn't heard from its daemon since
the hub started, or in over a day. This isn't a problem in itself: a machine that left the
hive, or whose copy was deleted, still shows its working copy. A machine still in the hive is
heard from once it next syncs, within half a minute.

### "This machine's daemon isn't running; `musubi daemon start` starts it."

Nothing keeps this machine's copies in sync. Start the daemon, and to have it start at login
from now on, run `musubi daemon install`.

## The daemon

### The daemon isn't running after a reboot

`create`, `join`, and `clone` start the daemon, but nothing starts it after a reboot until you
run `musubi daemon install`. On Linux, a daemon installed this way stops when you log out,
unless you run `loginctl enable-linger`.

### "the daemon exited (...) before it was ready" or "did not start listening"

The daemon failed as it started. The message includes the end of its log, or names the log.

### "... is not a private directory of this user's ..."

musubi uses a socket only in a directory that belongs to you and that no one else can write
to, so that no one else can put a socket of their own in its place. Remove the directory, and
musubi makes it again, or choose another place for the daemon's socket with `MUSUBI_SOCKET`.

### "... would be ... bytes longer than this system allows" or "... is ... bytes longer ..."

Unix socket paths are limited to about 100 bytes. For the daemon, choose a shorter path with
`MUSUBI_SOCKET` or `musubi.daemon.socket` in jj's config. For a hub, serve it from a directory
with a shorter path.

### "a hub is already running, serving ...; use --dir to run another"

Only one hub per user runs without `--dir`. Use that one, or stop it first.

## Surprises

### Your working copy is stale

Another machine changed the commit your working copy is on. Run `jj workspace update-stale`.
See [When another machine rewrites your working
copy](guides/working-across-machines.md#when-another-machine-rewrites-your-working-copy).

### A remote or setting changed back

Two machines changed the same remote or shared setting before either synced, and the later
write won everywhere, by each machine's clock. The daemon on the machine whose value was
replaced logs the old and new values. Set the value again. See [When machines
disagree](guides/working-across-machines.md#when-machines-disagree).

### `jj log` shows `main*` after a sync

In a colocated repository, jj exports bookmarks to git only when a command changes something,
so after a `jj` command that merged other machines' work, git's branches can lag jj's
bookmarks. The next command that changes something exports them, as does `jj git export`.

### An annotated tag is lightweight on other machines

musubi moves the commits a tag points to, not git's tag objects, so an annotated tag fetched
on one machine is a lightweight tag at the same commit on the others: `git describe` without
`--tags` passes over it, and `git tag -v` has nothing to verify. Fetch the tag on a machine
that needs it.
