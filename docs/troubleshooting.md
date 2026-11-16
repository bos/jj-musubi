# Troubleshooting

Diagnose sync problems and recover from the messages jj-musubi prints.

## Find a problem

- [Start with this copy](#start-with-this-copy)
- [Hub connections and SSH](#reaching-the-hub)
- [Hub startup and services](#hub-startup-and-services)
- [Joining and cloning](#joining-a-hive)
- [Copies, moves and duplicates](#copies-moves-and-duplicates)
- [Leaving and leases](#leaving-a-hive-or-forgetting-a-machine)
- [Upgrading](#upgrading)
- [Syncing and history rescue](#syncing)
- [Snapshot holds and cleanup](#sending-held-by-the-snapshot-publication-budget)
- [Status warnings](#what-musubi-status-reports) and [hub reports](#what-musubi-top-reports)
- [The daemon](#the-daemon)

## Start with this copy

In the affected repository, run:

```sh
musubi status
```

The report reads local state without contacting the hub and exits 0 even with a problem.
It can be stale if the daemon has stopped. “The hub has all its work” covers only edits jj
has snapshotted.

| What you find | What to do |
| --- | --- |
| Sending held by the snapshot budget | Follow [accidental-file recovery](#accidentally-added-files-and-sending-stopped). Receiving continues. |
| Daemon not running or not serving this copy | Follow [status warnings](#what-musubi-status-reports). |
| A sync error | Find the message below, fix its cause, then retry with `musubi sync`. |
| Local work sent, but not received elsewhere | Run `musubi status` on the receiving machine; `musubi top` shows all machines' reports. |

`musubi sync` doesn't snapshot edits. Exclude unwanted files before running jj to record them.
To stop background traffic, [pause the daemon](guides/manage.md#pause-syncing-or-leave);
`musubi leave` attempts a final sync.

`musubi list` checks hub reachability. `status` and `top --once` exit successfully even with
problems; `top` sends no unattended alerts.

Read the daemon log on the affected machine and the hub log on the hub's machine.
[Logging](reference/configuration.md#logging) lists paths for foreground, login and boot services.
Below, `devbox` is the hub's machine, `app` a hive (copies of one project), and `laptop` a
working machine.

## Reaching the hub

### "no hub given; pass --hub <host>, ..."

Pass `--hub` with the hub's ssh name, as printed by `musubi hub`, or run `musubi hub` here to
make this machine the hub. Creating, joining or cloning a hive, or running a hub, saves this
machine's first default. `jj config set --user musubi.hub <hub>` also sets a default.

### "`musubi` is not on the PATH of non-interactive shells on devbox"

ssh's non-interactive shell couldn't find `musubi`. Add its directory to `PATH` in
`~/.zshenv`, or near the top of `~/.bashrc`, before any early return for non-interactive
shells. Check from this machine:

```sh
ssh devbox musubi --version
```

If you cannot change that `PATH`, use the
[SSH command-path fallback](reference/configuration.md#ssh).

### "`musubi hub connect` on devbox failed: ..." or "ssh to devbox worked, but ..."

ssh worked, but no hub of this release answered. For "no hub has run on this machine", start
`musubi hub` there, or, if one already serves with `--dir`, add `--dir <dir>` to its `command=`
entry in `~/.ssh/authorized_keys`. Otherwise the message identifies what answered, such as
another release.

### "ssh to devbox failed: ..."

ssh itself failed; the rest of the message is what ssh said. Check that `ssh devbox` works
from this machine. The daemon runs ssh with your `~/.ssh/config` but with jj-musubi's own key,
and never prompts, so it can't reach a host that needs a password or a hardware key each time.

If ssh refuses jj-musubi's key, its line may have gone from `~/.ssh/authorized_keys` on the
hub's machine. Add it again, from this machine:

```sh
echo "restrict,command=\"musubi hub connect\" $(cat ~/.local/state/musubi/hub_key.pub)" |
  ssh devbox 'cat >> ~/.ssh/authorized_keys'
```

### "ssh to devbox did not connect" or "ssh to devbox did not connect: ..."

The hub didn't answer within half a minute, or a minute while joining. Check that
`ssh devbox true` finishes promptly: a `ProxyCommand` or shell startup file may be waiting
for input. "cannot run ssh: ..." means ssh could not start. If ssh works, check the hub's log
and restart a stuck hub; see [log locations](#start-with-this-copy).

### "the hub on devbox ended the connection before greeting"

The hub closed the connection or didn't answer within half a minute. The daemon retries.
If this persists, check the hub's log and restart it if stuck; see
[log locations](#start-with-this-copy).

### "the hub at devbox is out of reach", "no hub is serving ...", or "request timed out"

Check that `musubi hub` is running. `musubi sync` and `musubi list` report connection failures;
`musubi status` shows the last sync's error. A reason after the colon has its own entry above.
If the hub runs but its machine is idle, check its log and restart it if stuck.

Connecting times out after half a minute. Replies time out after two minutes; a large history
can take longer, so requests retry for about ten minutes before failing. Daemons reconnect
within seconds locally or about a minute over ssh, backing off after failures. Detecting wake
ends old ssh connections and clears that delay.

A slow transfer resumes where each attempt left off. It needs about 70 kbit/s spare bandwidth
(a megabyte in two minutes); below that, large syncs can't finish. `musubi sync` in a terminal
shows progress.

With `--dir`, add `--dir <dir>` to the hub's `command=` entry in `~/.ssh/authorized_keys`:
ssh otherwise reaches the hub last served without `--dir`.

### "ssh-keygen could not derive the missing public key"

jj-musubi keeps an existing private key and recreates its public-key file if missing or empty.
If this fails, check the `ssh-keygen` error and the private key's permissions or passphrase.
For a passphrase-protected key, restore `hub_key.pub` and retry. Both key files are in the
[state directory](reference/configuration.md#files-and-directories).

### "could not save musubi's public SSH key"

If `hub_key.pub` is a directory, remove that obstruction; otherwise fix the reported file or
permission error, then retry. A new key becomes active only once both files are ready.
Handle private-key save errors the same way.
## Hub startup and services

### "a hub is already running, serving ...; stop it, then run this again"

`musubi hub install` found a manually started hub. Stop it and retry installation. "a hub is
already serving ..." is the same refusal with `--dir`. A hub started by an earlier
`musubi hub install` keeps running.

### "the hub didn't start; see ..."

`musubi hub install` handed the hub to launchd or systemd, but it didn't answer within ten
seconds. Its log, which the message names, says why. The service manager tries again after a
failure; `musubi hub uninstall` stops it trying.

### The installed hub stops at logout or doesn't start after reboot

Run `musubi hub install --at-boot` on the hub's machine to start it without a login and keep
it running after logout. Keep your existing `--dir` if you use one. This replaces its login
service, on macOS and Linux. Run it without
`sudo`; it asks for administrator permission. Keep `--at-boot` when reinstalling, or reinstall
without it to switch back to login startup. The executable and hub data must be accessible
before login; boot startup doesn't wake a sleeping machine.

### "a boot hub service is already installed for this user; ..."

A hub installed with another state directory already owns this user's boot service. In the
shell environment used for that installation, run `musubi hub uninstall` first. Restore its
`MUSUBI_STATE_DIR` or `XDG_STATE_HOME` if you changed one, then uninstall as the same user.
This refusal leaves that hub running.

### "sudo refused permission to manage the hub's boot service"

The login or boot service already installed is unchanged. Retry `musubi hub install --at-boot`
or `musubi hub uninstall` as the same user, after obtaining sudo permission for that account.

### "run `musubi hub install --at-boot` without sudo; musubi requests it when needed"

Run the command in your normal shell without a `sudo` prefix, so the hub uses your home and
state directory. The command asks for administrator permission when installing the service.

### "a hub is already running, serving ...; use --dir to run another"

Only one hub per user runs without `--dir`. Use that one, or stop it first.

## Joining a hive

### "destination ... is not empty; choose a new or empty directory"

`musubi clone` requires a new or empty directory. Choose one with `musubi clone <hive> <dir>`,
or run `musubi join` in an existing repo. Without `<dir>`, clone uses the last part of
the hive name in the current directory; run elsewhere if that path exists.

### "can't name a directory after hive ..."

The hive's name ends in nothing that can name a directory, such as `..`, so give one, as in
`musubi clone <hive> <dir>`.

### Joining is refused

Join matches the copy's history and remote URLs to a hive. Find its refusal below:

- **"this repository has no commits to share yet; commit something first"**: an empty
  repo matches nothing. Commit something, or clone the hive with `musubi clone`.
- **"no hive on this hub shares history with this repository; `musubi create` starts one"**:
  start a hive with `musubi create`, or check that `--hub` names the hub you meant. If the
  hive's other copies name objects with another hash than this one
  (`git rev-parse --show-object-format` says which), make a copy with `musubi clone` instead.
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
  `musubi create`: the hub already has a hive for this repo. Run `musubi join`, or
  `musubi create <name>` to start another hive anyway.

### "this repository is already part of hive app; `musubi leave` first to join another"

`musubi create` or `musubi join --hive` would put the repo in a second hive. Run
`musubi leave` first. To move it, hive and all, to another hub, run `musubi join --hub <hub>`
instead.

### "the hub lacks this repository's hive, but it belongs in hive app (...): ..."

This copy's old hive is missing, but its history matches another hive on the hub. Its old
name belongs elsewhere or is unknown. Run `musubi leave --force`, then `musubi join` to join
the matching hive. If several match, use `musubi join --hive <name>` after leaving.

### "this repository's machine is already named laptop"

A copy's machine name is fixed when it first joins. Omit `--machine` or use its existing name.
For another name, make a copy with `musubi clone <hive> <dir> --machine <name>`.

If `musubi status` says the repo is not in a hive, an earlier release may have named it
during a refused join. Delete `.jj/repo/musubi/machine` and retry.

### "musubi needs all of a repository's history, and this one is a shallow clone ..."

A shallow or partial clone can't send other machines everything they need. Make a full copy
with `musubi clone <hive> <dir>`, if a hive has it, or with `jj git clone` without `--depth`.

### "this repository's git names objects with SHA-256, but hive app's with SHA-1, ..."

The repos use different object hashes and cannot share commit ids. Run
`musubi clone app <dir>` to use the hive's hash. To carry over work, run
`jj diff --git -r <rev>` here, `git apply` in the new copy, then `jj describe` there.
Copy binary files manually; the patch cannot carry them.

### "the hub has no record of this repository's hive ..."

The hub lost the hive, or this machine now reaches a different hub. `musubi list` shows
"(no longer on the hub)". If this is the intended hub, run `musubi join` in the copy to recreate
the hive; other machines fill it. Their repos retain the work. See
[Replace or move a hub](guides/manage.md#replace-or-move-a-hub).

### "this repository's hive was removed from the hub, ..."

Someone removed the hive with `musubi hub remove`, and this copy has left it, keeping
everything it has. To share the repo again, start a new hive with `musubi create`.

### "hub: this hive is being removed from the hub"

`musubi hub remove` is finishing the hive's pending work. No action is needed: this copy leaves
on its next sync, keeping everything it has. If removal fails, syncing continues as before.

### "this repository's hive, app, was removed from its hub; ..."

After a hive is removed, plain `musubi join` won't choose a matching hive. Use
`musubi join --hive <name>`, start one with `musubi create`, or run `musubi leave` then
`musubi join` to match as a new repo.

### "remote names ... have different fetch or push destinations than hive ... recorded"

An existing copy may say "remote destinations disagree with this hive's recorded names".
Remote names have fixed fetch and push destinations in a hive. Join checks effective URLs,
including Git aliases; `--hive` cannot bypass this. Clone checks global remotes and conditional
includes for the destination before making directories. Equivalent HTTPS and SSH URLs agree.

Rename a different destination with `jj git remote rename origin fork`, using an unused name,
then retry `musubi join`. Renaming does not release an earlier binding. A copy may omit a
remote entirely.

### "hive ... has inconsistent recorded remotes"

The hive recorded conflicting remote destinations, for example from a buggy peer. Joining
and cloning refuse without changing config or creating a destination. From a copy with
consistent remotes, run `musubi leave --force`, then `musubi create <new-name>` to start a hive.
Check other copies' remotes before leaving the old hive and joining the new one. Their
repos and work remain in place.

### "musubi.clone-config cannot include musubi.forget-after"

The copy's expiry policy is chosen locally when it joins or clones. Remove
`musubi.forget-after`, or the whole `musubi` table, from `musubi.clone-config` before
creating the hive. Select individual portable keys instead; see
[Configure each machine](guides/working-across-machines.md#configure-each-machine).

### "the hub returned a different hive during clone; run `musubi clone` again"

Clone refused the hub's answer before creating its destination. Retry `musubi clone`. If it
repeats, make sure the hub and this machine run the same build.

## Copies, moves and duplicates

See [Move, copy or restore a repo](guides/manage.md#move-copy-or-restore-a-repo).

### "this repository duplicates a copy in hive app, ..."

A filesystem copy carries the original's identity, so jj-musubi refuses to sync both. A path
in the message locates the original on this machine. Use the duplicate as a plain jj
repo, or use `musubi clone` for another syncing copy.

If you moved by copying and deleting the original, or restored a backup here, run
`musubi join --original` only after the original is gone.

### "the copy of this repository's key is at ..."

`musubi join --original` refuses while the copy it would replace is still there. Run it only
once that copy is gone.

### "this repository's record says it is part of hive app, but its machine key or jj config id is missing; ..."

Files in `.jj/repo` were deleted. Make a new copy with `musubi clone`; assigning this one a new
identity would show it as a second copy.

### "this repository belongs to another user (uid ...), not this one (uid ...)"

`musubi` ran as a user who doesn't own the repo, as under `sudo`. Run it as the owner.

### "the current directory no longer exists"

The current directory was deleted. `cd` to its replacement or another directory and retry.
`musubi status` reports this with exit status 0. Commands such as `musubi list` work anywhere
unless given a relative path.

### "can't reach this workspace's repository, ...: ..."

A workspace added with `jj workspace add` points to a repo that moved, disappeared or
became unreadable; jj also reports "Cannot access ...". Move the main workspace back, or:

1. From the main workspace's current location, run `jj workspace forget <name>` for the affected
   workspace.
2. Move the affected workspace's directory aside.
3. Recreate it with `jj workspace add <path> --name <name>`.
4. Copy back your changed files.

### `musubi list` shows a copy "not syncing: ..."

The copy is missing, its disk is unmounted, or another repo occupies its path. Nothing
is written there. A copy moved with `mv` resumes when jj or `musubi` runs in it; one returning
at its old path resumes automatically. `musubi leave <path>` stops looking for a missing copy;
`musubi forget` from another copy stops showing it there.

### `musubi list` shows this machine twice, as `laptop-1a2b` and `laptop-3c4d`

Two copies share this machine's name, perhaps after cloning a deleted copy without leaving.
Their id prefixes distinguish them. `musubi list` marks this one
(`here: /home/you/src/app as laptop-3c4d  synced 4s ago`); `musubi status` shows when the other
was used. If it's gone, run `musubi forget laptop-1a2b` with its name.

## Leaving a hive or forgetting a machine

### "couldn't tell hive app that this repository leaves: ..."

The final sync failed, so this repo remains in the hive and its daemon keeps trying.
That retry sends the forget recorded by `musubi leave`, hiding this copy elsewhere until next
used. Fix the cause and retry `musubi leave`, or use `musubi leave --force`. Force still
attempts a sync; if it fails, other machines show this copy until `musubi forget` removes it.
To pause traffic first, run [`musubi daemon stop`](guides/manage.md#pause-syncing-or-leave).

For "work done in this repository while it left kept it in the hive", a jj command ran during
each of the three leaving attempts. Stop those commands and retry `musubi leave`.

### "couldn't record what changed in the working copy: ..."

`musubi leave` snapshots files before leaving, and jj failed for the reason shown. For a stale
working copy, run `jj workspace update-stale`, then retry `musubi leave`.

### "Warning: Couldn't put back this repository's working copies (...)."

Leaving temporarily removed working copies from the view and failed to restore them. In
`jj op log`, find `musubi: leave`; use `jj op restore` on its preceding operation to restore
the missing working-copy commits.

### "Warning: Couldn't give this repository's working copies new commits (...)."

The repo has left its hive, but a working copy whose commit the hive abandoned didn't
get a new one. Run `jj new @-` in that workspace.

### "no machine laptop shows here in hive app; `musubi status` names those that do"

The copy left, was forgotten, or has another name. `musubi status` lists present copies, even
without workspaces. Use the machine part of a workspace name (`laptop` for `laptop/default@`),
or the unambiguous name from `musubi list`.

Name collisions can require `laptop-1a2b`, including when an old copy shared the name or a local
workspace starts `laptop/`. If id prefixes also collide, use the full id, as in
`laptop-1a2b3c4d`.

### "laptop is this machine; `musubi leave` takes this repository out of hive app"

`musubi forget` forgets other machines' copies. To take this one out, run `musubi leave`. If
another copy has this machine's name, `musubi list` and `musubi status` say which is this one:
forget the other by its name
([above](#musubi-list-shows-this-machine-twice-as-laptop-1a2b-and-laptop-3c4d)).

### "musubi.forget-after is neither `never` nor a duration such as `6h`; taking it for never"

The setting is unreadable or under one second (reported as "is shorter than a second, the least
it can be"). The daemon treats it as `never`. Set `never` or a duration of at least a second:
`jj config set --repo musubi.forget-after 6h`. See
[Settings](reference/configuration.md#settings).

### "musubi.forget-after in your user config is neither `never` nor a duration such as `6h`; fix it and run this again"

Or "... is shorter than a second, the least it can be; ...". The command joined nothing because
`musubi.forget-after` in the named config is unreadable or under one second. Fix it or unset it
with `jj config unset --user musubi.forget-after` (`--repo` for repo config), then retry
`musubi join`, `create` or `clone`.

### Workspace config overrides a lease

"musubi.forget-after in workspace config for … overrides --lease; unset it and run this again"

A workspace setting takes precedence over the repo setting `--lease` writes. The command
refuses a conflicting policy before joining. The path names the affected workspace, which
may be the workspace the daemon already serves when you rejoin from another one. Remove
its override, then retry the lease:

```sh
jj -R <workspace-path> config unset --workspace musubi.forget-after
musubi join --lease 6h
```

## Upgrading

See the [upgrade guide](guides/upgrading.md) for coordinated upgrades and installer requirements.

### "incompatible peer: protocol ... but this is protocol ..."

Install the same release or source build on every machine and hub. Before 1.0, either can
change the protocol. Set `musubi.upgrade-command` to follow the hub automatically; see
[Upgrade jj-musubi](guides/upgrading.md).

### "Upgrade: upgrading to musubi ... failed: ..."

The daemon's `musubi.upgrade-command` failed, exceeded an hour, or installed a different release
or build than the hub's. The message says which; `upgrade.log` holds its output. Fix the
command, running it manually with `MUSUBI_UPGRADE_TO` set to the named release or build, then
run `musubi daemon restart`. If the install path changed, run `musubi daemon install` too.

On Unix, a running installer survives daemon restart with its lock. The new daemon waits for
that lock before retrying on a later sync. The surviving command has no timeout monitor:
inspect `upgrade.log` and stop a stalled installer before retrying. Leave `upgrade.lock` in
place to prevent overlapping attempts.

Keep installers in the foreground and preserve standard input, which carries the lock. While
the launching daemon runs, a timeout stops the command and its process group on Unix, or just
the command process on Windows. Check for and stop detached installers yourself.

For `upgrade-from-source: no tag ... in ...` or `no commit ... in ...`, push the hub's release
tag or deployed commit to where this machine's source clone fetches, then run
`musubi daemon restart`. See [Deploy a build from
source](guides/upgrading.md#deploy-a-build-from-source).

### "the running daemon is musubi ..., but this is ...; restart it with `musubi daemon restart`"

You upgraded jj-musubi, but the daemon still runs the earlier version. Run
`musubi daemon restart`.

### "missing field `remote_bindings`" or "missing field `clone_config`" when starting a hub

This hub directory predates the remote-name preflight or clone-defaults format. Use a fresh hub
directory and rejoin from the existing copies, as [Upgrade
jj-musubi](guides/upgrading.md) describes. Keep the old directory as a backup; the
repos and their work remain on the copies.

### jj reports "stack limit reached"

jj 0.47.0's static Linux binary could panic with `stack limit reached`, even in a new repo;
[jj 0.47.1](https://github.com/jj-vcs/jj/releases/tag/v0.47.1) fixed it. Upgrade jj, put the new
binary first on `PATH`, check `jj --version`, then retry the failed command.

## Syncing

### "hub: no such blob" or "hub: attachment ... was not uploaded"

The hub deleted transfer data untouched for an hour, perhaps while this machine slept. The
daemon retries from what remains. If this happens during active transfers, upgrade both this
machine and the hub: earlier releases expired data an hour after its last write, even during
transfer.

### Identical divergent copies after an operation abandon

A command finishing on an old operation after `jj op abandon` can repeat a rebase already
performed by a merge, leaving copies with identical parents and contents. This also happens
without jj-musubi. Compare them with `jj log -r '<first> | <second>'` and
`jj diff --from <first> --to <second>`.

Only remove an unused leaf: check `jj log -r '<unwanted-commit>::'` for descendants, and check
bookmarks, tags and working copies before running:

```sh
jj abandon <unwanted-commit>
```

Keep copies used by other work or references. `jj abandon` rebases descendants onto the parents
and removes bookmarks; it does not move them to the equivalent copy. See
[known jj limitations](internals/races.md#known-jj-limitations).

### "jj cannot merge this machine's operations with the hive's (...)"

jj 0.47 can't merge some concurrent operations, such as rebases that form a loop. jj-musubi
holds back the incoming operations so jj commands here can still run. The message names a
local, unsent operation to revert before syncing can continue:

```sh
jj op revert <id>
```

Later work stays, rebased off the reverted changes. A change rewritten again since, such as
by describing it, becomes divergent as with `jj op revert` alone; `jj abandon` the unwanted
copy. The next sync names any further conflicting operation. If jj-musubi cannot identify one,
it lists unsent operations newest first; revert the one conflicting with the hive.

[Known jj limitations](internals/races.md#known-jj-limitations) describes the cases jj can't
merge.

### "cannot tell which operations jj abandoned"

If `jj op abandon` rewrites two operations to identical bytes, their ids also match and
jj-musubi cannot tell which one you meant to keep, so it stops before passing removals to the
hive. Run the hinted `jj op integrate <operation>`, then `musubi sync`, and inspect the restored
history before trying another abandon. `jj op restore` restores a view without the missing
ancestry. Avoid forcing equal timestamps on operations you may abandon.

If `jj util gc` already removed that history, integration cannot work. Follow the
[new-copy rescue](#this-repositorys-history-no-longer-matches-the-hives-so-it-cant-sync-again)
to bring your work into a new copy.

### "this repository's history no longer matches the hive's, so it can't sync again"

```text
this repository's history no longer matches the hive's, so it can't sync again: make a new
copy with `musubi clone`, bring this one's work across to it, then run `musubi leave --force`
here
```

Keep this repo: its commits remain available. Make a new copy here with `musubi clone`
and bring across work the hive lacks: changes since the last sync, or all work if the first
sync never finished. You can rescue the work before diagnosing the cause.

1. In the original copy, choose the commits you need. If you're rescuing files after a
   publication hold, first check their ancestors for unwanted content. You can also
   [copy files](guides/snapshots.md#recover-wanted-work).

2. In the original copy, give each commit at the tip of that work a bookmark (`jj log` shows
   them), and print where this repo keeps its Git data:

   ```sh
   jj bookmark create rescue-1 -r <change>
   jj git export
   jj git root
   ```

3. In the new copy, fetch and track those bookmarks, then remove the temporary remote:

   ```sh
   jj git remote add rescue <the path jj git root printed>
   jj git fetch --remote rescue -b 'rescue-*'
   jj bookmark track 'rescue-*' --remote rescue
   jj git remote remove rescue
   ```

   Both copies use the hive's object hash. If `jj log` shows divergent changes, the hive has
   rewritten commits beneath this work. Use `jj rebase` onto the hive's versions, then
   `jj abandon` the old ones.

Back in the original copy, run `musubi leave --force` after checking the rescued files and
commits in the new copy. It keeps that repo and still attempts a final sync before
leaving. If `musubi create` says this, the hive it made is empty, and this copy can't fill it:
run `musubi leave --force`, and remove the hive with `musubi hub remove`.

#### Why history can stop matching

Syncing stops to prevent abandoned operations returning to the hive; `musubi status` says
retrying won't help. This is expected when:

- The copy left or was forgotten (`musubi forget` or `musubi.forget-after`) while another
  machine ran `jj op abandon` and every remaining member accepted it. The hub no longer
  remembers the abandon to pass it on when this copy rejoins.
- Its first sync after `musubi join` or `musubi clone` never finished. The hub stops waiting
  after a day without contact, or an hour if the hub restarts while the copy is away, when
  another machine abandons operations meanwhile. For a new copy, none of its work reached the
  hive, including work from before joining.
- `jj op abandon` removed all history below unsynced work, then `jj util gc` deleted the old
  operations before jj-musubi read them. Those operations may be needed to preserve workspace
  ownership.

Use the rescue steps above. Otherwise, missing history (such as an op-head update lost in a
power cut) is a bug: report it at <https://github.com/bos/jj-musubi/issues> with the daemon's
log (`daemon.log` in the [state directory](reference/configuration.md#on-every-machine)).

### "the hub refused this machine's work: ..."

```text
the hub refused this machine's work: it lacks something the work needs, or brings back
operations `jj op abandon` removed (the hub's log says which)
```

The hub's log identifies missing dependencies or the return of abandoned operations. Either is
a bug: report it at <https://github.com/bos/jj-musubi/issues> with this machine's `daemon.log`
and the hub's log; see [log locations](#start-with-this-copy).

To continue, make a copy with `musubi clone`, bring across work since the last sync, then run
`musubi leave --force` in the original.

### "unknown field ... (written by a newer jj?)"

jj wrote operation fields this build of jj-musubi cannot preserve. Upgrade jj-musubi on the
machines and hub, following the runtime hint, then retry. See the
[upgrade guide](guides/upgrading.md).

### "the hub did not supply the objects this machine needs"

The hub's reply left some commits missing, as when the hive was recreated while this machine
was syncing. If the daemon serves this copy, it retries from the hub's current state.
Run `musubi sync` to retry at once. If the error persists, check the hub's log; see below if
every machine fails on the same object.

### Every machine's sync of a hive fails on the same object

If the hub's machine lost power, a file the hub wrote just before may be cut short, and every
sync that needs it fails. Stop the hub, delete the hive's `heads` file
(`musubi-hub/<hive id>/heads`), and start the hub again. It finds the store corrupt, sets it
aside under `removed/`, and creates an empty hive. Surviving copies refill it with work they
retained; work that existed only on a lost machine needs its backup.

### "the first sync failed: ..."

`create`, `join`, or `clone` set up the repo, but its first sync failed for the reason
given. The daemon keeps trying: fix the cause, and `musubi status` shows when it succeeds.

### Your working copy is stale

Another machine changed the commit your working copy is on. Run `jj workspace update-stale`.
See [When another machine rewrites your working
copy](guides/working-across-machines.md#when-another-machine-rewrites-your-working-copy).

### `jj log` shows `main*` after a sync

In a colocated repo, jj exports bookmarks to git only when a command changes something,
so after a `jj` command that merged other machines' work, git's branches can lag jj's
bookmarks. The next command that changes something exports them, as does `jj git export`.

### "Unable to create '.../refs/heads/main.lock': File exists" or "main@git: Failed to set"

An interrupted `git`, `jj` or `musubi` ref update may leave a lock, such as
`.git/refs/heads/main.lock` or `.git/packed-refs.lock`, blocking later exports. jj-musubi removes
it at ten minutes old when it next blocks a sync and logs that removal.

To clear it sooner, wait at least a minute and check that no `git` or `jj` command, including
an editor's, runs in the repo. Then delete the lock. jj exports the bookmark again at
its next export.

### An annotated tag is lightweight on other machines

jj-musubi shares the target commit, leaving the Git tag object on the fetching machine.
Elsewhere, `git describe` without `--tags` skips the tag and `git tag -v` cannot verify it.
Fetch the tag on any machine that needs it.

## Sending held by the snapshot publication budget

### Accidentally added files and sending stopped

Run `musubi sync --outgoing` without snapshotting or contacting the hub, then follow
[Snapshot limits and cleanup](guides/snapshots.md).

### Recover wanted work without approving held history

Use the [file-rescue workflow](guides/snapshots.md#recover-wanted-work) to keep wanted work
without importing the held history. For commits, use the
[bookmark rescue](#this-repositorys-history-no-longer-matches-the-hives-so-it-cant-sync-again);
fetching also brings ancestors, which may contain unwanted content.

### "sending held: snapshots retain ... exceeding the publication budget"

Follow [Snapshot limits and cleanup](guides/snapshots.md). Restarting the daemon does not clear
this hold; receiving continues. `musubi status` calls it "sending held: snapshot publication
budget".

### "outgoing work changed; ..."

The inspected history, limits or cleanup context changed. Repeat `musubi sync --outgoing`
or your `musubi sync --prune OPERATION...` preview and use its new token. Cleanup snapshots
edits before checking the token, so new edits can cause this refusal. Current work stays intact.

### Cleanup is refused

These refusals discard no operations; receiving continues. You can keep sending held while
deciding what to do. Inspect with `musubi sync --outgoing`, then try other operations, approve
the inspected history if you want it shared, or
[rescue wanted work](guides/snapshots.md#recover-wanted-work) without publishing it.

Applying cleanup can record edits before refusing a stale token; see
[outgoing work changed](#outgoing-work-changed-).

#### "operation ... was offered to the hub or predates publication tracking; ..."

Cleanup cannot prove the operation stayed local: an upload reply may have been lost, or the
operation predates publication tracking. Use [cleanup recovery](#cleanup-is-refused), or
[abandon shared history](guides/working-across-machines.md#abandoning-operations).

#### Cleanup cannot preserve earlier changes

"cannot safely prune this history: jj did not record enough information ..."

jj did not record which change versions the command selected. This includes older or custom
commands, undo, redo, operation restores, some Git imports reusing existing versions, and
Git-ref export retries. Cleanup cannot establish that it would preserve those versions.
Use [cleanup recovery](#cleanup-is-refused).

#### "this selection would change another copy's activity or membership; ..."

Removing these operations would change how a later concurrent forget of another copy resolves.
Cleanup can create activity for this copy, but cannot invent activity for another.
Use [cleanup recovery](#cleanup-is-refused).

#### "this cleanup cannot preserve ..." or "the prepared cleanup differs from its preview; ..."

The prepared cleanup did not reproduce the inspected state. Try fewer operations, or use
[cleanup recovery](#cleanup-is-refused). Update a stale workspace with `jj workspace update-stale`
before inspecting again.

### "cannot read this copy's record of attempted publications: ..."

The local publication record is damaged. Do not delete it to make history look unpublished.
Keep this copy's work and follow the [new-copy recovery
workflow](#this-repositorys-history-no-longer-matches-the-hives-so-it-cant-sync-again).

## What `musubi status` reports

### "Warning: Syncing fails: ..."

Find the quoted error on this page. A serving daemon retries and logs details at the path in
the hint; otherwise `musubi sync` retries now.

### "Warning: The daemon isn't running, so this repository syncs only when you run `musubi sync`."

Follow the [daemon startup instructions](#the-daemon-isnt-running-after-a-reboot). Until then,
run `musubi sync` to send and receive recorded work.

### "Warning: The daemon doesn't serve this repository."

The daemon hasn't started serving this copy, perhaps during restart after `musubi join`.
If this persists, run `musubi join` here again.

If the state directory was deleted or `MUSUBI_STATE_DIR` changed, `musubi status` instead
reports a duplicate. Use `musubi join --original`; see
[Move, copy or restore a repo](guides/manage.md#move-copy-or-restore-a-repo).

## What `musubi top` reports

See [monitoring](guides/manage.md#check-syncing) for checks and the
[display reference](reference/commands.md#read-musubi-top) for columns and controls.

### "... not heard from in 6m: offline, or its daemon isn't running"

The hub has heard nothing for over two minutes. Check `musubi status` there for a stopped
daemon or lost connection. Daemons report after each sync, at least every half minute, and
catch up after reconnecting. A long first sync reports only when done. A departed or deleted
copy can also show this for a day.

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
surviving copies refill it with the work they retained.

### "not heard from since the hub started" or "not heard from in a day: it may have left the hive"

A departed or deleted copy's workspace remains visible until `musubi forget` removes it.
An active copy reports once it syncs, within half a minute; check `musubi status` there.

### "This machine's daemon isn't running; `musubi daemon start` starts it."

Follow the [daemon startup instructions](#the-daemon-isnt-running-after-a-reboot). A machine
with no copies, such as a hub-only machine, needs no daemon and produces no warning.

## The daemon

### The daemon isn't running after a reboot

Run `musubi daemon start` to resume background syncing, or `musubi daemon install` to start
it now and at login. `create`, `join`, and `clone` start it without installing login startup.
On Linux, the installed daemon stops at logout unless you run `loginctl enable-linger`.

### "the daemon exited (...) before it was ready" or "did not start listening"

The daemon failed as it started. The message includes the end of its log, or names the log.

### "... is not a private directory of this user's ..."

The socket's directory must belong to you and be writable by you alone. If you own it, run
`chmod 700` on it. Otherwise remove the socket directory for jj-musubi to recreate, or choose
another with `MUSUBI_SOCKET`.

Do not remove the state directory named by `MUSUBI_STATE_DIR`: it lists the copies to sync.
Directories made with a permissive umask (such as `002`) or an earlier release may need fixing.

### "the daemon's socket ... is a relative path; ..."

`--socket`, `MUSUBI_SOCKET` or `musubi.daemon.socket` gave the daemon's socket relative to the
current directory, which would make commands run elsewhere start a daemon of their own. Give
the full path, or one starting with `~/`.

### "this machine's daemon already runs, listening on ..., not ..."

This command chose a different socket through `--socket`, `MUSUBI_SOCKET` or
`musubi.daemon.socket`. Use the same setting everywhere, or omit it to use the running daemon's
socket. Commands such as `musubi list` and `musubi status` refuse rather than bypassing it.

To move the daemon, run `musubi daemon stop`, then start it with the chosen socket. For login
startup, run `musubi daemon install` again with that setting. The message without "not" means
`musubi daemon` was run on the socket already in use.

### "running (pid ...), but not listening on ..." or "this machine's daemon (pid ...) isn't listening on ..."

The socket disappeared, perhaps through a `/tmp` or `$TMPDIR` cleaner. The daemon recreates
it within seconds; `musubi daemon stop` still works. If this persists, run
`musubi daemon restart`.

### "this machine's daemon (pid ...) isn't listening on ..., and can't be stopped from here" or "running (pid ...) elsewhere, ..."

The daemon doesn't answer and this command cannot signal it, as on Windows or from a container
sharing an outside daemon's state directory. Run `musubi daemon stop` where it runs, or end
its process there, then restart it.

### "... would be ... bytes longer than this system allows" or "... is ... bytes too long ..."

Unix socket paths are limited to about 100 bytes. For the daemon, choose a shorter path with
`MUSUBI_SOCKET` or `musubi.daemon.socket` in jj's config. For a hub, serve it from a directory
with a shorter path.

### "Warning: Could not start the daemon (...); syncing once instead."

The command synced once without starting a daemon. Fix the reported error, then follow the
[daemon startup instructions](#the-daemon-isnt-running-after-a-reboot).

### "Warning: The daemon isn't running, so this synced in its own process, ..."

`musubi sync` ran once without a daemon, as after `musubi daemon stop`. To resume background
syncing, follow the [daemon startup instructions](#the-daemon-isnt-running-after-a-reboot).

