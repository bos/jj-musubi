# Changelog

What changes in each release, and what to do on upgrading.

Until 1.0, a release may change the protocol, so run the same release on the hub and every
machine (see [Upgrading](README.md#upgrading)).

## Unreleased

- A hub matches a joining copy to a hive by the remote URLs only of joins to that hive. A copy
  carries the history of a hive it left into the next one it creates or joins, and the hub
  took the URLs of its joins to the old hive for the new one's too, so a later copy of the old
  hive was refused as matching both. A hub's existing hives keep URLs they took that way: to
  drop them, stop the hub, delete `index.json` in each hive's directory, the one named by its
  id in the hub's directory, and start the hub again, which rebuilds each.

- musubi now syncs repositories whose git names objects with SHA-256. A hive takes the hash
  of the copy that creates it, and the hub makes the hive's store with it, whatever git's
  default is. Before, the hub's store took git's default, so a SHA-256 copy, or every copy once
  git defaults to SHA-256, failed every sync with "final sha1 did not match". `musubi join`
  refuses a copy with the other hash, saying so, and `musubi clone` makes the copy with the
  hive's hash, whatever jj's `git.object-hash` setting says. This changes the protocol to 17:
  upgrade the hub and every machine together. A SHA-256 copy in a hive made before this change
  can't join it: make a copy with `musubi clone`, or start a hive of its own with
  `musubi create`.

- `musubi clone` makes the new repository itself, rather than running `jj git init`, so a
  destination starting with `-` works. Nothing needs doing on upgrading.

- Large syncs finish over links with as little as about 70 kbit/s to spare for musubi, a
  megabyte in two minutes. A machine now waits two minutes for each reply rather than 30
  seconds, and still gives up with "request timed out" after about ten minutes in which
  nothing moves. ssh now waits a minute without a word from the hub's machine, rather than 30
  seconds, before it ends the connection, so that it doesn't cut off a slow upload; so a
  machine takes up to a minute to notice a link that has died, unless it has just woken from
  sleep. The hub also lets go of a request whose machine has stopped waiting for it, rather
  than working it out for nobody while other machines wait. Upgrade the hub as well as every
  machine: against an older hub, a slow download can fail with "hub: no such blob" and start
  over.

- Large syncs over slow links finish. Each try at a large upload or download now carries on
  from where the last left off. Before, every try started over, so on a link too slow to move
  eight megabytes in 30 seconds, about 2 Mbit/s, it timed out at the same point each time,
  and the sync failed with "request timed out" again and again. After a timeout, a machine
  also moves less at a time, and a sync that keeps moving goes on rather than giving up. The
  hub now keeps a transfer's data while it is still moving. Before, it deleted it an hour
  after it was last written, so a sync whose transfers took longer failed with "hub: no such
  blob" or "hub: attachment ... was not uploaded". Upgrade the hub and every machine: each
  machine carries on from where it left off once it is upgraded, and the hub keeps a
  transfer's data while it moves once both are.

- `musubi leave` in a copy whose hive was removed from its hub takes it out, as it does any
  other copy. Previously it refused, advising `musubi join --hive`.

- `musubi.forget-after` set to a duration under a second, such as `500ms`, is reported as
  shorter than a second, the least it can be. Previously the message said it was neither
  `never` nor a duration.

- Hints that name a command with a path, such as `musubi list`'s `musubi leave <path>` and
  `musubi hub`'s `--hub <dir>`, quote the path as a shell needs, so that it can be pasted.

- When ssh to a hub hangs, the first sync to fail says "ssh to devbox did not connect", as
  later ones do. Previously it failed with a bare "disconnected", which `musubi status` showed
  too, since the reason came only once ssh had been stopped, a moment after the sync failed.

- The hub and the daemon log only warnings from all of jj's libraries, as the reference says.
  Previously they logged each lock and each index scan of the crates jj 0.47 split out of
  `jj_lib`, such as `jj_local_util` and `jj_default_index`.

- A hub on this machine given to `--hub` another way, as `../hub` or with a trailing `/`, is
  the same hub. Previously each spelling was kept as a hub of its own, so `musubi list` showed
  its hives under each. A copy that joined with such a spelling goes on showing under it:
  run `musubi join --hub <dir>` in it again, giving the hub's directory as `musubi hub` prints
  it.

- Commands run from a directory deleted meanwhile say "the current directory no longer
  exists" if they act on the repository there, and the others, such as `musubi list` and
  `musubi daemon stop`, work, given no relative path. `musubi status` says so, and exits 0.
  Previously every command failed with "No such file or directory".

- In a workspace whose repository can't be reached, as when the workspace it was added from
  has moved, commands say so: "can't reach this workspace's repository, ...". Previously
  `musubi status` said the directory wasn't in a jj repository, and other commands failed with
  "No such file or directory".

- `+` in `musubi top` slows the refresh to at most once an hour, as `--interval` allows.
  Previously it capped the refresh at once a minute, so after `--interval` above 60, pressing
  `+` made it faster.

- One daemon serves a machine's copies, whatever socket it listens on: a daemon holds a lock
  on the state directory, and won't start while another serves it. Previously a command run
  where `XDG_RUNTIME_DIR` differed, as under cron or after `sudo -u`, started a second daemon,
  and syncs of the same copies failed on each other's locks. Commands that choose no socket
  now use the one the running daemon listens on; one that chooses another is refused, saying
  where the daemon listens. Commands refuse a daemon from before this change until it is
  restarted: run `musubi daemon restart` after upgrading. A second daemon an earlier release
  started, or one that lost its socket, can't be found that way: `pgrep -fl 'musubi daemon'`
  lists them, to stop with `kill` before restarting.

- The daemon listens again within seconds when a temp cleaner deletes its socket, and `musubi
  daemon stop` stops it meanwhile. Previously nothing could reach, stop or replace it, and
  `musubi list` and `musubi status` said it wasn't running. They now say it runs but isn't
  listening.

- `--socket`, `MUSUBI_SOCKET` and `musubi.daemon.socket` read a path starting with `~/` as in
  the home directory, and refuse a relative one. Previously a relative path, `~/` included,
  gave a daemon for each directory commands ran in, and a directory named `~` in each. Give
  such a setting as an absolute path, or from `~/`; if `musubi daemon install` ran with a
  relative `MUSUBI_SOCKET`, run it again after fixing that.

- musubi makes its state directory readable and writable by you alone, whatever your umask.
  Previously, under a umask such as `002`, a daemon with `MUSUBI_STATE_DIR` set refused to
  start, as its socket was in a directory others could write to, and removing the directory
  didn't help. If a `MUSUBI_STATE_DIR` made before is writable by others, `chmod 700` it.

- A `musubi daemon install` that the service manager refuses leaves the daemon running, as it
  was, and removes the unit or agent it wrote. A `musubi hub install` for a directory another
  hub serves refuses before stopping the hub installed already. Previously each stopped what
  ran, and a failed daemon install left a unit `musubi daemon uninstall` didn't remove.

- A copy the hive forgot no longer brings back the parent of its working copy when another
  machine rewrote or abandoned that parent meanwhile. If the working copy was empty, as after
  `jj commit`, and another machine rewrote its parent, as `jj describe` or `jj rebase` does,
  or abandoned it, the copy's next `jj` command that recorded anything, such as a snapshot of
  an edit, made the old parent visible again on every machine: divergent beside its rewrite,
  or no longer abandoned. A copy a coding agent joined is forgotten after 6 hours unused, so
  this was easy to meet. Now its working copy moves as jj would have moved it, onto the
  rewrite or onto the abandoned commit's parent; if that changes its files, the next `jj`
  command there finds the working copy stale, as after any rewrite on another machine.
  Nothing needs doing on upgrading. To tidy up a parent that already came back beside its
  rewrite, move what was built on it onto the rewrite in its place, with
  `jj rebase -s <child> -o 'parents(<child>) ~ <old> | <rewrite>'`, then `jj abandon <old>`;
  abandon again one that came back after an abandon.

- A workspace of your own named like another machine's, as `beta/x` where a machine named
  beta has a workspace `x`, now stays yours: when you add it while beta adds `x` or joins the
  hive, when you add it, or rename one to it, after `jj workspace forget beta/x`, and through
  `jj undo` of forgetting it. Previously musubi could take it for beta's `x`: it got beta's
  working-copy commit, and editing in it moved beta's working copy, changing beta's files.
  While yours has that name, this machine shows all of beta's workspaces under a longer name,
  as `beta-1a2b/x` and `beta-1a2b/default`. A workspace already taken for beta's stays so on
  upgrading, and beta's `jj workspace list` doesn't list it under this machine's name. In
  that workspace, run `jj workspace rename` to a name without a `/`, then `jj new`, so that it
  no longer shares beta's working-copy commit, which may hold edits made on either machine.

- `musubi top` lists an offline machine among its issues once when it goes quiet, leaving room
  for new issues. The hive's issue count and the red machine row still show it. Nothing needs
  doing on upgrading.

- Copies now default to never being forgotten, including when an agent runs `musubi join`,
  `create` or `clone`. Use `--lease 6h` for a temporary copy that should be forgotten after six
  hours without a local operation. An explicit lease replaces the copy's repo policy; without
  one, existing config is kept. Existing six-hour policies are unchanged: run
  `jj config set --repo musubi.forget-after never` in persistent copies, then `musubi sync`.

- SSH key setup retries cleanly after a public-file write fails, including when an older public
  file is still present. A new key becomes active only after both halves are ready. Existing
  private keys are retained; a missing or empty `hub_key.pub` is recreated from its private key.
  Previously failed setup could leave an unusable pair, and later authorization could add the
  older public key. Fix the reported file error and retry the original command.

- Clone keeps the exact hive selected by its first name lookup. A different hive named
  with that hive's id could previously redirect the clone to the wrong repository during
  preflight. The hub now checks only the resolved id, and the client rejects a reply for
  another hive before creating directories. This changes the protocol to 16: upgrade the
  hub and every machine together. It adds no further hub metadata change.

- Concurrent first joins on one machine reuse one completed SSH key pair. Previously both
  could start `ssh-keygen` for the same files, causing a join to fail or replace the other's
  key. Key generation is locked until both files are ready, before either join probes or
  authorizes the key. Nothing needs doing on upgrading.

- `musubi forget` can find a present copy after it removes its last workspace with
  `jj workspace forget`. Previously it refused, claiming no machine of that name existed,
  because it found machines only through their workspaces. `musubi status` also keeps the
  correct qualified name for such a copy when local workspace names reserve its plain name.
  Nothing needs doing on upgrading.

- Clone fills missing jj settings once from defaults recorded when the hive was created:
  `user.name` and `user.email` by default. Set `musubi.clone-config` before creating a hive
  to select other keys, or `[]` for none. Existing destination settings win, and later syncs
  leave all configuration alone. This changes the protocol to 15 and the hub metadata;
  upgrade the hub and every machine together, initialize a fresh hub directory, and rejoin
  existing copies as described below. Move any desired `musubi.shared-config` selection to
  `musubi.clone-config` before recreating a hive; it now affects clone defaults only.

- Git remote definitions and jj configuration now stay local on each machine. Sync no
  longer copies URLs or repo config, so interrupted config updates cannot overwrite local
  edits. Configure remotes and rewrite/push protections explicitly on each machine that
  needs them; clones use the destination machine's `trunk()`. Remove `musubi.shared-config`
  and `musubi.share-credentials` from jj config; both settings are gone. Explicit joins
  still record credential-free URL hints for matching future copies. Join checks fixed
  fetch and push destinations for every remote name, including with `--hive` and on rejoin;
  clone checks inherited global remotes and recorded bindings before creating its directory.
  Destination-specific conditional includes are checked too. Different
  destinations need distinct names. This changes the protocol to 14 and the hub metadata:
  use a fresh hub directory, upgrade the hub and every machine together, then rejoin existing
  copies with `musubi join --hub <new-hub>`. Existing jj work and local config stay intact.

- Bracketed IPv6 remote URLs match in scp-style and `ssh://` forms, so automatic joining
  recognizes the same repository and each machine keeps its own spelling of its remote.
  Previously a colon inside the address was mistaken for the path separator. No remote URL
  changes are needed.

- The daemon reloads changed jj settings before each repository's next sync, including its
  signing configuration and `musubi.forget-after` in user config. Previously it kept the
  settings it opened the repository with, ignoring later user config edits. After changing
  settings, `musubi sync` waits for a sync with them; one already in progress may use the old
  settings. Nothing needs doing on upgrading.

- A hub recognizes its default directory through symbolic links when it prints commands for
  this machine. Previously, restarting it through another path to the same directory could
  ask for `--hub` unnecessarily. Nothing needs doing on upgrading.

- musubi exports bookmarks to git where jj does: in a repository with a workspace that is also
  a working tree of its git repository. Before, it exported them to any external git
  repository named `.git`, where jj writes them only on `jj git export`, and none for a
  workspace made with `jj workspace add --colocate` in a repository whose git store is inside
  `.jj`, where jj exports them in every command.

- A hub that fails to save what a push taught it about a hive, on a full disk say, tries again
  at the next push. Previously it could stay unsaved until a push brought something new, so
  that after a restart `musubi join` could refuse a copy of the hive's own repository, saying
  no hive on this hub shares history with it.

- A machine can clone or catch up on a hive too large for the hub to prepare a reply in 30
  seconds, or to take in a push of one. Previously every attempt timed out and the hub started
  the work over, so it never finished. Now a machine asks again every 30 seconds for about ten
  minutes, and the hub answers a repeat with the reply it already prepared. Nothing to do on
  upgrading.

- The hub keeps serving every other hive while `musubi hub remove` waits for the removed hive
  to finish what it is doing, and while `musubi join` looks for the hive a repository belongs
  in. Previously either could hold up every machine's syncs, so that they could time out. A
  machine of the hive being removed gets "hub: this hive is being removed from the hub" until
  the removal finishes, then leaves the hive as before. Nothing needs doing on upgrading.

- `musubi clone` refuses a nonempty destination before changing it. Previously it could
  share that directory's files and Git history with the hive. Choose a new or empty directory,
  or use `musubi join` to share an existing repository.

- Stream connections limit subscriptions and requests in flight, and refuse duplicate live
  ids. Previously a buggy peer could accumulate silent subscriptions without bound. This
  changes the protocol to 12: upgrade the hub and every machine together, then restart their
  daemons. No configuration change is needed.

- A forgotten copy keeps its own workspace names when another machine trims away their
  entire shared history, including names containing slashes and unsnapshotted edits.
  Interrupted syncs and translation-cache loss preserve that ownership too.

- A history trim still notices operations materialized before a crash when an earlier trim
  removed the last accepted base. It keeps new work syncing instead of refusing the copy.

- Commands that finish while a machine takes a history trim keep their original workspace
  ownership and operation identity, including after cache loss or a delayed command at the
  old operation.

- Trimming all shared history below unpublished work preserves which machine owns each
  workspace. The trim records workspace-name bindings and restores each copy's workspaces
  along with its last use. Upgrade the hub and all machines together and restart their
  daemons (protocol 11); earlier builds cannot interpret the new bindings.

- Trimming history preserves each workspace's snapshot basis, including secondary workspaces
  with unsnapshotted edits. A later stale update can no longer load the empty operation root
  as that workspace's previous snapshot and panic.

- musubi now supports jj 0.47.1. Upgrade jj on every machine, and upgrade the hub and every
  machine together, then restart their daemons. Builds using jj 0.47.0 or earlier cannot
  sync with this build. The 0.47.1 release fixes the static Linux binary failure in 0.47.0.
  Ordinary jj commands leave remote-bookmark conflicts unchanged when their Git refs have
  not moved; fetch explicitly to resolve them. They also finish pending Git exports after
  merging operation heads. Timestamp templates now use jiff's formatting,
  and JSON timestamps use `+00:00` for UTC. See
  [jj 0.47.0's release notes](https://github.com/jj-vcs/jj/releases/tag/v0.47.0) for format
  changes.

- A full history trim keeps a copy forgotten when its forget was accepted during a sync
  that is still finishing. Previously new work above that forget could bring the copy
  back into the hive.

- Trimming all previously shared operation history beneath new work keeps the other machines
  in the hive. Previously the hub could forget a machine and discard an abandonment before
  it had taken it, leaving that machine unable to sync. Repair also keeps the surviving
  work's latest-use time.

- Waking a machine also ends ssh connections already waiting to close or drain stderr.
  An old connection's failure can no longer restore the retry delay that waking cleared.

- On Unix, an automatic upgrade that times out stops its command's process group, including
  the foreground installer. Previously only the shell stopped, leaving its installer
  running with the upgrade lock and blocking retries. Upgrade scripts must stay in the
  foreground and preserve standard input; no configuration change is needed for such scripts.

- Canceled requests release their reply bookkeeping immediately. Previously a long-lived
  connection could retain it until the hub replied or the connection ended.

- Trimming operation history while a sync is finishing keeps the other copies in the hive.
  Previously an accepted push not yet saved as the sync base could make another copy appear
  forgotten, letting the hub discard the trim before that copy received it and permanently
  stopping its sync. A trim that removes all of a copy's earlier operations also preserves
  its own Git state, so an unchanged Git HEAD is not imported as a move.

- If a recreated hub cannot supply objects requested from its old history, the machine
  retries from the hub's current state. Previously one sync could keep asking for the same
  missing objects until another machine restored them, without checking the hub again.

- After restoring and abandoning operation history, a machine fetches objects that
  `jj util gc` removed even when its saved fetch base used to contain them. Previously the
  hub could keep omitting those objects and every retry failed, including after a restart.

- A machine keeps received abandonment records before writing the history they explain,
  even when it cannot apply them yet. If the producer leaves and the hub later loses the
  records, the receiving machine can republish them after a restart. Applying a record also
  removes another name of the same abandoned operation from its local history.

- After a hub rollback, a machine keeps an abandonment when another abandonment has changed
  the operation's name, including when it never held the older operation. Previously it
  could repeatedly push without publishing the abandonment, or repeatedly fail to sync.

- After a hub rollback, a machine takes an abandonment even when its old operation already
  descends from the hub's surviving operation. Previously it could stay idle with the
  abandonment untaken after another machine republished a cached recovery operation.

- After a hub rollback, an active machine can republish an abandonment after the machine
  that made it has left. It keeps its own work and all surviving branches of the abandoned
  history. Previously it could wait forever for the departed machine to sync again.

- After a hub rollback, a machine republishes an abandonment even if the hub already has
  its latest operation. Previously interrupted receipt and `jj` work could leave every
  machine idle while an abandonment remained unpublished.
- A sync interrupted while taking another machine's `jj op abandon` can publish it again
  if the hub then loses it. Previously that machine could retry the same rejected push
  indefinitely until another machine synced. Restarting while applying the abandon also
  resumes moving its operation heads and workspace records.
- A build of musubi's source can go to every machine between releases. Push it, then on the
  hub's machine, `upgrade-from-source --deploy` (in [contrib](contrib/upgrade-from-source))
  deploys `main`, or the revision you name, as a build named for the release it follows, the
  time and its commit, such as `musubi 0.3.0+20261102153012.4a0db205e1f0`. Restart the hub,
  and machines whose upgrade command is `upgrade-from-source` follow it, building that commit.
  Told a release, `upgrade-from-source` builds its tag, such as `v0.6.0`, not `main`. See
  [Deploy a build from source](docs/guides/manage.md#deploy-a-build-from-source).
- Contracting operation history now keeps each operation's original identity even when two
  operations have identical views and metadata. This changes the canonical encoding and ids
  (protocol 9, release 0.6.0, the first since 0.1.0): upgrade the hub and every machine
  together. Existing hives and their local musubi state must be recreated from preserved jj
  repositories: follow
  [Recreate hives when upgrading to 0.6.0](docs/guides/manage.md#recreate-hives-when-upgrading-to-060).
  If jj itself coalesces two operation ids while abandoning history, syncing stops with a
  command to restore the missing history.
- The hub forgets a `jj op abandon` once every machine still in the hive has taken it, so trimming
  history with `jj op abandon ..<operation>` no longer leaves the hub remembering every abandoned
  operation, though it keeps them on its disk. A machine that's offline delays this until it
  syncs. A copy that was away when the abandon happened, forgotten or out with `musubi leave`,
  stops syncing when it comes back, saying its history no longer matches the hive's: make a new
  copy with `musubi clone`.
- `jj op abandon` of operations the hive has is passed on to every machine, rather than
  stopping that copy syncing: the abandoned operations go from every machine's operation log
  and never come back. The protocol changed: upgrade the hub and every machine together, by
  hand, then run `musubi daemon restart` on each machine. The error that said a repository
  lost history the hive has now says its history no longer matches the hive's, and means a
  bug.
- A machine can upgrade musubi by itself to follow its hub: set `musubi.upgrade-command` to a
  command that installs the release in `$MUSUBI_UPGRADE_TO`, and the daemon runs it when a
  hub runs a newer release, then starts again from it. See [Upgrade
  musubi](docs/guides/manage.md#upgrade-musubi). Every message now carries the sender's
  release, so this release talks to no hub or machine of an earlier one: upgrade them all
  together, by hand this once. For musubi built from a jj repository of its source,
  [contrib/upgrade-from-source](contrib/upgrade-from-source) is such a command.
- On a terminal, `musubi create`, `join`, `clone` and `sync` show what the sync they wait on
  is doing: bytes sent or received, with a bar, commits being imported, operations applied,
  or waiting on the hub. They no longer print `Syncing...`. After upgrading, run `musubi
  daemon restart`: commands refuse a daemon from the release before.
- `create`, `join` and `clone` no longer print `Synced with the hub (hive at #N)`, nor `sync`
  `Synced (hive at #N)`, nor `musubi status` the hive's operation number: it meant nothing to
  anyone but musubi. A sync that worked prints nothing.
- When no hub serves a hub's directory, the error says so in a line, with `musubi hub` on a
  hint line of its own; `musubi list` and `musubi leave` no longer repeat it inside their own
  messages, and `leave`'s hint, `musubi leave --force`, is on a line of its own too.
- `musubi clone` says "Cloned hive ... into ..." once it has, rather than "Cloning" before,
  and no longer passes on jj's `Initialized repo in` line.
- A machine shows another machine that shares its name as `laptop-1a2b`, as the hub's list
  does, where it used to show it as `laptop`.
- A `jj` command that was already running when a repository joined its hive, or one run with
  `--at-op` at an operation from before it joined, no longer sends the repository's history
  from before the join to the hive. Its work syncs once jj merges it with the history since.
- Two machines are never shown under one name, as `laptop-1a2b/default@` could show two
  machines named `laptop` whose ids start alike, and another machine's working copy never
  shows under the name of a workspace of this machine's own. Where `laptop-1a2b` is taken, a
  machine shows under its whole id, `laptop-1a2b3c4d`.
- On the hub's machine, `--hub localhost`, or the machine's name as `musubi hub` prints it,
  now reaches the hub `musubi hub` serves there without `--dir` through its directory rather
  than over ssh, and so does such a name in `musubi.hub` or saved as the default hub. A copy
  there that joined by such a name goes on using ssh; run `musubi join --hub localhost` in it
  to stop.
- Without `--dir`, `musubi hub` serves `~/musubi-hub`, where it served `musubi-hub` in the
  current directory, unless that is a hub's. To go on serving a hub kept elsewhere, run
  `musubi hub` in its directory, or pass `--dir`, or move it to `~/musubi-hub`.
- `musubi hub install` runs the hub at login, with launchd on macOS and systemd on Linux, as
  `musubi daemon install` does the daemon; `musubi hub uninstall` stops it. A hub you set up
  as a systemd unit of your own, as the guide used to say, can go: stop and disable it, then
  run `musubi hub install` in the hub's directory, or with `--dir`. See
  [Keep the hub running](docs/guides/setup.md#keep-the-hub-running).
- Added `skills/jj-musubi` to help coding agents work in a hive.
  See [Coding agents](docs/guides/working-across-machines.md#coding-agents).
- musubi tells a copy from a repository made by copying its files, with `cp -a`, `rsync` or a
  backup, and doesn't sync the duplicate, where two repositories synced as one machine and
  overwrote each other's working copy. `musubi join --original` syncs a repository as the
  copy it was made from, once that is gone, as after restoring a backup onto a new machine.
  See [Move, copy or restore a repository](docs/guides/manage.md#move-copy-or-restore-a-repository).
- The daemon follows a copy moved with `mv`, once jj runs in it. It stops syncing a copy that
  is deleted or missing, or whose directory comes to hold another repository, writing
  nothing there, where it retried forever and wrote into whatever it found; a directory
  swapped for a copy of another hive could put each hive's work in the other. `musubi list`
  lists such copies, and `musubi leave <path>` stops syncing one. The daemon no longer keeps
  the directory it was started in, whose deletion stopped every repository on the machine
  syncing.
- A copy whose hive was removed remembers it: a plain `musubi join` says so, where it could
  join another hive whose history matched. `hive.toml` is kept, recording whether the copy
  joined, left, or its hive was removed.
- A copy that joins or starts a hive other than the one its history came from forgets the
  other copies that history brings, which the new hive used to list as members.
- musubi refuses to run in a repository another user owns, as under `sudo`, which left files
  the owner couldn't read.
- `musubi status` is a command of its own, no longer another name for `musubi list`. It shows
  what musubi does with the repository you're in: its hive, hub and machine name, its last
  sync, whether the hub has this machine's latest work, every machine's working copies, each
  copy in the hive, and the daemon's process, socket and log. It warns of what keeps the
  repository from syncing, saying what to do, and never starts the daemon or asks the hub, so
  scripts, agents and shell prompts can run it. `musubi list` no longer shows the current
  repository's details: run `musubi status` for them.
- Each machine picks up a renamed hive's new name as its daemon next syncs, rather than only
  once `musubi list` runs there. The hub answers a daemon's report of a sync with the hive's
  details, so a hub and machines must be upgraded together.
- `musubi sync`, `musubi leave` and `musubi join`, run in another workspace of a repository
  than the one it joined from, act on the repository the daemon serves: `sync` goes through
  the daemon rather than syncing alongside it, `leave` stops the daemon serving it, and `join`
  no longer has the daemon serve it twice.
- musubi prints through jj's own formatting: it colours what it prints as jj's `ui.color` and
  `colors` config say, and takes jj's `--color` flag (see
  [Colours](docs/reference/configuration.md#colours)); errors, warnings and hints read as
  jj's do, with hints and warnings on stderr. Logs are coloured only on a terminal, so
  `daemon.log`, and a hub's log written to a file, no longer hold colour codes.
- `musubi list` prints its hubs, hives and copies through a template in jj's template
  language, `musubi.templates.list` in jj's config, or one `-T` gives, as jj's list commands
  do; `-T 'json(self) ++ "\n"'` gives them as JSON. A hub with no hives no longer says so.
- `musubi status -T` prints its report through a template in jj's template language, and
  `musubi status -T 'json(self) ++ "\n"'` as JSON, for scripts and agents (see [`musubi status` as
  JSON](docs/reference/commands.md#musubi-status-as-json)).
- A command whose output stops being read, as in `musubi list | head`, no longer panics: it
  does all it would, printing nothing more there, and exits with status 3, as jj does then.
- `musubi sync` warns when it syncs in its own process because the daemon isn't running.
- When jj can't merge this machine's operations with the hive's (as when rebases on two
  machines form a loop), the sync error names the operation to revert, rather than listing
  every operation the hive doesn't have yet.
- `jj op restore` (or `jj undo`) back to an operation in which a remote bookmark was
  conflicted, as concurrent fetches on two machines leave one, no longer moves that remote
  bookmark and the bookmark tracking it backwards on every machine. Each machine resolves the
  conflict to the commit the remote bookmark had before the restore, where the machine that
  restored and the others used to resolve it differently, and the hive merged the two to an
  older commit, which a plain `git push` from a colocated repository could then push.
- On each machine, the daemon cleans up what `jj util gc` would, short of deleting git
  objects, so that a busy hive's copies stop growing with files jj no longer reads: replaced
  extras segments, keep refs beyond the heads, and operations nothing reachable needs, once
  two weeks old. It runs once enough has built up, at most once a week, and not on battery.
- The hub's store of each hive, and each machine's copy of the shared history
  (`.jj/repo/musubi/canonical`), are now one log, with views kept as deltas: an operation
  and its view take under a kilobyte, where they took two files and the view's full size.
  Stores made before aren't read. On upgrading, a hub makes each hive again, as for a
  corrupt store, and its machines fill it; a machine's copy made before can't sync, so make
  it again with `musubi clone`.
- A hive forgets a copy that has gone unused for longer than its `musubi.forget-after`, as
  `musubi forget` would, and shows it again once it's used. `musubi join`, `create` and
  `clone` set it, and say what they set: `6h` when an agent runs them (`CODEX_THREAD_ID`,
  `CODEX_SESSION_ID` or `CLAUDE_CODE_SESSION_ID` is set), `never` otherwise, unless jj's
  config sets it already. Copies that joined before have none, and are never forgotten
  until one is set: `jj config set --repo musubi.forget-after 6h`. `musubi list` shows each
  copy, when it was last used, and when it will be forgotten.
- `musubi leave` now takes the repository out of its hive: it records what changed in the
  working copy and tells the hive, with the copy's last work, so that the other machines
  stop showing its working copy and the hub stops counting it. It keeps its working copy. It
  fails if the hub can't be reached, where it used to leave without a word, which scripts
  that run it may need to allow for; `musubi leave --force` leaves without telling the hive.
- `musubi forget <machine>` forgets a machine that went away without leaving. The other
  machines stop showing its working copy, and the hub stops counting it. If it's still
  there, it comes back as soon as it's used. See
  [Take a repository or machine out](docs/guides/manage.md#take-a-repository-or-machine-out).
- Two machines that share a name are shown as `laptop-1a2b/default@` and
  `laptop-3c4d/default@` from then on, even after one leaves, so that a name never moves to
  another machine. On upgrading, a machine that shares its name with any machine its hive
  has had, even one long gone, is shown that way from then on, as `mac-2222/default@` where
  it was `mac/default@`.
- On upgrading, a copy in which no `jj` command has recorded an operation since it joined
  stops showing on the other machines until one does: earlier releases didn't record joining
  as the copy's own. Upgrade every machine together: a machine on an earlier release that
  another forgets loses its own working copy.
- musubi completes its commands, flags, and hive and hub names in your shell, once you add a
  line to your shell's startup file, and `musubi completion <shell>` prints a completion
  script. See
  [Complete commands in your shell](docs/reference/commands.md#complete-commands-in-your-shell).
- `musubi hub rm` is now `musubi hub remove`, with `rm` still short for it, and takes a
  hive's whole name or its id, not a prefix. Each machine's copy of a removed hive now leaves
  it as it next syncs, keeping everything it has, rather than failing to sync until someone
  runs `musubi leave`.
- After a hub loses its state, `musubi join` in one copy of each hive makes it again, and the
  other machines fill it: no more `musubi leave` and `musubi create` on every machine.
  `musubi join --hub <hub>` in each copy moves a hive to another hub.
- `musubi top` watches what flows through the hubs as it happens: each hive's bytes a second
  in and out, the operations and commits that came in, and which machines are offline,
  behind, or failing to sync. Daemons now report to the hub after every sync for it. See
  [Watch every machine](docs/guides/manage.md#watch-every-machine).
- musubi has no config file of its own any more: its settings are jj's, under `musubi`, so
  `jj config list musubi` shows them. `[daemon] log` and `socket` in musubi's `config.toml`
  are now `musubi.daemon.log` and `musubi.daemon.socket` in jj's user config, where
  `musubi.hub` chooses another default hub than the one the first join saved. What musubi
  records for itself, the repositories the daemon serves and that saved hub, is now
  `state.toml` in its state directory. `MUSUBI_CONFIG_DIR` is now `MUSUBI_STATE_DIR`, which
  no longer separates a second musubi's settings: give it a `JJ_CONFIG` of its own too. On
  upgrading:

  1. Move the file. On Linux and macOS, unless you set `XDG_CONFIG_HOME` or
     `XDG_STATE_HOME`:

     ```sh
     mv ~/.config/musubi/config.toml ~/.local/state/musubi/state.toml
     ```

     On Windows, rename `%APPDATA%\musubi\config.toml` to `state.toml`. Where
     `MUSUBI_CONFIG_DIR` was set, rename `config.toml` in it to `state.toml`.
  2. Set again what you had under `[daemon]`, with `jj config set --user musubi.daemon.log`
     or `musubi.daemon.socket`.
  3. Restart the daemon: `musubi daemon install` if it starts at login, so that the service
     finds jj's config as your shell does, or else `musubi daemon restart`.

  See [Configuration](docs/reference/configuration.md#settings).
- Adding musubi's ssh key on the hub's machine no longer joins it to the last line of an
  `~/.ssh/authorized_keys` that doesn't end in a newline, which spoiled both keys and could
  lock you out of that machine.
- The daemon keeps one connection to each hub, shared by every repository it serves there,
  where it kept one, and an ssh, for each: a machine with two dozen repositories on a hub ran
  two dozen ssh processes, and the hub's machine as many `musubi hub connect`. It opens
  another for each transfer of 16 MiB or more, while it lasts; `musubi.daemon.connections =
  "one"` keeps it to one connection to each hub, as where each new ssh is costly (see
  [Configuration](docs/reference/configuration.md#this-machines)).
- When syncing can't go on, the error says how to carry on, and `musubi status` says that
  retrying won't help, where it said that the daemon keeps trying.
- `musubi clone` checks out the hive's trunk, as `jj git clone` checks out a remote's
  default branch, where it left the new copy's working copy on the root commit, with no files.
- A daemon started at login on macOS, by `musubi daemon install`, no longer fails every sync
  with "Too many open files" once it serves some two dozen repositories: the daemon and the
  hub raise their limit on open files as far as the system allows, from launchd's 256.
- The daemon and the hub log only warnings from jj's library, whose notes on every lock it
  took and index it built made up most of `daemon.log`. `--log info` brings them back, as
  does `musubi.daemon.log = "info"` for the daemon.
- A ref's lock file, left by a `git`, `jj` or musubi killed partway through updating refs,
  no longer stops musubi updating that ref, or exporting its bookmark to `.git`, until you
  delete it: once the lock is ten minutes old, musubi removes it the next time it gets in
  the way, noting it in the daemon's log, and the update works at once, or for a bookmark,
  at the next export.
- The hub and machines talk differently, so upgrade the hub and every machine together.
- On upgrading: `hive.toml` and `state.toml` have changed, and the daemon serves nothing
  until each copy joins again. On each machine, run `musubi daemon restart`, then in each
  copy delete `.jj/repo/musubi/hive.toml` and run `musubi join`.

## 0.1.0

The first release. musubi keeps a jj repository in sync across your machines by replicating
its operation log, through a hub on one machine that the others reach over ssh.

- `musubi hub` runs a hub, which serves any number of repositories, each its own hive.
- `musubi create` starts a hive from a repository, `musubi join` adds another machine's copy
  of it, and `musubi clone` makes a new copy.
- A daemon on each machine keeps its repositories in sync, and catches up after the machine
  was offline. `musubi daemon install` starts it at login, with launchd on macOS, systemd on
  Linux, or the registry on Windows.
- `musubi list` shows the hub's hives and how each copy's syncing goes, `musubi sync` syncs
  now, and `musubi leave` stops syncing a repository. `musubi hub rename` and `musubi hub rm`
  manage the hub's hives.
- musubi works with jj 0.46.0. It stops with an error rather than sync an operation that a
  newer `jj` wrote with fields jj 0.46.0 doesn't know.
- Builds for Linux (static, x86_64 and aarch64), macOS (x86_64 and aarch64), and Windows
  (x86_64 and aarch64).
- Published on crates.io as `jj-musubi`.
