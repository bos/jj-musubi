# Changelog

## Unreleased

- A repo with a workspace of yours whose name has a `/`, such as `feat/x`, doesn't sync until
  you rename it, since other machines show each other's workspaces by names like
  `laptop/default`. Before, other machines showed it as `laptop/feat/x`. `musubi sync`,
  `musubi status`, `musubi create`, `musubi join`, `musubi resume` and `musubi leave` say which
  workspace it is and what to run: `jj workspace rename <new name>` in its directory, with no
  `/` in the new name. If instead it is a workspace you ran `jj workspace forget` on earlier,
  whose name another machine's workspace now uses, don't rename it: move out any ignored files
  you want to keep, then run `jj workspace remove <name>`, which saves the rest in a commit and
  deletes the directory. If the directory is missing, as on a disk not mounted, mount the disk
  and rename the workspace there, or run `jj workspace forget <name>` from another workspace of
  the repo. Syncing then picks up again, with what you did meanwhile. After upgrading, run `musubi daemon restart` on every machine: a
  daemon already running keeps the old behaviour until it restarts.

- On Windows, the paths musubi prints for a copy, as in `musubi list`, in the daemon's log and
  in hints that name a directory, no longer start with `\\?\`, the form cmd can't `cd` to:
  `C:\Users\me\app`, not `\\?\C:\Users\me\app`. A path that needs the prefix keeps it: one
  on a network share (`\\?\UNC\...`), one too long without it, or one with a name Windows
  reserves. A copy joined by an earlier release needs nothing done: the first musubi command
  to read `state.toml` rewrites its path. That conversion goes after 2027-02-23. On a machine
  that hasn't run musubi before then, `state.toml` keeps the old spelling, which no longer
  equals the path musubi finds the copy at: `musubi leave <path>` doesn't find the copy, and
  joining it again adds a second entry for it. Running any musubi command there before it
  upgrades past that date avoids this.

- `jj op abandon` of operations the hive already has no longer reaches other machines. The
  copy where you ran it stops syncing, with "this repository lost history the hive has (was
  `jj op abandon` run?)", and the other machines keep the operations; [Rescue work in a new
  copy](docs/troubleshooting.md#rescue-work-in-a-new-copy) says how to carry on there. Passing
  an abandon on never removed the abandoned data from the hub, or from other machines' disks.
  `musubi pause` and `musubi resume`, coming in this release, will remove data such as a
  committed secret from every machine. Abandoning operations from before a copy joined, or
  ones it hasn't sent yet, works as before.

- When a temp cleaner deletes the daemon's socket, the daemon now notices at once where the
  system reports the deletion, and listens there again, rather than at its next check a few
  seconds later; otherwise it still notices within a few seconds. So a `musubi` command run
  just after no longer waits for the daemon, or says it isn't listening. A daemon already
  running keeps checking only every few seconds until it restarts: run `musubi daemon
  restart` after upgrading.

- A copy that was away before its first sync finished, or that the hive forgot, no longer
  stops syncing because other machines abandoned operations meanwhile.

- When `jj op abandon` leaves a copy unable to tell which of the hive's operations it dropped,
  `musubi sync` no longer asks you to run `jj op integrate`. Such a copy now stops syncing
  with "this repository lost history the hive has", as any copy that lost history the hive
  has does. If you restore what you abandoned with `jj op integrate` before syncing again,
  the copy syncs on.

- musubi removes the files that earlier releases kept in a copy's `musubi` directory to pass
  `jj op abandon` on (`records.json`, `superseded`, `hub-renamings` and `originals`) the
  first time it opens the copy: nothing needs doing on upgrading. A copy that held drops it
  hadn't sent, or was taking records, keeps `records.json` and stops syncing, until a release
  after 2027-02-21, which no longer looks for the file.

- Upgrade the hub and every machine together: machines and hubs from before and after this
  release refuse each other ([Upgrade jj-musubi](docs/guides/upgrading.md)). Run `musubi sync`
  on every machine first, so that its work reaches the hub. A copy that ran `jj op abandon`
  and hadn't passed it on before upgrading stops with "this repository lost history the hive
  has". A hive where an earlier release passed `jj op abandon` on is made again, empty, the
  first time the upgraded hub opens it, and its machines fill it at their next sync, as after
  the hub loses its state. Nothing needs doing, but a machine that was offline when an earlier
  release passed on a `jj op abandon`, and so never took it, brings the abandoned operations
  back. A hub from a release after 2027-02-21 still makes such a hive again, but takes it for
  one whose files are damaged.

- `musubi hub` makes a new hub in `~/.local/share/musubi/hub` (`$XDG_DATA_HOME/musubi/hub`,
  or `%LOCALAPPDATA%\musubi\hub` on Windows) instead of `~/musubi-hub`. A hub already in
  `~/musubi-hub` stays there, and musubi keeps serving it, but a release after 2027-02-21
  will stop looking for it there. To keep it there for good, run
  `jj config set --user musubi.hub-dir '~/musubi-hub'` on the hub's machine. Don't move the
  directory: repositories on the hub's machine, and any service that runs the hub, name it by
  its path. A hub you run with `--dir`, that `musubi.hub-dir` names, or that
  `musubi hub install` set up isn't affected.

- `jj op restore` to an operation from before a second machine named `laptop` joined, or
  before you ran `musubi forget` on the laptop, brings back `laptop/default`. If you then ran a
  `jj` command and `jj op abandon` of the restore before the next sync, every machine showed the
  laptop's workspace as this machine's too, as `desk/laptop/default` on a machine named `desk`.
  It now stays the laptop's. Upgrading doesn't remove such a workspace: run
  `jj workspace forget laptop/default` on `desk`.

- Use the [jj-musubi Dev Container Feature](docs/guides/setup.md#use-musubi-in-a-dev-container)
  to install `musubi` and start its daemon in GitHub Codespaces or other dev containers.

- Set `musubi.hub-dir` in jj's user config to choose the default hub's data directory on
  the hub's machine. See [Configuration](docs/reference/configuration.md#this-machines).

- `musubi join` and `musubi create` try fetching conflicted Git remote bookmarks after their
  first sync, with a 30-second limit per remote, then sync the result. Forward moves still
  come from either copy. A fresh fetch can resolve conflicts from rewritten upstream history
  while preserving local work and checkout files. An unavailable remote leaves a warning and
  the conflict. Ordinary sync does not fetch Git remotes. No action is needed on upgrading.

- Set `musubi.auto-snapshot = true` in jj's config to record edits in local workspaces while
  the daemon runs, even when an editor or agent never runs `jj`. Run `musubi daemon restart`
  after replacing the executable by hand so the command and daemon use the same build. See
  [Record saves automatically](docs/guides/working-across-machines.md#record-saves-automatically).

- On illumos, `musubi daemon install` and `musubi hub install` set up an SMF service,
  `svc:/site/musubi/daemon:<you>` (or `hub`), that starts at boot and runs as you. Setting it
  up, and starting and stopping it, needs the Service Management rights profile, which amounts
  to root on that machine ([illumos](docs/guides/setup.md#illumos)). Before, both refused on
  illumos. Nothing needs doing on upgrading; to use it, run `musubi daemon install`,
  and `musubi hub install` on the hub's machine.

- `contrib/upgrade-from-source` works on illumos, whose `tar` it used to fail with. If you
  copied it into your dotfiles, copy it again.

- A `jj` command that runs while musubi applies another machine's rebase can commit a rebase
  that loops with it. jj then panics ("graph has cycle") on every command. The sync error
  used to say jj kept working, and named operations whose revert panicked too. It now says
  that jj fails, and names this machine's operation to revert, with the command that works:
  `jj --at-op <id> op revert <id>`. That undoes only that operation; the other machine's
  rebase stays.

## 0.47.1

This is the initial release.
