# Changelog

## Unreleased

- A workspace whose name has a `/`, such as `feat/x`, is no longer shown on other machines,
  which use names like `laptop/default` for each other's workspaces. It keeps working on its
  own machine, and `musubi status` and the daemon's log warn about it. After you upgrade a
  machine, other machines stop showing that machine's workspaces with a `/` in their names (as
  `desk/feat/x`) the next time it syncs; a machine not yet upgraded goes on showing its own. To
  show one again, run `jj workspace rename <new name>` in that workspace, with no `/` in the new
  name.

- A repo with other machines' workspaces no longer stops syncing with "this repository's
  history no longer matches the hive's" after `jj op abandon` of its whole history, a `jj`
  command, and `jj util gc` before the daemon synced. No action is needed on upgrading.

- `musubi hub` makes a new hub in `~/.local/share/musubi/hub` (`$XDG_DATA_HOME/musubi/hub`,
  or `%LOCALAPPDATA%\musubi\hub` on Windows) instead of `~/musubi-hub`. A hub already in
  `~/musubi-hub` stays there, and musubi keeps serving it, but a release after 2027-02-21
  will stop looking for it there. To keep it there for good, run
  `jj config set --user musubi.hub-dir '~/musubi-hub'` on the hub's machine. Don't move the
  directory: repositories on the hub's machine, and any service that runs the hub, name it by
  its path. A hub you run with `--dir`, that `musubi.hub-dir` names, or that
  `musubi hub install` set up isn't affected.

- `jj op abandon` of a machine's latest operation, while the machine was taking another
  machine's abandon (or after a crash while it did), could bring back an operation the other
  abandon dropped, in about half the runs. Upgrading doesn't repair a repository this already
  happened to: abandon that operation again.

- After `jj op abandon` of a machine's history, another machine's workspace no longer shows
  up as that machine's, as `m3/m1/default`, when a `jj` command run on the history from
  before the abandon (with `--at-op`, or one already running) finishes afterwards, or when
  a second abandon of the whole history came between, or when jj merged two such commands.
  The same holds when another machine renamed one of its workspaces meanwhile and an
  operation from before the second abandon was then abandoned itself.

- `jj op restore` to an operation from before a second machine named `laptop` joined, or
  before you ran `musubi forget` on the laptop, brings back `laptop/default`. If you then ran a
  `jj` command and `jj op abandon` of the restore before the next sync, every machine showed the
  laptop's workspace as this machine's too, as `desk/laptop/default` on a machine named `desk`.
  It now stays the laptop's. Upgrading doesn't remove such a workspace: run
  `jj workspace forget laptop/default` on `desk`.

- Keep the repo usable when `jj op abandon` removes an old operation head while the daemon
  is putting rewritten history back.

- Two `jj op abandon` commands in quick succession could bring back the operations the
  second one dropped, and undo the `jj` command run after it. Upgrading doesn't repair a
  repository this already happened to: abandon those operations again, and run the command
  again.

- After `jj op abandon`, a daemon that stopped partway through rewriting local history, and
  lost its translation cache before restarting, finishes the rewrite instead of failing every
  sync with "its local operation is missing". No action is needed on upgrading.

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

## 0.47.1

This is the initial release.
