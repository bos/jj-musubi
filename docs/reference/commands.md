# Command reference

Share repositories, check syncing, and run hubs and daemons.

Use `-h` for a summary or `--help` for all flags:

```sh
musubi --help
musubi <command> --help
```

Running `musubi` with no command is `musubi list`. [How jj-musubi works](../how-it-works.md)
explains hubs, hives, and copies.

## Share repos

| Command | Use it to |
| --- | --- |
| `create [<name>]` | Start a hive from the repo you're in, for other copies to join. |
| `join` | Join this copy to its matching hive, or recreate a lost hive on this hub or another named by `--hub`. A filesystem duplicate can take over the original's identity with `--original` once that copy is gone. |
| `clone <hive> [<dir>]` | Create a copy in a new or empty `<dir>`, making missing parents, and check out `trunk()` using local jj config. Without `<dir>`, use the hive name's last component (`dotfiles` for `bos/dotfiles`) in the current directory, even with an abbreviated hive name. The hive's creation defaults fill missing settings (name and email by default); existing settings win. Git remotes aren't copied. Objects use the hive's SHA-1 or SHA-256 hash, regardless of `git.object-hash`. |
| `leave` | Attempt a final sync, then leave the hive, keeping the repo and files. `--force` still attempts this sync but leaves even if it fails. `leave <path>` stops looking for a copy that is gone. See [Stop syncing on this machine or leave](../guides/manage.md#stop-syncing-on-this-machine-or-leave). |
| `forget <machine>` | Forget another machine's missing copy, or an old deleted copy here, even without workspaces. `musubi status` lists copies. Use the machine part of its workspace name: `laptop` for `laptop/default@`, `laptop-1a2b` for `laptop-1a2b/default@`, or its full id if prefixes collide (`laptop-1a2b3c4d/default@`). The name from `musubi list` also works if unambiguous. |
| `pause` | Stop every machine syncing this copy's hive, without syncing first, until `resume` or `pause --cancel`. `pause --cancel`, in any copy, lifts the pause, and what machines did meanwhile syncs; after `resume`, it stays on those machines. `join` and `clone` refuse a paused hive. See [Pause a whole hive](../guides/manage.md#pause-a-whole-hive). |
| `resume` | Make the paused hive again from this copy's current state, without its operation history, deleting the old history from the hub. It asks first, unless `--yes`, and refuses if the hive has work this copy hasn't received, unless `--force`. Every other copy then stops syncing for good, keeping what it has, and can't join again. See [Clean up history on every machine](../guides/manage.md#clean-up-history-on-every-machine). |

`create`, `join`, and `clone` take:

- `--hub <hub>`: the hub, as `musubi hub` prints it. On the hub's machine, its name or
  `localhost` means the hub `musubi hub` serves there without `--dir`, reached without ssh.
  Without it, they use this machine's default hub: the first it used, unless
  [`musubi.hub`](configuration.md#this-machines) names another.
- `--machine <name>`: this machine's name in the hive, which other machines show its working
  copies under. It defaults to jj's `operation.hostname`.
- `--lease <duration>`: forget this copy after that long without a local
  operation, such as `--lease 6h`. Sets `musubi.forget-after` in this copy's repo config.

`create` and `join` also take `--full-history`, to share the repo's whole operation
history rather than its current state, and `join` takes `--hive <name>` to join a hive of your
choosing. Without `--lease`, all three keep the copy's configured
[`musubi.forget-after`](configuration.md#settings), or set `never` when none is configured.
Agent-run commands have the same default. See [Set up a hub and machines](../guides/setup.md).

## See how syncing goes

| Command | Use it to |
| --- | --- |
| `list` | Show hubs' hives, local copies and sync state. `-T` uses a template; see `musubi list --help`. Use `-T 'json(self) ++ "\n"'` for JSON. |
| `status` | Report this copy's hive, hub, workspaces, last sync, pending work, other copies' activity and expiry, and daemon state. Warn of problems with sync or enabled background snapshots, such as a workspace whose name has a `/`, which keeps this copy from syncing ([why](../how-it-works.md#other-machines-workspaces)). Outside a hive, show the default hub and daemon. `-T` uses a template (`musubi status --help`); `-T 'json(self) ++ "\n"'` produces [JSON](#musubi-status-as-json). |
| `sync` | Sync this copy now. `--outgoing` inspects snapshot overhead without sending. `--approve TOKEN` approves the inspected history. `--prune OPERATION...` snapshots current edits and deletions, then discards unpublished operations while preserving current work and explicit change versions. Add `--dry-run` to preview recorded history without snapshotting or changing it. See [snapshot cleanup](../guides/snapshots.md). |
| `top` | Watch hub traffic and machines that are offline, behind, or failing. |

`status` reads local state without starting the daemon or contacting the hub. It always exits 0;
warnings and hints go to standard error.

Sending pauses above 1,000 extra file paths or 64 MiB in outgoing snapshots, beyond explicit
change history and shared content; receiving continues. `musubi sync --outgoing` lists extra
paths without snapshotting or contacting the hub. `Within publication budget` means the work
fits, not that it was sent. See [Snapshot limits and cleanup](../guides/snapshots.md) for the
workflow and [configuration](configuration.md#each-repos) for setting semantics.

### `musubi status` as JSON

`musubi status -T 'json(self) ++ "\n"'` prints one JSON object. Times are seconds since the Unix
epoch; durations are seconds. Unknown or inapplicable values are `null`, where `-T` keywords
give an empty string or false. The keyword `problem` maps to `not_synced`, else `hive.error`;
`status` comes from `hive.last_sync`, except during a snapshot hold, when it is
`sending held: snapshot publication budget`; `daemon_running` is `daemon.running`.

| Field | Value |
| --- | --- |
| `repository` | The workspace containing the current directory. `null` outside a jj repo or if unavailable; `not_synced` explains unavailable state. |
| `hive` | The repo's part in its hive, or `null` outside one: `name`, `id`, `hub`, `machine` (this machine's name in the hive), `head` (the hive's head, as of the last sync), `last_sync`, `error` (why its syncing fails), `paused` (while the last sync found the hive paused, who paused it, `by`, and when, `at`; else `null`), `sent` (whether the hub has all this machine's work, as far as the last sync tells), `forgotten`, `working_copies` (each with `name`, `commit`, `change` and `description`), and `copies` (each with `machine`, `this`, `last_used`, and `forget_after`, `null` for never). |
| `hive.snapshot_issues` | For enabled background snapshots, maps each affected local workspace name to the reason its latest attempt was skipped. The key is omitted when there are no issues. |
| `not_synced` | Why a recorded copy does not sync (such as a filesystem duplicate), or why its state is unavailable (such as a missing directory or repo). `hive` is `null` in these cases; otherwise `not_synced` is `null`. See [Move, copy or restore a repo](../guides/manage.md#move-copy-or-restore-a-repo). |
| `default_hub` | The hub commands use without `--hub`, or `null`. |
| `daemon` | `running` (`null` if unknown), `error` (why its state is unknown or a running daemon is unreachable), `pid`, `serving` (whether it serves this repo), `served` (repo count), `at_login` (whether `daemon install` set it to start on its own: at login, or at boot on illumos), `socket`, `log`, and `upgrade_failed` (`release` and `error` if its last upgrade to a release newer than this command failed, otherwise `null`). |

For unattended checks, read `daemon.running`, `daemon.serving`, `hive.error`, `hive.last_sync`
and `hive.sent` on each machine, allowing for expected offline periods. An old successful sync
isn't evidence of current health; a sender's `hive.sent` does not show that every receiver has
caught up. Neither `status` nor `top --once` signals reported problems with a failing exit status.
See [Monitor syncing](../guides/manage.md#check-syncing) for the workflow.

### Read `musubi top`

`musubi top` asks the known hubs for their reports and refreshes every five seconds.

```text
musubi top: 1 hub, every 5s
This machine's daemon is running, serving 2 repositories.
Hub devbox: up 3h12m, musubi 0.1.0, 2 hives.
Issues:
  app: gpu not heard from in 6m: offline, or its daemon isn't running

HIVE      HEAD  IN/s     OUT/s    OPS  COMMITS  MACHINES  ISSUES
app       #412  12 KiB/s 40 KiB/s 96   51       2/3       1
dotfiles  #88   0 B/s    0 B/s    3    1        1/1

app since the hub started:
  received 4.1 MiB and sent 12 MiB
  96 operations came in, with 51 commits, and 180 went out
  40 pushes moved the head, and 2 found it moved already
  MACHINE  HEARD   AT    MUSUBI  STATE
  devbox   3s ago  #412  0.1.0   up to date
  gpu      6m ago  #401  0.1.0   not heard from in 6m: offline, or its daemon isn't running
  laptop   2s ago  #412  0.1.0   up to date

  AGO     HEAD  FROM    OPS  COMMITS  WHAT
  2s ago  #412  laptop  1    1        snapshot working copy
```

The hive rows show transfer rates and incoming operations and commits since hub startup. Pick
a hive with the arrow keys to see its machines and latest updates, named as `jj op log` names
them.

| Field | Meaning |
| --- | --- |
| `HEAD` | The hub's current update number. |
| `AT` | A machine's last reported update; compare with `HEAD` to see if it caught up. |
| `IN/s`, `OUT/s` | Bytes per second received and sent by the hub. |
| `OPS`, `COMMITS` | Incoming operations and commits since the hub started. |
| `MACHINES` | Up-to-date reports over listed machines: `2/3` means two of three are up to date. |
| `ISSUES` | Problems reported for the hive. |
| `STATE` | The machine's reported sync state. A sleeping machine may be quiet without failing. |

Issues list unreachable hubs, failed requests and machines offline, behind or failing to sync.
An offline machine appears in the issues list when first found quiet; its row stays red and
`ISSUES` still counts it. It appears again if heard from and then quiet again. See
[troubleshooting](../troubleshooting.md#start-with-this-copy) for recovery.

`q` quits; space, Enter or `t` refreshes; `d`, `s` or `i` sets the refresh interval; Ctrl-L
redraws. `+` and `-` refresh less or more often. Without a terminal, or with `--once`, it prints
one snapshot without rates. `top` sends no unattended alerts; `--once` exits successfully even
with issues.

Reports live in hub memory. After a restart, machines reappear at their next sync, within half
a minute. Reports expire after a day without contact.

## Run the daemon

| Command | Use it to |
| --- | --- |
| `daemon install` | Start the daemon now and at login (at boot on illumos). |
| `daemon uninstall` | Stop the daemon and remove login startup (boot startup on illumos). |
| `daemon start` | Start the daemon in the background, unless it is running. |
| `daemon stop` | Stop background syncing for copies served by this daemon, keeping memberships and login startup (boot startup on illumos). The hub keeps running; explicit `sync` still works. |
| `daemon restart` | Stop the daemon and start it again, as after upgrading jj-musubi. |
| `daemon` | Run the daemon in the foreground, logging to the terminal. |

`create`, `join`, and `clone` start a missing daemon and wait for the first sync. `sync` uses
the daemon if running, or syncs directly with a warning. Each shows progress on a terminal.

## Run a hub

| Command | Use it to |
| --- | --- |
| `hub` | Run a hub, in the foreground. `--dir` chooses its directory, and `--advertise` the host name it tells other machines to use. |
| `hub install` | Start the hub now and at login, or at boot with `--at-boot`, as your user. Boot installation uses sudo; run the command without sudo. On illumos it starts at boot either way; installing it uses pfexec and the Service Management rights profile (see [illumos](../guides/setup.md#illumos)). Accepts the same flags as `hub`. macOS, Linux and illumos only. |
| `hub uninstall` | Stop the hub and remove its login or boot service. Removing a boot service uses sudo; on illumos, removing the hub's SMF service uses pfexec. |
| `hub rename <hive> <new-name>` | Rename a hive. |
| `hub remove <hive>` | Remove a hive from the hub. Each machine's copy leaves it as it hears. `rm` is an alias. |
| `hub connect` | Relay standard input and output to this machine's hub. Other machines use it over ssh. |

Hives can be named by an unambiguous prefix or id. `hub remove` requires a whole name or id.

`musubi hub` prints commands, including when local commands can omit `--hub`. It recognizes
symlinks to the default hub directory. If its saved path is too long, use the shorter `--hub`
path it prints.

## Complete commands in your shell

Add the line for your shell to complete commands, flags, paths, hives and hubs as you type.
Start a new shell after upgrading: the completion interface can change.

| Shell | Startup file | Line |
| --- | --- | --- |
| bash | `~/.bashrc` | `source <(COMPLETE=bash musubi)` |
| zsh | `~/.zshrc`, after `compinit` | `source <(COMPLETE=zsh musubi)` |
| fish | `~/.config/fish/config.fish` | `COMPLETE=fish musubi \| source` |
| elvish | `~/.config/elvish/rc.elv` | `eval (E:COMPLETE=elvish musubi \| slurp)` |
| PowerShell | `$PROFILE` | `$env:COMPLETE = "powershell"; musubi \| Out-String \| Invoke-Expression; Remove-Item Env:\COMPLETE` |

Hive completion waits up to two seconds for the default hub, then falls back to hives with
copies on this machine using that hub.

`musubi completion <shell>` prints a static script for commands, flags and paths, without hive
or hub names. Use it for nushell or packaged completion files. It accepts `bash`, `elvish`,
`fish`, `nushell`, `powershell` or `zsh`:

```sh
source <(musubi completion zsh)
```

## Investigate

`musubi debug` investigates hives; it is omitted from `musubi --help`.

Operations include each machine's Git refs and workspaces, so their ids differ between copies
and the hub. Commands such as `jj op restore <id>` take the local id. Run
`musubi debug op-id <id>` here to get its hive id, then run `musubi debug op-id` with that id
in the other machine's repo to find its local counterpart.

| Command | Use it to |
| --- | --- |
| `debug op-id <id>` | Translate an operation id between this machine's id and the hive's. |

## Global options

| Option | Effect |
| --- | --- |
| `--color <when>` | Choose when to colour what the command prints: `always`, `never`, `debug` (showing labels), or `auto` (only on a terminal). Without it, jj's `ui.color` says. See [Colours](configuration.md#colours). |
| `--log <filter>` | Choose what this command logs, as a filter in `RUST_LOG`'s syntax, such as `debug` or `musubi_sync=debug`. See [Logging](configuration.md#logging). |
| `--socket <path>` | Talk to the daemon on another control socket: an absolute path, or one starting with `~/`. See [Files and directories](configuration.md#files-and-directories). |

If a reader closes stdout early, as in `musubi list | head`, the command finishes its work,
stops printing and exits 3, as jj does.
