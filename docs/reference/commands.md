# Command reference

Every musubi command, grouped by task. Built-in help is the reference for flags: `-h` gives a
summary, and `--help` the full text.

```sh
musubi --help
musubi <command> --help
```

Running `musubi` with no command is `musubi list`. [How musubi works](../how-it-works.md)
explains hubs, hives, and copies.

## Share repositories

| Command | Use it to |
| --- | --- |
| `create [<name>]` | Start a hive from the repository you're in, for other copies to join. |
| `join` | Add this machine's copy of a repository to the hive it belongs in. In a copy already part of a hive, make the hive again on a hub that has lost it, or on another hub given with `--hub`. |
| `clone <hive> <dir>` | Make a new copy of a hive on this machine. |
| `leave` | Take the repository you're in out of its hive, telling the hive, and stop syncing it. It keeps everything it has. `--force` leaves without telling the hive, if its hub can't be reached. |
| `forget <machine>` | Forget another machine's copy that went away without leaving. Name the machine as its working copies are named here: `laptop` for `laptop/default@`, or `laptop-1a2b` for `laptop-1a2b/default@`. The name `musubi list` gives it also works, if no other machine has that name. |

`create`, `join`, and `clone` take:

- `--hub <hub>`: the hub, as `musubi hub` prints it. Without it, they use this machine's
  default hub: the first it used, unless [`musubi.hub`](configuration.md#this-machines)
  names another.
- `--machine <name>`: this machine's name in the hive, which other machines show its working
  copies under. It defaults to jj's `operation.hostname`.

`create` and `join` also take `--full-history`, to share the repository's whole operation
history rather than its current state, and `join` takes `--hive <name>` to join a hive of your
choosing. All three set the copy's [`musubi.forget-after`](configuration.md#settings)
unless jj's config sets it already. See [Set up a hub and machines](../guides/set-up.md).

## See how syncing goes

| Command | Use it to |
| --- | --- |
| `list` | Show the hubs' hives, this machine's copies of them, and whether each is syncing. `-T` prints only the hubs, hives and copies, with a template of your own, as jj's list commands do (see `musubi list --help`); `-T 'json(self) ++ "\n"'` gives them as JSON, for a script. |
| `status` | Show what musubi does with the repository you're in: its hive, hub and machine name, its last sync, whether the hub has this machine's latest work, each machine's working copies, each copy in the hive with when it was last used and when it will be forgotten, and the daemon's process, socket and log. Warn of what keeps it from syncing, and say what to do. Outside a hive, show the default hub and the daemon. `-T` prints only the report, with a template of your own (see `musubi status --help`); `-T 'json(self) ++ "\n"'` gives it as JSON, for a script or an agent (see [below](#musubi-status-as-json)). |
| `sync` | Sync the repository you're in now, and see at once whether it worked. |
| `top` | Watch what flows through the hubs, and which machines are offline, behind, or failing, as it happens. |

`status` never starts the daemon or asks the hub, so it answers at once, and it exits 0
whatever it reports: run it from a script, an agent, or a shell prompt. Its warnings and hints
go to standard error, as jj's do.

### `musubi status` as JSON

`musubi status -T 'json(self) ++ "\n"'` prints one JSON object, with times as seconds since
the Unix epoch, and durations in seconds. A value that can't be told, or doesn't apply, is
`null`, where `-T`'s keywords give an empty string or false. The keyword `problem` is
`hive.error` here, `status` comes from `hive.last_sync`, and `daemon_running` is
`daemon.running`.

| Field | Value |
| --- | --- |
| `repository` | The workspace the current directory is in, or `null` outside a jj repository. |
| `hive` | The repository's part in its hive, or `null` outside one: `name`, `id`, `hub`, `machine` (this machine's name in the hive), `head` (the hive's head, as of the last sync), `last_sync`, `error` (why its syncing fails), `sent` (whether the hub has all this machine's work, as far as the last sync tells), `forgotten`, `working_copies` (each with `name`, `commit`, `change` and `description`), and `copies` (each with `machine`, `this`, `last_used`, and `forget_after`, `null` for never). |
| `default_hub` | The hub commands use without `--hub`, or `null`. |
| `daemon` | `running`, or `null` with `error` saying why that can't be told; `pid`; `serving` (whether it serves this repository); `served` (how many repositories it serves); `at_login`; `socket`; and `log`. |

## Run the daemon

| Command | Use it to |
| --- | --- |
| `daemon install` | Start the daemon at login from now on, and now. |
| `daemon uninstall` | Stop starting the daemon at login, and stop it. |
| `daemon start` | Start the daemon in the background, unless it is running. |
| `daemon stop` | Stop the daemon. |
| `daemon restart` | Stop the daemon and start it again, as after upgrading musubi. |
| `daemon` | Run the daemon in the foreground, logging to the terminal. |

`create`, `join`, and `clone` start the daemon if it isn't running. `sync` uses the daemon if
it is running, and otherwise syncs by itself, saying that the daemon isn't running.

## Run a hub

| Command | Use it to |
| --- | --- |
| `hub` | Run a hub, in the foreground. `--dir` chooses its directory, and `--advertise` the host name it tells other machines to use. |
| `hub rename <hive> <new-name>` | Rename a hive. |
| `hub remove <hive>` | Remove a hive from the hub. Each machine's copy leaves it as it hears. `rm` is an alias. |
| `hub connect` | Relay standard input and output to this machine's hub. Other machines run it over ssh; you don't need to. |

Commands that take a hive accept its name, any prefix of the name that no other hive shares,
or its id. `hub remove` takes only a whole name or an id.

## Complete commands in your shell

musubi completes its commands, flags, and paths, and the names of hives and hubs, in bash,
zsh, fish, elvish, and PowerShell. Add the line for your shell to its startup file; your shell
then asks musubi as you type. How it asks can change between releases, so start a new shell
after upgrading.

| Shell | Startup file | Line |
| --- | --- | --- |
| bash | `~/.bashrc` | `source <(COMPLETE=bash musubi)` |
| zsh | `~/.zshrc`, after `compinit` | `source <(COMPLETE=zsh musubi)` |
| fish | `~/.config/fish/config.fish` | `COMPLETE=fish musubi \| source` |
| elvish | `~/.config/elvish/rc.elv` | `eval (E:COMPLETE=elvish musubi \| slurp)` |
| PowerShell | `$PROFILE` | `$env:COMPLETE = "powershell"; musubi \| Out-String \| Invoke-Expression; Remove-Item Env:\COMPLETE` |

To complete a hive's name, musubi asks the default hub for its hives, and your shell waits up
to two seconds for the answer. If none comes in time, as through a slow `ProxyCommand`, musubi
completes the hives of this machine's copies on that hub instead.

`musubi completion <shell>` instead prints a static script, which completes commands, flags,
and paths but not hive or hub names. Use it for nushell, which completion as you type doesn't
support, or to install a completion file with a package. It takes `bash`, `elvish`, `fish`,
`nushell`, `powershell`, or `zsh`:

```sh
source <(musubi completion zsh)
```

## Investigate

`musubi debug` holds tools for investigating a hive. It is left out of `musubi --help`.

| Command | Use it to |
| --- | --- |
| `debug op-id <id>` | Translate an operation id between this machine's id and the hive's. |

## Global options

| Option | Effect |
| --- | --- |
| `--color <when>` | Choose when to colour what the command prints: `always`, `never`, `debug` (showing labels), or `auto` (only on a terminal). Without it, jj's `ui.color` says. See [Colours](configuration.md#colours). |
| `--log <filter>` | Choose what this command logs, as a filter in `RUST_LOG`'s syntax, such as `debug` or `musubi_sync=debug`. See [Logging](configuration.md#logging). |
| `--socket <path>` | Talk to the daemon on another control socket. See [Files and directories](configuration.md#files-and-directories). |

When whatever reads a command's output stops before the end, as `head` does in `musubi list |
head`, the command still does all it would, printing nothing more there, and exits with
status 3, as jj does then.
