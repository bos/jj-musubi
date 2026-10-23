# Command reference

Built-in help is the reference for every flag:

```sh
musubi --help
musubi <command> --help
```

`-h` gives a summary, and `--help` the full text. Running `musubi` with no command is
`musubi list`.

## Share repositories

| Command | Use it to |
| --- | --- |
| `create [<name>]` | Start a hive from the repository you're in, for other copies to join. |
| `join` | Add this machine's copy of a repository to the hive it belongs in. In a copy that is part of a hive, make the hive again on a hub that has lost it, or on another hub given with `--hub`. |
| `clone <hive> <dir>` | Make a new copy of a hive on this machine. |
| `leave` | Stop syncing the repository you're in. It keeps everything it has. |

`create`, `join`, and `clone` take:

- `--hub <hub>`: the hub, as `musubi hub` prints it. Leave it out to use this machine's
  default hub, the first it used.
- `--machine <name>`: this machine's name in the hive, which other machines show its
  working copy under. It defaults to jj's `operation.hostname`.

`create` and `join` also take `--full-history`, to share the repository's whole operation
history rather than its current state, and `join` takes `--hive <name>` to join a hive of
your choosing. See [Set up a hub and machines](../guides/set-up.md).

## See how syncing goes

| Command | Use it to |
| --- | --- |
| `list` | Show the hubs' hives, this machine's copies of them, and whether each is syncing. In a hive's repository, also show its details. `status` is an alias. |
| `sync` | Sync the repository you're in now, and see at once whether it worked. |

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
it is running, and otherwise syncs by itself.

## Run a hub

| Command | Use it to |
| --- | --- |
| `hub` | Run a hub, in the foreground. `--dir` chooses its directory, and `--advertise` the host name it tells other machines to use. |
| `hub rename <hive> <new-name>` | Rename a hive. |
| `hub remove <hive>` | Remove a hive from the hub, by its whole name or id. Each machine's copy leaves it as it hears. `rm` is short for it. |
| `hub connect` | Relay standard input and output to this machine's hub. Other machines run it over ssh; you don't need to. |

Commands that take a hive accept its name, any prefix of the name that no other hive shares,
or its id; `hub remove` takes only a whole name or an id.

## Complete commands in your shell

musubi completes its commands, flags, and paths in bash, zsh, fish, elvish, and PowerShell,
and also the names of hives and hubs. To have it do so, run the line for your shell in its
startup file. Your shell then asks musubi as you type. The line sets up how it asks, which
may change in a new release of musubi, so run it again, as by starting a new shell, after
upgrading.

| Shell | Startup file | Line |
| --- | --- | --- |
| bash | `~/.bashrc` | `source <(COMPLETE=bash musubi)` |
| zsh | `~/.zshrc`, after `compinit` | `source <(COMPLETE=zsh musubi)` |
| fish | `~/.config/fish/config.fish` | `COMPLETE=fish musubi \| source` |
| elvish | `~/.config/elvish/rc.elv` | `eval (E:COMPLETE=elvish musubi \| slurp)` |
| PowerShell | `$PROFILE` | `$env:COMPLETE = "powershell"; musubi \| Out-String \| Invoke-Expression; Remove-Item Env:\COMPLETE` |

Completing a hive's name asks the default hub for its hives, and your shell waits up to two
seconds for the answer. If none comes in time, as from a hub reached through a slow
`ProxyCommand`, musubi completes the hives of this machine's copies on that hub instead.

`musubi completion <shell>` instead prints a script that completes commands, flags, and
paths, but not hive or hub names, without running musubi as you type. Use it in nushell, which
completion as you type doesn't support, or to install a completion file with a package. It
takes `bash`, `elvish`, `fish`, `nushell`, `powershell`, or `zsh`:

```sh
source <(musubi completion zsh)
```

## Investigate

`musubi debug` holds tools for investigating a hive, and is left out of `musubi --help`.

| Command | Use it to |
| --- | --- |
| `debug op-id <id>` | Translate an operation id between this machine's id and the hive's. |

## Global options

| Option | Effect |
| --- | --- |
| `--log <filter>` | Choose what this command logs, as a filter in `RUST_LOG`'s syntax, such as `debug` or `musubi_sync=debug`. See [Logging](configuration.md#logging). |
| `--socket <path>` | Talk to the daemon on another control socket. See [Files and directories](configuration.md#files-and-directories). |
