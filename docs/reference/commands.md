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
| `join` | Add this machine's copy of a repository to the hive it belongs in. |
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
| `hub rm <hive>` | Remove a hive from the hub. Its store moves to the hub's `removed/` directory. |
| `hub connect` | Relay standard input and output to this machine's hub. Other machines run it over ssh; you don't need to. |

Commands that take a hive accept its name, any prefix of the name that no other hive shares,
or its id.

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
