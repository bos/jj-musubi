# Debugging musubi

Work in the affected repository. Report findings before changing the hive, daemon, or hub.

1. Run `musubi status`. Read its warnings and hints, then the end of the daemon log it names.
2. Run `musubi sync` to retry and see errors directly.
3. Run `musubi top --once` to see which machines are offline, behind, or failing.
4. Find the error in the [troubleshooting
   guide](https://github.com/bos/jj-musubi/blob/main/docs/troubleshooting.md).

## Common problems

- **Daemon stopped:** run `musubi daemon start`.
- **`jj cannot merge this machine's operations with the hive's`:** run the `jj op revert <id>`
  named in the message. It reverts one of this machine's own operations.
- **Protocol mismatch:** install the same release everywhere, including the hub, then run
  `musubi daemon restart` on upgraded machines. Also restart if musubi reports an old daemon.
- **`(was jj op abandon run?)`:** this copy can no longer sync, but its work remains locally.
  With the user's agreement, follow the error's instructions to replace it and preserve work
  the hive lacks. Forget the old copy with `musubi forget <machine>`: use `laptop` for
  `laptop/default@`.
- **Unrecognised operation id:** ids differ between machines. Run `musubi debug op-id <id>` on
  the source machine to get the hive's id, then pass that id to the same command here.

## Debug logs

Without a daemon, `musubi --log musubi_sync=debug sync` logs a sync in its own process.
To log the daemon's requests, run `musubi daemon stop`, then
`musubi --log musubi_sync=debug daemon` in the foreground. Stop it when finished and run
`musubi daemon start` to resume background syncing.

Don't delete `.jj/repo/musubi/` or the hub's directory as a debugging step. Upgrade jj and
musubi together: each musubi release supports one jj release.
