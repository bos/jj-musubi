# Debugging musubi

Work in the affected repository. Report findings before changing the hive, daemon, or hub.

1. Run `musubi status`. Read its warnings and hints, then the end of the daemon log it names.
2. Run `musubi sync` to retry and see errors directly.
3. Run `musubi top --once` to see which machines are offline, behind, or failing.
4. Find the error in the [troubleshooting
   guide](https://github.com/bos/jj-musubi/blob/main/docs/troubleshooting.md).

## Common problems

- **Daemon stopped:** run `musubi daemon start`.
- **`jj cannot merge this machine's operations with the hive's`:** the message names a
  `jj op revert <id>`, which reverts one of this machine's own operations, or if it names none,
  lists this machine's operations the hive lacks, newest first, one of which conflicts with
  the hive's. Tell the user what `jj op show <id>` says the operation did, and revert it with
  their agreement.
- **`jj cannot merge this machine's concurrent operations: ... merge commit on the root
  commit`:** a jj bug that makes every jj command fail. Find the head in
  `.jj/repo/op_heads/heads` whose operation made the merge commit, as the message says, and
  with the user's agreement run `jj --at-op <head> op revert @` there.
- **Protocol mismatch:** install the same release everywhere, including the hub, then run
  `musubi daemon restart` on upgraded machines. Also restart if musubi reports an old daemon.
- **`history no longer matches the hive's`:** this copy can no longer sync, but its work
  remains locally. With the user's agreement, do as the message says: make a new copy with
  `musubi clone`, bring across the work this copy made since its last sync, then run
  `musubi leave --force` in this one. Other machines show the old copy until it is forgotten:
  run `musubi forget <machine>` in the new copy, naming it as `jj workspace list` shows it.
- **jj can't find an operation id from another machine:** operation ids differ between
  machines. Run `musubi debug op-id <id>` on the machine the id came from to get the hive's
  id, then `musubi debug op-id <hive id>` here to get this machine's.

## Debug logs

Without a daemon, `musubi --log musubi_sync=debug sync` logs a sync in its own process.
To log the daemon's requests, run `musubi daemon stop`, then
`musubi --log musubi_sync=debug daemon` in the foreground. Stop it when finished and run
`musubi daemon start` to resume background syncing.

Don't delete `.jj/repo/musubi/` or the hub's directory as a debugging step. Upgrade jj and
musubi together: each musubi release supports one jj release.
