# Understanding jj-musubi safety

jj-musubi shares finished and unfinished work and repository history between your machines.
Mistakes and bugs can affect every copy.

## What a sync can change

Each machine keeps its own repo and checkout. Background sync leaves checked-out files
alone: received work becomes available in the repo, and you choose when to check it out.
If another machine rewrites the commit you're using, jj reports a stale working copy;
[update it when you're
ready](guides/working-across-machines.md#when-another-machine-rewrites-your-working-copy).

Commits, bookmarks, Git refs and repo operations are shared. A mistaken rewrite,
restore or operation abandon can reach every machine. Concurrent edits can leave conflicted
bookmarks or divergent changes, as in local jj workspaces. The [working
guide](guides/working-across-machines.md) covers resolving conflicts and undoing shared changes.

Sync sees edits after jj snapshots them. The daemon, the background sync process, sends those
snapshots without creating them.

If the hub that passes history between machines loses its state, surviving repos can
[rebuild it](guides/manage.md#replace-or-move-a-hub) from retained work. Work held only on a lost
machine still needs that machine's backup.

## Pausing syncing, or leaving a hive

Pause background syncing for the copies this daemon serves:

```sh
musubi daemon stop
```

This leaves the hub and other machines running. An explicit `musubi sync` still syncs; the
[pause guide](guides/manage.md#pause-syncing-or-leave) covers restarting and disabling login
startup.

To stop automatic syncing for one repo, leave its **hive**, the group of copies it syncs
with. Leaving asks jj to snapshot files and attempts a final sync, keeping the repo and
files. From that repo:

```sh
musubi leave
```

`--force` permits leaving after a failed attempt; it does not skip that attempt. For a pause,
stop the daemon and keep the copy in its hive.

## When accidental files are snapshotted

jj records new, nonignored files in snapshots. Ignoring a tracked file and using
`jj file untrack` stops future tracking, but older snapshots retain its name and contents.
Deleting the current file does not remove those versions from outgoing history.

By default, sending pauses above 100 extra file paths or 8 MiB retained across outgoing
snapshots, beyond explicit change history and content already shared with the hive. Receiving
continues. These are bulk-upload limits, not a secrets filter: a password or API key in a
smaller snapshot can spread without a hold. Keep secrets ignored before jj records them.

[Snapshot limits and cleanup](guides/snapshots.md) explains inspection, approval and cleanup.
Cleanup preserves current work and explicit change versions but can discard older uncommitted
versions. Applying it asks jj to record current edits before checking that the preview still
applies. Approval sends the inspected history, including the unwanted files it contains.

## What the checks establish

Lean checks proofs about a model of the sync protocol. Its safety proofs cover every reachable
model state, for any number of machines, with message loss, duplication, delay, reordering and
process crashes. They establish retention of required history and objects and prevent received
history feeding back as new work. A separate model identifies which guarantees survive hub
rollback. These are proofs about the models, not every line of Rust or jj.

Tests compare the Rust implementation with executable Lean models. Repo tests run jj and
Git through concurrent commands, crashes and interrupted syncs, comparing results with jj's
own merges. They check the cases they run. Kani also checks Rust arithmetic and bounded push
sequences; those checks do not cover unbounded histories or the hub's storage implementations.
The [test guide](internals/testing.md) documents the checks, including
[Kani's bounds](internals/testing.md#kani-proofs).

The progress proofs assume edits and failures, including hub rollbacks, eventually stop,
copies resume successful syncing with correct replies, and snapshot holds are resolved,
disabled or approved. They also assume maintenance eventually stops adding repo
operations; they do not prove that it does. The [conformance guide](internals/conformance.md)
lists the formal assumptions.

Individual operation-abandonment steps have proofs, but a combined result covering every
sequence of abandonment and syncing is still missing. The [race catalogue](internals/races.md)
lists tested outcomes and known limitations.
