# Snapshot limits and cleanup

Inspect a sending hold, exclude accidental files, and either remove their older snapshots or
approve sending them. Receiving and local jj commands continue while sending is held.

## What counts toward the limits

Snapshots retain files after you remove them. By default, sending pauses above 100 extra file
paths or 8 MiB beyond intentional change history and content already shared with the hive.
Small accidental files, including secrets, can still sync.

`jj commit`, `describe`, `split`, `squash` and other commands that create or modify changes make
those versions intentional history, needing no approval. Bookmarking a working-copy version
also retains it intentionally; automatic bookmark moves don't approve later content. A partial
commit doesn't approve the unselected remainder.

Suppose `jj status` snapshots `README.txt`, `AGENTS.md` and accidental files. You commit only
`README.txt`, remove the accidental files, then run `jj status` again. The README is intentional
history; `AGENTS.md` is current work. Older snapshots retain the accidental files.

Limits apply across all outgoing history, including current work and older snapshots. Each
distinct version's full contents count once, even if you later made the file smaller; operation
rows in the report overlap. Intentional change history is exempt, so thousands of committed
files can sync within the budget.

## Inspect and exclude unwanted files

In the affected repository, run `musubi status`, then:

```sh
musubi sync --outgoing
```

`Sending held` lists extra paths and retaining operations. `Within publication budget` means
the work fits, not that it was sent. Neither command snapshots edits or contacts the hub.

Before recording more work, exclude unwanted files. Delete or move them if unneeded. To keep
a directory such as `scratch/` on disk, add it to `.gitignore`. If already tracked, run
`jj file untrack scratch/` too; ignoring tracked files alone isn't enough. Use
`jj file untrack <directory>` for another directory. Run `jj status` to record the intended
files, then inspect again with `musubi sync --outgoing`. Older snapshots may still retain them.

To send all reported content without cleanup, [approve the history or change
limits](#approve-the-history-or-change-limits).

## Preview cleanup

Use retaining operation ids from the report to preview removal:

```sh
musubi sync --prune a12b34c56d78 b23c45d67e89
```

The preview removes nothing. It reports remaining snapshot content, warns about losing older
uncommitted versions, and prints an apply command with a token bound to the preview.

Cleanup removes only history known never offered to the hub. A request whose reply was lost may
have propagated; history from before publication tracking began is also ineligible. For sent
history, see [Abandoning operations](working-across-machines.md#abandoning-operations).
If cleanup refuses, follow the
[refusal's recovery advice](../troubleshooting.md#cleanup-is-refused) or
[rescue wanted work](#recover-wanted-work) without approving the held history.

### Inspect older edits before cleanup

Before applying, inspect the operations in your preview for older edits you want to keep:

```sh
jj --ignore-working-copy op show --patch a12b34c56d78
```

Save needed files outside the repo using a commit id from that output as `<commit>`:

```sh
jj --at-op a12b34c56d78 file show -r <commit> AGENTS.md > ../AGENTS-before-cleanup.md
```

`--at-op` reads history without snapshotting current files. Compare the saved version with your
work before discarding it.

### Apply the checked preview

Copy the apply command printed by your preview, including its operation ids and token:

```sh
musubi sync --prune a12b34c56d78 b23c45d67e89 --apply <token-from-preview>
```

The token binds the previewed operations, history, limits and cleanup context. If files or
history change, preview again and use the new token. Applying snapshots unrecorded edits before
checking the token and refuses if they change the plan; those edits are preserved.

Cleanup preserves the README commit's id, current files including `AGENTS.md`, bookmarks and
workspace positions. Older uncommitted versions in removed snapshots may be lost, including
earlier `AGENTS.md` edits. Intentional change versions survive even if their operations are
removed. Cleanup removes whole operations, not individual files from a snapshot.

The preview reports content retained by other snapshots without extending your selection.
Current files remain required; [exclude unwanted files before
previewing](#inspect-and-exclude-unwanted-files).

Pruning disconnects operations; jj's garbage collection later reclaims unused objects. It
doesn't immediately reclaim disk space or erase secrets.

## Check and send

Run `musubi sync --outgoing` again. If the history is within budget:

```sh
musubi sync
musubi status
```

Check the useful files and the receiving machine's `jj log` before switching to it. If still
held, inspect the remaining retaining operations and preview another set. Resume a paused
daemon with `musubi daemon start` when ready.

## Approve the history or change limits

To send the history without cleanup, use the approval command printed by `--outgoing`:

```sh
musubi sync --approve <token-from-outgoing>
```

The token approves only the inspected outgoing history and limits, including accidental content.
New snapshots or incoming changes can invalidate it. A failed sync or offline hub doesn't: the
daemon can retry that publication, and `--outgoing` says "Approved for sending". Inspect again
if asked. Approval is optional.

Set different limits for a repo, or use `--user` for your default:

```sh
jj config set --repo musubi.publication.max-files 2000
jj config set --repo musubi.publication.max-bytes '16 MiB'
```

Zero disables a limit; setting both to zero disables the guard. `snapshot.auto-track = 'none()'`
prevents jj from adding new files automatically, changing your workflow; the budget doesn't
require it. The [configuration reference](../reference/configuration.md#each-repos)
defines the settings.

## Recover wanted work

Keep the original until the wanted files and commits appear on another machine.
Cloning can restart a paused daemon. Leaving the original, even with `--force`, attempts a
final sync; neither action isolates the held history. Read
[Pause syncing or leave](manage.md#pause-syncing-or-leave) before leaving.

Run `musubi clone <hive> <new-directory>`. Copy wanted files into its checkout, check the diff,
and describe or commit with jj. Never copy the original `.jj` or `.git` over the new one.
Inspect `musubi sync --outgoing`, sync, and check the receiving machine before removing the
original. Copying files avoids importing the old operation history.

To rescue commits instead, use the [bookmark rescue steps][bookmark-rescue].
Fetching brings ancestors too: inspect them for unwanted content before fetching.

[bookmark-rescue]:
  ../troubleshooting.md#this-repositorys-history-no-longer-matches-the-hives-so-it-cant-sync-again
