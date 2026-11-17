# Snapshot limits and cleanup

jj-musubi can keep large accidental additions from spreading to your other machines. You can
clean up the unwanted snapshots, or choose to send them.

It's not uncommon to accidentally add a lot of file data to a repo. You might mistakenly unpack
a tarball or zip file in a repo and discover that you've got thousands of new files not covered
by an existing `.gitignore` entry.

With jj's automatic snapshots, this can be kind of annoying: running a command like `jj status`
will cause you to unexpectedly snapshot all of those files. Because you don't normally look at
jj snapshots (I have never done so even once), this is an invisible tax. Deleting the files
creates a new snapshot that records their removal. If your tarball accident was large, the add
and remove snapshots could each be big.

By default, if jj-musubi sees more than 1,000 new file paths or 64 MiB of data in a snapshot that
hasn't been committed, it will put the sync of that snapshot on hold. The design assumption is
that these kinds of additions, without a commit, are usually accidental. The hold prevents these
presumed mistaken snapshots from spamming the op logs of your other repos in the hive.

If a snapshot gets used by a subsequent `jj commit` or other command that creates or modifies
changes, jj-musubi will automatically treat the snapshot as *intentional*, and lift the hold. A
commit of *some* snapshotted files will not cause leftover files from the snapshot to be
automatically approved.

{{< callout title="You might not care" >}}
  You could legitimately decide that this extra oversight isn't something you need. If so,
  you can either turn it off, or set the limits much higher.
{{< /callout >}}

## Inspecting and dropping unwanted files

Suppose we accidentally unpacked an archive into `scratch/data/`, and jj snapshotted 1,200 small
files before we noticed. Inspect the snapshots that retain them before choosing what to prune.
This reads recorded history without taking a new snapshot or contacting the hub (output trimmed
here):

```text
$ musubi sync --outgoing
Sending held: snapshots retain 1200 files, 1228800 bytes beyond intentional history.
...
Retaining operations (their byte counts overlap):
  a12b34c56d78  1200 files, 1228800 bytes  snapshot working copy
```

Deleting the files leaves their older versions in history. Pruning records your current edits
and deletions, then removes the selected operations while keeping the resulting commits and
their ids, bookmarks and workspace positions. It can discard older uncommitted versions of
files; if you want one, [save it first](#inspecting-older-edits-before-pruning).

Delete the accidental files, then use the ids from your report to prune their snapshots:

```text
$ rm -r scratch/data/
$ musubi sync --prune a12b34c56d78
Discarded 1 unpublished operation; current work is unchanged.
```

Pruning runs `jj util snapshot` in the invoking workspace before cleanup, so recent edits and
deletions are included. This follows jj's normal snapshot behavior, including importing changes
from colocated Git refs, which can rebase commits and update checkout files. Automatic stale
working-copy recovery is disabled for this step, even when `snapshot.auto-update-stale` is
enabled; follow jj's recovery hint if the workspace is already stale.

Every local workspace must have a current recorded basis, including secondary workspaces. If
cleanup names a workspace that needs updating, run `jj status` there and follow its recovery
hint, then retry. For inaccessible or missing workspace metadata, follow the
[recovery advice](../troubleshooting.md#accidental-files-and-cleanup).

Now check that the hold is lifted:

```text
$ musubi sync --outgoing
Within publication budget: snapshots retain 0 files, 0 bytes beyond intentional history.
$ musubi sync
```

If sending is still held, the report will list the remaining snapshots; prune the unwanted
ones too. To pick up your work elsewhere, follow
[Pick up on another machine](working-across-machines.md#pick-up-on-another-machine).

To keep the extracted files on disk, move them outside the repo instead of deleting them.
Or add `scratch/data/` to `.gitignore`, then run `jj file untrack scratch/data/`.
Ignoring a file that's already tracked doesn't stop jj from snapshotting it.

You can add `--dry-run` to preview cleanup of the last recorded state without snapshotting or
removing anything. Pending edits and deletions are included when you run the command without
`--dry-run`, so they can change the result. Pruning removes whole operations, so it can't remove
individual files from a snapshot. It doesn't immediately free disk space or erase secrets;
jj's garbage collection reclaims unused objects later.

Pruning is limited to operations this copy has never tried to send to the hub. If `musubi`
refuses a selection, it discards no operations; follow the
[recovery advice](../troubleshooting.md#accidental-files-and-cleanup). For history already
sent, see
[Abandoning operations](working-across-machines.md#abandoning-operations).

## Approve the history or change limits

You might have unpacked a large set of test data on purpose and want it on another machine.
To send it without committing it or cleaning up snapshots, copy the approval command printed by
`musubi sync --outgoing`. This approves all the outgoing history in the report, including any
accidental files:

```sh
musubi sync --approve <approval-token>
```

The token approves the outgoing history you inspected, with the limits in effect at that time.
New snapshots or incoming changes can invalidate it. If `musubi` asks you to inspect again, run
`musubi sync --outgoing` and use the new token.

If the sync fails or the hub is offline, the approval still holds: the daemon can retry sending
the same history. The outgoing report will say "Approved for sending".

If you often work with larger snapshots, you can raise the limits for this repo:

```sh
jj config set --repo musubi.publication.max-files 2000
jj config set --repo musubi.publication.max-bytes '128 MiB'
```

Use `--user` instead of `--repo` to set your defaults. Zero disables a limit; setting both to
zero disables the hold. See the
[configuration reference](../reference/configuration.md#each-repos) for details.

You can also set `snapshot.auto-track = 'none()'` to stop jj from automatically adding new
files. This changes your jj workflow; you don't need to do it to use jj-musubi's snapshot limits.

## Inspecting older edits before pruning

If you want an older uncommitted version of a file, inspect the snapshot that contains it:

```sh
jj --ignore-working-copy op show --patch a12b34c56d78
```

Take the file's commit id from that output and use it as `<commit>` to save a copy outside the
repo:

```sh
jj --at-op a12b34c56d78 file show -r <commit> AGENTS.md > ../AGENTS-before-cleanup.md
```

These commands read history without snapshotting your current files.

[bookmark-rescue]:
  ../troubleshooting.md#rescue-work-in-a-new-copy
