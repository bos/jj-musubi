# Race catalogue

Machines in a hive change the same repository concurrently, so every jj-level race that
two processes on one machine can have, machines can have too, plus a few of their own.
musubi's rule is that **replicated concurrency resolves exactly as jj resolves local
concurrency**: the result on every machine is what jj would produce if the same operations
had come from concurrent processes on one machine, and every machine ends up with the
same result. Where jj would silently do something harmful only because the operations came
from different machines, musubi detects it and stops.

Each entry below is pinned by a test in `crates/musubi-sync/tests/races/`, which runs real
colocated repositories through the real protocol core and hub storage. Every test ends
with `assert_converged`: running `jj` everywhere and syncing again reaches a fixed point
within a few rounds; every machine agrees on visible commits and bookmarks; in every
colocated repository the git branches match the bookmarks that are not conflicted; and
`jj status` creates no further operation.

The generated end-to-end tests (docs/testing.md) explore interleavings of the same actions
at random.

## Workspaces

Workspaces are per-machine (docs/design.md); only the commits they point at are shared.

| Race | Outcome | Test |
| --- | --- | --- |
| Two machines both use workspace `default` | Fine: each keeps its own `default@`; the other's working-copy commit is an ordinary commit. | `machines_may_share_a_workspace_name` |
| A machine tries to forget or use another machine's workspace | Impossible: it has no such workspace (jj warns "No such workspace"). | `other_machines_workspaces_are_not_visible_as_workspaces` |
| A machine adds, then forgets, a secondary workspace | Local to that machine; others only ever see the commits it creates. | `secondary_workspaces_stay_local` |
| A machine rewrites the parent of another machine's `@` | That machine follows the rewrite to its new `@`. jj then treats its working copy as stale; with `snapshot.auto-update-stale = true` its next command updates the files. | `rewriting_under_another_machines_working_copy_is_allowed` |
| …while that machine has unsnapshotted edits | The edits survive: jj snapshots them at the old operation before updating. At worst the working-copy change diverges. | `unsnapshotted_edit_survives_a_remote_rebase` |
| A machine abandons another machine's working-copy commit | The owner gives itself a fresh `@` on the parent, as jj does when you abandon `@` locally. | `abandoning_another_machines_working_copy_commit` |
| Another machine's working copy moves | Its label (`default@beta`) follows. When this machine rewrote it, the label catches up at the other machine's next operation. | `other_machines_workspaces_are_labeled` |
| A machine edits or forgets another machine's label | Local only; the next sync puts it back. | `labels_are_local` |
| A machine renames its workspace | The other machines' label for it follows. | `renamed_workspace_relabels` |
| Several machines share a hostname | Told apart by a random suffix in each machine's durable identity; labels become `default@mac-1a2b`. | `machines_sharing_a_hostname_are_told_apart` |

## Bookmarks and tags

| Race | Outcome | Test |
| --- | --- | --- |
| Same bookmark moved to different commits | Conflicted bookmark on every machine. Each colocated `.git` keeps its own branch value, because jj does not export conflicted bookmarks. No later `jj` command resolves it silently. Resolving it on one machine resolves it everywhere and updates every `.git`. | `same_bookmark_moved_to_different_commits` |
| Same bookmark created at the same commit | No conflict. | `same_bookmark_created_at_the_same_commit` |
| Same bookmark deleted on both machines | Deleted; no conflict. | `same_bookmark_deleted_on_both_machines` |
| Bookmark moved on one machine, deleted on another | jj's three-way result, the same on every machine. | `bookmark_moved_on_one_machine_and_deleted_on_another` |
| Branch moved with `git` behind jj's back while another machine moves the bookmark | The git move is imported by that machine's next `jj` command, as a local change; the hive converges, with no flip-flopping. | `git_branch_moved_behind_jj_while_another_machine_moves_it` |
| Same tag set to different commits | Conflicted tag on every machine. Each machine's `@git` tag keeps its own value. | `same_tag_created_at_different_commits` |
| Independent repositories with differing `main` join one hive | The histories merge at jj's shared root operation, and `main` is conflicted until someone resolves it. | `joining_repositories_with_conflicting_bookmarks` |

## Changes

| Race | Outcome | Test |
| --- | --- | --- |
| Same commit rewritten on two machines | A genuine divergent change, identical, with the same commit ids, on every machine. Any machine's `@` built on that commit is rebased by both rewrites and diverges too, as with two workspaces on one machine. Resolving the divergence anywhere resolves it everywhere. | `same_change_rewritten_on_two_machines` |
| Commit abandoned on one machine while another builds on it | The orphan is rebased onto the abandoned commit's parent exactly once, so nothing diverges. | `commit_abandoned_while_another_machine_builds_on_it` |
| Both machines squash different work into the same commit | A divergent change, the same everywhere. | `both_machines_squash_into_the_same_commit` |
| A conflicted commit made on one machine | Conflicted, with the same terms, on every machine; resolving it anywhere resolves it everywhere. | `conflicts_replicate_and_resolve` |
| Three machines build on, and one rewrites, the same commit | Merged one at a time through the hub; no spurious divergence. Independent merges on each machine would each rebase the same commits and create divergence, which is why the hub orders updates (docs/design.md). | `three_machines_build_on_the_same_commit` |

## Remotes

| Race | Outcome | Test |
| --- | --- | --- |
| One machine fetches | Every machine gets the remote bookmarks, and its `.git` gets the matching remote-tracking refs. | `fetch_on_one_machine_reaches_the_other` |
| Two machines fetch while the remote moves in between | The newer fetch descends from the older one, so jj resolves the remote bookmark to it; no conflict. | `concurrent_fetches_of_a_moving_remote` |
| One machine pushes | Every machine sees the pushed, tracked remote bookmark. | `push_from_one_machine` |

## Operation history

| Race | Outcome | Test |
| --- | --- | --- |
| `jj undo` when the latest operation came from another machine, even with both workspaces named `default` | jj refuses, naming the other machine's workspace (`default@alpha`), since musubi realizes other machines' operations under their label names. With `--allow-cross-workspace` the undo happens and replicates. To undo this machine's own earlier operation once others have arrived, use `jj op revert <op>`. | `undo_of_another_machines_operation`, `op_log_names_other_machines_workspaces` |
| `jj undo` and `jj redo` of this machine's own latest operation | As without musubi; both replicate. `jj redo` finds nothing to redo once another machine's operation has arrived after the undo. | `undo_and_redo_of_own_operation` |
| A command based at an older operation (`--at-op`, or a long-running command) | A concurrent local operation; jj merges it locally and the merge replicates. | `concurrent_operation_on_one_machine` |
| A machine misses many updates while working | Catches up with one merge. | `long_offline_machine_catches_up` |
| The hub restarts between one machine's push and another's fetch | Nothing lost: the head log and stores are durable. | `hub_restart_between_push_and_fetch` |
| A repository joins with its whole operation history | Other machines' op logs include that history. | `joining_with_full_history` |
| Two fresh, empty repositories form a hive | Works like any other join. | `empty_repositories_make_a_hive` |
| `jj op abandon` of operations the hub accepted, whether this machine's latest operation is its own or another machine's | **Replication pauses** for that repository, with an error, rather than reintroducing the abandoned operations or duplicating history. Planned: replicate it as a supersede record (docs/design.md). | `op_abandon_pauses_replication`, `op_abandon_under_a_realized_head_pauses_replication` |
| `jj op abandon` of only the history from before the machine joined, then `jj util gc` | Nothing changes for the other machines, and replication carries on: the rewritten join point maps to the same canonical join operation, by its view and metadata. | `op_abandon_of_pre_join_history_is_harmless` |
| Restart that loses the translation cache | Recovered from operation attributes and the durable join records; no duplicate realizations. | `restart_with_lost_cache`, `lost_cache_does_not_duplicate_realizations` |
| Colocated git state replicated verbatim | Would silently move bookmarks back. Translation exists to prevent this. | `verbatim_replication_reverts_bookmarks` (negative control) |

## Known jj limitations

These are jj 0.46 behaviors, reproducible on one machine with concurrent `jj` processes or
`--at-op`. musubi does not cause them, but more concurrency makes them likelier. The
generated end-to-end search found each of them.

| Behavior | Effect | Recovery |
| --- | --- | --- |
| One operation abandons, or moves away, a commit directly on the root, while a concurrent one makes it a parent of a merge commit | Reconciling them would rebase the merge commit onto the root, which jj's git backend refuses: every `jj` command then fails with "Failed to load the repo". Rare in established repositories, where commits on the root are ancestors of `trunk()` and so immutable. A jj bug, to be fixed in jj; until then musubi's sync error names it and gives the recovery. | On the machine that made the merge commit: `jj --at-op <its head> op revert @`. |
| `jj undo --allow-cross-workspace` of another workspace's `jj workspace rename` (two workspaces on one machine) | The undo puts the workspace back under its old name in the view, but the renamed workspace's working-copy state still records the new name, so jj finds no entry for it: `jj status` there says "No working copy", and neither `jj workspace rename` nor `jj workspace update-stale` helps. Workspaces are per-machine, so this cannot happen across machines. | `jj redo` from the workspace that ran the undo. |
| A git branch moved onto `@` with `git` while `@` has unsnapshotted edits | The next `jj` command snapshots the edits, rewriting `@`, and imports the branch pointing at the commit git saw, the pre-snapshot `@`. The branch keeps that commit visible, so `@`'s change is divergent. | `jj bookmark set <branch> -r @`, then abandon the old commit. |
| Any `jj` command, even `jj log`, that reconciles concurrent operations | The reconciliation can move bookmarks (it rebases descendants of rewritten commits), but a command that writes no operation of its own exports nothing, so in a colocated repository git branches lag the bookmarks (`jj log` shows `topic*`) until the next command that changes something. musubi exports after its own merges; when a `jj` command happens to merge first, git lags as it would without musubi. | Any command that changes something, such as `jj git export`. |

## Protocol-level races

Lost, duplicated, reordered, and delayed messages; concurrent pushes, where one wins and the
others merge and retry; node and hub crashes at every step; rogue pushes without uploads.
These are covered for any number of nodes by the Lean model's proofs, and checked against
the Rust core by `protocol_invariants` and `conformance` (docs/conformance.md).
