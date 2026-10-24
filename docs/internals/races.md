# Race catalogue

Machines in a hive change the same repository concurrently, so every jj-level race that
two processes on one machine can have, machines can have too, plus a few of their own.
musubi's rule is that **replicated concurrency resolves exactly as jj resolves local
concurrency**: the result on every machine is what jj would produce if the same operations
had come from concurrent processes on one machine, and every machine ends up with the
same result. Where jj would silently do something harmful only because the operations came
from different machines, musubi detects it and stops.

Each entry below is pinned by a test. Most are in `crates/musubi-sync/tests/races/`, which
runs real repositories, colocated unless the entry says otherwise, through the real protocol
core and hub storage; a few that need the binary are in `crates/musubi/tests/cli.rs`, and a
few that test one layer are beside that layer's other tests. Most tests in `races/` end with
`assert_converged`: running `jj` everywhere and syncing again reaches a fixed point within a
few rounds; every machine agrees on visible commits and bookmarks; in every colocated
repository the git branches match the bookmarks that are not conflicted; and `jj status`
creates no further operation. A few, such as those where replication pauses, check
something else instead.

The generated end-to-end tests (docs/internals/testing.md) explore interleavings of the same
actions at random.

## Workspaces

Each machine's workspaces are its own, and every machine shows the others' as workspaces
named after the machine (`beta/default`) (docs/internals/design.md).

| Race | Outcome | Test |
| --- | --- | --- |
| Two machines both use workspace `default` | Fine: each keeps its own `default@`, and shows the other's as `alpha/default@` or `beta/default@`. | `machines_may_share_a_workspace_name` |
| A machine forgets another machine's workspace | Local only: nothing changes elsewhere, not even an empty working-copy commit, which `jj workspace forget` would otherwise abandon. The next sync shows the workspace again, even if the other machine has done nothing since. So too when the forget merges with a line of history from before that working copy existed, or before that machine joined. | `other_machines_workspaces_are_theirs`, `other_machines_workspaces_are_theirs_through_a_merge` |
| …while that machine builds on its working-copy commit | Nothing moves. `jj workspace forget` abandons the empty commit on the forgetting machine, but the hive keeps it, and the forgetting machine shows the workspace again as its next sync starts, before it merges what the other machine built. A forget made while a sync is under way merges as on one machine, the other machine's work rebased off the commit. | `forgetting_another_machines_workspace_moves_nothing_built_on_it` |
| A machine forgets another machine's workspace, then rewrites or abandons the parent of its empty `@` | jj, no longer seeing that `@`, leaves it on the old parent. musubi lets it go rather than bring the old parent back as a divergent copy, and the other machine gets a fresh `@` where jj would have moved it: on the rewritten parent, or on the abandoned parent's own parent. Since a rewrite keeps the change id, a parent moved with `jj rebase -r` counts as rewritten, as it does when jj merges concurrent operations, though a local `jj rebase -r` would have left the working copy behind. | `forgotten_working_copies_dont_keep_rewritten_parents`, `forgotten_working_copies_follow_an_abandon_to_the_parent`, `forgotten_working_copies_follow_a_parent_rebased_by_an_abandon`, `forgotten_working_copies_follow_a_moved_parent` |
| A machine forgets another machine's workspace, then, before syncing, abandons its `@`, which the forget left visible: it has edits, or another commit is built on it | As it would had the workspace still been there: the abandon stands, and the other machine gets a fresh `@` on the parent. musubi keeps a forgotten `@` visible only where the forget abandoned it. | `forgotten_working_copies_can_be_abandoned`, `forgotten_working_copies_built_on_can_be_abandoned` |
| A machine adds, then forgets, a secondary workspace | Every machine shows it while it exists. | `secondary_workspaces_show_everywhere` |
| A machine rewrites the parent of another machine's `@` | jj moves that machine's workspace at once, as it moves any workspace's, and that machine follows. jj then treats its working copy as stale until `jj workspace update-stale` updates the files, or, with `snapshot.auto-update-stale = true`, its next command does. | `rewriting_under_another_machines_working_copy_is_allowed`, `other_machines_working_copies_follow_rewrites` |
| …while that machine has unsnapshotted edits | The edits survive: jj snapshots them at the old operation before updating. At worst the working-copy change diverges. | `unsnapshotted_edit_survives_a_remote_rebase` |
| A machine abandons another machine's working-copy commit | jj gives that workspace a new commit on the parent, as for any workspace, and its machine adopts it. | `abandoning_another_machines_working_copy_commit` |
| A machine renames its workspace | The other machines show the new name. | `renamed_workspace_shows_renamed` |
| A machine renames or forgets its workspace while another machine rewrites its working copy | The rename or forget wins, as when jj merges concurrent operations on one machine: musubi merges workspaces three-way as jj does, removals first. | `e2e_smoke`, `workspace_merge_matches_jj` |
| Several machines share a hostname | Told apart by a random suffix in each machine's stored identity, and shown as `mac-1a2b/default`. | `machines_sharing_a_hostname_are_told_apart` |
| A workspace name git can't store as a ref, an import in a repository that isn't colocated, or a git remote named after a machine | Nothing happens: other machines' working copies are never git refs, so git can't drop them, and jj's import never abandons work because of them. | `git_never_sees_other_machines_working_copies` |

## Copies that go away

A forget of a copy removes the copy's work it saw, and only the copy's own work brings it
back (docs/internals/design.md, "Copies that go away").

| Race | Outcome | Test |
| --- | --- | --- |
| A machine forgets another machine's copy | Every machine stops showing its working copies; its empty working-copy commit is abandoned, and its work stays. The forgotten copy keeps its working copy, on the hidden commit, with no new one for the others to see, and stays forgotten however often its daemon syncs, until its next work. | `a_forgotten_copy_comes_back_with_its_next_work` |
| …and the forgotten copy's next work leaves its working copy alone, as creating a bookmark does | It shows again with a new working-copy commit on the old one's parent, as jj gives a workspace whose commit is abandoned: the forget abandoned its empty one. | `a_forgotten_copy_back_by_other_work_gets_a_new_working_copy` |
| …and the forgotten copy realizes the forget together with the operation before it | It keeps its working copy, as its realization of that operation had it. | `a_forgotten_copy_keeps_its_working_copy_through_a_run` |
| …and the forget, which saw the copy add a workspace, merges with work from before it | The copy keeps its workspaces as its latest work left them, whichever parent the merge lists first. | `a_forgotten_copy_keeps_its_latest_workspaces_through_a_merge` |
| A machine forgets a copy that is working meanwhile | The work the forget didn't see keeps the copy. | `work_a_forget_didnt_see_keeps_the_copy` |
| …having rewritten the copy's working-copy commit before forgetting it | The merge keeps the old commit hidden, beside its rewrite, and the copy, present by its work, follows the rewrite. | `a_rewrite_before_a_forget_sticks_through_a_merge` |
| A copy leaves while another machine pushes | It merges its forget with the push, and stays gone. Its working-copy commit, which has changes, stays as an ordinary commit, and it keeps its working copy. | `leaving_sticks_through_a_merge` |
| Two machines forget the same copy at once | They agree. A forget of a copy already gone writes nothing. | `concurrent_forgets_agree` |
| A machine undoes its forget of another copy, or restores a view from before it | The forget stands: only the copy's own work brings it back. The copy's workspaces come back in that machine's view, under names the hive no longer gives them, and it takes them for no machine's, its own included, and drops them as it syncs. | `undoing_a_forget_brings_back_nothing` |
| A machine's own workspace is named with a `/`, as `feat/x` | Its own, shared as `alpha/feat/x`. | `own_workspaces_with_a_slash_are_own` |
| …and named like another machine's, as `beta/x`, before that machine joins or after | Its own all the same, while the hive has forgotten this machine too, and after `jj undo` of forgetting it; it shows that machine as `beta-1a2b`. | `own_workspaces_named_like_another_machine_are_own` |
| A copy leaves, its empty working-copy commit abandoned by its forget, or leaves after another machine forgot it | It gets a new working-copy commit, as jj gives a workspace whose commit is abandoned: no next work of its shows it again. | `a_copy_that_leaves_gets_a_new_working_copy` |
| A copy is unused for longer than its `musubi.forget-after` | Any other machine's daemon forgets it, as `musubi forget` would, and it comes back with its next work. A copy that recorded none, or `never`, isn't forgotten, nor is a machine's own copy by its own daemon. | `unused_copies_are_forgotten_after_their_forget_after` |
| A forgotten copy changes its `musubi.forget-after` | Recording it is the copy's work, so the copy shows again, and is forgotten by the new value. | `changing_forget_after_is_work` |
| A copy that left joins again | It shows again at once: joining is its work. | `a_copy_that_left_shows_again_once_it_joins` |
| A machine rewrites the working-copy commit of a copy the hive has forgotten | No machine sees it as a working copy, so no workspace moves with it; the copy follows the rewrite itself, as jj would have moved it. | `a_forgotten_working_copy_follows_its_rewrite` |

## Bookmarks and tags

| Race | Outcome | Test |
| --- | --- | --- |
| Same bookmark moved to different commits | Conflicted bookmark on every machine. Each colocated `.git` keeps its own branch value, because jj does not export conflicted bookmarks. No later `jj` command resolves it silently. Resolving it on one machine resolves it everywhere and updates every `.git`. | `same_bookmark_moved_to_different_commits` |
| Same bookmark created at the same commit | No conflict. | `same_bookmark_created_at_the_same_commit` |
| Same bookmark deleted on both machines | Deleted; no conflict. | `same_bookmark_deleted_on_both_machines` |
| Bookmark moved on one machine, deleted on another | jj's three-way result, the same on every machine. | `bookmark_moved_on_one_machine_and_deleted_on_another` |
| Branch moved with `git` behind jj's back while another machine moves the bookmark | The git move is imported by that machine's next `jj` command, as a local change; the hive converges, with no flip-flopping. | `git_branch_moved_behind_jj_while_another_machine_moves_it` |
| Same tag set to different commits | Conflicted tag on every machine. Each machine's `@git` tag keeps its own value. | `same_tag_created_at_different_commits` |
| One machine fetches an annotated tag | A known limitation: every machine's jj has the tag, at the same commit, but only that machine's `.git` has the tag object, with its message, tagger and any signature. The others' `.git` has a lightweight tag at the commit, so there `git describe` without `--tags` passes it over, and `git tag -v` has nothing to verify. jj records a tag by its commit, and musubi moves the commits a view needs, not tag objects. | `an_annotated_tag_arrives_lightweight` |
| Independent repositories with differing `main` join one hive | The histories merge at jj's shared root operation, and `main` is conflicted until someone resolves it. | `joining_repositories_with_conflicting_bookmarks` |

## Changes

| Race | Outcome | Test |
| --- | --- | --- |
| Same commit rewritten on two machines | A genuine divergent change, identical, with the same commit ids, on every machine. Any machine's `@` built on that commit is rebased by both rewrites and diverges too, as with two workspaces on one machine. Resolving the divergence anywhere resolves it everywhere. | `same_change_rewritten_on_two_machines` |
| Commit abandoned on one machine while another builds on it | The orphan is rebased onto the abandoned commit's parent exactly once, so nothing diverges. | `commit_abandoned_while_another_machine_builds_on_it` |
| Both machines squash different work into the same commit | A divergent change, the same everywhere. | `both_machines_squash_into_the_same_commit` |
| A conflicted commit made on one machine | Conflicted, with the same terms, on every machine; resolving it anywhere resolves it everywhere. | `conflicts_replicate_and_resolve` |
| Three machines build on, and one rewrites, the same commit | Merged one at a time through the hub; no spurious divergence. Independent merges on each machine would each rebase the same commits and create divergence, which is why the hub orders updates (docs/internals/design.md). | `three_machines_build_on_the_same_commit` |
| One machine rewrites a commit another builds on, with commit signing on | The commits musubi rebases when it merges the two are signed, as jj's own rewrites would be: musubi loads jj's signing config as jj does. | `rewrites_are_signed_as_jj_signs_them` |

## Remotes

| Race | Outcome | Test |
| --- | --- | --- |
| One machine fetches | Every machine gets the remote bookmarks, and its `.git` gets the matching remote-tracking refs. | `fetch_on_one_machine_reaches_the_other` |
| Two machines fetch while the remote moves in between | The newer fetch descends from the older one, so jj resolves the remote bookmark to it; no conflict. | `concurrent_fetches_of_a_moving_remote` |
| Two machines fetch while the remote is force-pushed in between | The remote bookmark is conflicted, which jj won't export, and every `jj` command resolves a conflicted remote bookmark to what `.git` has. So musubi writes one side to every machine's `.git`, replacing whatever value from the conflict or jj's record was there, and every machine settles on that fetch, not on an older one some machine's `.git` still had. The side is the one committed last, which is not necessarily the later fetch; the next fetch corrects it. | `conflicted_remote_bookmark_resolves_to_a_fetched_side`, `conflicted_remote_bookmark_resolves_despite_a_stale_record` |
| One machine pushes | Every machine sees the pushed, tracked remote bookmark. | `push_from_one_machine` |
| One machine stops tracking a remote bookmark | Every machine stops: a later fetch on any of them moves the remote bookmark but not the local one. | `untracking_a_remote_bookmark_reaches_every_machine` |
| A machine adds, renames, or removes a git remote, or changes its URL | Every machine does the same to its git config (docs/internals/design.md, "Hive settings"), along with the remote bookmarks, which jj renames or forgets in the replicated view. | `remote_added_on_one_machine_reaches_the_others`, `remote_renamed_and_removed_everywhere` |
| Two machines change the same remote's URL at once | The later write wins everywhere, by the writing machines' clocks; the other machine's value is replaced, and its daemon logs it. | `remote_changed_on_two_machines_at_once` |
| One machine changes a remote's URL while another changes its push URL | Two writes to one remote: the later wins, whichever reaches the hub first, whichever machine merges, and whatever either does meanwhile. Clock skew can make the earlier win. | `the_later_change_to_a_remote_wins`, `the_later_change_wins_reaching_the_hub_last`, `working_on_after_the_earlier_change_makes_no_difference` |
| A machine sets or unsets a shared repo config key (`revset-aliases."immutable_heads()"`, `revset-aliases."trunk()"`, `git.private-commits`, or one `musubi.shared-config` names) | Every machine does the same. Other repo config stays each machine's own. | `shared_config_reaches_every_machine`, `other_config_is_shared_only_when_named`, `settings_are_shared_through_the_binary` |
| Two machines set a shared config key differently at once | The later write wins, as for remotes. | `shared_config_set_on_two_machines_at_once` |
| A machine joins with remotes of its own | Its remotes join the hive's, even one by a name the hive once removed, but where both have a remote of the same name pointing to different repositories, the hive's wins. | `joining_machine_merges_its_remotes_with_the_hives`, `a_joining_machine_keeps_a_remote_the_hive_removed` |
| A machine spells a remote through a `url.<base>.insteadOf` rule, an alias or a redirect to a mirror, or its https URL carries credentials | The remote goes as written and as git expands it there. A machine whose git expands it the same way, as one with the same alias, keeps it as written; another gets the expansion, a mirror's URL included; the writing machine keeps its own spelling. The hub matches joining machines on either. Unless `musubi.share-credentials` is set, the credentials never leave the machine, not even in the command line jj records with the operation that added the remote. | `remotes_go_as_written_and_as_expanded`, `one_hub_many_hives` |
| Machines reach one remote by different URLs (https and ssh, say) | Each keeps its own, joining or later, through moves, renames, and push URL changes on either machine, and after missing several changes; only pointing the remote at another repository replicates, and a push URL to where it used to point goes. A rename seen together with another change to the same remote isn't recognized as one: the remote is replaced, in the hive's spelling, and its remote-tracking refs go with it until the next sync brings them back. | `machines_keep_their_own_spelling_of_a_shared_remote`, `changes_to_a_remote_reach_machines_with_their_own_spelling`, `a_push_url_to_the_old_repository_goes_when_the_remote_moves`, `a_rename_keeps_each_machines_spelling`, `a_machine_that_lags_behind_respellings_takes_later_changes` |
| `jj git colocation disable` or `enable` while `musubi daemon` runs | The daemon's next sync fails, since the repository it had open moved its git store. The daemon reopens the repository after any failed sync and retries after its backoff, so it carries on. | `daemon_carries_on_after_colocation_changes` |

## Kinds of repository

Not races: kinds of repository and history a hive carries.

| Kind | Outcome | Test |
| --- | --- | --- |
| A machine's repository isn't colocated | Fine: its git store is inside `.jj`, where musubi reads and writes objects, with no `.git` to keep in step. Its work and bookmarks reach colocated machines, whose `.git` gets the branches, theirs reach it, and it merges concurrent work like any other machine. | `colocated_and_non_colocated_repositories_share_a_hive` |
| History has a submodule | Fine: trees name the submodule's commit, which no machine needs, and nothing transfers it or asks for it. | `history_with_a_submodule_replicates` |
| A shallow or partial clone | Refused, at once, with a pointer to `musubi clone`: starting a hive, joining one, and syncing a repository that has become one since it joined. Neither can send everything an operation requires, which the hub accepts only whole. musubi's git also sets `GIT_NO_LAZY_FETCH`, so a git that knows it never fetches from a promisor remote. | `shallow_clones_are_refused`, `shallow_and_partial_clones_are_incomplete` |

## Operation history

| Race | Outcome | Test |
| --- | --- | --- |
| `jj undo` when the latest operation came from another machine, even with both workspaces named `default` | jj refuses, naming the other machine's workspace (`alpha/default`), since musubi realizes other machines' operations under those workspaces' names. With `--allow-cross-workspace` the undo happens and replicates. To undo this machine's own earlier operation once others have arrived, use `jj op revert <op>`. | `undo_of_another_machines_operation`, `op_log_names_other_machines_workspaces` |
| `jj undo` past another machine's undo, or of it with `--allow-cross-workspace`, then `jj redo` | As on one machine: jj continues along the undo stack. jj finds the stack by the operation id in an undo's description ("undo: restore to operation <id>"), so musubi translates that id between machines, as it does in `redo:`, `restore to operation` and `revert operation` descriptions. | `undo_stack_continues_across_machines`, `undo_and_redo_of_another_machines_undo` |
| `jj op restore` (or undo or redo) on one machine, back to before another machine's latest working-copy change | Every machine's working copy goes back to where it was then, as jj restores every workspace on one machine; the other machine's working copy is stale until `jj workspace update-stale` updates the files, or, with `snapshot.auto-update-stale = true`, its next command does. | `op_restore_restores_other_machines_working_copies` |
| `jj undo` and `jj redo` of this machine's own latest operation | As without musubi; both replicate. `jj redo` finds nothing to redo once another machine's operation has arrived after the undo. | `undo_and_redo_of_own_operation` |
| A command based at an older operation (`--at-op`, or a long-running command) | A concurrent local operation; jj merges it locally and the merge replicates. | `concurrent_operation_on_one_machine` |
| A machine misses many updates while working | Catches up with one merge. | `long_offline_machine_catches_up` |
| The hub restarts between one machine's push and another's fetch | Nothing lost: the head log and stores are on disk. | `hub_restart_between_push_and_fetch` |
| A repository joins with its whole operation history | Other machines' op logs include that history. | `joining_with_full_history` |
| Two fresh, empty repositories form a hive | Works like any other join. | `empty_repositories_make_a_hive` |
| `jj op abandon` of operations the hub accepted, whether this machine's latest operation is its own or another machine's | **Replication pauses** for that repository, with an error, rather than reintroducing the abandoned operations or duplicating history. Planned: replicate it as a supersede record (docs/internals/design.md). | `op_abandon_pauses_replication`, `op_abandon_under_a_realized_head_pauses_replication` |
| `jj op abandon` of only the history from before the machine joined, then `jj util gc` | Nothing changes for the other machines, and replication carries on: the rewritten join point maps to the same canonical join operation, by its view and metadata. | `op_abandon_of_pre_join_history_is_harmless` |
| Restart that loses the translation cache | Recovered from operation attributes and the join records; no duplicate realizations. | `restart_with_lost_cache`, `lost_cache_does_not_duplicate_realizations` |
| A crash while realized operations are still being written, some in full, some only as far as their views | None of them was recorded, so they are realized again after the restart, as the same operations; no duplicate realizations. | `crash_with_writes_in_flight` |
| Colocated git state replicated verbatim | Would silently move bookmarks back. Translation exists to prevent this. | `verbatim_replication_reverts_bookmarks` (negative control) |

## Known jj limitations

These are jj 0.46 behaviors, reproducible on one machine with concurrent `jj` processes or
`--at-op`. musubi does not cause them, but more concurrency makes them likelier. The
generated end-to-end search found each of them.

| Behavior | Effect | Recovery | Test |
| --- | --- | --- | --- |
| One operation abandons, or moves away, a commit directly on the root, while a concurrent one makes it a parent of a merge commit | Reconciling them would rebase the merge commit onto the root, which jj's git backend refuses: every `jj` command would then fail with "Failed to load the repo". Rare in established repositories, where commits on the root are ancestors of `trunk()` and so immutable. musubi doesn't apply another machine's operation that jj can't merge with this machine's own (it tries the merge first, in both orders): the sync fails, naming this machine's operations the hive doesn't have yet, and jj keeps working. Two operations on one machine still break it. | Revert the conflicting operation the sync error names with `jj op revert <id>`; musubi then catches up. Between two operations on one machine: `jj --at-op <one head> op revert @`. | `root_parent_merge_bug_is_explained` |
| Concurrent operations whose rebases form a loop: one moves X, and Y on it, onto Z, while another moves Z onto Y | jj panics merging them ("graph has cycle"), and so on every load: every `jj` command crashes. musubi doesn't apply another machine's operation that jj can't merge with this machine's own, as above, so across machines jj keeps working; two operations on one machine still break it. | As above. | `rebases_that_form_a_loop_pause_instead_of_breaking_jj` |
| `jj undo --allow-cross-workspace` of another workspace's `jj workspace rename` (two workspaces on one machine) | The undo puts the workspace back under its old name in the view, but the renamed workspace's working-copy state still records the new name, so jj finds no entry for it: `jj status` there says "No working copy", and neither `jj workspace rename` nor `jj workspace update-stale` helps. Workspaces are per-machine, so this cannot happen across machines. | `jj redo` from the workspace that ran the undo. | — |
| A git branch moved onto `@` with `git` while `@` has unsnapshotted edits | The next `jj` command snapshots the edits, rewriting `@`, and imports the branch pointing at the commit git saw, the pre-snapshot `@`. The branch keeps that commit visible, so `@`'s change is divergent. | `jj bookmark set <branch> -r @`, then abandon the old commit. | — |
| Any `jj` command, even `jj log`, that reconciles concurrent operations | The reconciliation can move bookmarks (it rebases descendants of rewritten commits), but a command that writes no operation of its own exports nothing, so in a colocated repository git branches lag the bookmarks (`jj log` shows `topic*`) until the next command that changes something. musubi exports after its own merges; when a `jj` command happens to merge first, git lags as it would without musubi. | Any command that changes something, such as `jj git export`. | `bookmark_moved_by_a_node_merge_is_exported` (musubi's own merges) |

## Protocol-level races

Lost, duplicated, reordered, and delayed messages; concurrent pushes, where one wins and the
others merge and retry; node and hub crashes at every step; rogue pushes without uploads.
These are covered for any number of nodes by the Lean model's proofs, and checked against
the Rust core by `protocol_invariants` and `conformance` (docs/internals/conformance.md).
