# Duplicates, moves and keys

Users duplicate, move, delete, restore and replace repositories with ordinary file commands.
This page says which of those cases musubi handles and how, which it leaves out, and which
test pins each. The code is `crates/musubi/src/copy.rs`.

## Terms

- A **copy** is a machine's repository that belongs to a hive, as in the user guide.
- A **duplicate** is a repository made from a copy's files without musubi: `cp -a`, `rsync`,
  or a backup restored. The copy it was made from is the **original**.
- A copy's **key** identifies it to the hive. It is kept in `.jj/repo/musubi/machine` (the
  file name is historical). Every operation that is the copy's work carries its key, and the
  hive uses the key to decide which workspaces are whose.
- A repository's **config-id** is jj's name for it, in `.jj/repo/config-id`. jj keeps, in the
  user's jj config directory, the path at which it last saw each config-id. When it finds a
  repository at a different path, it decides as follows (`handle_metadata_path` in jj's
  `lib/src/secure_config.rs`):
  - if nothing is at the old path any more, the repository was **moved**, and keeps its
    config-id;
  - if a file created at the new path appears at the old path too, it is the same directory
    reached two ways, such as a bind mount, and keeps its config-id;
  - otherwise it is a **duplicate**, and jj gives it a new config-id.

  So a repository keeps its config-id through `mv`, on one disk or across disks, and through
  unmounting and mounting again. A duplicate on the same machine gets a new one the first time
  jj, or musubi, opens it while its original still exists. A duplicate on another machine, or
  opened with another jj config directory, keeps it: jj has no record of where it was.
- A copy's **record** is `.jj/repo/musubi/hive.toml`. It names the hive, the hub and the
  machine, the copy's config-id, and its state: joined, left, or hive removed.
- The daemon's **entries**, in `state.toml`, are the copies it syncs: one per key, each with
  its key, hive id, config-id, and the path of the workspace it was joined in.
- **The copy of a key**, on a machine, is the repository whose config-id is the one in its
  record and in this machine's entry for its key. There is at most one: jj gives a duplicate on
  the same machine a new config-id, and a duplicate from elsewhere has no entry here.
- A **suspended** entry is one the daemon has stopped syncing, because its path doesn't hold
  the copy. It writes nothing to the entry's path, and looks again with the backoff it retries
  any failure with, up to a minute.

A duplicate carries its original's key. Two repositories with one key look to the hive like a
single workspace: each one's edits make the other's working copy stale, and
`jj workspace update-stale` overwrites one's files with the other's. So musubi never syncs a
duplicate. The config-id and the daemon's entries tell them apart: jj's decision on one
machine, and the entries across machines.

## Rules

- **R1. musubi syncs only the copy of a key.** Before any command that syncs, joins, leaves
  or forgets, in a repository with a record, musubi has jj resolve the repository's
  config-id, and checks that it is the copy of its key (`copy::standing`). A repository whose
  record says it left, or that its hive was removed, is a duplicate too if its config-id isn't
  its record's: joining it would join under the key of the copy it was made from. A
  repository jj takes for the copy is a duplicate all the same while this machine's entry for
  its key holds the copy in another directory (`copy::refine`), which a copy moved away, run
  in by jj, and moved back leaves jj unable to tell. If the repository is a duplicate, the
  command refuses, and says so. If this machine's entry still holds the copy, at its path or
  where jj last saw it, it names that path, and says `musubi clone` makes a new copy.
  Otherwise, the original may be gone, as after a move made by copying and deleting, and it
  suggests `musubi join --original` (R2) as well. `musubi status` shows a duplicate as not
  synced, and why, never with its original's status.

- **R2. `--original` adopts a repository as the copy.** Some repositories are the copy as
  far as the user knows, but not by R1: a backup restored onto a new machine, a move made by
  copying and then deleting, a copy whose machine lost musubi's state directory. For these,
  `musubi join --original` makes this machine's entry for the key hold this repository, writes
  its config-id into its record, and joins again under its key. It refuses if this machine's
  entry for the key still holds the copy, at its path or where jj last saw it, and names that
  path.

- **R3. The daemon checks before every sync.** Before each sync, the daemon reads the record,
  key and config-id at the entry's path, from the files alone, and checks them against the
  entry (`copy::check`). If they don't match, it suspends the entry. So a directory replaced
  by another repository is never synced into the first one's hive, nor has its status written
  into it. A sync that fails checks again before reopening anything. The daemon wakes when jj adds a file to `op_heads/heads`,
  which it does for each new operation, not when files are removed, so `rm -rf` doesn't
  start a sync. A copy whose `.jj/repo` directory was replaced by an identical one, as by
  restoring a backup in place, is opened afresh, and watched again.

- **R4. A moved copy is found again.** A suspended entry asks jj where its config-id was last
  seen (`copy::moved_to`). If the copy of the key is there, the entry takes that path and
  syncs again, unless a command changed the entry meanwhile. jj records the new path the first time it runs after a move, so a moved copy
  syncs again once jj runs in it. Any musubi command run in the copy of a key also moves its
  entry there. If the copy isn't found, as after `rm -rf` or while a disk is unmounted, the
  entry stays suspended and syncs again if the copy comes back. `musubi list` shows suspended
  entries as copies "not syncing", saying why, and `musubi leave <path>` removes one.

- **R5. One entry per key.** A second jj workspace of a synced repository has the same key,
  so `musubi join` there joins it again through the same entry, keeping its path. When an
  entry takes a path, by a join, a clone or R4, any other entry at that path is dropped.

- **R6. Opening a repository creates nothing.** Only `join`, `create` and `clone` create a
  key, a record or a config-id where there is none. Opening a repository, `musubi list`,
  `musubi sync` and the daemon never do; they let jj give a duplicate a new config-id, as every
  jj command does. A missing key or record suspends the entry.

- **R7. A record is never deleted.** `musubi leave` marks it left. When the hub replies that
  the hive was removed, which a hub that lost its state never says, the daemon marks the record
  removed and drops the entry. A plain `musubi join` in a repository whose hive was removed
  says so, rather than matching another hive by history; `musubi join --hive` and `musubi
  create` work as in a repository that left.

- **R8. A new hive doesn't inherit members.** When a copy joins or creates a hive whose id
  isn't the one its record holds, its join forgets every key that is present
  ([design.md](design.md#copies-that-go-away)) in its history but not at the hive's head, nor
  joining it, other than its own. The hub's join reply lists those keys. Joining the same hive,
  including one made again on another hub, forgets nothing.

- **R9. One user per copy.** On Unix, musubi refuses to run in a repository whose `.jj/repo`
  is owned by a user other than the one running it, checking before jj opens it, and says to
  run it as the owner.

- **R10. A daemon has no working directory of its own.** A command that starts the daemon
  starts it in musubi's state directory, so deleting or moving the repository it was started
  from doesn't affect it: gix needs the current directory whenever it opens a repository.

## Out of scope

These cases are left out because they are rare, or because handling them would cost more than
it's worth. Each says what happens if it occurs anyway.

- **Giving a duplicate a key of its own.** A duplicate shares the original's working-copy
  commits, and the hive's names for its earlier operations depend on the original's key. So
  it would need fresh working-copy commits and a durable record of when its key changed.
  `musubi clone` gives a new copy without either.
- **Starting a new hive from a duplicate.** It is refused like any other command (R1), even
  a duplicate of a copy that left, or the copy itself if it was moved by copying, and jj ran
  in its new place before the old one was deleted. Clone the repository's git remote afresh,
  and `musubi create` there.
- **A duplicate made, then the original moved, then the duplicate used first.** jj sees the
  original's old path empty and takes the duplicate for the moved repository, so the duplicate
  becomes the copy and the original is refused. musubi agrees with jj here rather than second-
  guess it; `musubi join --original` in the original undoes it, once the duplicate is deleted.
- **A copy moved, and a new repository made at a path jj last saw it at, before jj runs in
  the copy.** jj takes the copy for a duplicate, and the new repository's entry replaces the
  old one (R5). `musubi join --original` in the moved copy adopts it (R2).
- **A repository moved, deleted or replaced during a sync.** R3 checks before each sync, and
  a sync that fails checks again before reopening. Closing the gap would mean pinning the
  directory with an open handle throughout, through jj's path-based API. A sync cut short
  this way may leave a git ref's lock file behind in the moved repository, which makes its
  syncs fail until the lock is removed, as after a crash.
- **A VM, disk image or home directory cloned with musubi's state directory, while the
  original still runs** (a VM snapshot, Migration Assistant, a full restore onto a new
  machine). Both machines have the same entries and config-ids, so both sync under one key.
  Clone without musubi's state directory, and run `musubi clone` on the new machine.
- **Losing musubi's state directory.** The daemon forgets its entries, so nothing syncs until
  `musubi join --original` runs in each copy.
- **Deleting files inside `.jj/repo/musubi`.** The entry is suspended (R6), and the repository
  refuses musubi's commands. `musubi leave <path>` stops looking for it, and `musubi clone`
  makes a new copy.
- **File-syncing tools (Dropbox, Syncthing, iCloud) syncing `.jj`.** They corrupt jj's own
  state. [comparison.md](../comparison.md) says not to do this.
- **VM shared folders (9p, virtiofs, vboxsf, NFS),** where inotify and file locks may not work
  across. The daemon's 30-second poll still syncs.
- **Two daemons syncing one repository as the same user,** with different state directories.
  Both sync it, and the hive converges.
- **Moving or deleting a repository on Windows while the daemon has its files open.** Windows
  may refuse. Untested.
- **A power cut.** AGENTS.md: surviving one isn't a goal.
- **Display problems:** two machines given the same name, one hub reached by several names,
  a removed hive listed beside a live one of the same name, and `join --hive` not saying which
  settings it took. Each is worth fixing on its own.

## Catalogue

Each case, what musubi does, and the test in `crates/musubi/tests/cli.rs` that pins it.

| Case | Behaviour | Test |
| --- | --- | --- |
| `mv` the repository | Syncs again once jj runs in it (R4). | `moved_copies_sync_again` |
| Disk unmounted, then mounted again | Suspended, then synced again (R4). | `moved_copies_sync_again` |
| `mv` or delete the directory the daemon was started from | Nothing else stops syncing (R10). | `the_daemon_outlives_the_directory_it_was_started_in` |
| `rm -rf` a copy while its daemon runs | `rm` succeeds; the entry is suspended and listed until `musubi leave <path>` (R3, R4). | `deleted_copies_stop_syncing` |
| Deleted, then `musubi clone` again at the same path | The clone's entry takes the path, and the old entry is dropped (R5). | `deleted_copies_stop_syncing` |
| `cp -a` a copy, or restore a backup beside it | `musubi status` there says it is a duplicate, and names the original (R1). | `duplicates_are_never_synced` |
| …then `musubi join`, `sync`, `leave` or `join --original` there | Refused (R1, R2). | `duplicates_are_never_synced` |
| A duplicate of a copy that left, then `musubi join` there | Refused (R1). | `copy::tests`, and `join_refuses_duplicate` in the model |
| A duplicate on another machine (`rsync`, a backup restored there, a container image), or a move made by copying and deleting | Refused, until `musubi join --original` once the original is gone (R1, R2). | `a_copy_restored_elsewhere_syncs_as_the_original` |
| A backup restored in place | The copy: it syncs as before, fetching its own later work (R3). | `a_copy_restored_in_place_syncs_as_before` |
| A copy's directory replaced by a repository in no hive, or reinitialised | Suspended, with nothing written there (R3). | `a_replaced_copy_is_never_synced_into_its_hive` |
| …replaced by a copy of another hive | Synced into its own hive, never the first (R3, R4). | `a_replaced_copy_is_never_synced_into_its_hive` |
| `.jj/repo/musubi/machine` deleted | Not synced, and no new key made (R6). | `a_copy_without_its_key_is_not_synced` |
| A second jj workspace, with `musubi join` run in it too | Joins again, through the same entry; `musubi leave` there takes the copy out (R5). | `commands_in_another_workspace_act_on_the_repository` |
| A bind mount, joined through both paths | One entry, as for a second workspace: both paths reach the same `.jj/repo` (R5). | — (needs root) |
| `sudo musubi join` | Refused (R9). | — (needs root) |
| `musubi hub remove`, then a plain `musubi join` | Says the hive was removed (R7). | `copies_leave_a_removed_hive` |
| A copy that left one hive creates or joins another | Its join forgets the old hive's copies (R8). | `a_new_hive_doesnt_inherit_members` |
| `musubi join` killed partway, when joining a hive again | The daemon keeps syncing the copy: its `add` request restarts the copy's sync in one step, so nothing stops it between. | — |

## The model

`formal/Musubi/Copies.lean` models directories that the user moves, duplicates, deletes and
replaces, jj's config-id decision, records, entries and hives, and proves:

- `right_hive`: a hive accepts work only from a repository whose record says it joined that
  hive, under the key of the entry it was synced for;
- `duplicates_refused`: while a key's entry holds its copy, a repository at another path with
  the same key is never the copy, whatever jj decides about it. jj alone isn't enough
  (`duplicate_taken_for_moved`): a copy moved away, run in by jj there, and moved back leaves jj
  taking a duplicate made next for the moved repository, which `copy::refine` catches;
- `join_refuses_duplicate`: `join` refuses a repository whose record says it left, or that its
  hive was removed, once jj has given it a config-id of its own;
- `only_join_makes_keys`;
- `moves_followed`: a copy moved where jj last saw it is followed once jj runs in it. A copy
  moved, run in by jj, moved back, and moved again after its old place was reused is taken for
  a duplicate (`move_taken_for_duplicate`), a case left out above;
- `daemon_writes_nothing`: syncing and following a move change nothing on disk.

`copy::standing`, `copy::refine` and `copy::check` are checked against it through the oracle,
for every combination of their inputs over a small domain
([conformance.md](conformance.md#copies)).
