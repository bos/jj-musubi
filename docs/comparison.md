# How jj-musubi compares with other approaches

The alternatives are pushing through a Git remote, copying repository files, or working on
one remote machine.

## Pushing and fetching through a git remote

`jj git push --change @` and `jj git fetch` transfer commits that bookmarks point to. They
leave behind other commits, including unfinished work you haven't pushed, and the operation
log. `jj undo` and `jj op log` therefore stay per-machine. Pushing normally requires a
description and no conflicts; fetched bookmarks start untracked and immutable until tracked.
Each handoff needs a push and fetch.

Since jj 0.42, fetching a rewrite with the same change id rebases local descendants onto it.
Rewriting a change on both machines still produces divergence, as with jj-musubi.

A Git remote shares work with other people without a hub. Alongside jj-musubi, a fetch or push
on any machine updates remote bookmarks throughout the hive.

## File syncing: Dropbox, Syncthing, iCloud, rsync, NFS

> [!WARNING]
> I don't recommend file syncing for source-code checkouts.

jj's [concurrency docs](https://docs.jj-vcs.dev/latest/technical/concurrency/) describe merging
file-synced repos while retaining commits and exposing conflicts. They also warn of
Git-backend corruption, possible lost bookmark pointers, and limited testing of colocated
repos.

File syncing copies checked-out files and machine-specific state, including workspaces and
what jj last saw in `.git`. Two machines can fight over one checkout. jj-musubi replicates
the repo while keeping each machine's checkout and local state separate.

If you use file syncing, work on one machine at a time and finish syncing before switching.

> [!WARNING] Do not combine file syncing with jj-musubi
>
> Copying jj-musubi's metadata makes the destination look like a duplicate repo, which
> jj-musubi refuses to sync. Use `musubi clone` to make another copy.

## Working on one remote machine

With `ssh`, `tmux`, `mosh` or VS Code's Remote-SSH, work stays in one repo on the remote
machine. You need a working connection to use it.

This suits an always-reachable machine that builds faster than the others. jj-musubi lets
you work and build in each machine's own copy, including offline.

## Tools for jj

jj's [roadmap](https://docs.jj-vcs.dev/latest/roadmap/) describes a server and daemon for
cloud-hosted repos and operation logs, like Google's internal system, without a target
date.

[jj-sync](https://github.com/allouis/jj-sync) pushes and fetches work in progress through a
Git remote under refs of its own, without the operation log.

## Comparison

| | jj-musubi | File syncing | A git remote | One remote machine |
| --- | --- | --- | --- | --- |
| **Transfers** | Operations, commits, bookmarks, remote bookmarks | Every file, `.jj` and `.git` included | Bookmarked commits | Terminal and editor traffic |
| **Working copies** | Each machine's own | Shared (and fought over) | Each machine's own | One |
| **Op log and undo across machines** | Yes | Yes (when it works) | No | Not needed |
| **Work offline** | Yes | Yes | Yes | No |
| **By hand** | Nothing | Nothing | Push, fetch, track bookmarks | Nothing |
| **Needs** | A hub, ssh | A sync service | A remote | Reliable network |

Git remote definitions and jj configuration stay local in jj-musubi. Its default
[snapshot limits](guides/snapshots.md) pause sending
above 100 extra paths or 8 MiB; you can approve or clean up the held work.

The facts about other tools here were checked on November 16, 2026.
