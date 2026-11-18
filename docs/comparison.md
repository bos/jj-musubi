# How jj-musubi compares with other approaches

jj-musubi is useful when you often switch machines in the middle of work, work across several
machines, or run remote coding agents and want to see or coordinate their changes as they work.
It shares unfinished work and jj history automatically. In return, you run a hub that passes
history between machines and a background daemon on each working machine.

## Pushing and fetching through a git remote

If you switch machines occasionally, you're very organized, and you don't mind some extra work,
a Git remote may be all you need. Decide what work you want to move around, create a temporary
commit and push it, then fetch it on the other machine. You choose what leaves each repo, and
you can use the same remote you already use to share work with other people.

The friction starts to build when you want to switch before that work is ready to push. jj's
[Git integration](https://docs.jj-vcs.dev/latest/bookmarks/) transfers commits through
bookmarks; unfinished work you haven't pushed stays behind, as does the operation log.

jj-musubi syncs your work once jj snapshots it, including changes with conflicts or no
description. You can inspect work on another machine's and pick up from it without preparing a
branch for the handoff. Shared history also lets you inspect or undo operations made on another
machine, as the [working guide](guides/working-across-machines.md#undo-across-machines)
explains.

[jj-sync](https://github.com/allouis/jj-sync) is an older approach that automates pushing and
fetching work in progress through a Git remote under refs of its own. It might an option if you
want handoffs without running a hub, though it does not share the operation log. Its README also
warns that if two machines amend and push the same change, the second push overwrites the
first(!). jj-musubi keeps both versions as a divergent change for you to resolve.

You can keep using Git alongside jj-musubi. A fetch or push on any machine updates the remote
bookmarks in every synced copy, so you only need to do it once.

## Peer-to-peer sync with jj-mesh

[jj-mesh](https://github.com/baptiste0928/jj-mesh) works much like jj-musubi: it syncs commits,
bookmarks and the operation log between your machines. Instead of a hub reached over ssh, its
machines use [iroh](https://www.iroh.computer/) to connect through NAT. Iroh's public servers
help machines find each other and relay traffic when a direct connection fails. jj-mesh also
snapshots working copies on a timer and updates stale ones for you. Every repo you add syncs to
every paired machine.

jj-mesh includes unit and integration tests. [jj-musubi's safety page](safety.md) describes its
proofs, conformance tests and end-to-end search.

## Working on one remote machine

If a devbox already has the tools and compute you need, connecting over `ssh` or VS Code's
Remote-SSH keeps all your work in one place. There is no repo handoff to arrange, though you
need a working connection to use it.

jj-musubi is useful when you also want to work in your laptop's own checkout, build on another
machine, or keep working offline. Each machine has a local repo and catches up whenever it can
reach the hub. Sync brings history into those repos; it does not change the files you are
editing on disk. The [handoff
guide](guides/working-across-machines.md#pick-up-on-another-machine) shows how to check out
synced work.

## File syncing: Dropbox, Syncthing, iCloud, rsync, NFS

File syncing looks like a similar way to carry everything with you, but it also copies the
checkout and machine-specific state. Two machines can then overwrite each other's checked-out
files. jj's [concurrency docs](https://docs.jj-vcs.dev/latest/technical/concurrency/) describe
how jj can merge file-synced history, but warn of possible Git-backend corruption, lost bookmark
pointers, and limited testing of colocated repos. I don't recommend file syncing for source-code
checkouts.

> [!WARNING] Do not combine file syncing with jj-musubi
>
> Copying jj-musubi's metadata makes the destination look like a duplicate repo, which
> jj-musubi will refuse to sync. Use `musubi clone` to make another copy.
