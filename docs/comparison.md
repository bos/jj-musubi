# How musubi compares with other approaches

There are several ways to work on one jj repository from more than one machine. They differ in
what they carry between machines, what they leave behind, and how much you do by hand.

| | musubi | File syncing | A git remote | One remote machine |
| --- | --- | --- | --- | --- |
| Carries | Operations, commits, bookmarks, remotes | Every file, `.jj` and `.git` included | Bookmarked commits | Nothing to carry |
| Working copies | Each machine's own | Shared, and fought over | Each machine's own | One |
| Operation log and undo across machines | Yes | Yes, when it works | No | Not needed |
| Work offline | Yes | Yes | Yes | No |
| By hand | Nothing | Nothing | Push, fetch, track bookmarks | Nothing |
| Needs | A hub, ssh | A sync service | A remote | A fast, steady link |

## File syncing: Dropbox, Syncthing, iCloud, rsync, NFS

jj's storage is designed so that a file-syncing tool can merge copies of a repository changed
on different machines. jj's
[concurrency docs](https://docs.jj-vcs.dev/latest/technical/concurrency/) say that then "no
changes to the repo will be lost", and that conflicting changes "will appear as conflicts".
They also say that there are "known bugs in this area", that "with the Git backend,
repository corruption is possible because the backend is not entirely lock-free", and that
colocated repositories are the least tested. jj's issue tracker has reports of locking errors,
missing objects, and stray file changes from repositories synced this way.

File syncing also syncs the working copy, so two machines fight over one checkout, and over
the state jj keeps about each machine, such as its workspaces and what it last saw in `.git`.
musubi replicates only the repository, through jj's own code, and keeps each machine's
working copy and per-machine state its own.

File syncing is still a good fit when you use one machine at a time and let the sync finish
in between, or when you want ignored files and build output carried along too. Don't use it
on a repository musubi syncs as well: the file-syncing tool makes each machine's copy a copy
of the other's files, which musubi stops syncing, rather than let them overwrite each other.

## Pushing and fetching through a git remote

You can push work in progress to a remote from one machine and fetch it on another, with
`jj git push --change @` and `jj git fetch`. That carries only commits a bookmark points to,
so it leaves behind any commit without one, including the other machine's working copy unless
you push it. It leaves behind the operation log too, so `jj undo` and `jj op log` stay
per-machine. By default, jj refuses to push a commit with no description or with conflicts,
and on the other machine, fetched bookmarks start out untracked, and so immutable, until you
track them. Each move takes a push on one machine and a fetch on the other.

Recent jj releases make fetched rewrites behave better: since jj 0.42, `jj git fetch` rebases
local descendants of a commit that was rewritten elsewhere, where the rewritten commit keeps its
change id. But a commit rewritten on both machines still shows up as divergent, as it would with
musubi.

A remote remains the way to share work with other people, and needs no hub. musubi works
alongside it: a fetch or push on any machine in a hive updates every machine's remote
bookmarks.

## Working on one remote machine

Instead of syncing, you can do all your work on one machine, reached from the others with
ssh, `tmux` or `mosh`, or an editor's remote mode such as VS Code's Remote-SSH. There is one
repository and nothing to sync, but every keystroke and build goes over the link, and you
can't work while it is down.

That suits a machine that is always reachable and builds faster than the others. musubi suits
working on each machine's own copy, building locally, and working offline.

## Tools for jj

jj's [roadmap](https://docs.jj-vcs.dev/latest/roadmap/) describes a server and daemon for
storing repositories and their operation logs in the cloud, like one Google runs internally,
with no date. [jj-sync](https://github.com/allouis/jj-sync) is a script that pushes and
fetches work in progress through a git remote under refs of its own, without the operation
log.

The facts about other tools here were checked on October 24, 2026.
