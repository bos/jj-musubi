# jj-musubi: live sync for jujutsu

jj-musubi keeps your [jujutsu (jj)](https://jj-vcs.dev) repositories in sync across machines,
including work in progress. This lets you work on your laptop, then pick up on another machine
where you left off, without needing to stop and commit. Syncing runs in the background.

One machine runs a **hub**, which stores shared history and coordinates updates. A **daemon** on
each machine that you do work on talks to the hub over ssh to sync its local repos. A collection
of synced copies of a repo is a **hive**. One hub can serve many hives.

Engineers at Meta have similar workflows via Sapling's Commit Cloud, and engineers at Google
from an internal jj server. jj-musubi brings these workflows to your own machines. It's similar
to extending jj's concept of a workspace to multiple machines.

## What jj-musubi makes possible

jj-musubi's syncing makes repos on different machines operate like jj workspaces. They each
retain their own local histories, so they work fine offline, but when online they continually
sync live.

- **Share in-progress work between machines.** Commits, rebases, snapshots, and so on should
  sync within moments of jj completing an operation. Other machines show the laptop's
  working-copy commit as `laptop/default@` in `jj log`, ready to check out.
- **Run coding agents in parallel.** Give agents on multiple machines their own workspaces, then
  review, build, or extend that work from any machine. A [skill for
  agents](skills/jj-musubi/SKILL.md) helps agents coordinate.
- **Fetch or push once.** Run `jj git fetch` on one machine, and every machine gets the new
  `main@origin`. Push from your devbox and your laptop shows it pushed.
- **Work offline.** Keep working while disconnected. Your laptop and other machines catch up
  once you're back online.
- **Megamerge across machines.** A unique jj party trick is the [megamerge
  workflow](https://isaaccorbrey.com/notes/jujutsu-megamerges-for-fun-and-profit). I've never
  personally used it, but jj-musubi makes it easy to do across multiple machines.

```text
laptop:~/src/app$ jj describe -m "Add retry logic to the fetcher"
Working copy  (@) now at: kkmpptxz 8d0b4e11 Add retry logic to the fetcher
Parent commit (@-)      : zzzzzzzz 00000000 (empty) (no description set)

devbox:~/src/app$ jj log
@  vruxwmqv me@example.com 2026-10-23 10:14:02 default@ 3f2a1c9e
│  (empty) (no description set)
│ ○  kkmpptxz me@example.com 2026-10-23 10:14:01 laptop/default@ 8d0b4e11
├─╯  Add retry logic to the fetcher
◆  zzzzzzzz root() 00000000
```

Run `jj new laptop/default@` on the devbox to check out a new change based on that work.
The [handoff guide](docs/guides/working-across-machines.md#pick-up-on-another-machine) covers
switching back.

Machine-checked proofs model the sync protocol. Tests compare the implementation with those
models and inject failures into syncs between jj repos. [Understanding jj-musubi
safety](docs/safety.md) covers what sync changes, how the checks test it, and their limits.

## Get started

[Get started](https://www.serpentine.com/software/jj-musubi/get-started/) covers installing
jj-musubi and connecting your first machines. For service installation and other setup choices,
see the [setup guide](https://www.serpentine.com/software/jj-musubi/guides/set-up/).

## Learn more

- [How jj-musubi works](docs/how-it-works.md): what replicates and what stays on each machine.
- [Work across machines](docs/guides/working-across-machines.md): handoffs, coding agents,
  stale working copies and undo.
- [Manage hives, machines and hubs](docs/guides/manage.md): membership, leaving and replacing
  a hub.
- [Snapshot limits and cleanup](docs/guides/snapshots.md): inspect and resolve held work.
- [Command reference](docs/reference/commands.md),
  [configuration and logging](docs/reference/configuration.md), and
  [shell completion](docs/reference/commands.md#complete-commands-in-your-shell)
- [Other approaches](docs/comparison.md): Git remotes, file syncing and working over ssh.

The [user guide](docs/README.md) lists every page; `musubi <command> --help` lists every flag.

## License

Copyright 2026 Voxel Labs, Inc. Licensed under the [Apache License, Version 2.0](LICENSE).
