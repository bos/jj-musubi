# Documentation guidance

`docs/` holds the user guide. `docs/internals/` holds the contributor docs, which can use the
design's own terms. The rules below apply to the user guide, the README, built-in help, and
messages musubi prints.

## Audience and vocabulary

Readers know git and ssh, and some jj. In the guides and the reference, use jj's terms, such as
working copy, workspace, bookmark, and change id, without explaining them again.

The README, [how-it-works.md](how-it-works.md), [safety.md](safety.md) and the website's
landing page are also for readers who know git and have barely used jj, and who will leave
unless they quickly see what musubi does for them. Lead with what they get, in their own
work: picking up on another machine, agents on several machines, fetching and pushing once.
Say what a jj term means in a few words the first time it matters, and don't lead with the
operation log, which few jj users look at: it's how musubi works, not why anyone wants it.
Don't hedge about how new musubi is.

Use musubi's own nouns consistently:

- A **hub** is a `musubi hub` process and its directory. "The hub's machine" is where it
  runs.
- A **hive** is one repository as a hub knows it, with every machine's copy of it.
- A **machine** is a computer taking part, with one **daemon**. Its **copy** of a repository
  is a jj repository on it that belongs to a hive.
- To **join** is to make a copy part of a hive, and to **sync** is what the daemon does.

Don't use the design's internal terms in user docs: node, canonical operation, realization,
canonicalize, supersede, bundle, translation. Say what happens instead: "the hive's id for an
operation", "the operations this machine sent". Link to `docs/internals/` for the mechanism.

In messages and hints, name commands in full, as `musubi join`. In docs, quote messages as
musubi prints them.

## What commands print

musubi is a Unix tool used alongside jj, and prints as jj does: little, and only what the user
needs.

- A command that did what it was asked prints at most a line saying what changed, or nothing
  if that's obvious. A command whose output is what was asked for, such as `musubi list`,
  prints only that.
- Print no narration ("Saved ... as the default"), no settings or defaults the user didn't ask
  about, and no hint they needn't act on. Ids, counts and sequence numbers from inside musubi,
  such as a hive's operation number, aren't for users.
- A command that waits on a sync, as `create`, `join`, `clone` and `sync` do, shows on a
  terminal what the sync is doing, as jj shows a fetch, and clears it when done: silence there
  reads as a hang. Nothing shows when output isn't a terminal.
- An error is one line: what went wrong, in the user's terms, with no explanation of why
  musubi works that way. A hint, if any, is one more line naming the command to run. Why, and
  every other way out, belong in [troubleshooting.md](troubleshooting.md).
- Output a script reads goes to stdout, everything else to stderr, as in jj.

## Help and guides

Built-in `--help` is the reference for flags; its text is in the doc comments of
`crates/musubi/src/main.rs`. A command's first paragraph is its summary, for `-h` and the
command list; further paragraphs show only with `--help`. Guides explain when and why to use
a command, rather than repeating its flags.

## Where to edit

- [README.md](../README.md): what musubi is, installing, and the quick start.
- [how-it-works.md](how-it-works.md): what replicates, and how machines' changes combine.
- [safety.md](safety.md): what musubi promises, and how the proofs and tests check it, for
  readers deciding whether to trust it. Keep it in step with `docs/internals/` and
  `formal/README.md`, which it summarizes.
- `guides/`: workflows, step by step, upgrading included.
- `reference/`: every command, setting, file, and environment variable.
- [troubleshooting.md](troubleshooting.md): messages users see, and what to do about each.
- [comparison.md](comparison.md): other ways to do what musubi does. It cites its sources;
  recheck them, and update its date, when editing it.
- [README.md](README.md) here: the index, when pages are added or moved.

When a change adds a command, flag, setting, or message a user acts on, update the reference
and, where users will meet it, the troubleshooting page.
