# Documentation guidance

`docs/` holds the user guide. `docs/internals/` holds the contributor docs, which can use the
design's own terms. The rules below apply to the user guide, the README, built-in help, and
messages musubi prints.

## Audience and vocabulary

Readers know jj, git, and ssh. Use jj's terms, such as operation, working copy, workspace,
bookmark, and change id, without explaining them again.

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

## Help and guides

Built-in `--help` is the reference for flags; its text is in the doc comments of
`crates/musubi/src/main.rs`. A command's first paragraph is its summary, for `-h` and the
command list; further paragraphs show only with `--help`. Guides explain when and why to use
a command, rather than repeating its flags.

## Where to edit

- [README.md](../README.md): what musubi is, installing, and the quick start.
- [how-it-works.md](how-it-works.md): what replicates, and how machines' changes combine.
- `guides/`: workflows, step by step, upgrading included.
- `reference/`: every command, setting, file, and environment variable.
- [troubleshooting.md](troubleshooting.md): messages users see, and what to do about each.
- [comparison.md](comparison.md): other ways to do what musubi does. It cites its sources;
  recheck them, and update its date, when editing it.
- [README.md](README.md) here: the index, when pages are added or moved.

When a change adds a command, flag, setting, or message a user acts on, update the reference
and, where users will meet it, the troubleshooting page.
