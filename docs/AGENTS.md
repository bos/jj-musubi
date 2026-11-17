# Documentation guidance

`docs/` holds the user guide. `docs/internals/` holds the contributor docs, which can use the
design's own terms. The rules below apply to the user guide, the README, built-in help, and
messages printed by `musubi`.

## Audience and vocabulary

Readers know git and ssh, and some jj. In the guides and the reference, use jj's terms, such as
working copy, workspace, bookmark, and change id, without explaining them again.

The README, [how-it-works.md](how-it-works.md), [safety.md](safety.md) and the website's
landing page are also for readers who know git and have barely used jj, and who will leave
unless they quickly see what jj-musubi does for them. Lead with what they get, in their own
work: picking up on another machine, agents on several machines, fetching and pushing once.
Say what a jj term means in a few words the first time it matters, and don't lead with the
operation log, which few jj users look at: it's how jj-musubi works, not why anyone wants it.
Don't hedge about how new jj-musubi is.

Cut filler, repetition and needless qualification. Keep a modifier when removing it would
change the claim or the action a reader should take, and state that distinction directly.
Review whole paragraphs and sections: give each explanation one home, place it where the
reader needs it, and link back instead of repeating it. Cut sentences that announce a topic
without explaining it and reassurance unsupported by concrete behavior or evidence.
Describe checks through commands and observable results. Keep supported jj-version
prerequisites out of the prose; dependency metadata owns version pins.

Introduce concepts where the reader first needs them. Say what a hub, hive, daemon or
snapshot does and why it matters before relying on the term, including on pages reached
directly from search. A definition later in the guide doesn't fix an unexplained first use.
Distinguish recorded work arriving in a repository from checkout files changing on disk.

Write guides around the reader's task. Setup names the machine, terminal and directory for
each step, explains commands that keep running, and ends with a successful-sync check.
Troubleshooting starts with the symptom, how to establish the current state, and safe next
actions; explanations of rare causes follow the recovery steps. State when a diagnostic is
cached, snapshots files, contacts the hub, or exits successfully despite reporting a problem.

Give safety reassurance through concrete behavior and evidence. Explain what sync changes,
what mistakes propagate, how to pause or leave, and what survives each action. Describe the
scope of proofs and tests without turning them into a blanket guarantee. Keep operating
instructions near the actions that need them, with links to deeper evidence.

Call the software package and project **jj-musubi**. Its command and executable are **`musubi`**;
format command names as code, including standalone mentions. Keep literal names unchanged:
configuration keys such as `musubi.hub`, paths such as `.jj/repo/musubi`, service names,
environment variables, and quoted command output.

Prefer “repo” and “repos” in prose. “Repository” or “repositories” may introduce the term
on its first mention in a file. Keep commands, identifiers and quoted output as printed.

Use jj-musubi's own nouns consistently:

- A **hub** is a `musubi hub` process and its directory. "The hub's machine" is where it
  runs.
- A **hive** is one repo as a hub knows it, with every machine's copy of it.
- A **machine** is a computer taking part, with one **daemon**. Its **copy** of a repo
  is a jj repo on it that belongs to a hive.
- To **join** is to make a copy part of a hive, and to **sync** is what the daemon does.

Don't use the design's internal terms in user docs: node, canonical operation, realization,
canonicalize, supersede, bundle, translation. Say what happens instead: "the hive's id for an
operation", "the operations this machine sent". Link to `docs/internals/` for the mechanism.

In messages and hints, name commands in full, as `musubi join`. In docs, quote messages as
`musubi` prints them.

## What commands print

The `musubi` command runs alongside jj, and prints as jj does: little, and only what the user
needs.

- A command that did what it was asked prints at most a line saying what changed, or nothing
  if that's obvious. A command whose output is what was asked for, such as `musubi list`,
  prints only that.
- Print no narration ("Saved ... as the default"), no settings or defaults the user didn't ask
  about, and no hint they needn't act on. Ids, counts and sequence numbers from inside jj-musubi,
  such as a hive's operation number, aren't for users.
- A command that waits on a sync, as `create`, `join`, `clone` and `sync` do, shows on a
  terminal what the sync is doing, as jj shows a fetch, and clears it when done: silence there
  reads as a hang. Nothing shows when output isn't a terminal.
- An error is one line: what went wrong, in the user's terms, with no explanation of why
  jj-musubi works that way. A hint, if any, is one more line naming the command to run. Put
  further explanation in the guide that owns the workflow.
- Output a script reads goes to stdout, everything else to stderr, as in jj.

## Help and guides

Built-in `--help` is the reference for flags; its text is in the doc comments of
`crates/musubi/src/cli.rs`. A command's first paragraph is its summary, for `-h` and the
command list; further paragraphs show only with `--help`. Guides explain when and why to use
a command, rather than repeating its flags.

Each page starts with a short introduction beneath its heading. Keep that prose in the guide: the
website displays it and uses the opening paragraph for search and index descriptions.

## Where to edit

- [README.md](../README.md): what jj-musubi is and links into the user guide.
- [get-started.md](get-started.md): installing and connecting the first machines. The website
  imports this complete page; never assemble a website page from README sections.
- [how-it-works.md](how-it-works.md): what replicates, what stays local, and how machines'
  changes combine. Keep mechanisms and maintenance procedures in their own guides or internals.
- [safety.md](safety.md): what jj-musubi promises, and how the proofs and tests check it, for
  readers deciding whether to trust it. Keep it in step with `docs/internals/` and
  `formal/README.md`, which it summarizes. Link to detailed proof and test catalogues there.
- [guides/setup.md](guides/setup.md): prerequisites through the first sync and its checks, then
  persistent services and optional setup choices.
- [guides/working-across-machines.md](guides/working-across-machines.md): handoffs, agents,
  stale files, undo, conflicts, and fetching and pushing.
- [guides/snapshots.md](guides/snapshots.md): the complete workflow for inspecting, excluding,
  saving, pruning or approving snapshot content. Keep cleanup hazards beside cleanup commands.
- [guides/manage.md](guides/manage.md): checking sync reports, membership, leases, pause/leave,
  uninstalling, moving copies and replacing hubs.
- [guides/upgrading.md](guides/upgrading.md): release upgrades by hand or with automatic
  installers, including building releases from source. Keep intermediate builds out of the
  user guide.
- [reference/commands.md](reference/commands.md): command lookup, output contracts, dashboard
  controls, JSON, completion and diagnostic commands. Built-in help owns flag syntax.
- [reference/configuration.md](reference/configuration.md): setting semantics, environment,
  SSH key and agent details, logging and paths.
- [troubleshooting.md](troubleshooting.md): common symptoms, immediate safe actions and links
  to complete workflows. It owns new-copy history rescue. Keep it short; do not catalogue errors
  whose messages and hints already give the recovery action.
- [comparison.md](comparison.md): other ways to do what jj-musubi does. It cites its sources;
  recheck them, and update its date, when editing it.
- [README.md](README.md) here: the index, when pages are added or moved.

Use short summaries at entry points and link to the owning page for a complete procedure.
When moving a section, update incoming links across the repo and read the resulting
pages as a continuous task. Check prerequisites, success checks and consequences at each step.

When a change adds a command, flag, setting, or message a user acts on, update the reference
or owning guide. Update troubleshooting when it changes how a common problem is diagnosed
or recovered from.
