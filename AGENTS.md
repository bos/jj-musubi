# Working on jj-musubi

The working agreement for this repository, for people and coding agents alike.
[CONTRIBUTING.md](CONTRIBUTING.md) covers setup and the slow runs outside `just check`.

## Priorities

musubi rewrites people's jj repositories where they work, across machines, so correctness and
robustness come first: the Lean models, conformance tests, fuzzing and the end-to-end search
are never paused or cut to make room for other work. What users see gets the same care
alongside them, not after: a confusing message, or a step that doesn't work as the guide says,
is a bug like any other.

## Source control

This is a jj repository: use jj, never git.

## Checks

`just check` runs every local check (see the justfile). The test suite alone takes about two
minutes, so each check runs once, by whoever owns it:

- While working, run only what the change touches: typically one test, one test file
  (`cargo nextest run -p musubi-jj -E 'test(/^join::/)'`), or one crate
  (`cargo nextest run -p musubi-jj`).
- Fix any failing check before asking for a review.
- Once the change is final, its author runs `just check`. A request for review says that all
  checks passed, or, if only a subset ran, exactly which passed.
- A reviewer doesn't run the checks again, not even `cargo check`, but reads the diff and
  reasons about it. Run one targeted test only when a specific finding depends on its result,
  and say so.
- After acting on a review, rerun only what those changes can affect.

## Tests

Before adding, changing, removing, or reviewing a test, read
[docs/internals/testing-philosophy.md](docs/internals/testing-philosophy.md). Write new tests as
[docs/internals/efficient-tests.md](docs/internals/efficient-tests.md) says. Restructure an
existing test to fit it, or measure as it describes, only when the task is making tests
faster; otherwise run the checks as above.

## Reviews

Have subagents review every change before it is pushed, as
[docs/internals/code-reviews.md](docs/internals/code-reviews.md) says: a change to a command,
message, help text or the user guide gets a reviewer reading it as a new user would. Evaluate
each finding: decide whether it is correct, since a finding can be wrong, and if so, what to do
about it, and do that before pushing.

## Resilience

The hub only stitches together copies of a repository that exist anyway, so it needn't be
durable: a hub that loses its state is deleted and made again. Don't add durability, or
recovery from torn (partly written) files, to it.

musubi makes no synchronous fsyncs, on the hub or on any machine: surviving a power cut isn't
a goal. A sync in the background, off the path of every request, is fine. ext4
(`auto_da_alloc`) also writes a file out at once in two cases: when a file truncated to
nothing is closed, even one empty already, and when a file is renamed over another. So on a
path that runs often:

- Write a tempfile through its own handle, never by reopening its path.
- Don't rewrite a file whose contents haven't changed.
- Overwrite in place (then `set_len`) or append, rather than replace.

## Compatibility

Until 1.0, musubi promises no compatibility with earlier releases. Rename flags, config keys
and wire formats outright, with no aliases or migrations, but:

- If a change alters the wire format and `PROTOCOL_VERSION` hasn't changed since the latest
  `v*` tag (`jj tag list`), bump it, so that machines and hubs of different releases refuse
  each other, saying so; with no tag yet, leave it alone. Never change how an `Envelope`
  (`crates/musubi-sync/src/wire.rs`) encodes the versions it starts with: every release reads
  them first.
- Say what breaks, and what a user must do on upgrading, under an Unreleased heading at the top
  of `CHANGELOG.md`, adding the heading if it's missing.

## Style

- Comments and Markdown wrap at 98 columns; rustfmt formats code at 100.
- A commit's subject says what it does in plain words, as an imperative sentence with no
  trailing period: "Refuse bytes after the end of a frame or a message". Its body, if it
  needs one, says why.

## Documentation

`docs/` is the user guide and `docs/internals/` the contributor docs.
[docs/AGENTS.md](docs/AGENTS.md) says which page owns what, and the vocabulary for users. A
change to what users see updates the user guide and the built-in help with it.
