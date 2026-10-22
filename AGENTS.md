# Working on jj-musubi

How coding agents work in this repository.

## Source control

This is a jj repository: use jj, never git.

## Checks

`just check` is the full local check (see the justfile). The test suite alone takes about
two minutes, so each check runs once, run by whoever owns it.

- While working, run only what the change touches: typically one test, one test file
  (`cargo nextest run -p musubi-jj -E 'test(/^join::/)'`), or one crate
  (`cargo nextest run -p musubi-jj`).
- Don't ask for a review if any checks fail. Fix them first.
- Once the change is final, its author runs `just check`, and says in any request for review
  either exactly which checks passed if a subset, or otherwise that all of them did.
- A reviewer doesn't run the checks again, not even `cargo check`. A review reads the diff
  and reasons about it. Run one targeted test only when a specific finding depends on its
  result, and say so.
- After fixing what a review found, rerun only what the fixes can affect.

## Reviews

Have a subagent review every fix before it is pushed, and fix what the review finds first.

## Resilience

The hub only stitches together copies of a repository that exist anyway, so it needn't be
durable: a hub that loses its state is deleted and made again. Don't add durability, or
recovery from torn files, to it.

musubi makes no synchronous fsyncs, on the hub or on any machine: surviving a power cut isn't
a goal. A sync in the background, off the path of every request, is fine. ext4 also writes a
file out at once in two cases (`auto_da_alloc`): when a file truncated to nothing is closed,
even one empty already, and when a file is renamed over another. So on a path that runs
often:

- Write a tempfile through its own handle, never by reopening its path.
- Don't rewrite a file whose contents haven't changed.
- Overwrite in place (then `set_len`) or append, rather than replace.

## Compatibility

Until 1.0, musubi promises no compatibility with earlier releases. Rename flags, config keys
and wire formats outright, with no aliases or migrations, but:

- If a change alters the wire format and `PROTOCOL_VERSION` hasn't changed since the latest
  `v*` tag (`jj tag list`), bump it, so that machines and hubs of different releases refuse
  each other, saying so; with no tag yet, leave it alone. Never change how an `Envelope`
  encodes the versions it starts with: every release reads them first.
- Say what breaks, and what a user must do on upgrading, under an Unreleased heading at the top
  of `CHANGELOG.md`, adding the heading if it's missing.
