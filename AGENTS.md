# Working on jj-musubi

How coding agents work in this repository.

## Source control

This is a jj repository: use jj, never git.

## Checks

`just check` is the full local check (see the justfile). The test suite alone takes about
two minutes, so each check runs once, run by whoever owns it.

- While working, run only what the change touches: one test, one test file
  (`cargo nextest run -p musubi-jj --test join`), or one crate (`cargo nextest run -p
  musubi-jj`).
- Once the change is final, its author runs `just check`, and says in any request for review
  exactly which checks passed.
- A reviewer doesn't run the checks again, not even `cargo check`. A review reads the diff
  and reasons about it. Run one targeted test only when a specific finding depends on its
  result, and say so.
- After fixing what a review found, rerun only what the fixes can affect.

## Reviews

Have a subagent review every fix before it is pushed, and fix what the review finds first.

## Compatibility

musubi hasn't been released, so there is nothing to stay compatible with. Rename flags,
config keys and wire formats outright, with no aliases or migrations, and leave
`PROTOCOL_VERSION` alone.
