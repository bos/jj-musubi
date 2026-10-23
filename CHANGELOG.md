# Changelog

What changes in each release of musubi, and what to do on upgrading. Until 1.0, a release may
change the protocol, so run the same release on the hub and every machine (see
[Upgrading](README.md#upgrading)).

## Unreleased

- musubi completes its commands, flags, and hive and hub names in your shell, once you add a
  line to your shell's startup file, and `musubi completion <shell>` prints a completion
  script. See
  [Complete commands in your shell](docs/reference/commands.md#complete-commands-in-your-shell).

## 0.1.0

The first release. musubi keeps a jj repository in sync across your machines by replicating
its operation log, through a hub on one machine that the others reach over ssh.

- `musubi hub` runs a hub, which serves any number of repositories, each its own hive.
- `musubi create` starts a hive from a repository, `musubi join` adds another machine's copy
  of it, and `musubi clone` makes a new copy.
- A daemon on each machine keeps its repositories in sync, and catches up after the machine
  was offline. `musubi daemon install` starts it at login, with launchd on macOS, systemd on
  Linux, or the registry on Windows.
- `musubi list` shows the hub's hives and how each copy's syncing goes, `musubi sync` syncs
  now, and `musubi leave` stops syncing a repository. `musubi hub rename` and `musubi hub rm`
  manage the hub's hives.
- musubi works with jj 0.46.0. It stops with an error rather than sync an operation that a
  newer `jj` wrote with fields jj 0.46.0 doesn't know.
- Builds for Linux (static, x86_64 and aarch64), macOS (x86_64 and aarch64), and Windows
  (x86_64 and aarch64).
- Published on crates.io as `jj-musubi`.
