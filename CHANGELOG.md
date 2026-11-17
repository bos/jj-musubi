# Changelog

## Unreleased

- Commands now reach the daemon in a new way, so a daemon from an earlier build must be
  restarted after you upgrade. The one exception is a daemon from a build that writes no build
  line to `daemon.pid`, which no newer build can stop: end it by hand once, by the process id
  the error message gives, then run `musubi daemon start`. After that, run the new build's
  `musubi daemon restart` after each upgrade, which stops the old daemon and starts one of the
  new build. A command from the new build says so, and does nothing else until you do. An older
  `musubi` can't stop a daemon of the new build: restart it with the new one. Stopping the
  daemon never signals a process: `musubi daemon stop` asks it to stop, and if it doesn't
  answer, says how to end it by hand.
- You forget another machine's workspace here, say `laptop/default`, and a sync shows it again.
  If you then run a `jj` command and, before syncing, `jj op abandon` the sync's operation, the
  workspace stays the laptop's. It used to become a workspace of this machine's own, and the
  laptop's showed beside it as `laptop-1a2b/default`.

## 0.47.0

This is the first pre-release.
