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

## 0.47.0

This is the first pre-release.
