# Changelog

## Unreleased

- Commands now reach the daemon in a new way, so a daemon from an earlier build must be
  restarted after you upgrade. A command from the new build says so, and does nothing else until
  you run the new build's `musubi daemon restart`, which stops the old daemon and starts one of
  the new build. On Windows, the new build's `musubi daemon restart` force-stops a daemon from
  an earlier build, with no cleanup. An older `musubi` can't stop a daemon of the new build:
  restart it with the new one.

## 0.47.0

This is the first pre-release.
