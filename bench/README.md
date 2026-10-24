# Benchmarks

Scripts that measure musubi, on localhost, against `git clone` and `git fetch`, and against
`jj git clone`, `jj git fetch` and `jj git push`: time, and bytes on the wire as counted by a
TCP proxy. Where a script compares with git, the machine that clones does so twice, with
`jj git clone` and with plain `git clone`.

They need `/usr/bin/python3`, `git`, `jj`, `ssh-keygen` and a release build of `musubi`.

| Script | Measures |
| --- | --- |
| `bench.py REPO REPS` | Initial transfer (seed, clone, join with an existing clone), incremental changes from one machine to another, no-op syncs, a week away (upstream's commits land a day at a time, one machine works on them, and the other catches up at the end), daemon latency and idle traffic, and a clone after a long operation log. `--delay-ms` adds latency to every route. |
| `stalebase.py REPO PUSHES KB` | Whether a machine downloads again what it uploaded itself. |
| `oplog.py REPO N...` | How `musubi clone` scales with the length of the hive's operation log. |
| `daemonslots.py REPO N` | Whether a long-running daemon keeps up as received packs accumulate. |
| `report.py` | Markdown tables from the results of `bench.py` and `oplog.py`. |
| `tracestats.py`, `tracelist.py` | Summaries of the git processes in `GIT_TRACE2_EVENT` files. |

`proxy.py` is the byte-counting proxy the scripts start, and `env/` holds the jj and git
config they run with.

## Running

```sh
cargo build --release -p jj-musubi
bench/setup_sources.sh jj=$HOME/dev/jj git=https://github.com/git/git
/usr/bin/python3 -I bench/bench.py jj 5
/usr/bin/python3 -I bench/stalebase.py jj 5 200
```

`setup_sources.sh` builds the server repositories: a synthetic one, `small`, and a copy of
each `NAME=SOURCE` it is given, a local clone or a URL; a `NAME` is letters, digits and
underscores. Each has `main` as it was a week before its newest commit, for bench.py's week
phase to bring in the rest. The scripts take a repository by name.

The scripts pick free ports, so nothing else gets in their way, but run one at a time: each
measures time.

- `$MUSUBI_BENCH_DIR` holds the server repositories, runs and results; by default
  `bench/work`. Each run's hub listens on `runs/<run>/hub/run/hub.sock` in it, and each
  machine's daemon on `runs/<run>/cfg<machine>/daemon.sock`. A socket's path must fit in 103
  bytes (107 on Linux), so from a checkout with a long path, point `$MUSUBI_BENCH_DIR`
  somewhere shorter.
- `$MUSUBI` overrides the binary, by default `target/release/musubi`.
- `$MUSUBI_BENCH_PERF`, set to `perf record`'s options such as `-a -g`, runs each measurement
  of bench.py, stalebase.py and oplog.py under perf, into `runs/<run>/perf/`, and its result
  names the file.

`just bench-smoke` runs every script once, as briefly as each allows, against the small
repository and a debug build, in a directory of its own. CI runs it on Linux so that the
scripts keep up with the CLI. It measures nothing.

## What a measurement includes

Each machine has a state directory of its own, with its key already made. `musubi create`,
`join` and `clone` start a daemon to do their first sync, so their times include that; the
scripts then stop it, and only `musubi sync` moves anything until a script starts daemons
itself.

Machines reach the hub as they would over ssh, through one proxy route each, but without ssh
itself. `ssh.py` stands in for ssh, as `$MUSUBI_SSH`: given a `--hub` of `127.0.0.1:PORT`, it
connects to that route's port, and at the route's other end `sshd.py` runs
`musubi hub connect` for each connection. So:

- The bytes counted are musubi's own stream, without ssh's handshake, encryption and
  keepalives. (Keepalives go every 10 s on a quiet connection, and would about double idle
  daemons' traffic.)
- The times include starting `ssh.py`, a Python process, for each connection, but no
  handshake.
- Machines that aren't measured (the machine that creates the hive in `oplog.py`, and both
  machines in `daemonslots.py`) name the hub by its directory instead, as on the hub's
  machine.

## The canonical store

`crates/musubi-jj/examples/canonical.rs` measures the canonical store alone (the log of
canonical operations that the hub and each machine keep), without machines, a hub or the
network: how it keeps up as the operation log grows long, as busy agents make it. It builds a
store of `OPS` operations, each a snapshot of a working copy in a repository with 400 heads
and 200 bookmarks. It then times opening the store, walking every operation's parents as a
hub does on opening it, and what a join does: exporting every operation, working out which
commits they need, and importing them into an empty store. It also prints the log's size,
and, on the run that builds the store, one view's.

```sh
cargo run --release -p musubi-jj --example canonical -- /dev/shm/canonical 200000
cargo run --release -p musubi-jj --example canonical -- /dev/shm/canonical 200000 --import-only
```

If the directory already holds a store built to the end, the run uses it as it is, whatever
`OPS` says, so a second run skips building it. `--import-only` times only the import, of the
bundle the last run exported, for profiling it, as under `perf record`.
