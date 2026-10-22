# Benchmarks

Scripts that measure jj-musubi against `git clone` and `git fetch`, and `jj git clone`,
`jj git fetch` and `jj git push`, on localhost: time, and bytes on the wire as counted by
a TCP proxy. They need `/usr/bin/python3`, `git`, `jj`, `ssh-keygen` and a release build
of `musubi`.

| Script | Measures |
| --- | --- |
| `bench.py REPO REPS` | Initial transfer (seed, clone, join with an existing clone), incremental changes from one machine to another, no-op syncs, a week away (upstream's commits land a day at a time, one machine works on them, and the other catches up at the end), daemon latency and idle traffic, and a clone after a long operation log. `--delay-ms` adds latency to every route. |
| `stalebase.py REPO PUSHES KB` | Whether a node downloads again what it uploaded itself. |
| `oplog.py REPO N...` | How `musubi clone` scales with the length of the hive's operation log. |
| `daemonslots.py REPO N` | Whether a long-running daemon keeps up as received packs accumulate. |
| `report.py` | Markdown tables from the results of `bench.py` and `oplog.py`. |
| `tracestats.py`, `tracelist.py` | Summaries of the git processes in `GIT_TRACE2_EVENT` files. |

`proxy.py` is the byte-counting proxy the scripts start; `env/` holds the jj and git
config they run with.

Machines reach the hub as they would over ssh, through one proxy route each. `ssh.py`, as
`$MUSUBI_SSH`, takes the `--hub` it is given, `127.0.0.1:PORT`, for a route's port and
relays to it, and at the route's other end `sshd.py` runs `musubi hub connect` for each
connection. The bytes counted are musubi's own stream, without ssh's handshake,
encryption and keepalives (every 10 s on a quiet connection, which would add about as
much again to idle daemons' traffic), and the times include starting `ssh.py`, a Python
process, for each connection, but no handshake. Machines that aren't measured, the first
in `oplog.py` and both in `daemonslots.py`, name the hub by its directory instead, as on
the hub's machine.
Each machine has a config directory of its own, with its key already made.
`musubi create`, `join` and `clone` start a daemon to do their first sync, so their times
include that; the scripts stop it, and only `musubi sync` moves anything until they start
daemons themselves.

## Running

```sh
cargo build --release -p musubi
bench/setup_sources.sh jj=$HOME/dev/jj git=https://github.com/git/git
/usr/bin/python3 -I bench/bench.py jj 5
/usr/bin/python3 -I bench/stalebase.py jj 5 200
```

`setup_sources.sh` builds the server repositories: a small synthetic one, and a copy of
each `NAME=SOURCE` it is given, a local clone or a URL; a `NAME` is letters, digits and
underscores. Each has `main` as it was a week before its newest commit, for bench.py's
week phase to bring in the rest; server repositories built before the week phase existed
need building again. The scripts take a repository by name (`small`, or a `NAME`).

In the git world, B is both a `jj git clone` and a plain `git clone`. With
`$MUSUBI_BENCH_PERF` set to `perf record`'s options, such as `-a -g`, each measurement
(of bench.py, stalebase.py and oplog.py) runs under perf, into `runs/<run>/perf/`, and its
result names the file.

Server repositories, runs and results go under `$MUSUBI_BENCH_DIR`, by default
`bench/work`. `$MUSUBI` overrides the binary, by default `target/release/musubi`. Each run's
hub listens on a socket in its directory, `runs/<run>/hub/run/hub.sock`, and each
machine's daemon on `runs/<run>/cfg<machine>/daemon.sock`, whose paths must fit in 103
bytes (107 on Linux): from a checkout with a long path, point `$MUSUBI_BENCH_DIR`
somewhere shorter.

The scripts listen on ports that are free when they start, so nothing else gets in their
way, but run one at a time: each measures time.

`just bench-smoke` runs every script once, as briefly as each allows, against the small
repository and a debug build, in a directory of its own; CI runs it on Linux, so that the
scripts keep up with the CLI. It measures nothing.
