# Benchmarks

Scripts that measure jj-musubi against `jj git clone`, `jj git fetch` and `jj git push`
on localhost: time, and bytes on the wire as counted by a TCP proxy. They need `python3`,
`git`, `jj`, `nats-server` and a release build of `musubi`.

| Script | Measures |
| --- | --- |
| `bench.py REPO REPS` | Initial transfer (seed, clone, join with an existing clone), incremental changes from one machine to another, no-op syncs, daemon latency and idle traffic, and a clone after a long operation log. `--delay-ms` adds latency to every route. |
| `stalebase.py REPO PUSHES KB` | Whether a node downloads again what it uploaded itself. |
| `oplog.py REPO N...` | How `musubi clone` scales with the length of the hive's operation log. |
| `daemonslots.py REPO N` | Whether a long-running daemon keeps up as received packs accumulate. |
| `report.py` | Markdown tables from the results of `bench.py` and `oplog.py`. |
| `tracestats.py`, `tracelist.py` | Summaries of the git processes in `GIT_TRACE2_EVENT` files. |

`proxy.py` is the byte-counting proxy the scripts start; `env/` holds the jj and git
config they run with.

## Running

```sh
cargo build --release -p musubi
JJ_SRC=~/dev/jj GIT_SRC=~/dev/git bench/setup_sources.sh
/usr/bin/python3 -I bench/stalebase.py jj 5 200
```

`setup_sources.sh` builds the server repositories: a small synthetic one, and copies of
local clones of jj and git when `JJ_SRC` and `GIT_SRC` name them. The scripts take a
repository by name (`small`, `jj`, `git`).

Server repositories, runs and results go under `$MUSUBI_BENCH_DIR`, by default
`bench/work`. `$MUSUBI` overrides the binary, by default `target/release/musubi`.

The scripts use fixed ports (47222, 47822, 47418, and 47501 to 47599), so run one at a
time.
