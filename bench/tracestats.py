"""Summarize a GIT_TRACE2_EVENT file: git subprocesses by command, count and total time."""
import json, sys, collections
starts, exits = {}, {}
for path in sys.argv[1:]:
    for line in open(path):
        try:
            e = json.loads(line)
        except ValueError:
            continue
        sid = e.get("sid", "")
        if "/" in sid:  # child of another git process
            continue
        if e.get("event") == "start":
            starts[sid] = e.get("argv", [])
        elif e.get("event") in ("exit", "atexit"):
            exits[sid] = e.get("t_abs", 0.0)
agg = collections.defaultdict(lambda: [0, 0.0])
for sid, argv in starts.items():
    cmd = " ".join(argv[1:]) or argv[0]
    agg[cmd][0] += 1
    agg[cmd][1] += exits.get(sid, 0.0)
for cmd, (n, t) in sorted(agg.items(), key=lambda kv: -kv[1][1]):
    print(f"{n:6d} {t:9.3f}s  {cmd}")
