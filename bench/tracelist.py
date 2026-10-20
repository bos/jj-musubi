"""List each top-level git process in GIT_TRACE2_EVENT files: elapsed seconds and argv."""
import json, sys
starts, exits = {}, {}
for path in sys.argv[1:]:
    for line in open(path):
        try:
            e = json.loads(line)
        except ValueError:
            continue
        sid = e.get("sid", "")
        if "/" in sid:
            continue
        if e.get("event") == "start":
            starts[sid] = (e.get("time"), e.get("argv", []))
        elif e.get("event") in ("exit", "atexit"):
            exits[sid] = e.get("t_abs", 0.0)
for sid, (t, argv) in sorted(starts.items(), key=lambda kv: kv[1][0] or ""):
    print(f"{t} {exits.get(sid, 0):8.3f}s {' '.join(argv[1:])[:100]}")
