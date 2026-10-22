"""Turns results/*.json into Markdown tables (median, with min-max in brackets)."""

import json
import os
import statistics
import sys

B = os.path.dirname(os.path.abspath(__file__))
WORK = os.environ.get("MUSUBI_BENCH_DIR") or f"{B}/work"
RESULTS = f"{WORK}/results"
# The README's repositories first, smallest first; then the others by name.
ORDER = ("small", "jj", "git")


def ordered(names):
    return sorted(names, key=lambda r: (ORDER.index(r) if r in ORDER else len(ORDER), r))


NAMES = os.listdir(RESULTS) if os.path.isdir(RESULTS) else []
# bench.py's results, by repository; the other scripts' names, and delayed runs', have a dash,
# which a repository's name never does.
REPOS = ordered(n[:-5] for n in NAMES if n.endswith(".json") and "-" not in n)


def load(r):
    with open(f"{RESULTS}/{r}.json") as f:
        return json.load(f)


def fmt_b(n):
    n = float(n)
    for unit in ("B", "KiB", "MiB", "GiB"):
        if abs(n) < 1024 or unit == "GiB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024


def fmt_t(t):
    return f"{t * 1000:.0f} ms" if t < 1 else f"{t:.2f} s"


def stat(values, f):
    values = [v for v in values if v is not None]
    if not values:
        return "-"
    med = statistics.median(values)
    lo, hi = min(values), max(values)
    if len(values) == 1 or lo == hi:
        return f(med)
    return f"{f(med)} [{f(lo)}–{f(hi)}]"


def initial():
    print("### Initial transfer (second machine)\n")
    print("| repo | tool | time | bytes down | bytes up | total |")
    print("| --- | --- | --- | --- | --- | --- |")
    for r in REPOS:
        d = load(r)["initial"]
        rows = [
            ("`git clone`", d.get("plain_git_clone_B", [])),
            ("`jj git clone`", d["git_clone_B"]),
            ("`musubi clone`", d["musubi_clone_B"]),
            ("`musubi join` (has a git clone already)", [d["musubi_join_existing_C"]]),
            ("first machine `musubi create` (seeds hub)", [d["musubi_seed_A"]]),
        ]
        for name, ms in rows:
            if not ms:
                continue
            print(
                f"| {r} | {name} | {stat((m['t'] for m in ms), fmt_t)} | "
                f"{stat((m['down'] for m in ms), fmt_b)} | {stat((m['up'] for m in ms), fmt_b)} | "
                f"{stat((m['total'] for m in ms), fmt_b)} |"
            )
    print()


def scenarios():
    print("### Incremental changes, A to B\n")
    print(
        "| repo | change | ops | jj git push | musubi push (A) | git fetch | jj git fetch "
        "| musubi fetch (B) | jj git total bytes | musubi total bytes |"
    )
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for r in REPOS:
        sc = load(r).get("scenarios", {})
        for s, rows in sc.items():
            if not rows:
                continue
            g = lambda k, f: stat(  # noqa: E731
                (row[k][f] if k in row else None for row in rows), fmt_b if f != "t" else fmt_t
            )
            ops = statistics.median(row["hub_store"]["n_ops"] for row in rows)
            print(
                f"| {r} | {s} | {ops:.0f} | {g('git_push', 't')}, {g('git_push', 'total')} | "
                f"{g('musubi_push', 't')}, {g('musubi_push', 'total')} | "
                f"{g('plain_git_fetch', 't')}, {g('plain_git_fetch', 'total')} | "
                f"{g('git_fetch', 't')}, {g('git_fetch', 'total')} | "
                f"{g('musubi_fetch', 't')}, {g('musubi_fetch', 'total')} | "
                f"{stat((row['git_push']['total'] + row['git_fetch']['total'] for row in rows), fmt_b)} | "
                f"{stat((row['musubi_push']['total'] + row['musubi_fetch']['total'] for row in rows), fmt_b)} |"
            )
    print()
    print("Hub-side detail (musubi): what each push added to the hub store\n")
    print("| repo | change | ops | view bytes | op bytes | pack bytes |")
    print("| --- | --- | --- | --- | --- | --- |")
    for r in REPOS:
        sc = load(r).get("scenarios", {})
        for s, rows in sc.items():
            if not rows:
                continue
            hs = lambda k: stat((row["hub_store"][k] for row in rows), fmt_b)  # noqa: E731
            print(
                f"| {r} | {s} | {statistics.median(row['hub_store']['n_ops'] for row in rows):.0f} | "
                f"{hs('views_bytes')} | {hs('ops_bytes')} | {hs('pack_bytes')} |"
            )
    print()


def noop():
    print("### No-op sync\n")
    print("| repo | git fetch | jj git fetch | jj git push | musubi sync (B) | musubi sync (A) |")
    print("| --- | --- | --- | --- | --- | --- |")
    for r in REPOS:
        no = load(r).get("noop")
        if not no:
            continue
        cell = lambda k: f"{stat((m['t'] for m in no.get(k, [])), fmt_t)}, {stat((m['total'] for m in no.get(k, [])), fmt_b)}"  # noqa: E731
        print(
            f"| {r} | {cell('plain_git_fetch')} | {cell('git_fetch')} | {cell('git_push')} | "
            f"{cell('musubi_B')} | {cell('musubi_A')} |"
        )
    print()


def week():
    print("### A week away: B catches up\n")
    print(
        "Upstream's commits land on main a day at a time, and each day A fetches them, rebases "
        "its feature onto them and works on it, and pushes (in musubi's world, syncs). B, away "
        "all week, then catches up at once.\n"
    )
    print(
        "| repo | upstream commits | hub ops | git fetch | jj git fetch | musubi sync (B) "
        "| A's daily jj git push | A's daily musubi sync |"
    )
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for r in REPOS:
        wk = load(r).get("week")
        if not wk:
            continue
        cell = lambda m: f"{fmt_t(m['t'])}, {fmt_b(m['total'])}"  # noqa: E731
        daily = lambda k: (  # noqa: E731
            f"{stat((m['t'] for m in wk.get(k, [])), fmt_t)}, "
            f"{stat((m['total'] for m in wk.get(k, [])), fmt_b)}"
        )
        print(
            f"| {r} | {wk['upstream_commits']} | {wk['hub_store']['n_ops']} | "
            f"{cell(wk['plain_git_fetch'])} | {cell(wk['git_fetch'])} | "
            f"{cell(wk['musubi_fetch'])} | {daily('git_A_pushes')} | {daily('musubi_A_syncs')} |"
        )
    print()


def daemon():
    print("### Latency: operation on A until visible on B\n")
    print("| repo | musubi daemons | bytes A/B per op | git push+fetch | bytes A/B |")
    print("| --- | --- | --- | --- | --- |")
    for r in REPOS:
        dm = load(r).get("daemon")
        if not dm:
            continue
        ml, gl = dm["musubi_latency"], dm["git_latency"]
        print(
            f"| {r} | {stat((m['latency'] for m in ml), fmt_t)} | "
            f"{fmt_b(statistics.median(m['A_bytes'] for m in ml))} / "
            f"{fmt_b(statistics.median(m['B_bytes'] for m in ml))} | "
            f"{stat((m['latency'] for m in gl), fmt_t)} | "
            f"{fmt_b(statistics.median(m['A_bytes'] for m in gl))} / "
            f"{fmt_b(statistics.median(m['B_bytes'] for m in gl))} |"
        )
    print()
    print("Idle daemons\n")
    for r in REPOS:
        dm = load(r).get("daemon")
        if not dm:
            continue
        i = dm["idle"]
        per_hour = lambda n: fmt_b(n * 3600 / i["seconds"])  # noqa: E731
        print(
            f"- {r}: over {i['seconds']:.0f} s, node A {i['A_up'] + i['A_down']} B, node B "
            f"{i['B_up'] + i['B_down']} B ({per_hour(i['A_up'] + i['A_down'])}/hour per node)"
        )
    print()


def disk():
    print("### Disk use\n")
    keys = [
        ("git_server", "git server (bare)"),
        ("hub_total", "musubi hub total"),
        ("hub_git", "  hub git/"),
        ("hub_canonical", "  hub canonical/"),
        ("hub_blobs", "  hub blobs/"),
        ("A_git", "git-world A .git"),
        ("A_jj", "git-world A .jj"),
        ("Am_git", "musubi A .git"),
        ("Am_jj", "musubi A .jj"),
        ("Am_musubi", "  of which .jj/repo/musubi"),
        ("B_git", "git-world B .git"),
        ("B_jj", "git-world B .jj"),
        ("Bp_git", "plain git B .git"),
        ("Bm_git", "musubi B .git"),
        ("Bm_jj", "musubi B .jj"),
        ("Bm_musubi", "  of which .jj/repo/musubi"),
    ]
    whens = ("disk_after_initial", "disk_after_scenarios", "disk_after_week")
    print(
        "| | "
        + " | ".join(f"{r} (after initial / after scenarios / after week)" for r in REPOS)
        + " |"
    )
    print("| --- |" + " --- |" * len(REPOS))
    for k, name in keys:
        cells = []
        for r in REPOS:
            d = load(r)
            sizes = (d.get(when, {}).get(k) for when in whens)
            cells.append(" / ".join(fmt_b(n) if n is not None else "-" for n in sizes))
        print(f"| {name} | " + " | ".join(cells) + " |")
    print()
    for r in REPOS:
        d = load(r)
        for when in whens:
            hs = d.get(when, {}).get("hub_store")
            if hs:
                print(f"- {r} {when}: hub has {hs['n_ops']} ops ({fmt_b(hs['ops_bytes'])}), "
                      f"{hs['n_views']} views ({fmt_b(hs['views_bytes'])}), {hs['n_packs']} packs "
                      f"({fmt_b(hs['pack_bytes'])})")
    print()


def oplog():
    print("### Clone after a long operation log\n")
    for r in REPOS:
        ol = load(r).get("oplog")
        if not ol:
            continue
        c = ol["clone_D"]
        first = load(r)["initial"]["musubi_clone_B"]
        print(
            f"- {r}: after {ol['added']['n_ops']} more ops ({fmt_b(ol['added']['views_bytes'])} of views), "
            f"`musubi clone` took {fmt_t(c['t'])} and {fmt_b(c['total'])}, versus "
            f"{fmt_t(statistics.median(m['t'] for m in first))} and "
            f"{fmt_b(statistics.median(m['total'] for m in first))} on a fresh hive"
        )
    for r in ordered(n[len("oplog-") : -5] for n in NAMES if n.startswith("oplog-")):
        p = f"{RESULTS}/oplog-{r}.json"
        if os.path.exists(p):
            d = json.load(open(p))
            print(f"\n{r} (oplog.py): `jj git clone` {fmt_t(d['git_clone']['t'])}, {fmt_b(d['git_clone']['total'])}\n")
            print("| hub ops | clone time | clone bytes | B's .jj |")
            print("| --- | --- | --- | --- |")
            for m in d["points"]:
                print(f"| {m['hub_ops']} | {fmt_t(m['t'])} | {fmt_b(m['total'])} | {fmt_b(m['disk_jj'])} |")
    print()


if __name__ == "__main__":
    initial()
    scenarios()
    noop()
    week()
    daemon()
    disk()
    oplog()
