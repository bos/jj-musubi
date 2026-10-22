"""Does a node re-download its own uploads? (accepted_base only moves when a node pulls.)

Usage: /usr/bin/python3 -I stalebase.py REPO N_PUSHES FILE_KB

A' pushes N_PUSHES commits, each adding FILE_KB of random (incompressible) data, syncing
after each. B' then makes one small change and syncs. Finally A' syncs, and we measure how
much it downloads: ideally only B's operation and its tiny working-copy commit.
Results: $WORK/results/stalebase-REPO.json.
"""

import json
import os
import shutil
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402
from bench import B, MUSUBI, WORK, PORT_GIT, ROUTES, CONTROL, hub_route, machine, measure, member, sh, start


def main():
    repo, pushes, kb = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    run = f"{WORK}/runs/stalebase-{repo}"
    if os.path.exists(run):
        shutil.rmtree(run)
    os.makedirs(run)
    bench.RUN = run
    bench.LOG = open(f"{run}/log.txt", "w")
    start(["git", "daemon", "--reuseaddr", "--listen=127.0.0.1", f"--port={PORT_GIT}",
           f"--base-path={run}", "--export-all", run], name="gitdaemon")
    start(["/usr/bin/python3", "-I", f"{B}/proxy.py", str(CONTROL)]
          + [f"{n}:{lp}:{tp}" for n, (lp, tp) in ROUTES.items()], name="proxy")
    bench.start_hub(f"{run}/hub")
    for port in (PORT_GIT, CONTROL):
        bench.wait_port(port)
    shutil.copytree(f"{WORK}/srv/{repo}.git", f"{run}/srv/{repo}.git")
    Am, Bm = f"{run}/Am", f"{run}/Bm"
    sh(["jj", "git", "clone", "--colocate", f"git://127.0.0.1:{PORT_GIT}/srv/{repo}.git", Am], cwd=run)
    cfgA, cfgB = machine("A"), machine("B")
    res = {"repo": repo, "pushes": pushes, "file_kb": kb}
    res["seed_A"] = measure("hubA", lambda: member(
        ["create", repo, "--hub", hub_route("hubA"), "--machine", "A"], cwd=Am, e=cfgA))
    res["clone_B"] = measure("hubB", lambda: member(
        ["clone", repo, Bm, "--hub", hub_route("hubB"), "--machine", "B"], cwd=run, e=cfgB))
    res["A_catchup_after_B_joined"] = measure(
        "hubA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=cfgA)[0])
    res["B_settle"] = measure("hubB", lambda: sh([MUSUBI, "sync"], cwd=Bm, e=cfgB)[0])
    res["A_pushes"] = []
    for i in range(pushes):
        with open(f"{Am}/blob-{i}.bin", "wb") as f:
            f.write(os.urandom(kb * 1024))
        sh(["jj", "commit", "-m", f"A: add blob {i}"], cwd=Am)
        res["A_pushes"].append(measure(
            "hubA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=cfgA)[0]))
    res["accepted_base_A_before"] = open(f"{Am}/.jj/repo/musubi/accepted_base").read().strip()
    sh(["jj", "describe", "-m", "B: a small change"], cwd=Bm)
    res["B_sync"] = measure("hubB", lambda: sh([MUSUBI, "sync"], cwd=Bm, e=cfgB)[0])
    res["A_pull"] = measure("hubA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=cfgA)[0])
    res["A_pull_again"] = measure("hubA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=cfgA)[0])
    packs = sorted(
        (e.stat().st_size, e.name) for e in os.scandir(f"{Am}/.git/objects/pack")
        if e.name.endswith(".pack"))
    res["A_packs"] = packs
    os.makedirs(f"{WORK}/results", exist_ok=True)
    with open(f"{WORK}/results/stalebase-{repo}.json", "w") as f:
        json.dump(res, f, indent=1)
    for k in ("seed_A", "clone_B", "A_catchup_after_B_joined", "B_settle", "B_sync", "A_pull",
              "A_pull_again"):
        m = res[k]
        print(f"{k:28s} {m['t']:7.2f}s up {m['up']:>10} down {m['down']:>10}")
    for i, m in enumerate(res["A_pushes"]):
        print(f"A push {i}: {m['t']:.2f}s up {m['up']} down {m['down']}")
    bench.stop_all()


if __name__ == "__main__":
    main()
