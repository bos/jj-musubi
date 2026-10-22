"""Reproduces a long-running daemon running out of gix pack-index slots.

Usage: /usr/bin/python3 -I daemonslots.py REPO ITERATIONS

Starts musubi daemons on A' and a fresh clone B', then makes one new commit at a time on
A' and waits for it to reach B'. Each commit adds FILES new files, so that B receives at
least 100 objects (`fetch.unpackLimit`) and keeps them as a pack rather than unpacking
them: every update adds a pack to B's .git, until `gc --auto` consolidates them at 50
(`gc.autoPackLimit`). A gix object store has a fixed number of index slots,
max(1.1 x packs at open, 32), so run past 32 packs. Results:
$WORK/results/daemonslots-REPO.json.
"""

import json
import os
import shutil
import signal
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402
from bench import MUSUBI, WORK, PORT_GIT, machine, member, rev, sh, start  # noqa: E402


FILES = 100


def packs(repo):
    return len([e for e in os.scandir(f"{repo}/.git/objects/pack") if e.name.endswith(".pack")])


def main():
    repo, iterations = sys.argv[1], int(sys.argv[2])
    run = f"{WORK}/runs/daemonslots-{repo}"
    if os.path.exists(run):
        shutil.rmtree(run)
    os.makedirs(run)
    bench.RUN = run
    bench.LOG = open(f"{run}/log.txt", "w")
    start(["git", "daemon", "--reuseaddr", "--listen=127.0.0.1", f"--port={PORT_GIT}",
           f"--base-path={run}", "--export-all", run], name="gitdaemon")
    hub = f"{run}/hub"
    bench.start_hub(hub)
    bench.wait_port(PORT_GIT)
    shutil.copytree(f"{WORK}/srv/{repo}.git", f"{run}/srv/{repo}.git")
    Am, Bm = f"{run}/Am", f"{run}/Bm"
    sh(["jj", "git", "clone", "--colocate", f"git://127.0.0.1:{PORT_GIT}/srv/{repo}.git", Am], cwd=run)
    sh(["jj", "bookmark", "track", "feature@origin"], cwd=Am)
    # Both reach the hub through its directory, as on the hub's machine: no ssh, no proxy.
    cfgA, cfgB = machine("A"), machine("B")
    member(["create", repo, "--hub", hub, "--machine", "A"], cwd=Am, e=cfgA)
    member(["clone", repo, Bm, "--hub", hub, "--machine", "B"], cwd=run, e=cfgB)
    sh([MUSUBI, "sync"], cwd=Am, e=cfgA)
    sh([MUSUBI, "sync"], cwd=Bm, e=cfgB)
    res = {"repo": repo, "packs_at_daemon_start": packs(Bm), "iterations": []}
    da = start([MUSUBI, "daemon"], cwd=Am, e=machine("A", RUST_LOG="warn"), name="daemonA")
    db = start([MUSUBI, "daemon"], cwd=Bm, e=machine("B", RUST_LOG="warn"), name="daemonB")
    time.sleep(3)
    for i in range(iterations):
        sh(["jj", "new", "feature"], cwd=Am)
        os.makedirs(f"{Am}/slots/{i}")
        for k in range(FILES):
            with open(f"{Am}/slots/{i}/{k}.txt", "w") as f:
                f.write(f"change {i}, file {k}\n")
        sh(["jj", "commit", "-m", f"slots {i}"], cwd=Am)
        sh(["jj", "bookmark", "set", "feature", "-r", "@-"], cwd=Am)
        want = rev(Am, "feature")
        t0 = time.perf_counter()
        ok = False
        while time.perf_counter() - t0 < 40:
            if rev(Bm, "feature") == want:
                ok = True
                break
            time.sleep(0.05)
        res["iterations"].append(
            {"i": i, "delivered": ok, "seconds": time.perf_counter() - t0, "B_packs": packs(Bm)})
        print(res["iterations"][-1], flush=True)
        if not ok:
            break
    bench.stop(da, signal.SIGINT)
    bench.stop(db, signal.SIGINT)
    log = open(f"{run}/daemonB.log").read()
    res["slot_errors"] = log.count("too few index slots")
    res["first_error"] = next((line for line in log.splitlines() if "WARN" in line), None)
    # A fresh process (as `musubi sync` is) sizes its slots from the packs on disk now.
    _, p = sh([MUSUBI, "sync"], cwd=Bm, e=cfgB, check=False)
    res["fresh_sync_rc"] = p.returncode
    res["B_feature_after_fresh_sync_matches"] = rev(Bm, "feature") == rev(Am, "feature")
    os.makedirs(f"{WORK}/results", exist_ok=True)
    with open(f"{WORK}/results/daemonslots-{repo}.json", "w") as f:
        json.dump(res, f, indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "iterations"}, indent=1))
    bench.stop_all()


if __name__ == "__main__":
    main()
