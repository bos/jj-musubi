"""How a new node's `musubi clone` scales with the length of the hive's operation log.

Usage: /usr/bin/python3 -I oplog.py REPO CHECKPOINT [CHECKPOINT ...]

Seeds a hive from srv/REPO.git, then grows its history with `jj describe` operations on A'
(syncing every 50), and at each checkpoint (total operations added) clones a fresh machine
through the byte-counting proxy. Compares with `jj git clone` of the same server repo,
which does not depend on the operation count. Results: $WORK/results/oplog-REPO.json.
"""

import json
import os
import shutil
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402
from bench import MUSUBI, WORK, PORT_GIT, ROUTES, hub_route, machine, measure, member, sh


def main():
    repo = sys.argv[1]
    checkpoints = [int(x) for x in sys.argv[2:]]
    run, hub = bench.start_local_run(repo, "oplog")
    Am = f"{run}/Am"
    sh(["jj", "git", "clone", "--colocate", f"git://127.0.0.1:{PORT_GIT}/srv/{repo}.git", Am], cwd=run)
    cfgA = machine("A")
    # A' reaches the hub through its directory, as on the hub's machine, outside the proxy.
    member(["create", repo, "--hub", hub, "--machine", "A"], cwd=Am, e=cfgA)
    res = {"repo": repo, "points": []}
    git_clone = measure(
        "gitB",
        lambda: sh(["jj", "git", "clone", "--colocate",
                    f"git://127.0.0.1:{ROUTES['gitB'][0]}/srv/{repo}.git", f"{run}/Bgit"],
                   cwd=run)[0],
    )
    res["git_clone"] = git_clone
    done = 0
    for n, target in enumerate([0] + checkpoints):
        t0 = time.perf_counter()
        while done < target:
            sh(["jj", "describe", "-m", f"history {done}"], cwd=Am)
            done += 1
            if done % 50 == 0:
                sh([MUSUBI, "sync"], cwd=Am, e=cfgA)
        sh([MUSUBI, "sync"], cwd=Am, e=cfgA)
        build = time.perf_counter() - t0
        n_ops = bench.hub_stats(hub)["n_ops"]
        dest = f"{run}/D{n}"
        m = measure(
            "hubD",
            lambda: member(["clone", repo, dest, "--hub", hub_route("hubD"), "--machine", f"D{n}"],
                           cwd=run, e=machine(f"D{n}")),
        )
        m["hub_ops"] = n_ops
        m["hub_store"] = bench.hub_stats(hub)
        m["added_ops"] = done
        m["build_seconds"] = build
        m["disk_jj"] = bench.du(f"{dest}/.jj")
        res["points"].append(m)
        print(f"{repo}: {n_ops} hub ops: clone {m['t']:.2f}s {m['total']} bytes", flush=True)
        shutil.rmtree(dest)
        os.makedirs(f"{WORK}/results", exist_ok=True)
        with open(f"{WORK}/results/oplog-{repo}.json", "w") as f:
            json.dump(res, f, indent=1)
    bench.stop_all()


if __name__ == "__main__":
    main()
