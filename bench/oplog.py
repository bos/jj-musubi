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
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bench  # noqa: E402
from bench import B, MUSUBI, WORK, PORT_GIT, PORT_MONITOR, PORT_NATS, ROUTES, CONTROL, env, http_json, measure, sh, start


def main():
    repo = sys.argv[1]
    checkpoints = [int(x) for x in sys.argv[2:]]
    run = f"{WORK}/runs/oplog-{repo}"
    if os.path.exists(run):
        shutil.rmtree(run)
    os.makedirs(run)
    bench.RUN = run
    bench.LOG = open(f"{run}/log.txt", "w")
    start(["nats-server", "-a", "127.0.0.1", "-p", str(PORT_NATS), "-m", str(PORT_MONITOR)], name="nats")
    start(
        ["git", "daemon", "--reuseaddr", "--listen=127.0.0.1", f"--port={PORT_GIT}",
         f"--base-path={run}", "--export-all", run],
        name="gitdaemon",
    )
    start(
        ["/usr/bin/python3", "-I", f"{B}/proxy.py", str(CONTROL)]
        + [f"{n}:{lp}:{tp}" for n, (lp, tp) in ROUTES.items()],
        name="proxy",
    )
    for port in (PORT_NATS, PORT_MONITOR, PORT_GIT, CONTROL):
        bench.wait_port(port)
    shutil.copytree(f"{WORK}/srv/{repo}.git", f"{run}/srv/{repo}.git")
    Am = f"{run}/Am"
    sh(["jj", "git", "clone", "--colocate", f"git://127.0.0.1:{PORT_GIT}/srv/{repo}.git", Am], cwd=run)
    hubp = start(
        [MUSUBI, "hub", "--dir", f"{run}/hub", "--nats", f"nats://127.0.0.1:{PORT_NATS}"],
        stdout=subprocess.PIPE,
        name="hub",
    )
    hive = hubp.stdout.readline().decode().strip()
    bench.HUB_RPC_SUBJECT = f"musubi.{hive}.rpc"
    time.sleep(0.5)
    cfgA = env(MUSUBI_CONFIG_DIR=f"{run}/cfgA")
    sh([MUSUBI, "join", hive, "--hub", f"nats://127.0.0.1:{PORT_NATS}", "--machine", "A"], cwd=Am, e=cfgA)
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
        n_ops, _ = bench.dir_stats(f"{run}/hub/canonical/operations")
        dest = f"{run}/D{n}"
        m = measure(
            "natsD",
            lambda: sh([MUSUBI, "clone", hive, dest, "--hub",
                        f"nats://127.0.0.1:{ROUTES['natsD'][0]}", "--machine", f"D{n}"],
                       cwd=run, e=env(MUSUBI_CONFIG_DIR=f"{run}/cfgD{n}"))[0],
            musubi=True,
        )
        m["hub_ops"] = n_ops
        m["hub_store"] = bench.hub_stats(f"{run}/hub")
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
