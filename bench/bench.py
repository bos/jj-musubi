"""jj-musubi versus `jj git clone/fetch/push`: time and bytes on localhost.

Usage: /usr/bin/python3 -I bench.py REPO REPS [--phases initial,scenarios,noop,daemon,oplog]
                                         [--oplog-ops N] [--clones N]

REPO is one of the server repositories built by setup_sources.sh (small, jj, git).
Results go to $WORK/results/REPO.json; logs to $WORK/runs/REPO/log.txt (see README.md).

Topology (all 127.0.0.1):
  git world:    A, B  --proxy(gitA|gitB)-->  git daemon  --> runs/REPO/srv-git/REPO.git
  musubi world: A', B' --proxy(natsA|natsB)--> nats-server <-- hub (direct, counted via /connz)
The proxy (proxy.py) counts TCP payload bytes per route in both directions.
"""

import argparse
import atexit
import json
import os
import shutil
import signal
import socket
import subprocess
import sys
import time
import urllib.request

B = os.path.dirname(os.path.abspath(__file__))
# Server repositories, runs and results; see README.md.
WORK = os.environ.get("MUSUBI_BENCH_DIR") or f"{B}/work"
MUSUBI = os.environ.get("MUSUBI") or f"{os.path.dirname(B)}/target/release/musubi"
PORT_NATS, PORT_MONITOR, PORT_GIT = 47222, 47822, 47418
ROUTES = {
    "gitA": (47501, PORT_GIT),
    "gitB": (47502, PORT_GIT),
    "natsA": (47511, PORT_NATS),
    "natsB": (47512, PORT_NATS),
    "natsC": (47513, PORT_NATS),
    "natsD": (47514, PORT_NATS),
}
CONTROL = 47599

BASE_ENV = dict(os.environ)
BASE_ENV.update(
    JJ_CONFIG=f"{B}/env/jjconfig.toml",
    GIT_CONFIG_GLOBAL=f"{B}/env/gitconfig",
    GIT_CONFIG_NOSYSTEM="1",
    PATH=f"{os.path.dirname(MUSUBI)}:" + os.environ["PATH"],
    RUST_LOG="warn",
)
for k in ("MUSUBI_CONFIG_DIR", "GIT_DIR", "GIT_WORK_TREE", "GIT_TRACE2_EVENT"):
    BASE_ENV.pop(k, None)

PROCS = []
LOG = None


def log(*parts):
    line = " ".join(str(p) for p in parts)
    print(line, flush=True)
    if LOG:
        LOG.write(line + "\n")
        LOG.flush()


def env(**extra):
    e = dict(BASE_ENV)
    e.update({k: str(v) for k, v in extra.items()})
    return e


def sh(args, cwd=None, e=None, check=True, timeout=7200):
    t = time.perf_counter()
    p = subprocess.run(
        args, cwd=cwd, env=e or BASE_ENV, capture_output=True, text=True, timeout=timeout
    )
    dt = time.perf_counter() - t
    if LOG:
        LOG.write(f"$ {' '.join(args)}  (cwd={cwd}) [{dt:.3f}s rc={p.returncode}]\n")
        if p.stdout.strip():
            LOG.write(p.stdout[-4000:] + "\n")
        if p.stderr.strip():
            LOG.write(p.stderr[-4000:] + "\n")
        LOG.flush()
    if check and p.returncode != 0:
        raise RuntimeError(f"{args} failed ({p.returncode}): {p.stderr[-2000:]}")
    return dt, p


def start(args, cwd=None, e=None, stdout=None, name=""):
    logf = open(f"{RUN}/{name or 'proc'}.log", "a")
    p = subprocess.Popen(
        args,
        cwd=cwd,
        env=e or BASE_ENV,
        stdout=stdout or logf,
        stderr=logf,
        start_new_session=True,
    )
    PROCS.append(p)
    return p


def stop(p, sig=signal.SIGTERM):
    if p.poll() is None:
        try:
            os.killpg(p.pid, sig)
        except ProcessLookupError:
            pass
        try:
            p.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()


def stop_all():
    for p in reversed(PROCS):
        stop(p)


atexit.register(stop_all)


def wait_port(port, timeout=20):
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            socket.create_connection(("127.0.0.1", port), timeout=0.5).close()
            return
        except OSError:
            time.sleep(0.05)
    raise RuntimeError(f"port {port} never opened")


def counters():
    s = socket.create_connection(("127.0.0.1", CONTROL))
    s.sendall(b"GET\n")
    data = b""
    while not data.endswith(b"\n"):
        chunk = s.recv(65536)
        if not chunk:
            break
        data += chunk
    s.close()
    return json.loads(data)


def http_json(path):
    with urllib.request.urlopen(f"http://127.0.0.1:{PORT_MONITOR}{path}") as r:
        return json.loads(r.read())


HUB_RPC_SUBJECT = None


def hub_conn():
    """in/out payload bytes and msgs of the hub's NATS connection (by its rpc subscription)."""
    if HUB_RPC_SUBJECT is None:
        return {"in_bytes": 0, "out_bytes": 0, "in_msgs": 0, "out_msgs": 0}
    data = http_json("/connz?subs=1&limit=10000")
    for c in data.get("connections", []):
        if HUB_RPC_SUBJECT in (c.get("subscriptions_list") or []):
            return {k: c[k] for k in ("in_bytes", "out_bytes", "in_msgs", "out_msgs")}
    return {"in_bytes": 0, "out_bytes": 0, "in_msgs": 0, "out_msgs": 0}


def varz():
    v = http_json("/varz")
    return {k: v[k] for k in ("in_bytes", "out_bytes", "in_msgs", "out_msgs")}


def measure(route, fn, musubi=False):
    c0 = counters()[route]
    v0, h0 = (varz(), hub_conn()) if musubi else (None, None)
    dt = fn()
    if musubi:
        time.sleep(0.05)  # let the hub's head notice land in the counters
    c1 = counters()[route]
    out = {
        "t": dt,
        "up": c1["up"] - c0["up"],
        "down": c1["down"] - c0["down"],
        "conns": c1["conns"] - c0["conns"],
    }
    out["total"] = out["up"] + out["down"]
    if musubi:
        v1, h1 = varz(), hub_conn()
        hub = {k: h1[k] - h0[k] for k in h0}
        out["hub_in"] = hub["in_bytes"]  # payload the hub published (replies, notices)
        out["hub_out"] = hub["out_bytes"]  # payload delivered to the hub (requests)
        out["hub_msgs"] = hub["in_msgs"] + hub["out_msgs"]
        # Payload bytes the node exchanged, per nats-server: everything minus the hub's.
        out["nats_node_in"] = (v1["in_bytes"] - v0["in_bytes"]) - hub["in_bytes"]
        out["nats_node_out"] = (v1["out_bytes"] - v0["out_bytes"]) - hub["out_bytes"]
        out["nats_msgs"] = (v1["in_msgs"] - v0["in_msgs"]) + (v1["out_msgs"] - v0["out_msgs"])
    return out


def du(path):
    if not os.path.exists(path):
        return 0
    out = subprocess.run(["du", "-sk", path], capture_output=True, text=True).stdout
    return int(out.split()[0]) * 1024


def dir_stats(path):
    n, size = 0, 0
    if os.path.isdir(path):
        for entry in os.scandir(path):
            if entry.is_file():
                n += 1
                size += entry.stat().st_size
    return n, size


def hub_stats(hub):
    n_ops, ops_bytes = dir_stats(f"{hub}/canonical/operations")
    n_views, views_bytes = dir_stats(f"{hub}/canonical/views")
    n_packs, pack_bytes = 0, 0
    pdir = f"{hub}/git/objects/pack"
    if os.path.isdir(pdir):
        for entry in os.scandir(pdir):
            if entry.name.endswith(".pack"):
                n_packs += 1
                pack_bytes += entry.stat().st_size
    return dict(
        n_ops=n_ops,
        ops_bytes=ops_bytes,
        n_views=n_views,
        views_bytes=views_bytes,
        n_packs=n_packs,
        pack_bytes=pack_bytes,
    )


def stats_delta(a, b):
    return {k: b[k] - a[k] for k in a}


def rev(repo, ref):
    _, p = sh(["git", "-C", repo, "rev-parse", "--verify", "-q", ref], check=False)
    return p.stdout.strip()


# ---------------------------------------------------------------------------------------
# Scenarios: identical jj commands in both worlds.


def jj(repo, *args):
    return sh(["jj", *args], cwd=repo)[0]


def scenario(name, repo, i):
    t = 0.0
    if name == "new_commit":
        t += jj(repo, "new", "feature")
        os.makedirs(f"{repo}/bench-reps", exist_ok=True)
        with open(f"{repo}/bench-reps/rep-{i}.txt", "w") as f:
            f.write(f"small change {i}\n" * 5)
        t += jj(repo, "commit", "-m", f"bench: small commit {i}")
        t += jj(repo, "bookmark", "set", "feature", "-r", "@-")
        return t, "feature"
    if name == "describe":
        t += jj(repo, "describe", "feature", "-m", f"bench: reworded {i}")
        return t, "feature"
    if name == "rebase":
        dest = "main" if i % 2 == 0 else "main-"
        t += jj(repo, "rebase", "-s", "roots(::feature ~ ::main)", "-o", dest)
        return t, "feature"
    if name == "bookmark_move":
        target = "feature-" if i % 2 == 0 else "feature--"
        t += jj(repo, "bookmark", "set", "marker", "-r", target, "--allow-backwards")
        return t, "marker"
    if name == "abandon":
        t += jj(repo, "abandon", "--retain-bookmarks", "feature")
        return t, "feature"
    raise ValueError(name)


SCENARIOS = ["new_commit", "describe", "rebase", "bookmark_move", "abandon"]


# ---------------------------------------------------------------------------------------


def main():
    global RUN, LOG, HUB_RPC_SUBJECT
    ap = argparse.ArgumentParser()
    ap.add_argument("repo")
    ap.add_argument("reps", type=int)
    ap.add_argument("--phases", default="initial,scenarios,noop,daemon,oplog")
    ap.add_argument("--clones", type=int, default=3)
    ap.add_argument("--oplog-ops", type=int, default=300)
    ap.add_argument("--latency-reps", type=int, default=10)
    ap.add_argument("--idle-seconds", type=int, default=150)
    ap.add_argument("--delay-ms", type=float, default=0, help="one-way delay added by the proxy")
    args = ap.parse_args()
    phases = set(args.phases.split(","))
    R = args.repo
    tag = f"{R}-delay{args.delay_ms:g}ms" if args.delay_ms else R
    RUN = f"{WORK}/runs/{tag}"
    if os.path.exists(RUN):
        shutil.rmtree(RUN)
    os.makedirs(RUN)
    LOG = open(f"{RUN}/log.txt", "w")
    res = {"repo": R, "reps": args.reps, "delay_ms": args.delay_ms, "started": time.time()}

    def save():
        os.makedirs(f"{WORK}/results", exist_ok=True)
        with open(f"{WORK}/results/{tag}.json", "w") as f:
            json.dump(res, f, indent=1)

    # --- services ---------------------------------------------------------------------
    start(
        ["nats-server", "-a", "127.0.0.1", "-p", str(PORT_NATS), "-m", str(PORT_MONITOR)],
        name="nats",
    )
    start(
        [
            "git",
            "daemon",
            "--reuseaddr",
            "--listen=127.0.0.1",
            f"--port={PORT_GIT}",
            f"--base-path={RUN}",
            "--export-all",
            "--enable=receive-pack",
            "--informative-errors",
            RUN,
        ],
        e=env(GIT_TRACE2_EVENT=f"{RUN}/trace-gitdaemon.json"),
        name="gitdaemon",
    )
    start(
        ["/usr/bin/python3", "-I", f"{B}/proxy.py", str(CONTROL)]
        + [f"{n}:{lp}:{tp}:{args.delay_ms:g}" for n, (lp, tp) in ROUTES.items()],
        name="proxy",
    )
    for port in (PORT_NATS, PORT_MONITOR, PORT_GIT, CONTROL):
        wait_port(port)

    srv_rel = f"srv-git/{R}.git"
    shutil.copytree(f"{WORK}/srv/{R}.git", f"{RUN}/{srv_rel}")
    shutil.copytree(f"{WORK}/srv/{R}.git", f"{RUN}/srv-m/{R}.git")
    url = lambda route: f"git://127.0.0.1:{ROUTES[route][0]}/{srv_rel}"  # noqa: E731
    direct_m = f"git://127.0.0.1:{PORT_GIT}/srv-m/{R}.git"
    A, Bg = f"{RUN}/A", f"{RUN}/B"
    Am, Cm = f"{RUN}/Am", f"{RUN}/Cm"
    cfg = lambda name, **kw: env(MUSUBI_CONFIG_DIR=f"{RUN}/cfg{name}", **kw)  # noqa: E731
    natsurl = lambda route: f"nats://127.0.0.1:{ROUTES[route][0]}"  # noqa: E731

    def track(repo):
        jj(repo, "bookmark", "track", "feature@origin", "marker@origin")

    # --- initial transfer --------------------------------------------------------------
    init = res.setdefault("initial", {})
    log(f"== {R}: initial transfer")
    # git world
    init["git_clone_A"] = measure(
        "gitA",
        lambda: sh(["jj", "git", "clone", "--colocate", url("gitA"), A], cwd=RUN)[0],
    )
    track(A)
    init["git_clone_B"] = []
    for k in range(args.clones):
        dest = f"{RUN}/Bclone{k}"
        m = measure(
            "gitB",
            lambda: sh(["jj", "git", "clone", "--colocate", url("gitB"), dest], cwd=RUN)[0],
        )
        m["disk_git"], m["disk_jj"] = du(f"{dest}/.git"), du(f"{dest}/.jj")
        init["git_clone_B"].append(m)
        log("git clone B", k, m)
        if k < args.clones - 1:
            shutil.rmtree(dest)
        else:
            os.rename(dest, Bg)
    track(Bg)

    # musubi world
    sh(["jj", "git", "clone", "--colocate", direct_m, Am], cwd=RUN)
    track(Am)
    hub = f"{RUN}/hub"
    hubp = start(
        [MUSUBI, "hub", "--dir", hub, "--nats", f"nats://127.0.0.1:{PORT_NATS}"],
        e=env(RUST_LOG="info", GIT_TRACE2_EVENT=f"{RUN}/trace-hub.json"),
        stdout=subprocess.PIPE,
        name="hub",
    )
    hive = hubp.stdout.readline().decode().strip()
    HUB_RPC_SUBJECT = f"musubi.{hive}.rpc"
    for _ in range(100):
        if hub_conn()["in_msgs"] or any(
            HUB_RPC_SUBJECT in (c.get("subscriptions_list") or [])
            for c in http_json("/connz?subs=1").get("connections", [])
        ):
            break
        time.sleep(0.05)
    res["hive"] = hive
    h0 = hub_stats(hub)
    init["musubi_seed_A"] = measure(
        "natsA",
        lambda: sh(
            [MUSUBI, "join", hive, "--nats", natsurl("natsA"), "--machine", "A"],
            cwd=Am,
            e=cfg("A"),
        )[0],
        musubi=True,
    )
    init["musubi_seed_A"]["hub_store"] = stats_delta(h0, hub_stats(hub))
    log("musubi seed", init["musubi_seed_A"])
    init["musubi_clone_B"] = []
    for k in range(args.clones):
        dest = f"{RUN}/Bmclone{k}"
        h0 = hub_stats(hub)
        m = measure(
            "natsB",
            lambda: sh(
                [MUSUBI, "clone", hive, dest, "--nats", natsurl("natsB"), "--machine", f"B{k}"],
                cwd=RUN,
                e=cfg(f"B{k}"),
            )[0],
            musubi=True,
        )
        m["hub_store"] = stats_delta(h0, hub_stats(hub))
        m["disk_git"], m["disk_jj"] = du(f"{dest}/.git"), du(f"{dest}/.jj")
        m["disk_musubi"] = du(f"{dest}/.jj/repo/musubi")
        init["musubi_clone_B"].append(m)
        log("musubi clone B", k, m)
    # The daemon config names the clone's path, so B' stays where it was cloned.
    Bm = f"{RUN}/Bmclone{args.clones - 1}"
    cfgB = f"B{args.clones - 1}"
    # A machine that already has a git clone joins the hive.
    sh(["jj", "git", "clone", "--colocate", direct_m, Cm], cwd=RUN)
    track(Cm)
    h0 = hub_stats(hub)
    init["musubi_join_existing_C"] = measure(
        "natsC",
        lambda: sh(
            [MUSUBI, "join", hive, "--nats", natsurl("natsC"), "--machine", "C"],
            cwd=Cm,
            e=cfg("C"),
        )[0],
        musubi=True,
    )
    init["musubi_join_existing_C"]["hub_store"] = stats_delta(h0, hub_stats(hub))
    log("musubi join existing C", init["musubi_join_existing_C"])
    # A' catches up with the joins, then B' with A'.
    init["musubi_A_catchup"] = measure(
        "natsA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=cfg("A"))[0], musubi=True
    )
    init["musubi_B_catchup"] = measure(
        "natsB", lambda: sh([MUSUBI, "sync"], cwd=Bm, e=cfg(cfgB))[0], musubi=True
    )
    for _ in range(2):
        sh([MUSUBI, "sync"], cwd=Am, e=cfg("A"))
        sh([MUSUBI, "sync"], cwd=Bm, e=cfg(cfgB))

    def disk():
        return {
            "git_server": du(f"{RUN}/{srv_rel}"),
            "A_git": du(f"{A}/.git"),
            "A_jj": du(f"{A}/.jj"),
            "B_git": du(f"{Bg}/.git"),
            "B_jj": du(f"{Bg}/.jj"),
            "hub_total": du(hub),
            "hub_git": du(f"{hub}/git"),
            "hub_canonical": du(f"{hub}/canonical"),
            "hub_extras": du(f"{hub}/extras"),
            "hub_blobs": du(f"{hub}/blobs"),
            "Am_git": du(f"{Am}/.git"),
            "Am_jj": du(f"{Am}/.jj"),
            "Am_musubi": du(f"{Am}/.jj/repo/musubi"),
            "Bm_git": du(f"{Bm}/.git"),
            "Bm_jj": du(f"{Bm}/.jj"),
            "Bm_musubi": du(f"{Bm}/.jj/repo/musubi"),
            "hub_store": hub_stats(hub),
        }

    res["disk_after_initial"] = disk()
    save()

    # --- incremental scenarios ---------------------------------------------------------
    if "scenarios" in phases:
        sc = res.setdefault("scenarios", {s: [] for s in SCENARIOS})
        for i in range(args.reps):
            for s in SCENARIOS:
                row = {"rep": i}
                # git world
                row["local_git"], bm = scenario(s, A, i)
                row["git_push"] = measure(
                    "gitA", lambda: sh(["jj", "git", "push", "--tracked"], cwd=A)[0]
                )
                row["git_fetch"] = measure("gitB", lambda: sh(["jj", "git", "fetch"], cwd=Bg)[0])
                for ref in ("feature", "marker"):
                    a, b = rev(A, ref), rev(Bg, ref)
                    assert a and a == b, f"git world diverged on {ref}: {a} vs {b}"
                # musubi world
                row["local_musubi"], bm = scenario(s, Am, i)
                h0 = hub_stats(hub)
                row["musubi_push"] = measure(
                    "natsA",
                    lambda: sh(
                        [MUSUBI, "sync"],
                        cwd=Am,
                        e=cfg("A", GIT_TRACE2_EVENT=f"{RUN}/trace-A-{s}-{i}.json"),
                    )[0],
                    musubi=True,
                )
                row["hub_store"] = stats_delta(h0, hub_stats(hub))
                row["musubi_fetch"] = measure(
                    "natsB",
                    lambda: sh(
                        [MUSUBI, "sync"],
                        cwd=Bm,
                        e=cfg(cfgB, GIT_TRACE2_EVENT=f"{RUN}/trace-B-{s}-{i}.json"),
                    )[0],
                    musubi=True,
                )
                for ref in ("feature", "marker"):
                    a, b = rev(Am, ref), rev(Bm, ref)
                    assert a and a == b, f"musubi world diverged on {ref}: {a} vs {b}"
                sc[s].append(row)
                log(
                    f"{R} rep {i} {s}: git push {row['git_push']['total']}B "
                    f"{row['git_push']['t']:.2f}s fetch {row['git_fetch']['total']}B "
                    f"{row['git_fetch']['t']:.2f}s | musubi push {row['musubi_push']['total']}B "
                    f"{row['musubi_push']['t']:.2f}s fetch {row['musubi_fetch']['total']}B "
                    f"{row['musubi_fetch']['t']:.2f}s ops {row['hub_store']['n_ops']} "
                    f"views {row['hub_store']['views_bytes']}B"
                )
            save()
        res["disk_after_scenarios"] = disk()
        save()

    # --- no-op -------------------------------------------------------------------------
    if "noop" in phases:
        no = res.setdefault("noop", {"git_fetch": [], "git_push": [], "musubi_B": [], "musubi_A": []})
        for _ in range(5):
            no["git_fetch"].append(measure("gitB", lambda: sh(["jj", "git", "fetch"], cwd=Bg)[0]))
            no["git_push"].append(
                measure("gitA", lambda: sh(["jj", "git", "push", "--tracked"], cwd=A)[0])
            )
            no["musubi_B"].append(
                measure("natsB", lambda: sh([MUSUBI, "sync"], cwd=Bm, e=cfg(cfgB))[0], musubi=True)
            )
            no["musubi_A"].append(
                measure("natsA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=cfg("A"))[0], musubi=True)
            )
        log("noop", json.dumps(no)[:2000])
        save()

    # --- daemons: latency and idle cost ------------------------------------------------
    if "daemon" in phases:
        dm = res.setdefault("daemon", {})
        da = start([MUSUBI, "daemon"], cwd=Am, e=cfg("A", RUST_LOG="info"), name="daemonA")
        db = start([MUSUBI, "daemon"], cwd=Bm, e=cfg(cfgB, RUST_LOG="info"), name="daemonB")
        time.sleep(5)
        lat = dm.setdefault("musubi_latency", [])
        for k in range(args.latency_reps):
            c0 = counters()
            hc0 = hub_conn()
            t_cmd = jj(Am, "describe", "feature", "-m", f"bench: latency {k}")
            t0 = time.perf_counter()
            want = rev(Am, "feature")
            while True:
                if rev(Bm, "feature") == want:
                    break
                if time.perf_counter() - t0 > 60:
                    raise RuntimeError("musubi daemon never delivered")
                time.sleep(0.005)
            seen = time.perf_counter() - t0
            time.sleep(2.0)  # let both daemons go idle before reading counters
            c1 = counters()
            hc1 = hub_conn()
            lat.append(
                {
                    "cmd": t_cmd,
                    "latency": seen,
                    "A_bytes": (c1["natsA"]["up"] + c1["natsA"]["down"])
                    - (c0["natsA"]["up"] + c0["natsA"]["down"]),
                    "B_bytes": (c1["natsB"]["up"] + c1["natsB"]["down"])
                    - (c0["natsB"]["up"] + c0["natsB"]["down"]),
                    "hub_bytes": (hc1["in_bytes"] + hc1["out_bytes"])
                    - (hc0["in_bytes"] + hc0["out_bytes"]),
                }
            )
            log("musubi latency", lat[-1])
        glat = dm.setdefault("git_latency", [])
        for k in range(args.latency_reps):
            c0 = counters()
            t_cmd = jj(A, "describe", "feature", "-m", f"bench: latency {k}")
            t0 = time.perf_counter()
            sh(["jj", "git", "push", "--tracked"], cwd=A)
            t_push = time.perf_counter() - t0
            sh(["jj", "git", "fetch"], cwd=Bg)
            seen = time.perf_counter() - t0
            assert rev(A, "feature") == rev(Bg, "feature")
            c1 = counters()
            glat.append(
                {
                    "cmd": t_cmd,
                    "latency": seen,
                    "push": t_push,
                    "A_bytes": (c1["gitA"]["up"] + c1["gitA"]["down"])
                    - (c0["gitA"]["up"] + c0["gitA"]["down"]),
                    "B_bytes": (c1["gitB"]["up"] + c1["gitB"]["down"])
                    - (c0["gitB"]["up"] + c0["gitB"]["down"]),
                }
            )
            log("git latency", glat[-1])
        # Idle cost.
        time.sleep(3)
        c0, hc0, t0 = counters(), hub_conn(), time.time()
        time.sleep(args.idle_seconds)
        c1, hc1, t1 = counters(), hub_conn(), time.time()
        dm["idle"] = {
            "seconds": t1 - t0,
            "A_up": c1["natsA"]["up"] - c0["natsA"]["up"],
            "A_down": c1["natsA"]["down"] - c0["natsA"]["down"],
            "B_up": c1["natsB"]["up"] - c0["natsB"]["up"],
            "B_down": c1["natsB"]["down"] - c0["natsB"]["down"],
            "hub_in": hc1["in_bytes"] - hc0["in_bytes"],
            "hub_out": hc1["out_bytes"] - hc0["out_bytes"],
            "hub_msgs": hc1["in_msgs"] + hc1["out_msgs"] - hc0["in_msgs"] - hc0["out_msgs"],
        }
        log("idle", dm["idle"])
        stop(da, signal.SIGINT)
        stop(db, signal.SIGINT)
        save()

    # --- operation-log length: clone cost after a long history ---------------------------
    if "oplog" in phases and args.oplog_ops > 0:
        ol = res.setdefault("oplog", {})
        h0 = hub_stats(hub)
        t0 = time.perf_counter()
        for k in range(args.oplog_ops):
            jj(Am, "describe", "feature", "-m", f"bench: history {k}")
            if k % 50 == 49:
                sh([MUSUBI, "sync"], cwd=Am, e=cfg("A"))
        sh([MUSUBI, "sync"], cwd=Am, e=cfg("A"))
        ol["build_seconds"] = time.perf_counter() - t0
        ol["added"] = stats_delta(h0, hub_stats(hub))
        ol["hub_store"] = hub_stats(hub)
        dest = f"{RUN}/Dm"
        h0 = hub_stats(hub)
        m = measure(
            "natsD",
            lambda: sh(
                [MUSUBI, "clone", hive, dest, "--nats", natsurl("natsD"), "--machine", "D"],
                cwd=RUN,
                e=cfg("D", GIT_TRACE2_EVENT=f"{RUN}/trace-D-clone.json"),
            )[0],
            musubi=True,
        )
        m["disk_jj"] = du(f"{dest}/.jj")
        m["disk_musubi"] = du(f"{dest}/.jj/repo/musubi")
        ol["clone_D"] = m
        log("oplog clone", ol)
        save()

    res["finished"] = time.time()
    save()
    stop_all()


if __name__ == "__main__":
    main()
