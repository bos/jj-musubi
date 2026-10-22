"""jj-musubi versus `git clone/fetch` and `jj git clone/fetch/push`: time and bytes on localhost.

Usage: /usr/bin/python3 -I bench.py REPO REPS [--phases initial,scenarios,noop,week,daemon,oplog]
                                         [--oplog-ops N] [--clones N]

REPO is one of the server repositories built by setup_sources.sh (small, or a NAME it was given).
Results go to $WORK/results/REPO.json; logs to $WORK/runs/REPO/log.txt (see README.md).

Topology (all 127.0.0.1):
  git world:    A, B  --proxy(gitA|gitB)-->  git daemon  --> runs/REPO/srv-git/REPO.git
  musubi world: A', B' --ssh.py--proxy(hubA|hubB)--> sshd.py --musubi hub connect--> hub
The proxy (proxy.py) counts TCP payload bytes per route in both directions. In the git
world, B is both a `jj git clone` and a plain `git clone`.

With $MUSUBI_BENCH_PERF set, each measurement runs under `perf record`, given those options
(as in "-a -g"), into runs/REPO/perf/; its file is the measurement's "perf".
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

B = os.path.dirname(os.path.abspath(__file__))
# Server repositories, runs and results; see README.md.
WORK = os.environ.get("MUSUBI_BENCH_DIR") or f"{B}/work"
MUSUBI = os.environ.get("MUSUBI") or f"{os.path.dirname(B)}/target/release/musubi"


def free_ports(n):
    """`n` ports on 127.0.0.1 that nothing listens on, so that a run clashes with nothing
    else running, another run included."""
    socks = [socket.create_server(("127.0.0.1", 0)) for _ in range(n)]
    ports = [s.getsockname()[1] for s in socks]
    for s in socks:
        s.close()
    return ports


# sshd.py listens on PORT_SSHD, the hub's end of the hub* routes; the proxy listens on each
# route's port, and on CONTROL for its counters.
PORT_SSHD, PORT_GIT, CONTROL, *_ports = free_ports(9)
ROUTES = {
    "gitA": (_ports[0], PORT_GIT),
    "gitB": (_ports[1], PORT_GIT),
    "hubA": (_ports[2], PORT_SSHD),
    "hubB": (_ports[3], PORT_SSHD),
    "hubC": (_ports[4], PORT_SSHD),
    "hubD": (_ports[5], PORT_SSHD),
}

BASE_ENV = dict(os.environ)
BASE_ENV.update(
    JJ_CONFIG=f"{B}/env/jjconfig.toml",
    GIT_CONFIG_GLOBAL=f"{B}/env/gitconfig",
    GIT_CONFIG_NOSYSTEM="1",
    PATH=f"{os.path.dirname(MUSUBI)}:" + os.environ["PATH"],
    RUST_LOG="warn",
    MUSUBI_SSH=f"{B}/ssh.py",
)
for k in ("MUSUBI_CONFIG_DIR", "MUSUBI_SOCKET", "GIT_DIR", "GIT_WORK_TREE", "GIT_TRACE2_EVENT"):
    BASE_ENV.pop(k, None)

PROCS = []
LOG = None
PERF = os.environ.get("MUSUBI_BENCH_PERF")


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


def start(args, cwd=None, e=None, name=""):
    logf = open(f"{RUN}/{name or 'proc'}.log", "a")
    p = subprocess.Popen(
        args,
        cwd=cwd,
        env=e or BASE_ENV,
        stdout=logf,
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


def killed(*_):
    # Once, so that a second signal doesn't cut stopping everything short.
    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, signal.SIG_IGN)
    sys.exit(1)


# Killed, a script stops what it started too; under nohup, it carries on.
for _sig in (signal.SIGTERM, signal.SIGHUP):
    if signal.getsignal(_sig) != signal.SIG_IGN:
        signal.signal(_sig, killed)


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


def measure(route, fn):
    c0 = counters()[route]
    perf = perf_start(route) if PERF else None
    try:
        dt = fn()
        time.sleep(0.05)  # let the last bytes, as a connection closes, land in the counters
        c1 = counters()[route]
    finally:
        if perf:
            perf_stop(perf)
    out = {
        "t": dt,
        "up": c1["up"] - c0["up"],
        "down": c1["down"] - c0["down"],
        "conns": c1["conns"] - c0["conns"],
    }
    out["total"] = out["up"] + out["down"]
    if perf:
        out["perf"] = perf[1]
    return out


def perf_start(route):
    os.makedirs(f"{RUN}/perf", exist_ok=True)
    path = f"perf/{len(os.listdir(f'{RUN}/perf')):03d}-{route}.data"
    with open(f"{RUN}/perf.log", "a") as logf:
        p = subprocess.Popen(
            ["perf", "record", *PERF.split(), "-o", f"{RUN}/{path}"], stdout=logf, stderr=logf
        )
    # perf creates its file as it starts, and soon after records; with -a, once it has listed
    # what is running.
    try:
        deadline = time.time() + 10
        while not os.path.exists(f"{RUN}/{path}"):
            if p.poll() is not None or time.time() > deadline:
                raise RuntimeError(f"perf record didn't start; see {RUN}/perf.log")
            time.sleep(0.01)
        time.sleep(0.5)
        if p.poll() is not None:
            raise RuntimeError(f"perf record exited ({p.returncode}); see {RUN}/perf.log")
    except BaseException:
        p.kill()
        p.wait()
        raise
    return p, path


def perf_stop(perf):
    p, path = perf
    p.send_signal(signal.SIGINT)
    p.wait()
    return path


def start_hub(hub, **extra):
    """Starts a hub serving `hub`, and sshd.py, which the hub* routes reach it through, and
    waits for the hub to listen."""
    cfg = f"{RUN}/cfg-hub"
    p = start([MUSUBI, "hub", "--dir", hub], e=env(MUSUBI_CONFIG_DIR=cfg, **extra), name="hub")
    start(
        ["/usr/bin/python3", "-I", f"{B}/sshd.py", str(PORT_SSHD), MUSUBI, hub],
        e=env(MUSUBI_CONFIG_DIR=cfg),
        name="sshd",
    )
    deadline = time.time() + 20
    while not os.path.exists(f"{hub}/run/hub.sock"):
        if p.poll() is not None:
            raise RuntimeError(f"the hub exited: {open(f'{RUN}/hub.log').read()[-2000:]}")
        if time.time() > deadline:
            raise RuntimeError(f"the hub never listened; see {RUN}/hub.log")
        time.sleep(0.05)
    wait_port(PORT_SSHD)


def hub_route(route):
    """The --hub that reaches the hub through `route`: ssh.py takes it for host:port."""
    return f"127.0.0.1:{ROUTES[route][0]}"


def machine(name, **extra):
    """The environment of musubi machine `name`: a config directory of its own, holding the
    key it reaches hubs by, as one that has joined a hub before has."""
    cfg = f"{RUN}/cfg{name}"
    if not os.path.exists(f"{cfg}/hub_key"):
        # Private, or musubi won't put the daemon's socket in it.
        os.makedirs(cfg, mode=0o700, exist_ok=True)
        sh(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", f"{cfg}/hub_key"])
    return env(MUSUBI_CONFIG_DIR=cfg, **extra)


def member(args, cwd, e):
    """Runs `musubi create`, `join` or `clone`, and stops the daemon it leaves serving the
    repository, so that nothing syncs but `musubi sync` until the daemon phase. Returns the
    command's time, which includes starting the daemon and its first sync."""
    try:
        return sh([MUSUBI, *args], cwd=cwd, e=e)[0]
    finally:
        sh([MUSUBI, "daemon", "stop"], cwd=cwd, e=e)


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


def hive_dir(hub):
    """The directory of the one hive the hub holds, once it holds one."""
    hives = [e.path for e in os.scandir(hub) if os.path.exists(f"{e.path}/hive.toml")]
    assert len(hives) <= 1, f"the hub holds {len(hives)} hives"
    return hives[0] if hives else None


def hub_stats(hub):
    # Before the hive exists, its paths are missing, which counts as empty.
    hive = hive_dir(hub) or f"{hub}/no-hive"
    n_ops, ops_bytes = dir_stats(f"{hive}/canonical/operations")
    n_views, views_bytes = dir_stats(f"{hive}/canonical/views")
    n_packs, pack_bytes = 0, 0
    pdir = f"{hive}/git/objects/pack"
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


def week_days(srv):
    """The week setup_sources.sh held back from `srv`'s main, which ends at
    refs/bench/upstream: for each day, the last commit on its first-parent line made by the
    day's end, or None while there is none yet."""
    span = "main..refs/bench/upstream"
    _, p = sh(["git", "-C", srv, "log", "--first-parent", "--reverse", "--format=%H %ct", span])
    line = [(c, int(t)) for c, t in (entry.split() for entry in p.stdout.splitlines())]
    start = line[-1][1] - 7 * 86400
    days, latest = [], None
    for d in range(1, 8):
        latest = next((c for c, t in reversed(line) if t <= start + d * 86400), latest)
        days.append(latest)
    days[-1] = line[-1][0]
    return days


def work_day(repo, d, commits, describes):
    """A day of work: bring in upstream's, rebase the feature onto it, and add to it."""
    jj(repo, "git", "fetch")
    jj(repo, "rebase", "-s", "roots(::feature ~ ::main)", "-o", "main")
    os.makedirs(f"{repo}/bench-week", exist_ok=True)
    for i in range(commits):
        jj(repo, "new", "feature")
        with open(f"{repo}/bench-week/day-{d}-{i}.txt", "w") as f:
            f.write(f"day {d}, change {i}\n" * 5)
        jj(repo, "commit", "-m", f"bench: day {d} commit {i}")
        jj(repo, "bookmark", "set", "feature", "-r", "@-")
    for i in range(describes):
        jj(repo, "describe", "feature", "-m", f"bench: day {d} commit {commits - 1}, take {i}")


# ---------------------------------------------------------------------------------------


def main():
    global RUN, LOG
    ap = argparse.ArgumentParser()
    ap.add_argument("repo")
    ap.add_argument("reps", type=int)
    ap.add_argument("--phases", default="initial,scenarios,noop,week,daemon,oplog")
    ap.add_argument("--clones", type=int, default=3)
    ap.add_argument("--week-commits", type=int, default=3, help="commits A makes each day")
    ap.add_argument("--week-describes", type=int, default=5, help="rewordings A makes each day")
    ap.add_argument("--oplog-ops", type=int, default=300)
    ap.add_argument("--latency-reps", type=int, default=10)
    ap.add_argument("--idle-seconds", type=int, default=150)
    ap.add_argument("--delay-ms", type=float, default=0, help="one-way delay added by the proxy")
    args = ap.parse_args()
    phases = set(args.phases.split(","))
    R = args.repo
    tag = f"{R}-delay{args.delay_ms:g}ms" if args.delay_ms else R
    if "week" in phases:
        srv = f"{WORK}/srv/{R}.git"
        week = subprocess.run(
            ["git", "-C", srv, "rev-parse", "-q", "--verify", "refs/bench/upstream"],
            capture_output=True,
        )
        if week.returncode != 0:
            sys.exit(
                f"srv/{R}.git holds back no week for the week phase; run setup_sources.sh again"
            )
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
    # Last, as it takes longest to start, so that the others' ports are soon taken.
    hub = f"{RUN}/hub"
    start_hub(hub, RUST_LOG="info", GIT_TRACE2_EVENT=f"{RUN}/trace-hub.json")
    for port in (PORT_GIT, CONTROL):
        wait_port(port)

    srv_rel = f"srv-git/{R}.git"
    shutil.copytree(f"{WORK}/srv/{R}.git", f"{RUN}/{srv_rel}")
    shutil.copytree(f"{WORK}/srv/{R}.git", f"{RUN}/srv-m/{R}.git")
    url = lambda route: f"git://127.0.0.1:{ROUTES[route][0]}/{srv_rel}"  # noqa: E731
    direct_m = f"git://127.0.0.1:{PORT_GIT}/srv-m/{R}.git"
    A, Bg, Bp = f"{RUN}/A", f"{RUN}/B", f"{RUN}/Bp"
    Am, Cm = f"{RUN}/Am", f"{RUN}/Cm"

    def track(repo):
        jj(repo, "bookmark", "track", "feature@origin", "marker@origin")

    def git_world_agrees():
        for ref in ("main", "feature", "marker"):
            a, b = rev(A, ref), rev(Bg, ref)
            assert a and a == b, f"git world diverged on {ref}: {a} vs {b}"
            p = rev(Bp, f"refs/remotes/origin/{ref}")
            assert a == p, f"plain git diverged on {ref}: {a} vs {p}"

    def musubi_world_agrees():
        for ref in ("main", "feature", "marker"):
            a, b = rev(Am, ref), rev(Bm, ref)
            assert a and a == b, f"musubi world diverged on {ref}: {a} vs {b}"

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
    init["plain_git_clone_B"] = []
    for k in range(args.clones):
        dest = f"{RUN}/Bpclone{k}"
        m = measure("gitB", lambda: sh(["git", "clone", "-q", url("gitB"), dest], cwd=RUN)[0])
        m["disk_git"] = du(f"{dest}/.git")
        init["plain_git_clone_B"].append(m)
        log("plain git clone B", k, m)
        if k < args.clones - 1:
            shutil.rmtree(dest)
        else:
            os.rename(dest, Bp)

    # musubi world
    sh(["jj", "git", "clone", "--colocate", direct_m, Am], cwd=RUN)
    track(Am)
    # The hive is named after the repository.
    h0 = hub_stats(hub)
    init["musubi_seed_A"] = measure(
        "hubA",
        lambda: member(
            ["create", R, "--hub", hub_route("hubA"), "--machine", "A"], cwd=Am, e=machine("A")
        ),
    )
    init["musubi_seed_A"]["hub_store"] = stats_delta(h0, hub_stats(hub))
    log("musubi seed", init["musubi_seed_A"])
    hive = hive_dir(hub)
    init["musubi_clone_B"] = []
    for k in range(args.clones):
        dest = f"{RUN}/Bmclone{k}"
        h0 = hub_stats(hub)
        m = measure(
            "hubB",
            lambda: member(
                ["clone", R, dest, "--hub", hub_route("hubB"), "--machine", f"B{k}"],
                cwd=RUN,
                e=machine(f"B{k}"),
            ),
        )
        m["hub_store"] = stats_delta(h0, hub_stats(hub))
        m["disk_git"], m["disk_jj"] = du(f"{dest}/.git"), du(f"{dest}/.jj")
        m["disk_musubi"] = du(f"{dest}/.jj/repo/musubi")
        init["musubi_clone_B"].append(m)
        log("musubi clone B", k, m)
    # The daemon config names the clone's path, so B' stays where it was cloned.
    Bm = f"{RUN}/Bmclone{args.clones - 1}"
    nameB = f"B{args.clones - 1}"
    # A machine that already has a git clone joins the hive.
    sh(["jj", "git", "clone", "--colocate", direct_m, Cm], cwd=RUN)
    track(Cm)
    h0 = hub_stats(hub)
    init["musubi_join_existing_C"] = measure(
        "hubC",
        lambda: member(
            ["join", "--hub", hub_route("hubC"), "--machine", "C"], cwd=Cm, e=machine("C")
        ),
    )
    init["musubi_join_existing_C"]["hub_store"] = stats_delta(h0, hub_stats(hub))
    log("musubi join existing C", init["musubi_join_existing_C"])
    # A' catches up with the joins, then B' with A'.
    init["musubi_A_catchup"] = measure(
        "hubA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=machine("A"))[0]
    )
    init["musubi_B_catchup"] = measure(
        "hubB", lambda: sh([MUSUBI, "sync"], cwd=Bm, e=machine(nameB))[0]
    )
    for _ in range(2):
        sh([MUSUBI, "sync"], cwd=Am, e=machine("A"))
        sh([MUSUBI, "sync"], cwd=Bm, e=machine(nameB))

    def disk():
        return {
            "git_server": du(f"{RUN}/{srv_rel}"),
            "A_git": du(f"{A}/.git"),
            "A_jj": du(f"{A}/.jj"),
            "B_git": du(f"{Bg}/.git"),
            "B_jj": du(f"{Bg}/.jj"),
            "Bp_git": du(f"{Bp}/.git"),
            "hub_total": du(hub),
            "hub_git": du(f"{hive}/git"),
            "hub_canonical": du(f"{hive}/canonical"),
            "hub_extras": du(f"{hive}/extras"),
            "hub_blobs": du(f"{hive}/blobs"),
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
                row["plain_git_fetch"] = measure(
                    "gitB", lambda: sh(["git", "fetch", "-q"], cwd=Bp)[0]
                )
                git_world_agrees()
                # musubi world
                row["local_musubi"], bm = scenario(s, Am, i)
                h0 = hub_stats(hub)
                row["musubi_push"] = measure(
                    "hubA",
                    lambda: sh(
                        [MUSUBI, "sync"],
                        cwd=Am,
                        e=machine("A", GIT_TRACE2_EVENT=f"{RUN}/trace-A-{s}-{i}.json"),
                    )[0],
                )
                row["hub_store"] = stats_delta(h0, hub_stats(hub))
                row["musubi_fetch"] = measure(
                    "hubB",
                    lambda: sh(
                        [MUSUBI, "sync"],
                        cwd=Bm,
                        e=machine(nameB, GIT_TRACE2_EVENT=f"{RUN}/trace-B-{s}-{i}.json"),
                    )[0],
                )
                musubi_world_agrees()
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
        no = res.setdefault(
            "noop",
            {k: [] for k in ("git_fetch", "plain_git_fetch", "git_push", "musubi_B", "musubi_A")},
        )
        for _ in range(5):
            no["git_fetch"].append(measure("gitB", lambda: sh(["jj", "git", "fetch"], cwd=Bg)[0]))
            no["plain_git_fetch"].append(
                measure("gitB", lambda: sh(["git", "fetch", "-q"], cwd=Bp)[0])
            )
            no["git_push"].append(
                measure("gitA", lambda: sh(["jj", "git", "push", "--tracked"], cwd=A)[0])
            )
            no["musubi_B"].append(
                measure("hubB", lambda: sh([MUSUBI, "sync"], cwd=Bm, e=machine(nameB))[0])
            )
            no["musubi_A"].append(
                measure("hubA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=machine("A"))[0])
            )
        log("noop", json.dumps(no)[:2000])
        save()

    # --- a week: upstream moves on and A works, while B is away; then B catches up -------
    if "week" in phases:
        wk = res.setdefault("week", {})
        servers = (f"{RUN}/{srv_rel}", f"{RUN}/srv-m/{R}.git")
        days = week_days(servers[0])
        wk["upstream_commits"] = int(
            sh(["git", "-C", servers[0], "rev-list", "--count", f"main..{days[-1]}"])[1].stdout
        )
        h0 = hub_stats(hub)
        wk["git_A_pushes"], wk["musubi_A_syncs"] = [], []
        for d, commit in enumerate(days):
            if commit:
                for srv in servers:
                    sh(["git", "-C", srv, "update-ref", "refs/heads/main", commit])
            for repo in (A, Am):
                work_day(repo, d, args.week_commits, args.week_describes)
            wk["git_A_pushes"].append(
                measure("gitA", lambda: sh(["jj", "git", "push", "--tracked"], cwd=A)[0])
            )
            wk["musubi_A_syncs"].append(
                measure("hubA", lambda: sh([MUSUBI, "sync"], cwd=Am, e=machine("A"))[0])
            )
        wk["hub_store"] = stats_delta(h0, hub_stats(hub))
        wk["git_fetch"] = measure("gitB", lambda: sh(["jj", "git", "fetch"], cwd=Bg)[0])
        wk["plain_git_fetch"] = measure("gitB", lambda: sh(["git", "fetch", "-q"], cwd=Bp)[0])
        wk["musubi_fetch"] = measure(
            "hubB", lambda: sh([MUSUBI, "sync"], cwd=Bm, e=machine(nameB))[0]
        )
        for repo in (A, Am):
            assert rev(repo, "main") == days[-1], f"{repo} didn't bring in upstream's week"
        git_world_agrees()
        musubi_world_agrees()
        log("week", json.dumps(wk))
        res["disk_after_week"] = disk()
        save()

    # --- daemons: latency and idle cost ------------------------------------------------
    if "daemon" in phases:
        dm = res.setdefault("daemon", {})
        da = start([MUSUBI, "daemon"], cwd=Am, e=machine("A", RUST_LOG="info"), name="daemonA")
        db = start([MUSUBI, "daemon"], cwd=Bm, e=machine(nameB, RUST_LOG="info"), name="daemonB")
        time.sleep(5)
        lat = dm.setdefault("musubi_latency", [])
        for k in range(args.latency_reps):
            c0 = counters()
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
            lat.append(
                {
                    "cmd": t_cmd,
                    "latency": seen,
                    "A_bytes": (c1["hubA"]["up"] + c1["hubA"]["down"])
                    - (c0["hubA"]["up"] + c0["hubA"]["down"]),
                    "B_bytes": (c1["hubB"]["up"] + c1["hubB"]["down"])
                    - (c0["hubB"]["up"] + c0["hubB"]["down"]),
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
        c0, t0 = counters(), time.time()
        time.sleep(args.idle_seconds)
        c1, t1 = counters(), time.time()
        dm["idle"] = {
            "seconds": t1 - t0,
            "A_up": c1["hubA"]["up"] - c0["hubA"]["up"],
            "A_down": c1["hubA"]["down"] - c0["hubA"]["down"],
            "B_up": c1["hubB"]["up"] - c0["hubB"]["up"],
            "B_down": c1["hubB"]["down"] - c0["hubB"]["down"],
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
                sh([MUSUBI, "sync"], cwd=Am, e=machine("A"))
        sh([MUSUBI, "sync"], cwd=Am, e=machine("A"))
        ol["build_seconds"] = time.perf_counter() - t0
        ol["added"] = stats_delta(h0, hub_stats(hub))
        ol["hub_store"] = hub_stats(hub)
        dest = f"{RUN}/Dm"
        h0 = hub_stats(hub)
        m = measure(
            "hubD",
            lambda: member(
                ["clone", R, dest, "--hub", hub_route("hubD"), "--machine", "D"],
                cwd=RUN,
                e=machine("D", GIT_TRACE2_EVENT=f"{RUN}/trace-D-clone.json"),
            ),
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
