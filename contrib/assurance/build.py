"""Join verified observations with code structure, explicit proof scope and stable layout."""

import hashlib
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

import graph
import taxonomy
from common import (
    HERE,
    ROOT,
    harness_hashes,
    production_files,
    source,
    source_identity,
    write_json,
)


def mutation_results(outcomes, log_root=None):
    """Compile failures and timeouts must never count as tests detecting a broken program."""
    by_file = defaultdict(Counter)
    sites = []
    labels = {
        "CaughtMutant": "noticed",
        "MissedMutant": "missed",
        "Unviable": "unviable",
        "Timeout": "timeout",
        "Success": "baseline",
    }
    for o in outcomes["outcomes"]:
        mutant = (
            o["scenario"].get("Mutant") if isinstance(o["scenario"], dict) else None
        )
        if not mutant:
            continue
        label = labels.get(o["summary"])
        if not label:
            raise ValueError("Unknown mutation outcome: " + o["summary"])
        if label == "noticed" and log_root is not None:
            # Nextest can stop a test before cargo-mutants' outer timeout. Its exit code
            # then looks like a test failure to cargo-mutants. Keep timeout-only runs apart.
            log = (Path(log_root) / o["log_path"]).read_text()
            summaries = re.findall(r"Summary \[.*?\] \d+ tests run:([^\n]+)", log)
            if summaries:
                summary = summaries[-1]
                timed_out = re.search(r"([1-9]\d*) timed out", summary)
                failed = re.search(r"([1-9]\d*) (?:failed|exec failed)", summary)
                if timed_out and not failed:
                    label = "timeout"
        by_file[mutant["file"]][label] += 1
        sites.append(
            {
                "file": mutant["file"],
                "line": mutant["span"]["start"]["line"],
                "change": mutant["name"],
                "outcome": label,
                "reportedOutcome": o["summary"],
            }
        )
    return {
        "files": {f: dict(c) for f, c in sorted(by_file.items())},
        "sites": sorted(sites, key=lambda s: (s["file"], s["line"], s["change"])),
    }


def load_catalog():
    catalog = json.loads((HERE / "catalog.json").read_text())
    ids = {e["id"] for e in catalog["evidence"]}
    for claim in catalog["claims"]:
        claim["evidence"] = [id for id in claim["evidence"] if id in ids]
        missing = [p for p in claim["code"] if not (ROOT / p).exists()]
        if missing:
            raise ValueError(f"Update catalog claim {claim['id']}: missing {missing}")
    for e in catalog["evidence"]:
        definition = catalog["sources"][e["source"]]
        path, symbol = definition["path"], definition.get("symbol")
        if not (ROOT / path).exists():
            raise ValueError(f"Update catalog evidence {e['id']}: missing {path}")
        if symbol and not re.search(
            r"\b" + re.escape(symbol) + r"\b", (ROOT / path).read_text()
        ):
            raise ValueError(
                f"Update catalog evidence {e['id']}: missing {path}::{symbol}"
            )
    return catalog


def inventory(catalog):
    files = []
    for p in production_files():
        text = p.read_text()
        for a, b, _ in reversed(list(source.gated_items(text))):
            text = text[:a] + "\n" * text[a:b].count("\n") + text[b:]
        files.append(
            {
                "id": p.relative_to(ROOT).as_posix(),
                "codeLines": sum(
                    bool(l.strip()) for l in source.mask_literals(text).splitlines()
                ),
                "source": p.relative_to(ROOT).as_posix(),
            }
        )
    return {"files": files, "claims": catalog["claims"]}


def assign_roles(network, catalog):
    defaults = {
        "musubi": "interface",
        "musubi-core": "protocol",
        "musubi-hub": "storage",
        "musubi-jj": "history",
        "musubi-sync": "coordination",
        "musubi-transport": "transport",
    }
    roles = dict(catalog["nodeRoles"])
    for id, n in network["nodes"].items():
        if id not in roles:
            # Known namespaces carry a curated role; otherwise show an explicit unknown.
            family = n["name"].split("::")[0]
            candidates = {
                value
                for old_id, value in catalog["nodeRoles"].items()
                if old_id.startswith("crates/" + n["crate"] + "/src/" + family + "/")
            }
            roles[id] = (
                next(iter(candidates))
                if len(candidates) == 1
                else (
                    defaults.get(n["crate"], "other")
                    if n["kind"] == "crate"
                    else "other"
                )
            )
    return {id: roles[id] for id in sorted(network["nodes"])}


def build(runs, output, seed=9):
    identity = source_identity()
    catalog = load_catalog()
    network = graph.build(inventory(catalog), seed)
    functions, by_file = taxonomy.index_functions()
    captures, observations, mutation = [], [], {"files": {}, "sites": []}
    offset, effort = 0.0, 0.0
    for directory in sorted(
        (Path(p).resolve() for p in runs),
        key=lambda p: (
            {"tests": 0, "fuzz": 1, "mutation": 2}[
                json.loads((p / "manifest.json").read_text())["kind"]
            ],
            str(p),
        ),
    ):
        manifest = json.loads((directory / "manifest.json").read_text())
        if manifest["sourceDigest"] != identity["sourceDigest"]:
            raise ValueError(
                f"{directory}: source fingerprint differs; collect this revision again"
            )
        if manifest.get("harnessHashes") != harness_hashes(manifest["kind"]):
            raise ValueError(f"{directory}: test/fuzz harness fingerprint differs")
        if "ended" not in manifest:
            raise ValueError(f"{directory}: collection did not finish")
        if manifest["kind"] != "mutation" and manifest.get("exitCode") != 0:
            raise ValueError(f"{directory}: capture failed")
        captures.append({k: v for k, v in manifest.items() if k != "sourceHashes"})
        if manifest["kind"] == "mutation":
            if mutation["sites"]:
                raise ValueError("Pass only one mutation capture")
            outcomes = json.loads((directory / "mutants.out/outcomes.json").read_text())
            plan = json.loads((directory / "mutation-plan.json").read_text())
            if outcomes.get("end_time") is None or outcomes.get("total_mutants") != len(
                plan
            ):
                raise ValueError(f"{directory}: mutation run is incomplete")
            mutation = mutation_results(outcomes, directory / "mutants.out")
            continue
        paths = sorted(
            directory.glob("tests/*/test.json")
            if manifest["kind"] == "tests"
            else directory.glob("*/*/test.json")
        )
        records = [json.loads(p.read_text()) | {"folder": p.parent} for p in paths]
        records.sort(key=lambda r: (r["ended"], r["id"]))
        if not records:
            raise ValueError(f"{directory}: no observations")
        start = min(r["started"] for r in records)
        for r in records:
            coverage = json.loads((r["folder"] / "lines.json").read_text())
            ops = sorted(p.name for p in (r["folder"] / "oracle-ops").glob("*"))
            if any(op not in catalog["oracleModels"] for op in ops):
                raise ValueError(
                    f"{r['id']}: add new oracle operations to catalog.json: {ops}"
                )
            if manifest["kind"] == "tests":
                function = taxonomy.find_function(r["id"], functions)
                tags = taxonomy.classify(r["id"], function, by_file, ops)
                t = offset + r["ended"] - start
                run_seconds = r["ended"] - r["started"]
            else:
                tags = ["fuzz"]
                done = re.search(
                    r"Done (\d+) runs in (\d+) second",
                    (r["folder"] / "fuzz.log").read_text(),
                )
                if not done:
                    raise ValueError(f"{r['folder']}: no libFuzzer completion record")
                run_seconds = float(done[2])
                t = observations[-1]["t"] + run_seconds if observations else run_seconds
                r["inputs"] = int(done[1])
            effort += run_seconds
            models = sorted(
                {
                    f"formal/Musubi/{model}.lean"
                    for op in ops
                    for model in catalog["oracleModels"].get(op, [])
                }
            )
            observations.append(
                {
                    "t": round(t, 3),
                    "e": round(effort, 3),
                    "n": r["id"],
                    "m": tags,
                    "ok": r["exitCode"] == 0,
                    "lines": coverage,
                    "models": models,
                    "inputs": r.get("inputs"),
                    "corpusFiles": r.get("corpusFiles"),
                }
            )
        offset = observations[-1]["t"]
    # Capture order is explicit and stable: tests first, then fuzz; mutation is a separate measure.
    # Each run retains its own execution timestamps; gaps between captures are not test effort.
    if not observations:
        raise ValueError(
            "Build needs a test or fuzz capture for executable-line mappings"
        )
    universe = defaultdict(set)
    for event in observations:
        for file, coverage in event["lines"].items():
            universe[file].update(coverage["all"])
    first = {f: defaultdict(dict) for f in universe}
    counts = Counter()
    chains = []
    for index, event in enumerate(observations, 1):
        counts.update(event["m"])
        if event["models"]:
            chains.append(
                {"test": event["n"], "models": event["models"], "event": index}
            )
        if not event["ok"]:
            continue
        for file, coverage in event["lines"].items():
            for tag in event["m"]:
                for line in coverage["hit"]:
                    first[file][tag].setdefault(line, index)
    # A Kani overlay is explicitly the ordinary Rust tests that execute its proved helpers.
    targets = [
        ("crates/musubi-sync/src/blobs.rs", "new_from"),
        ("crates/musubi-sync/src/remote.rs", "window"),
        ("crates/musubi-sync/src/wire.rs", "chunk_size"),
        ("crates/musubi-sync/src/service.rs", "reaches_end"),
    ]
    kani_tests = set()
    for file, name in targets:
        if name not in by_file[file]:
            raise ValueError(f"Update Kani helper mapping: {file}::{name}")
        function = by_file[file][name]
        for index, event in enumerate(observations, 1):
            name = event["n"]
            candidate = (
                (
                    file.endswith("/blobs.rs")
                    and name.endswith(
                        (
                            "::chunk_past_the_largest_offset_is_ignored",
                            "::receive_follows_the_prefix_model",
                        )
                    )
                )
                or (
                    file.endswith("/wire.rs")
                    and name.endswith("::wire::tests::a_full_chunk_fits")
                )
                or (
                    file.endswith(("/remote.rs", "/service.rs"))
                    and (
                        "musubi-sync::it::transfer::" in name
                        or name.endswith(
                            "::remote::tests::downloads_give_up_on_a_blob_that_keeps_failing"
                        )
                    )
                )
            )
            if not candidate:
                continue
            if any(
                function["start"] <= n <= function["end"]
                for n in event["lines"].get(file, {}).get("hit", [])
            ):
                kani_tests.add(index)
    for index in sorted(kani_tests):
        event = observations[index - 1]
        if event["ok"]:
            for file, coverage in event["lines"].items():
                for line in coverage["hit"]:
                    first[file]["kani"].setdefault(line, index)
    counts["kani"] = len(kani_tests)
    mechanisms = catalog["mechanisms"]
    for m in mechanisms:
        m["tests"] = counts[m["id"]]
        m["status"] = "recorded" if counts[m["id"]] else "not measured"
        if m["id"] == "mutation":
            m["tests"] = len(mutation["sites"])
            m["status"] = "recorded" if mutation["sites"] else "not measured"
    claims = catalog["claims"]
    evidence = catalog["evidence"]
    # Actual changed sites, rather than a guessed whole-module coverage percentage.
    for file in mutation["files"]:
        cid, eid = "mutation:" + file, "mutation-evidence:" + file
        claims.append({"id": cid, "code": [file], "evidence": [eid]})
        evidence.append({"id": eid, "claim": cid, "mechanism": "mutation"})
        network["nodes"][file]["claims"].append(cid)
        network["nodes"]["crate:" + network["nodes"][file]["crate"]]["claims"].append(
            cid
        )
    node_roles = assign_roles(network, catalog)
    roles = catalog["roles"] + (
        [{"id": "other", "name": "Unclassified role", "series": None}]
        if "other" in node_roles.values()
        else []
    )
    measured = {
        "sourceRevision": captures[0]["sourceRevision"],
        "sourceDigest": identity["sourceDigest"],
        "duration": observations[-1]["t"] if observations else 1,
        "effort": observations[-1]["e"] if observations else 1,
        "passed": sum(e["ok"] for e in observations if "fuzz" not in e["m"]),
        "failed": sum(not e["ok"] for e in observations),
        "coverageGroups": sorted(
            tag for tag, count in counts.items() if count and tag != "mutation"
        ),
        "events": [{k: v for k, v in e.items() if k != "lines"} for e in observations],
        "files": {
            f: {
                "lines": sorted(lines),
                "hash": hashlib.sha256((ROOT / f).read_bytes()).hexdigest(),
                "first": {
                    tag: [arrivals.get(n, 0) for n in sorted(lines)]
                    for tag, arrivals in sorted(first[f].items())
                },
            }
            for f, lines in sorted(universe.items())
        },
        "proofChains": chains,
        "mutation": mutation,
        "captures": captures,
        "captureId": hashlib.sha256(
            json.dumps(
                [{k: v for k, v in e.items() if k != "lines"} for e in observations],
                sort_keys=True,
            ).encode()
        ).hexdigest(),
        "fuzzCheckpoints": sum("fuzz" in e["m"] for e in observations),
        "fuzzInputs": sum(e.get("inputs") or 0 for e in observations),
        "limits": [
            "Executable Rust lines, not branches, assertions or complete proof coverage.",
            "Each test or fuzz checkpoint contributes at completion; no within-checkpoint timestamps.",
            "Replay concatenates captured run times; it excludes time between separate captures.",
            "Fuzz runtime uses libFuzzer’s reported seconds; compilation and export are excluded.",
            "Kani colours are related Rust tests, not solver results.",
            "Killed children may not flush LLVM profiles.",
        ],
    }
    data = {
        "schema": 2,
        "generator": {
            "revision": identity["sourceRevision"],
            "files": {
                p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                for p in sorted(HERE.glob("*"))
                if p.suffix in (".py", ".js", ".json", ".css", ".in")
            },
        },
        "mechanisms": mechanisms,
        "claims": claims,
        "evidence": evidence,
        "roles": roles,
        "nodeRoles": node_roles,
        "network": network,
        "measured": measured,
        "layout": {
            "version": 1,
            "seed": seed,
            "algorithm": "Sorted force simulation, SHA-256 per-node initialization, fixed 520 steps",
        },
    }
    write_json(output, data)
    return data
