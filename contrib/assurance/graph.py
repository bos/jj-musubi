"""Extract imports and compute a sorted, fixed-seed force layout; no browser simulation."""

import hashlib
import math
import random
import re
from pathlib import Path

import tomllib
from common import ROOT
from common import source as loc


def build(data, seed=9):
    roles = {
        "musubi": "Commands & daemon",
        "musubi-core": "Protocol",
        "musubi-hub": "Hub storage",
        "musubi-jj": "jj integration",
        "musubi-sync": "Sync engine",
        "musubi-transport": "Transport",
    }
    descriptions = {
        "musubi": "Commands, background synchronization and machine configuration.",
        "musubi-core": "The protocol state machines, independent of repositories and network I/O.",
        "musubi-hub": "The hub’s stored histories, identities and matching.",
        "musubi-jj": "Translate and realize operations in real jj repositories.",
        "musubi-sync": "Connect protocol state machines to repositories, stores and transfer.",
        "musubi-transport": "Framing and delivery over local or remote connections.",
    }
    crates = {}
    for name in sorted({Path(f["id"]).parts[1] for f in data["files"]}):
        manifest = tomllib.loads((ROOT / "crates" / name / "Cargo.toml").read_text())
        crates[name] = {
            "id": "crate:" + name,
            "kind": "crate",
            "crate": name,
            "name": roles.get(name, name),
            "label": name,
            "description": descriptions.get(name, name),
            "path": f"crates/{name}",
            "package": manifest["package"]["name"],
            "aliases": {
                manifest["package"]["name"].replace("-", "_"),
                name.replace("-", "_"),
            },
            "files": [],
            "lines": 0,
            "claims": [],
        }
        if "lib" in manifest and "name" in manifest["lib"]:
            crates[name]["aliases"].add(manifest["lib"]["name"])
    aliases = {alias: name for name, c in crates.items() for alias in c["aliases"]}
    modules = {}
    by_module = {}
    texts = {}
    for f in sorted(data["files"], key=lambda f: f["id"]):
        p = Path(f["id"])
        name = p.parts[1]
        if name not in crates:
            continue
        rel = p.relative_to(Path("crates") / name / "src")
        parts = tuple(rel.with_suffix("").parts)
        if parts[-1] in {"lib", "main", "mod"}:
            parts = parts[:-1]
        node = {
            "id": f["id"],
            "kind": "module",
            "crate": name,
            "name": "::".join(parts) or "(crate root)",
            "label": name + "::" + ("::".join(parts) or "root"),
            "path": f["id"],
            "lines": f["codeLines"],
            "claims": [c["id"] for c in data["claims"] if f["id"] in c["code"]],
            "namespace": list(parts),
            "source": f["source"],
        }
        modules[node["id"]] = node
        by_module[(name, parts)] = node["id"]
        crates[name]["files"].append(node["id"])
        crates[name]["lines"] += node["lines"]
        source = (ROOT / p).read_text()
        for start, end, _ in reversed(list(loc.gated_items(source))):
            source = (
                source[:start] + "\n" * source[start:end].count("\n") + source[end:]
            )
        texts[node["id"]] = loc.mask_literals(source)

    def flatten(tree):
        tree = re.sub(r"\s+as\s+(?:\w+|_)", "", tree).strip()
        if "{" not in tree:
            return [tree.strip().rstrip(":")]
        start = tree.index("{")
        depth = 0
        end = None
        for i, ch in enumerate(tree[start:], start):
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    end = i
                    break
        if end is None:
            return []
        prefix = tree[:start]
        items = []
        part = ""
        depth = 0
        for ch in tree[start + 1 : end] + ",":
            if ch == "," and depth == 0:
                if part.strip():
                    items += flatten(prefix + part.strip())
                part = ""
            else:
                part += ch
                if ch == "{":
                    depth += 1
                elif ch == "}":
                    depth -= 1
        return items

    def resolve(node, path):
        parts = [p for p in re.sub(r"\s", "", path).split("::") if p and p != "*"]
        if not parts:
            return None
        if parts[-1] == "self" and len(parts) > 1:
            parts.pop()
        package = node["crate"]
        context = node["namespace"]
        candidates = []
        if parts[0] in aliases:
            package = aliases[parts[0]]
            candidates = [parts[1:]]
        elif parts[0] == "crate":
            candidates = [parts[1:]]
        elif parts[0] == "self":
            candidates = [context + parts[1:]]
        elif parts[0] == "super":
            base = context[:]
            while parts and parts[0] == "super":
                base = base[:-1]
                parts = parts[1:]
            candidates = [base + parts]
        else:
            candidates = [context + parts, parts]
        # Qualified paths resolve to the deepest module that exists. A root import stays a
        # dependency on the public root API; its re-export is represented by another edge.
        for candidate in candidates:
            for size in range(len(candidate), -1, -1):
                if (
                    size == 0
                    and candidate
                    and candidate[0] not in {"crate", "self", "super"}
                    and path.split("::")[0] not in aliases
                    and path.split("::")[0] not in {"crate", "self", "super"}
                ):
                    continue
                target = by_module.get((package, tuple(candidate[:size])))
                if target:
                    return target
        return None

    imports = []
    external = 0
    unresolved = []
    seen = set()
    for id, node in modules.items():
        source = texts[id]
        inline_modules = []
        for declaration in re.finditer(r"\bmod\s+(\w+)\s*\{", source):
            depth = 1
            end = declaration.end()
            while depth and end < len(source):
                if source[end] == "{":
                    depth += 1
                elif source[end] == "}":
                    depth -= 1
                end += 1
            inline_modules.append((declaration.start(), end, declaration[1]))
        for match in re.finditer(r"\buse\s+([^;]+);", source, re.DOTALL):
            line = source[: match.start()].count("\n") + 1
            context = {
                **node,
                "namespace": node["namespace"]
                + [
                    name
                    for start, end, name in inline_modules
                    if start < match.start() < end
                ],
            }
            for path in flatten(match[1]):
                path = re.sub(r"\s", "", path)
                target = resolve(context, path)
                if target and target != id:
                    key = (id, target, path)
                    if key not in seen:
                        seen.add(key)
                        imports.append(
                            {
                                "id": len(imports),
                                "source": id,
                                "target": target,
                                "binding": path,
                                "line": line,
                            }
                        )
                elif not target:
                    if (
                        path.startswith(("crate::", "self::", "super::"))
                        or path.split("::")[0] in aliases
                    ):
                        unresolved.append({"source": id, "binding": path, "line": line})
                    else:
                        external += 1
    imports.sort(key=lambda i: (i["source"], i["target"], i["binding"]))
    for index, item in enumerate(imports):
        item["id"] = index
    for c in crates.values():
        c["claims"] = sorted(
            {cid for fid in c["files"] for cid in modules[fid]["claims"]}
        )
        c.pop("aliases")
    nodes = {**{c["id"]: c for c in crates.values()}, **modules}

    def aggregate(ids):
        displayed = set(ids)

        def mapped(id):
            return id if id in displayed else "crate:" + modules[id]["crate"]

        links = {}
        for item in imports:
            a, b = mapped(item["source"]), mapped(item["target"])
            if a == b:
                continue
            key = (a, b)
            if key not in links:
                links[key] = {
                    "id": a + ">" + b,
                    "source": a,
                    "target": b,
                    "weight": 0,
                    "imports": [],
                }
            links[key]["weight"] += 1
            links[key]["imports"].append(item["id"])
        return sorted(links.values(), key=lambda e: e["id"])

    def layout(ids, links, anchors=None):
        rng = random.Random(seed)
        ids = sorted(ids)
        links = sorted(links, key=lambda e: e["id"])
        n = len(ids)
        points = {
            id: [
                math.cos(i / n * 2 * math.pi) * 180,
                math.sin(i / n * 2 * math.pi) * 180,
            ]
            for i, id in enumerate(ids)
        }
        if anchors:
            for id in ids:
                c = nodes[id]["crate"]
                ax, ay = anchors[c]
                rng = random.Random(hashlib.sha256(f"{seed}:{id}".encode()).digest())
                angle = rng.random() * math.tau
                r = rng.random() * 50
                points[id] = [ax + math.cos(angle) * r, ay + math.sin(angle) * r]
        velocity = {id: [0.0, 0.0] for id in ids}
        max_lines = max(nodes[id]["lines"] for id in ids)
        radii = {
            id: 6 + math.sqrt(nodes[id]["lines"] / max_lines) * 18
            if nodes[id]["kind"] == "crate"
            else 4 + math.sqrt(nodes[id]["lines"] / max_lines) * 7
            for id in ids
        }
        for step in range(520):
            forces = {id: [0.0, 0.0] for id in ids}
            for i, a in enumerate(ids):
                for b in ids[i + 1 :]:
                    dx = points[a][0] - points[b][0]
                    dy = points[a][1] - points[b][1]
                    d = max(0.1, math.hypot(dx, dy))
                    minimum = radii[a] + radii[b] + 15
                    force = (
                        2400 / (d * d) + (minimum - d) * 0.5
                        if d < minimum
                        else 2400 / (d * d)
                    )
                    if anchors and nodes[a]["crate"] != nodes[b]["crate"]:
                        force *= 1.9
                    fx = dx / d * force
                    fy = dy / d * force
                    forces[a][0] += fx
                    forces[a][1] += fy
                    forces[b][0] -= fx
                    forces[b][1] -= fy
            for edge in links:
                a, b = edge["source"], edge["target"]
                dx = points[b][0] - points[a][0]
                dy = points[b][1] - points[a][1]
                d = max(0.1, math.hypot(dx, dy))
                rest = radii[a] + radii[b] + 95 / (1 + math.log1p(edge["weight"]))
                stiffness = 0.022 * (1 + math.log1p(edge["weight"]))
                if anchors and nodes[a]["crate"] != nodes[b]["crate"]:
                    stiffness *= 0.16
                force = (d - rest) * stiffness
                fx = dx / d * force
                fy = dy / d * force
                forces[a][0] += fx
                forces[a][1] += fy
                forces[b][0] -= fx
                forces[b][1] -= fy
            for id in ids:
                if anchors:
                    ax, ay = anchors[nodes[id]["crate"]]
                    forces[id][0] += (ax - points[id][0]) * 0.09
                    forces[id][1] += (ay - points[id][1]) * 0.09
                else:
                    forces[id][0] -= points[id][0] * 0.012
                    forces[id][1] -= points[id][1] * 0.012
                for axis in [0, 1]:
                    velocity[id][axis] = (velocity[id][axis] + forces[id][axis]) * 0.65
                    points[id][axis] += max(-6, min(6, velocity[id][axis]))
        return {id: [round(x, 3), round(y, 3)] for id, (x, y) in points.items()}

    component_ids = [c["id"] for c in crates.values()]
    component_links = aggregate(component_ids)
    component_points = layout(component_ids, component_links)
    anchors = {
        name: [component_points[c["id"]][0] * 4, component_points[c["id"]][1] * 4]
        for name, c in crates.items()
    }
    views = {
        "components": {
            "nodes": component_ids,
            "links": component_links,
            "positions": component_points,
        }
    }
    module_ids = list(modules)
    module_links = aggregate(module_ids)
    views["modules"] = {
        "nodes": module_ids,
        "links": module_links,
        "positions": layout(module_ids, module_links, anchors),
    }
    data["network"] = {
        "nodes": nodes,
        "imports": imports,
        "views": views,
        "unresolved": unresolved,
        "externalBindingsOmitted": external,
        "measurement": "Distinct resolved Rust import paths, with test/fuzz/Kani-only blocks excluded. Repeated identical paths within a file count once.",
        "limits": "A static import graph, not a call graph. Macros, dynamic dispatch and runtime frequency are not measured. External libraries are omitted. Conditional production code for different platforms is included together.",
        "assurance": "Curated claim-to-source links. A lit module has related evidence; this does not establish that all its code is tested or proved.",
    }
    return data["network"]
