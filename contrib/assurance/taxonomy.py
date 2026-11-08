"""Classify recorded executions by their source and actual use of the Lean oracle."""

import os
import re
from collections import defaultdict

import tomllib
from common import ROOT, source


def index_functions():
    functions = defaultdict(list)
    by_file = defaultdict(dict)
    packages = {
        p.parent.name: tomllib.loads(p.read_text())["package"]["name"]
        for p in ROOT.glob("crates/*/Cargo.toml")
    }
    for path in sorted(ROOT.glob("crates/**/*.rs")):
        text = path.read_text()
        masked = source.mask_literals(text)
        relative = path.relative_to(ROOT).as_posix()
        package = packages[path.relative_to(ROOT).parts[1]]
        for m in re.finditer(
            r"\b(?:async\s+)?fn\s+(\w+)\s*(?:<[^;{}]*>)?\s*\(", masked
        ):
            a = masked.find("{", m.end())
            semicolon = masked.find(";", m.end())
            if a < 0 or (semicolon >= 0 and semicolon < a):
                continue
            depth, b = 1, a + 1
            while depth and b < len(masked):
                depth += (masked[b] == "{") - (masked[b] == "}")
                b += 1
            # Its own attributes and doc comments: from the end of the item, statement or block
            # opening before it, outside literals, so not a neighbour's attributes.
            start = max(masked.rfind(c, 0, m.start()) for c in "};{") + 1
            entry = {
                "path": relative,
                "name": m[1],
                "body": text[a:b],
                "start": text.count("\n", 0, m.start()) + 1,
                "end": text.count("\n", 0, b) + 1,
                "hegel": "#[hegel::test" in text[start : m.start()],
                "attributes": text[start : m.start()],
            }
            functions[package, m[1]].append(entry)
            by_file[relative][m[1]] = entry
    return functions, by_file


def built_here(function):
    """Whether this platform compiles `function`: a test can have a version for Unix and
    another, of the same name, for Windows. Only `#[cfg(unix)]` and `#[cfg(windows)]` on the
    function itself count; other platform conditions leave both versions in, which
    `find_function` refuses as ambiguous rather than guess."""
    other = "#[cfg(unix)]" if os.name == "nt" else "#[cfg(windows)]"
    return other not in function.get("attributes", "")


def find_function(identity, functions):
    parts = identity.split("::")
    candidates = [f for f in functions[parts[0], parts[-1]] if built_here(f)]

    def score(f):
        tokens = set(re.split(r"[/_.]", f["path"]))
        return sum(p in tokens for p in parts[1:-1])

    ordered = sorted(candidates, key=lambda f: (-score(f), f["path"], f["start"]))
    if not ordered or (len(ordered) > 1 and score(ordered[0]) == score(ordered[1])):
        raise ValueError(f"Missing or ambiguous test source: {identity}")
    return ordered[0]


def uses_snapshot(function, by_file, seen=None):
    seen = set() if seen is None else seen
    key = function["path"], function["name"]
    if key in seen:
        return False
    seen.add(key)
    body = source.mask_literals(function["body"])
    if re.search(r"\bassert_(?:(?:debug|json|yaml|ron|compact_json)_)?snapshot!", body):
        return True
    calls = set(re.findall(r"\b(\w+)\s*\(", body))
    return any(
        uses_snapshot(f, by_file, seen)
        for name, f in by_file.get(function["path"], {}).items()
        if name in calls
    )


def classify(identity, function, by_file, oracle_ops):
    tags = set()
    if function["hegel"]:
        tags.add("hegel")
    if oracle_ops:
        tags.add("conformance")
    if not tags:
        if "::e2e_search::" in identity:
            tags.add("smoke")
        elif "::cli::" in identity:
            tags.add("cli")
        elif "::races::" in identity:
            tags.add("races")
        elif identity.startswith("musubi-transport::contract::"):
            tags.add("contracts")
        elif "/src/" in function["path"] or identity.startswith(
            "musubi-core::protocol::"
        ):
            tags.add("unit")
        else:
            tags.add("integration")
    if "::races::" in identity:
        tags.add("races")
    if (
        "::it::faults::" in identity
        or "::it::lies::" in identity
        or identity.endswith(
            (
                "::memory_transport_with_faults",
                "::stream_transport_can_fail_requests_while_disconnected",
            )
        )
        or re.search(r"\.(?:kill|crash)\s*\(", source.mask_literals(function["body"]))
    ):
        tags.add("faults")
    if uses_snapshot(function, by_file):
        tags.add("snapshots")
    return sorted(tags)
