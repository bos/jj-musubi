"""Estimate the balance of production, proof/model, test and miscellaneous code."""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
GROUPS = ("Production", "Proof/model", "Tests", "Misc")
# Hide Rust comments and literals before looking for item boundaries. In particular, braces
# and cfg attributes in raw snapshot strings must not change a test module's extent.
LITERAL = re.compile(
    r'//[^\n]*|/\*|(?:br|cr|r)(?P<hashes>\#*)"|"(?:\\.|[^"\\])*"'
    r"|'(?:\\(?:u\{[^}]*\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'",
    re.DOTALL,
)
GATE = re.compile(r"^#\[cfg\((.*)\)\]", re.MULTILINE)


def mask_literals(source):
    pieces = []
    end = 0
    while match := LITERAL.search(source, end):
        pieces.append(source[end:match.start()])
        stop = match.end()
        if match.group() == "/*":
            depth = 1
            while depth:
                token = re.search(r"/\*|\*/", source[stop:])
                if token is None:
                    raise ValueError("unclosed Rust comment")
                depth += 1 if token.group() == "/*" else -1
                stop += token.end()
        elif match.group("hashes") is not None:
            closing = '"' + match.group("hashes")
            stop = source.find(closing, stop)
            if stop < 0:
                raise ValueError("unclosed Rust raw string")
            stop += len(closing)
        pieces.append(re.sub(r"[^\n]", " ", source[match.start():stop]))
        end = stop
    pieces.append(source[end:])
    return "".join(pieces)


def gated_items(source):
    """Find rustfmt's top-level test/fuzz-only and Kani items, including their attributes."""
    masked = mask_literals(source)
    covered_until = 0
    for match in GATE.finditer(masked):
        if match.start() < covered_until:
            continue
        gate = re.sub(r"\s", "", match[1])
        if gate == "kani":
            group = "Proof/model"
        elif gate in ("test", "fuzzing", "any(test,fuzzing)", "any(fuzzing,test)") or gate.startswith(
            "all(test,"
        ):
            group = "Tests"
        else:
            continue
        # Each attribute is balanced, as is the following item. A module or function ends
        # with its closing brace; a use, declaration or out-of-line module with a semicolon.
        depth = 0
        item = False
        for i in range(match.start(), len(masked)):
            char = masked[i]
            if char == "#" and depth == 0 and not item:
                continue
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
                if depth == 0 and item and char == "}":
                    covered_until = i + 1
                    yield match.start(), covered_until, group
                    break
            elif depth == 0 and not char.isspace():
                item = True
                if char == ";":
                    covered_until = i + 1
                    yield match.start(), covered_until, group
                    break
        else:
            raise ValueError("unclosed Rust item")


def test_modules(path, source, spans):
    """Follow test-only out-of-line modules, which may have ordinary source filenames."""
    for start, end, group in spans:
        if group != "Tests":
            continue
        item = source[start:end]
        module = re.search(r"\bmod\s+(\w+)\s*;\s*$", mask_literals(item))
        if not module:
            continue
        explicit = re.search(r'#\[path\s*=\s*"([^"]+)"\]', item)
        if explicit:
            yield (path.parent / explicit[1]).resolve()
        else:
            base = path.parent if path.stem in ("lib", "main", "mod") else path.with_suffix("")
            yield (base / (module[1] + ".rs")).resolve()
            yield (base / module[1] / "mod.rs").resolve()


def category(path, language, external_tests):
    if path in external_tests or "tests" in path.parts or path.parts[0] == "fuzz":
        return "Tests"
    if "musubi-testutil" in path.parts or path.parts[:2] == ("formal", "test"):
        return "Tests"
    if language == "Lean":
        if path.stem.endswith("Test") or path.name in ("Oracle.lean", "ExecJson.lean"):
            return "Tests"
        return "Proof/model"
    if path.parts[0] == "crates" and "src" in path.parts and language == "Rust":
        return "Production"
    return "Misc"


def count(paths):
    try:
        result = subprocess.run(
            ["tokei", "--output", "json", "--hidden", "--exclude", ".jj", "--exclude", ".git",
             "--exclude", "Cargo.lock", "--exclude", "lake-manifest.json", *map(str, paths)],
            cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
        )
    except FileNotFoundError:
        raise ValueError("install tokei and put it on PATH") from None
    data = json.loads(result.stdout)
    # Use only each file's own statistics: code fences and doc comments have child reports
    # in tokei's JSON and must not be counted again as source code.
    return [(language, Path(report["name"]).resolve(), report["stats"]["code"])
            for language, stats in data.items() if language != "Total"
            for report in stats["reports"]]


def summarize():
    reports = count([ROOT])
    rust = {}
    external_tests = set()
    for language, path, _ in reports:
        if language == "Rust":
            source = path.read_text(encoding="utf-8")
            spans = list(gated_items(source))
            rust[path] = (source, spans)
            external_tests.update(test_modules(path, source, spans))
    external_tests = {p.relative_to(ROOT) for p in external_tests}
    totals = {group: Counter() for group in GROUPS}
    with tempfile.TemporaryDirectory(prefix="musubi-loc-") as tmp:
        fragments = {}
        for language, path, lines in reports:
            relative = path.relative_to(ROOT)
            group = category(relative, language, external_tests)
            column = language if language in ("Rust", "Lean") else "Other"
            if language == "Rust" and group == "Production":
                source, spans = rust[path]
                # Count complete items with tokei, then subtract them from their source
                # file. This preserves tokei's treatment of comments and multiline strings.
                for start, end, item_group in spans:
                    fragment = Path(tmp).resolve() / f"{len(fragments)}.rs"
                    fragment.write_text(source[start:end] + "\n", encoding="utf-8")
                    fragments[fragment] = (item_group, column)
            totals[group][column] += lines
        if fragments:
            for _, path, lines in count([tmp]):
                group, column = fragments[path]
                totals[group][column] += lines
                totals["Production"][column] -= lines
    return totals


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    totals = summarize()
    columns = ("Rust", "Lean", "Other")
    total = sum(sum(row.values()) for row in totals.values())
    print(f"{'Code lines':<13}" + "".join(f"{c:>10}" for c in (*columns, "Total", "Share")))
    for group, row in (*totals.items(), ("Total", sum(totals.values(), Counter()))):
        n = sum(row.values())
        share = n / total if total else 0
        print(f"{group:<13}" + "".join(f"{row[c]:>10,}" for c in columns)
              + f"{n:>10,}{share:>9.1%}")
    production = sum(totals["Production"].values())
    assurance = sum(totals["Proof/model"].values()) + sum(totals["Tests"].values())
    if production:
        print(f"\nProof/model + tests: {assurance / production:.2f}x production")
    print("Excludes blank lines, comments, documentation, lockfiles and ignored build output.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        sys.exit(f"loc: {error}")
