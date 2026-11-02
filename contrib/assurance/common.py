"""Portable paths, source identity and LLVM coverage import."""

import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location("loc", ROOT / "contrib/loc.py")
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def production_files():
    candidates = sorted(ROOT.glob("crates/*/src/**/*.rs"))
    external = set()
    for p in candidates:
        external.update(
            source.test_modules(
                p, p.read_text(), list(source.gated_items(p.read_text()))
            )
        )
    return [
        p
        for p in candidates
        if p.parts[len(ROOT.parts) + 1] != "musubi-testutil"
        and p.resolve() not in external
        and not p.name.endswith("_tests.rs")
    ]


def harness_hashes(kind):
    files = (
        sorted((ROOT / "fuzz").glob("**/*.rs"))
        if kind == "fuzz"
        else sorted(ROOT.glob("crates/*/tests/**/*.rs"))
        + sorted(ROOT.glob("crates/*/src/**/*.rs"))
    )
    files = [p for p in files if "target" not in p.parts]
    if kind == "fuzz":
        files += [ROOT / "fuzz/Cargo.toml", ROOT / "fuzz/Cargo.lock"]
    return {
        p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in files
    }


def source_identity():
    # Source assets such as include_str!("defaults.toml") affect the shipped binary too.
    assets = [p for p in ROOT.glob("crates/*/src/**/*") if p.is_file() and p.suffix != ".rs"]
    files = production_files() + sorted(assets) + sorted((ROOT / "formal").glob("**/*.lean"))
    files = [p for p in files if ".lake" not in p.parts]
    files += sorted(ROOT.glob("crates/*/Cargo.toml"))
    files += sorted(ROOT.glob("crates/*/build.rs"))
    files += [
        p
        for p in (
            ROOT / ".cargo/config.toml",
            ROOT / "formal/lakefile.toml",
            ROOT / "formal/lake-manifest.json",
        )
        if p.exists()
    ]
    files += [
        ROOT / name for name in ("Cargo.toml", "Cargo.lock", "formal/lean-toolchain")
    ]
    hashes = {
        p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in files
    }
    digest = hashlib.sha256(json.dumps(hashes, sort_keys=True).encode()).hexdigest()
    revision = subprocess.check_output(
        [
            "jj",
            "log",
            "-r",
            "@",
            "--no-graph",
            "-T",
            "commit_id",
        ],
        cwd=ROOT,
        text=True,
    ).strip()
    return {"sourceDigest": digest, "sourceRevision": revision, "sourceHashes": hashes}


def run(command, *, cwd=ROOT, env=None, log=None, check=True):
    if log:
        Path(log).parent.mkdir(parents=True, exist_ok=True)
        with Path(log).open("w") as output:
            return subprocess.run(
                command,
                cwd=cwd,
                env=env,
                stdout=output,
                stderr=subprocess.STDOUT,
                check=check,
            )
    return subprocess.run(command, cwd=cwd, env=env, check=check)


def llvm_tools(toolchain="stable"):
    rustc = Path(
        subprocess.check_output(
            ["rustup", "which", "--toolchain", toolchain, "rustc"], text=True
        ).strip()
    )
    version = subprocess.check_output([str(rustc), "-Vv"], text=True)
    host = next(
        s.split(": ", 1)[1] for s in version.splitlines() if s.startswith("host:")
    )
    directory = rustc.parent.parent / "lib/rustlib" / host / "bin"
    for name in ("llvm-cov", "llvm-profdata"):
        if not (directory / name).exists():
            raise RuntimeError(
                f"{name} missing: rustup component add llvm-tools-preview "
                f"--toolchain {toolchain}"
            )
    return directory, version


def export_coverage(directory, objects, profiles, toolchain="stable"):
    llvm, _ = llvm_tools(toolchain)
    profiles = sorted(map(str, profiles))
    if not profiles:
        raise RuntimeError(f"No raw profiles in {directory}")
    merged = Path(directory) / "coverage.profdata"
    merge = subprocess.run(
        [
            str(llvm / "llvm-profdata"),
            "merge",
            "-sparse",
            "--failure-mode=all",
            *profiles,
            "-o",
            str(merged),
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    write_json(
        Path(directory) / "coverage-quality.json",
        {"profiles": len(profiles), "warnings": merge.stderr},
    )
    if merge.returncode:
        raise RuntimeError(merge.stderr)
    command = [
        str(llvm / "llvm-cov"),
        "export",
        "-format=lcov",
        "-skip-functions",
        "-skip-branches",
        "-skip-expansions",
        "-instr-profile=" + str(merged),
        str(objects[0]),
    ]
    for obj in objects[1:]:
        command += ["-object", str(obj)]
    result = subprocess.run(command, text=True, capture_output=True, check=True)
    if result.stderr:
        (Path(directory) / "llvm-warnings.txt").write_text(result.stderr)
    allowed = {p.relative_to(ROOT).as_posix(): p for p in production_files()}
    excluded = {}
    for name, path in allowed.items():
        text = path.read_text()
        excluded[name] = {
            line
            for a, b, _ in source.gated_items(text)
            for line in range(text.count("\n", 0, a) + 1, text.count("\n", 0, b) + 2)
        }
    counts, current = {}, None
    for line in result.stdout.splitlines():
        if line.startswith("SF:"):
            try:
                current = Path(line[3:]).relative_to(ROOT).as_posix()
            except ValueError:
                # Saved binaries may refer to the checkout where the capture was made.
                current = next(
                    (
                        name
                        for name in allowed
                        if line[3:] == name or line[3:].endswith("/" + name)
                    ),
                    None,
                )
            if current not in allowed:
                current = None
        elif current and line.startswith("DA:"):
            number, count = map(int, line[3:].split(",")[:2])
            if number not in excluded[current]:
                values = counts.setdefault(current, {})
                values[number] = max(values.get(number, 0), count)
    compact = {
        f: {"all": sorted(lines), "hit": sorted(n for n, c in lines.items() if c)}
        for f, lines in sorted(counts.items())
    }
    write_json(Path(directory) / "lines.json", compact)
    return compact
