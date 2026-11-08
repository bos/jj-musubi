"""Collectors keep commands, source identities, raw profiles and normalized observations."""

import json
import os
import platform
import re
import subprocess
import time
from pathlib import Path

import tomllib
from common import (
    HERE,
    ROOT,
    export_coverage,
    harness_hashes,
    llvm_tools,
    run,
    source_identity,
    write_json,
)


def manifest(directory, kind, settings):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    if (directory / "manifest.json").exists():
        raise ValueError(f"{directory} already contains a run; choose a new directory")
    value = dict(
        schema=1,
        sourceIdentityVersion=2,
        kind=kind,
        platform=platform.platform(),
        started=time.time(),
        settings=settings,
        python=platform.python_version(),
        harnessHashes=harness_hashes(kind),
        **source_identity(),
    )
    write_json(directory / "manifest.json", value)
    return directory, value


def test_config(config, profile):
    # Coverage and its per-process profile writes slow the native campaigns considerably.
    config = re.sub(
        r'(\bperiod\s*=\s*")(\d+)(s")',
        lambda m: m[1] + str(int(m[2]) * 4) + m[3],
        config,
    )
    experimental = tomllib.loads(config).get("experimental", [])
    experimental = sorted(set(experimental) | {"wrapper-scripts"})
    config = re.sub(r"^experimental\s*=.*\n", "", config, flags=re.MULTILINE)
    config = "experimental = " + json.dumps(experimental) + "\n" + config
    config += (
        "\n[scripts.wrapper.assurance-record]\ncommand = "
        + json.dumps(["python3", str(HERE / "record_test.py")])
        + "\n"
    )
    config += f"\n[[profile.{profile}.scripts]]\nfilter = 'all()'\nrun-wrapper = 'assurance-record'\n"
    return config


def tests(directory, seed=42, jobs=4, profile="default", cases=50, toolchain="stable"):
    directory, record = manifest(
        directory,
        "tests",
        {
            "seed": seed,
            "jobs": jobs,
            "profile": profile,
            "cases": cases,
            "toolchain": toolchain,
        },
    )
    target = json.loads(
        subprocess.check_output(
            [
                "cargo",
                "+" + toolchain,
                "metadata",
                "--no-deps",
                "--format-version",
                "1",
            ],
            cwd=ROOT,
            text=True,
        )
    )["target_directory"]
    env = dict(
        os.environ,
        ASSURANCE_RUN=str(directory),
        ASSURANCE_APP_BINARY=str(Path(target) / "debug/musubi"),
        ASSURANCE_REAL_ORACLE=str(ROOT / "formal/.lake/build/bin/oracle"),
        MUSUBI_CONFORMANCE_CASES=str(cases),
        RUSTC_WORKSPACE_WRAPPER=str(HERE / "instrument.py"),
        LLVM_PROFILE_FILE=str(directory / "list-%m-%p.profraw"),
        HEGEL_SEED=str(seed),
        HEGEL_DATABASE="disabled",
        CARGO_BUILD_JOBS=str(jobs),
    )
    run(["lake", "build"], cwd=ROOT / "formal", log=directory / "oracle-build.log")
    config = test_config((ROOT / ".config/nextest.toml").read_text(), profile)
    cfg = directory / "nextest.toml"
    cfg.write_text(config)
    command = [
        "cargo",
        "+" + toolchain,
        "nextest",
        "run",
        "--workspace",
        "--config-file",
        str(cfg),
        "--test-threads",
        str(jobs),
        "--profile",
        profile,
    ]
    record["commands"] = [command]
    record["rustc"] = llvm_tools(toolchain)[1]
    record["nextest"] = subprocess.check_output(
        ["cargo", "+" + toolchain, "nextest", "--version"], text=True
    ).strip()
    record["lean"] = subprocess.check_output(
        ["lake", "env", "lean", "--version"], cwd=ROOT / "formal", text=True
    ).strip()
    write_json(directory / "manifest.json", record)
    result = run(command, env=env, log=directory / "nextest.log", check=False)
    record.update(executionEnded=time.time(), executionExitCode=result.returncode)
    write_json(directory / "manifest.json", record)
    if result.returncode:
        raise RuntimeError(f"Tests failed; inspect {directory / 'nextest.log'}")
    export_tests(directory, toolchain)


def export_tests(directory, toolchain="stable"):
    directory = Path(directory).resolve()
    record = json.loads((directory / "manifest.json").read_text())
    if record.get("executionExitCode") != 0:
        raise ValueError("No successful test execution to export")
    if llvm_tools(toolchain)[1] != record["rustc"]:
        raise ValueError(
            "Coverage export needs the exact rustc/LLVM version recorded in manifest.json; select it with --toolchain"
        )
    for p in sorted((directory / "tests").glob("*/test.json")):
        if (p.parent / "lines.json").exists():
            continue
        value = json.loads(p.read_text())
        export_coverage(
            p.parent,
            [
                (directory / p)
                if not Path(p).is_absolute()
                else (
                    Path(p)
                    if Path(p).exists()
                    else directory / "objects" / Path(p).name
                )
                for p in value["objects"]
            ],
            p.parent.glob("*.profraw"),
            toolchain,
        )
    record.update(ended=time.time(), exitCode=0)
    write_json(directory / "manifest.json", record)


def fuzz(directory, toolchain="nightly", seconds=60, checkpoints=4, seed=42, jobs=4):
    directory, record = manifest(
        directory,
        "fuzz",
        {
            "toolchain": toolchain,
            "seconds": seconds,
            "checkpoints": checkpoints,
            "seed": seed,
            "jobs": jobs,
        },
    )
    _llvm, record["rustc"] = llvm_tools(toolchain)
    record["cargoFuzz"] = subprocess.check_output(
        ["cargo", "fuzz", "--version"], text=True
    ).strip()
    write_json(directory / "manifest.json", record)
    targets = sorted(
        b["name"] for b in tomllib.loads((ROOT / "fuzz/Cargo.toml").read_text())["bin"]
    )
    env = dict(
        os.environ,
        RUSTC_WRAPPER=str(HERE / "instrument.py"),
        CARGO_BUILD_JOBS=str(jobs),
    )
    build = directory / "build"
    prefix = ["cargo", "+" + toolchain, "fuzz"]
    commands = []
    for target in targets:
        corpus = directory / target / "corpus"
        corpus.mkdir(parents=True)
        for step in range(checkpoints):
            folder = directory / target / f"checkpoint-{step:03}"
            folder.mkdir()
            seconds_here = seconds // checkpoints + (step < seconds % checkpoints)
            command = prefix + [
                "run",
                "--dev",
                "--sanitizer",
                "none",
                "--target-dir",
                str(build),
                target,
                str(corpus),
                "--",
                f"-seed={seed + step}",
                f"-max_total_time={seconds_here}",
                "-timeout=10",
                "-artifact_prefix=" + str(folder) + "/",
            ]
            event = {
                "id": f"fuzz::{target}::{step}",
                "target": target,
                "checkpoint": step,
                "command": command,
                "seed": seed + step,
            }
            started = time.time()
            result = run(
                command,
                env=dict(env, LLVM_PROFILE_FILE=str(folder / "%m-%p.profraw")),
                log=folder / "fuzz.log",
                check=False,
            )
            event.update(
                started=started,
                ended=time.time(),
                exitCode=result.returncode,
                corpusFiles=len(list(corpus.iterdir())),
            )
            write_json(folder / "test.json", event)
            # Cargo-fuzz uses its explicit --target, even on the host. Discover the host
            # from rustc so captures remain portable across macOS and Linux.
            host = next(
                s.split(": ", 1)[1]
                for s in record["rustc"].splitlines()
                if s.startswith("host:")
            )
            binary = build / host / "debug" / target
            event["binary"] = str(binary)
            if list(folder.glob("*.profraw")):
                export_coverage(folder, [binary], folder.glob("*.profraw"), toolchain)
            write_json(folder / "test.json", event)
            commands.append(command)
            record["commands"] = commands
            write_json(directory / "manifest.json", record)
            if result.returncode:
                raise RuntimeError(f"Fuzzer failed: {folder / 'fuzz.log'}")
    record.update(ended=time.time(), exitCode=0)
    write_json(directory / "manifest.json", record)


def mutation(directory, jobs=4, toolchain="stable", shard=None):
    """The mutation campaign, or with `shard` as (k, n), its kth of n shards (numbered from
    0), which other machines can run at the same time: `build` takes every shard together."""
    settings = {
        "jobs": jobs,
        "cases": 150,
        "seed": 42,
        "database": "disabled",
        "toolchain": toolchain,
    }
    if shard:
        settings["shard"] = f"{shard[0]}/{shard[1]}"
    directory, record = manifest(directory, "mutation", settings)
    campaign = [
        "cargo",
        "+" + toolchain,
        "mutants",
        "--package",
        "musubi-core",
        "--file",
        "crates/musubi-core/src/hub.rs",
        "--file",
        "crates/musubi-core/src/node.rs",
        "--test-tool",
        "nextest",
        "--timeout",
        "600",
        "--jobs",
        str(jobs),
        "--jobserver-tasks",
        str(jobs + 2),
        "--no-shuffle",
        "--output",
        str(directory),
    ]
    # Round-robin, so that each shard takes mutants from every file, and they finish together.
    command = campaign + (
        ["--shard", settings["shard"], "--sharding", "round-robin"] if shard else []
    )
    env = dict(
        os.environ,
        MUSUBI_ORACLE=str(ROOT / "formal/.lake/build/bin/oracle"),
        MUSUBI_CONFORMANCE_CASES="150",
        HEGEL_SEED="42",
        HEGEL_DATABASE="disabled",
    )
    run(
        ["lake", "build", "oracle"],
        cwd=ROOT / "formal",
        log=directory / "oracle-build.log",
    )
    record["commands"] = [command]
    record["cargoMutants"] = subprocess.check_output(
        ["cargo", "+" + toolchain, "mutants", "--version"], text=True
    ).strip()
    record["rustc"] = llvm_tools(toolchain)[1]
    record["nextest"] = subprocess.check_output(
        ["cargo", "+" + toolchain, "nextest", "--version"], text=True
    ).strip()
    record["lean"] = subprocess.check_output(
        ["lake", "env", "lean", "--version"], cwd=ROOT / "formal", text=True
    ).strip()
    # The whole campaign's plan, which the shards together must cover, and this run's part.
    plan = json.loads(
        subprocess.check_output(
            campaign + ["--list", "--json"], env=env, cwd=ROOT, text=True
        )
    )
    write_json(directory / "mutation-plan.json", plan)
    if shard:
        plan = json.loads(
            subprocess.check_output(
                command + ["--list", "--json"], env=env, cwd=ROOT, text=True
            )
        )
        if not plan:
            raise ValueError(
                f"Shard {settings['shard']} has no mutants: split the campaign into fewer shards"
            )
    write_json(directory / "manifest.json", record)
    result = run(command, env=env, log=directory / "mutation.log", check=False)
    record.update(ended=time.time(), exitCode=result.returncode)
    write_json(directory / "manifest.json", record)
    outcomes = json.loads((directory / "mutants.out/outcomes.json").read_text())
    if outcomes.get("end_time") is None or outcomes.get("total_mutants") != len(plan):
        raise RuntimeError(f"Mutation run incomplete: {directory / 'mutation.log'}")
