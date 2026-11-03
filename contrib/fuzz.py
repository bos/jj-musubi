"""Build fuzz targets once, then run them within a shared process budget."""

import argparse
import asyncio
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent


def available_jobs():
    if hasattr(os, "sched_getaffinity"):
        return len(os.sched_getaffinity(0))
    return getattr(os, "process_cpu_count", os.cpu_count)() or 1


def positive(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be at least 1")
    return number


class Failed(Exception):
    pass


async def execute(command, env, output=None):
    # A separate group lets cancellation stop cargo's rustc children too.
    spawning = asyncio.create_task(asyncio.create_subprocess_exec(
        *command, cwd=ROOT, env=env, stdout=output,
        stderr=subprocess.STDOUT if output is not None else None,
        start_new_session=True,
    ))
    process = None
    try:
        # Keep the handle even if cancellation arrives while the process is being started.
        process = await asyncio.shield(spawning)
        return await process.wait()
    finally:
        if process is None:
            process = await spawning
        if process.returncode is None:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                await asyncio.wait_for(process.wait(), timeout=3)
            except asyncio.TimeoutError:
                pass
        # A child may outlive the group leader, including one that ignores SIGTERM.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        await process.wait()


async def workers(commands, jobs, env, logs):
    slots = asyncio.Semaphore(jobs)
    failed = asyncio.Event()

    async def worker(index, target, command):
        async with slots:
            if failed.is_set():
                return
            log = logs / f"{target}-{index}.log"
            with log.open("wb") as output:
                code = await execute(command, env, output)
            if code:
                failed.set()
                # Keep full output on disk, but bound what an error prints.
                with log.open("rb") as output:
                    output.seek(0, os.SEEK_END)
                    output.seek(max(0, output.tell() - 16000))
                    sys.stderr.write(output.read().decode(errors="replace"))
                raise Failed(f"{target} exited with status {code}; see {log}")

    tasks = [
        asyncio.create_task(worker(index, target, command))
        for index, (target, command) in enumerate(commands)
    ]
    try:
        done, _ = await asyncio.wait(tasks, return_when=asyncio.FIRST_EXCEPTION)
        for task in done:
            task.result()
    finally:
        for task in tasks:
            if not task.done():
                task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)


def plan(targets, jobs, smoke):
    # With fewer cores than targets, bounded runs free slots for the remaining targets.
    count = len(targets) if smoke else max(jobs, len(targets))
    return [targets[index % len(targets)] for index in range(count)]


async def run(options, arguments, env, targets, triple):
    target_dir = ROOT / "fuzz" / "target"
    build = ["cargo", "fuzz", "build", "--target", triple, "--target-dir", str(target_dir)]
    if options.target != "all":
        build.append(options.target)
    if await execute(build, env):
        raise Failed("could not build fuzz targets")

    logs_dir = target_dir / "fuzz-logs"
    logs_dir.mkdir(parents=True, exist_ok=True)
    logs = Path(tempfile.mkdtemp(prefix="run-", dir=logs_dir))
    commands = []
    for target in plan(targets, options.jobs, options.smoke):
        corpus = ROOT / "fuzz" / "corpus" / target
        artifacts = ROOT / "fuzz" / "artifacts" / target
        corpus.mkdir(parents=True, exist_ok=True)
        artifacts.mkdir(parents=True, exist_ok=True)
        commands.append((target, [
            str(target_dir / triple / "release" / target),
            f"-artifact_prefix={artifacts}{os.sep}", *arguments, str(corpus),
        ]))
    print(f"Fuzzing with {min(options.jobs, len(commands))} workers; logs: {logs}",
          file=sys.stderr, flush=True)
    await workers(commands, options.jobs, env, logs)


def main():
    parser = argparse.ArgumentParser(add_help=False, description=__doc__, epilog=(
        "Other arguments are passed to libFuzzer. All targets default to "
        "-max_total_time=300 per worker; one target runs until stopped. "
        "Corpora and crashes are shared per target under fuzz/."
    ))
    parser.add_argument("--help", action="help", help="show this help message and exit")
    parser.add_argument("target", nargs="?", default="all", help="target name (default: all)")
    parser.add_argument("--jobs", type=positive,
                        default=os.environ.get("MUSUBI_FUZZ_JOBS", available_jobs()),
                        help="total workers (default: available CPUs, or MUSUBI_FUZZ_JOBS)")
    parser.add_argument("--smoke", action="store_true", help="run each target for 2000 inputs")
    options, arguments = parser.parse_known_args()
    arguments = [arg for arg in arguments if arg != "--"]
    for arg in arguments:
        if not arg.startswith("-") or arg.split("=", 1)[0] in (
            "-fork", "-jobs", "-workers", "-merge", "-minimize_crash",
        ):
            parser.error("use libFuzzer options without subprocesses; set workers with --jobs")
    if options.smoke:
        arguments.append("-runs=2000")
    elif options.target == "all":
        time_limit = next((arg for arg in reversed(arguments)
                           if arg.startswith("-max_total_time=")), "-max_total_time=300")
        try:
            positive(time_limit.split("=", 1)[1])
        except (ValueError, argparse.ArgumentTypeError):
            parser.error("all-target runs need a positive -max_total_time")
        arguments.append(time_limit)

    env = os.environ.copy()
    rustc = subprocess.check_output(
        ["rustup", "which", "--toolchain", "nightly", "rustc"], text=True,
    ).strip()
    env["PATH"] = str(Path(rustc).parent) + os.pathsep + env["PATH"]
    # Match cargo-fuzz's address-sanitizer runtime setting for the binaries run directly.
    env["ASAN_OPTIONS"] = env.get("ASAN_OPTIONS", "") + ":detect_odr_violation=0"
    targets = subprocess.check_output(["cargo", "fuzz", "list"], cwd=ROOT,
                                      env=env, text=True).split()
    if options.target != "all":
        if options.target not in targets:
            parser.error(f"unknown target {options.target!r}; choose from {', '.join(targets)}")
        targets = [options.target]
    version = subprocess.check_output([rustc, "-vV"], env=env, text=True)
    triple = next(line.removeprefix("host: ") for line in version.splitlines()
                  if line.startswith("host: "))

    interrupted = []

    async def campaign():
        loop = asyncio.get_running_loop()
        task = asyncio.current_task()

        def stop(sig):
            if not interrupted:
                interrupted.append(sig)
                task.cancel()

        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            loop.add_signal_handler(sig, stop, sig)
        await run(options, arguments, env, targets, triple)

    try:
        asyncio.run(campaign())
    except asyncio.CancelledError:
        return 128 + interrupted[0]
    except Failed as error:
        print(f"fuzz: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"fuzz: {error}", file=sys.stderr)
        sys.exit(1)
