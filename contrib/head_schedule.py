#!/usr/bin/env python3
"""Search and replay operation-head schedules on Linux."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TEST = "head_schedule::run"


def test_binary():
    build = subprocess.Popen(
        [
            "cargo", "test", "--locked", "-p", "musubi-jj", "--test", "it",
            "--no-run", "--message-format=json-render-diagnostics",
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        text=True,
    )
    executables = []
    with build.stdout as output:
        for line in output:
            message = json.loads(line)
            if (
                message.get("reason") == "compiler-artifact"
                and message["target"]["name"] == "it"
                and message["target"]["kind"] == ["test"]
            ):
                executables.append(message["executable"])
    if build.wait():
        sys.exit(build.returncode)
    if len(executables) != 1 or not executables[0]:
        sys.exit("Cargo did not report the musubi-jj integration test executable")
    return [executables[0], TEST, "--exact", "--ignored", "--nocapture"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest="mode", required=True)
    search = modes.add_parser("search", help="explore schedules from the initial repository")
    search.add_argument("--unpublished", action="store_true", help="start with unpublished work")
    search.add_argument(
        "--concurrent", action="store_true",
        help="race a second native command: an abandon, or what --peer says",
    )
    search.add_argument(
        "--peer", choices=["abandon", "write"], default="abandon",
        help="with --concurrent, what the second command does (default abandon)",
    )
    search.add_argument("--out", type=Path, default=ROOT / "target/head-schedule.json")
    replay = modes.add_parser("replay", help="replay a saved schedule and verify its states")
    replay.add_argument("input", type=Path)
    replay.add_argument(
        "--actions-only", action="store_true",
        help="run the same actions after a code change without comparing saved states",
    )
    replay.add_argument("--rr", type=Path, metavar="DIRECTORY", help="record replay with rr")
    replay.add_argument(
        "--rr-as-root", action="store_true",
        help="use sudo for rr and run its tracee under your original UID and GID",
    )
    branch = modes.add_parser("branch", help="replay a prefix and explore other next actions")
    branch.add_argument("input", type=Path)
    branch.add_argument("--at", type=int, required=True, help="number of actions to keep")
    branch.add_argument("--out", type=Path, default=ROOT / "target/head-schedule-branch.json")
    for mode in (search, replay, branch):
        mode.add_argument(
            "--steps", type=int, metavar="N",
            help="the most actions a schedule may take (default 8, or 14 with --concurrent)",
        )
    args = parser.parse_args()

    if sys.platform != "linux":
        parser.error("the operation-head scheduler runs on Linux")
    if not shutil.which("cc"):
        parser.error("a C compiler named cc is required")
    if args.mode == "branch" and args.at < 0:
        parser.error("--at must be nonnegative")
    if getattr(args, "peer", "abandon") != "abandon" and not args.concurrent:
        parser.error("--peer requires --concurrent")
    if args.steps is not None and args.steps < 1:
        parser.error("--steps must be positive")
    rr = getattr(args, "rr", None)
    if getattr(args, "rr_as_root", False) and not rr:
        parser.error("--rr-as-root requires --rr DIRECTORY")
    recorder = shutil.which("rr") if rr else None
    if getattr(args, "rr_as_root", False):
        recorder = "/usr/bin/rr" if Path("/usr/bin/rr").is_file() else None
    if rr and not recorder:
        parser.error("rr is required to record a replay")

    settings = {"MUSUBI_HEAD_SCHEDULE_MODE": args.mode}
    if args.mode != "search":
        settings["MUSUBI_HEAD_SCHEDULE_INPUT"] = str(args.input.resolve(strict=True))
    if args.mode != "replay":
        target = args.out.resolve()
        if getattr(args, "input", None) and target == args.input.resolve():
            parser.error("the branch output must differ from its input")
        target.parent.mkdir(parents=True, exist_ok=True)
        settings["MUSUBI_HEAD_SCHEDULE_OUTPUT"] = str(target)
    if args.mode == "branch":
        settings["MUSUBI_HEAD_SCHEDULE_AT"] = str(args.at)
    if getattr(args, "unpublished", False):
        settings["MUSUBI_HEAD_SCHEDULE_UNPUBLISHED"] = "1"
    if getattr(args, "concurrent", False):
        settings["MUSUBI_HEAD_SCHEDULE_CONCURRENT"] = "1"
        settings["MUSUBI_HEAD_SCHEDULE_PEER"] = args.peer
    if args.steps is not None:
        settings["MUSUBI_HEAD_SCHEDULE_STEPS"] = str(args.steps)
    if getattr(args, "actions_only", False):
        settings["MUSUBI_HEAD_SCHEDULE_ACTIONS_ONLY"] = "1"

    command = test_binary()
    if rr:
        destination = rr.resolve()
        if destination.exists():
            parser.error(f"rr trace destination already exists: {destination}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        record = [recorder, "record", "-n", "-o", str(destination)]
        if args.rr_as_root:
            # The recorder needs perf access on some hosts. Drop privileges before passing
            # caller-selected programs or environment into the recorded test.
            invoke = [
                "sudo", "--", *record, "/usr/bin/setpriv",
                f"--reuid={os.getuid()}", f"--regid={os.getgid()}", "--init-groups",
                "/usr/bin/env", f"PATH={os.environ['PATH']}", f"HOME={Path.home()}",
                *(f"{name}={value}" for name, value in settings.items()),
            ]
            return subprocess.call([*invoke, *command], cwd=ROOT)
        command = [*record, *command]

    env = {key: value for key, value in os.environ.items()
           if not key.startswith("MUSUBI_HEAD_SCHEDULE_")}
    env.update(settings)
    return subprocess.call(command, cwd=ROOT, env=env)


if __name__ == "__main__":
    sys.exit(main())
