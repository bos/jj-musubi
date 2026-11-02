#!/usr/bin/env python3
"""Collect and render the code assurance network without chat-local files."""

import argparse
import sys
from pathlib import Path

import collect


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("tests", "fuzz", "mutation"):
        p = sub.add_parser(name, help=f"Collect {name} observations")
        p.add_argument("--out", type=Path, required=True, help="New capture directory")
        p.add_argument("--jobs", type=int, default=4)
        p.add_argument("--toolchain", default="nightly" if name == "fuzz" else "stable")
        if name in ("tests", "fuzz"):
            p.add_argument("--seed", type=int, default=42)
        if name == "tests":
            p.add_argument(
                "--cases", type=int, default=50, help="Conformance cases per test"
            )
            p.add_argument(
                "--profile", default="default", choices=["default", "ci", "search"]
            )
        if name == "fuzz":
            p.add_argument("--seconds", type=int, default=60, help="Seconds per target")
            p.add_argument("--checkpoints", type=int, default=4)
    p = sub.add_parser(
        "export", help="Resume coverage export after a successful test run"
    )
    p.add_argument("--run", type=Path, required=True)
    p.add_argument(
        "--toolchain", default="stable", help="Toolchain matching the capture compiler"
    )
    p = sub.add_parser(
        "build", help="Build the source graph and join completed captures"
    )
    p.add_argument("--run", action="append", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--seed", type=int, default=9)
    p = sub.add_parser(
        "render", help="Render a frozen dataset without running any tests"
    )
    p.add_argument("dataset", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--standalone", action="store_true")
    args = vars(parser.parse_args())
    name = args.pop("command")
    if name in ("tests", "fuzz", "mutation", "export") and sys.platform not in (
        "darwin", "linux"
    ):
        parser.error("Assurance collection and coverage export require macOS or Linux")
    if name == "export":
        collect.export_tests(args["run"], args["toolchain"])
    elif name == "build":
        import build

        build.build(args["run"], args["out"], args["seed"])
    elif name == "render":
        import render

        render.render(args["dataset"], args["out"], args["standalone"])
    else:
        if (
            args["jobs"] <= 0
            or args.get("checkpoints", 1) <= 0
            or args.get("seconds", 1) <= 0
            or args.get("cases", 1) <= 0
        ):
            parser.error("jobs, cases, checkpoints and seconds must be positive")
        if name == "fuzz" and args["checkpoints"] > args["seconds"]:
            parser.error("fuzz checkpoints cannot exceed the seconds budget")
        args["directory"] = args.pop("out")
        getattr(collect, name)(**args)


if __name__ == "__main__":
    main()
