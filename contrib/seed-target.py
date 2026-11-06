#!/usr/bin/env python3
"""Seed an independent Cargo target directory before building a new workspace."""

import argparse
from contextlib import ExitStack
import fcntl
import os
from pathlib import Path
import shutil
import subprocess
import sys


# Cargo renamed its profile locks in 1.98. Lock both generations: the old file
# remains on disk, but locking only it no longer excludes a build.
LOCK_NAMES = (".cargo-lock", ".cargo-build-lock", ".cargo-artifact-lock")
NO_HARDLINKS = str(2**64 - 1)


def seed(source: Path, destination: Path) -> None:
    source = source.resolve(strict=True)
    if os.path.lexists(destination):
        raise ValueError(f"already exists: {destination}")
    destination = destination.resolve()
    staging = destination.with_name(destination.name + ".partial")
    if not source.is_dir():
        raise ValueError(f"source is not a directory: {source}")
    for path in (destination, staging):
        if path.is_relative_to(source) or source.is_relative_to(path):
            raise ValueError(f"source and destination must be separate trees: {path}")
        if os.path.lexists(path):
            raise ValueError(f"already exists: {path}")
    # Profile locks occur directly under target/ or below a target triple.
    locks = sorted(
        path
        for pattern in ("*", "*/*")
        for profile in source.glob(pattern)
        if profile.is_dir() and not profile.is_symlink()
        for name in LOCK_NAMES
        if (path := profile / name).is_file()
    )
    if not locks:
        raise ValueError(f"no Cargo profile locks in {source}; build the source workspace first")

    with ExitStack() as stack:
        for path in locks:
            handle = stack.enter_context(path.open("rb"))
            try:
                fcntl.flock(handle, fcntl.LOCK_SH | fcntl.LOCK_NB)
            except BlockingIOError:
                raise ValueError(f"{source} is locked by a build; seed between builds") from None

        # Relative links within the tree remain independent after copying.
        # Absolute links, including ones into source, keep the old location.
        for root, dirs, files in os.walk(source):
            for name in dirs + files:
                path = Path(root) / name
                if path.is_symlink() and (
                    Path(os.readlink(path)).is_absolute()
                    or not path.resolve().is_relative_to(source)
                ):
                    raise ValueError(f"symlink depends on a path outside the copied tree: {path}")

        destination.parent.mkdir(parents=True, exist_ok=True)
        # Do not share inodes even for hashed deps/ artifacts: rustc can
        # overwrite explicit outputs in place. Reflinks still work normally.
        result = subprocess.run(
            [
                "cargo",
                "shared-target",
                "--src",
                str(source),
                "--dest",
                str(destination),
                "--min-shared-size",
                NO_HARDLINKS,
            ],
            capture_output=True,
            text=True,
        )
        # Btrfs can clone across subvolumes with different device numbers.
        # Ask the tool first; copy across devices only if it failed before
        # creating any staged output. Never hide a partially completed run.
        if (
            result.returncode
            and source.stat().st_dev != destination.parent.stat().st_dev
            and not os.path.lexists(staging)
            and not os.path.lexists(destination)
        ):
            shutil.copytree(source, staging, symlinks=True)
            staging.rename(destination)
            print(f"seeded {destination} by copying files")
            return
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        result.check_returncode()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="existing target directory, idle while seeding")
    parser.add_argument("destination", type=Path, help="new target directory; must not exist")
    args = parser.parse_args()
    try:
        seed(args.source, args.destination)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
