#!/usr/bin/env python3
"""Build the Lean oracle under the lock shared with standalone Rust tests."""

import argparse
import errno
import os
from pathlib import Path
import subprocess
import sys
import time


FORMAL = Path(__file__).resolve().parent.parent / "formal"


def lock_oracle(handle):
    """Match Rust File::lock: flock on Unix, an overlapping byte range on Windows."""
    if os.name == "nt":
        import msvcrt

        # Locking beyond EOF is allowed. The first byte overlaps Rust's whole-file lock,
        # including when its lock file is empty; no write is needed before obtaining it.
        handle.seek(0)
        while True:
            try:
                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                return
            except OSError as error:
                if error.errno not in (errno.EACCES, errno.EAGAIN, errno.EDEADLK):
                    raise
                time.sleep(0.05)
    else:
        import fcntl

        fcntl.flock(handle.fileno(), fcntl.LOCK_EX)


def build(full):
    lake = FORMAL / ".lake"
    lake.mkdir(parents=True, exist_ok=True)
    # Closing releases the lock, including on a failed build, smoke check, or interruption.
    with (lake / "oracle-build.lock").open("a+b") as lock:
        lock_oracle(lock)
        subprocess.run(
            ["lake", "build", *([] if full else ["oracle"])], cwd=FORMAL, check=True
        )
        if full:
            # Keep the existing smoke script as the single owner of its input and comparison.
            subprocess.run(["sh", "test/run_smoke.sh"], cwd=FORMAL, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--full", action="store_true", help="check all proofs and smoke examples too"
    )
    args = parser.parse_args()
    try:
        build(args.full)
    except subprocess.CalledProcessError as error:
        return error.returncode if error.returncode >= 0 else 128 - error.returncode
    except OSError as error:
        print(f"build-oracle: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        return 130
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
