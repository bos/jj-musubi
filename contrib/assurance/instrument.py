#!/usr/bin/env python3
"""Instrument only musubi source, including path dependencies of the fuzz workspace."""

import os
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[2]
args = sys.argv[1:]
if any(
    a.endswith(".rs")
    and (
        Path(a).resolve().is_relative_to(root / "crates")
        or Path(a).resolve().is_relative_to(root / "fuzz")
    )
    for a in args
):
    args += ["-C", "instrument-coverage"]
os.execv(args[0], args)
