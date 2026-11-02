#!/usr/bin/env python3
"""Relay the real oracle unchanged, recording which model requests a Rust test makes."""

import json
import os
import re
import subprocess
import sys
from pathlib import Path

folder = Path(os.environ["ASSURANCE_TEST_DIR"]) / "oracle-ops"
folder.mkdir(exist_ok=True)
child = subprocess.Popen([os.environ["ASSURANCE_REAL_ORACLE"]], stdin=subprocess.PIPE)
seen = set()
try:
    for line in sys.stdin.buffer:
        request = json.loads(line)
        op = request.get("op", "unknown")
        if not isinstance(op, str) or not re.fullmatch(r"[a-zA-Z0-9_]+", op):
            raise ValueError("Unexpected oracle operation")
        if op not in seen:
            (folder / op).touch()
            seen.add(op)
        child.stdin.write(line)
        child.stdin.flush()
finally:
    child.stdin.close()
sys.exit(child.wait())
