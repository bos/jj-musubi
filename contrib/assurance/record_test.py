#!/usr/bin/env python3
"""Associate one nextest attempt, child processes and oracle use with its profiles."""

import fcntl
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

identity = os.environ["NEXTEST_BINARY_ID"] + "::" + os.environ["NEXTEST_TEST_NAME"]
folder = (
    Path(os.environ["ASSURANCE_RUN"])
    / "tests"
    / hashlib.sha256(identity.encode()).hexdigest()[:20]
)
folder.mkdir(parents=True, exist_ok=False)
env = dict(
    os.environ,
    LLVM_PROFILE_FILE=str(folder / "%m-%p.profraw"),
    ASSURANCE_TEST_DIR=str(folder),
    MUSUBI_ORACLE=str(Path(__file__).with_name("oracle.py")),
)
objects = []
commands = [Path(sys.argv[1])]
if os.environ["NEXTEST_BINARY_ID"].startswith("jj-musubi::"):
    commands.append(Path(os.environ["ASSURANCE_APP_BINARY"]))
store = Path(os.environ["ASSURANCE_RUN"]) / "objects"
store.mkdir(exist_ok=True)
for binary in commands:
    destination = store / hashlib.sha256(str(binary).encode()).hexdigest()[:20]
    with (store / (destination.name + ".lock")).open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if not destination.exists():
            shutil.copy2(binary, destination)
    objects.append(
        destination.relative_to(Path(os.environ["ASSURANCE_RUN"])).as_posix()
    )
started = time.time()
result = subprocess.run(sys.argv[1:], env=env, check=False)
record = {
    "id": identity,
    "objects": objects,
    "binary": os.environ["NEXTEST_BINARY_ID"],
    "name": os.environ["NEXTEST_TEST_NAME"],
    "command": sys.argv[1:],
    "started": started,
    "ended": time.time(),
    "exitCode": result.returncode,
    "attempt": os.environ.get("NEXTEST_ATTEMPT"),
    "runId": os.environ["NEXTEST_RUN_ID"],
}
(folder / "test.json").write_text(json.dumps(record, sort_keys=True))
sys.exit(result.returncode)
