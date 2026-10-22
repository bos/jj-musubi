#!/bin/sh
# Replays test/smoke.jsonl through the oracle and compares with test/smoke.expected.
set -e
cd "$(dirname "$0")/.."
lake build oracle >/dev/null
.lake/build/bin/oracle < test/smoke.jsonl | diff - test/smoke.expected
echo "smoke test passed"
