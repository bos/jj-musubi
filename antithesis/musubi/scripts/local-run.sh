#!/usr/bin/env bash
# The local loop: runs the workload with coverage builds of musubi, for SECONDS (default 300)
# after setup completes, and saves logs, SDK output and coverage under OUT (default a new
# directory in /tmp). With EVENTUALLY_AFTER=<seconds>, the driver runs its eventually then,
# and exits.
#
#   scripts/build.sh --coverage && scripts/local-run.sh [SECONDS]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
seconds=${1:-300}
out=${OUT:-$(mktemp -d /tmp/musubi-local.XXXXXX)}
mkdir -p "$out"
cd "$here/../config"
export COMPOSE_FILE="docker-compose.yaml:$here/docker-compose.coverage.yaml"
export COMPOSE_PROJECT_NAME=musubi-local
export DRIVER_EVENTUALLY_AFTER=${EVENTUALLY_AFTER:-}
docker compose down -v --remove-orphans >/dev/null 2>&1 || true
# The containers have fixed names: remove them however this ends, so that a validation or
# another run can start. The coverage volume goes with them, once read.
trap 'docker compose down -v >/dev/null 2>&1 || true' EXIT
docker compose up -d
docker compose exec -T driver /opt/antithesis/test/v1/main/first_start_workload
echo "waiting for setup complete"
timeout 600 sh -c 'until docker compose exec -T driver grep -qs antithesis_setup /tmp/sdk.jsonl; do sleep 5; done' \
    || { docker compose logs driver | tail -40; exit 1; }
echo "setup complete; running for ${seconds}s"
sleep "$seconds"
docker compose ps -a > "$out/ps.txt"
for tool in "jq --version" "jj --version" "musubi --version" "git --version" "curl --version"; do
    docker compose exec -T m1 $tool >/dev/null 2>&1 && echo "ok: $tool" || echo "MISSING: $tool"
done > "$out/tools.txt"
docker compose cp driver:/tmp/sdk.jsonl "$out/sdk.jsonl"
for s in hub m1 m2 m3; do
    docker compose cp "$s:/coverage/$s/sdk.jsonl" "$out/sdk-$s.jsonl" 2>/dev/null || true
done
docker compose logs --no-color > "$out/logs.txt"
docker compose stop -t 30
# Coverage: merge every service's profiles, and report on musubi's own source. build.sh
# --coverage checks that musubi-coverage-tools's /out/musubi is the binary that ran.
docker run --rm -v musubi-local_coverage:/coverage -v "$out":/results musubi-coverage-tools:latest sh -c '
    set -e
    bin=$(rustc --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin
    find /coverage -name "*.profraw" > /tmp/profiles
    "$bin/llvm-profdata" merge -sparse -f /tmp/profiles -o /results/musubi.profdata
    ignore="(cargo/registry|/rustc/)"
    "$bin/llvm-cov" report /out/musubi -instr-profile=/results/musubi.profdata \
        -ignore-filename-regex="$ignore" > /results/coverage.txt
    "$bin/llvm-cov" report /out/musubi -instr-profile=/results/musubi.profdata \
        -ignore-filename-regex="$ignore" -show-functions /src/crates > /results/functions.txt
'
# Assertions that would fail in a run.
jq -rs '[.[].antithesis_assert // empty] | group_by(.message)[]
  | select(if .[0].assert_type == "sometimes" then any(.hit and .condition) | not
           else any(.hit and (.condition | not)) or (.[0].must_hit and (any(.hit) | not)) end)
  | "\(.[0].display_type)\t\(.[0].message)"' "$out"/sdk*.jsonl > "$out/failing.txt"
echo "results in $out:"
cat "$out/tools.txt" "$out/failing.txt"
tail -3 "$out/coverage.txt" || true
