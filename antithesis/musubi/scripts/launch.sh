#!/usr/bin/env bash
# Builds, validates and launches the workload on Antithesis for HOURS compute hours (at least
# 12 on the standard tier). Check the task's compute budget before each launch.
#
#   scripts/launch.sh HOURS [DESCRIPTION]
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
hours=${1:?compute hours}
description=${2:-musubi workload}
"$here/build.sh"
config="$here/../config"
snouty validate "$config"
# The working copy is what was built: name its commit, which jj rewrites as it changes, and
# the newest pushed commit below it, which others can find.
jj=(jj --repository "$here/../../.." log --no-graph -T 'commit_id.short()')
commit=$("${jj[@]}" -r @ 2>/dev/null || echo unknown)
base=$("${jj[@]}" -r 'heads(::@ & ::remote_bookmarks())' 2>/dev/null || echo unknown)
snouty launch --launcher basic_test --config "$config" \
    --test-name musubi --description "$description" \
    --max-compute-hours "$hours" \
    --fault-tolerance high_availability \
    --fault-exclusions '^driver$' \
    --param attrs.workload=musubi \
    --param attrs.sut_commit="$commit" \
    --param attrs.sut_base="$base" \
    --param attrs.plugin_version=0.2.1
