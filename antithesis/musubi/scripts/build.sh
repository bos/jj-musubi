#!/usr/bin/env bash
# Builds the workload's images, musubi-node and musubi-driver, and with --coverage also the
# local loop's musubi-node-coverage and musubi-coverage-tools.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
dockerfile="$here/../image/Dockerfile"
# The jj the machines run must be the release musubi builds against.
lib=$(sed -n 's/^jj-lib = { version = "=\([^"]*\)".*/\1/p' "$root/Cargo.toml")
if ! grep -q "download/v$lib/" "$dockerfile"; then
    echo "image/Dockerfile downloads another jj than jj-lib $lib: update its URL and sha256" >&2
    exit 1
fi
# BuildKit compiles musubi, the driver and OpenSSH at once: give each a third of the machine,
# or JOBS each (AGENTS.md, "Checks").
jobs=${JOBS:-$(( $(nproc) / 3 > 0 ? $(nproc) / 3 : 1 ))}
cd "$here/../config"
docker compose build --build-arg JOBS="$jobs"
images=(musubi-node:latest musubi-driver:latest)
if [[ ${1:-} == --coverage ]]; then
    docker build -q --build-arg JOBS="$jobs" --target node-coverage \
        -t musubi-node-coverage:latest -f "$dockerfile" "$root"
    docker build -q --build-arg JOBS="$jobs" --target coverage-tools \
        -t musubi-coverage-tools:latest -f "$dockerfile" "$root"
    images+=(musubi-node-coverage:latest)
    # The coverage report reads the tools image's binary against profiles from the node
    # image's: they must be the same build, which only BuildKit's cache makes them.
    sum() { docker run --rm --entrypoint sha256sum "$1" "$2" | cut -d' ' -f1; }
    if [[ $(sum musubi-node-coverage:latest /usr/local/bin/musubi) \
        != $(sum musubi-coverage-tools:latest /out/musubi) ]]; then
        echo "musubi-node-coverage and musubi-coverage-tools have different musubi builds" >&2
        exit 1
    fi
fi
# Every image copies the ssh keys from the Dockerfile's `keys` stage, which BuildKit builds
# once and caches: check that they all got the same.
keys() { docker run --rm --entrypoint cat "$1" /root/.ssh/authorized_keys | sha256sum; }
first=$(keys "${images[0]}")
for image in "${images[@]:1}"; do
    if [[ $(keys "$image") != "$first" ]]; then
        echo "$image has other ssh keys than ${images[0]}: clear the build cache and build again" >&2
        exit 1
    fi
done
echo "built ${images[*]}"
