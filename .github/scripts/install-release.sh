#!/usr/bin/env bash
# Installs one binary from a GitHub release into a directory on the job's PATH, after checking
# the downloaded archive against a pinned SHA-256. Runs under bash on Linux, macOS and Windows.
#
# Usage: install-release.sh <owner/repo> <tag> <asset> <sha256> <binary>
set -euo pipefail

repo=$1 tag=$2 asset=$3 sha256=$4 binary=$5

# On Windows, Git Bash wants POSIX paths, and PATH wants Windows ones.
unix_path() { if command -v cygpath >/dev/null; then cygpath -u "$1"; else printf '%s\n' "$1"; fi; }
native_path() { if command -v cygpath >/dev/null; then cygpath -w "$1"; else printf '%s\n' "$1"; fi; }

bin="$(unix_path "$RUNNER_TEMP")/bin"
work=$(mktemp -d)
mkdir -p "$bin" "$work/x"

curl --fail --location --silent --show-error --retry 3 \
    --output "$work/$asset" "https://github.com/$repo/releases/download/$tag/$asset"

if command -v sha256sum >/dev/null; then
    actual=$(sha256sum "$work/$asset" | cut -d' ' -f1)
else
    actual=$(shasum -a 256 "$work/$asset" | cut -d' ' -f1)
fi
if [ "$actual" != "$sha256" ]; then
    echo "$asset: expected SHA-256 $sha256, got $actual" >&2
    exit 1
fi

case $asset in
    *.zip) unzip -q "$work/$asset" -d "$work/x" ;;
    *) tar -xzf "$work/$asset" -C "$work/x" ;;
esac
find "$work/x" -type f \( -name "$binary" -o -name "$binary.exe" \) -exec cp {} "$bin" \;
if [ ! -f "$bin/$binary" ] && [ ! -f "$bin/$binary.exe" ]; then
    echo "$asset holds no $binary" >&2
    exit 1
fi
native_path "$bin" >> "$GITHUB_PATH"
