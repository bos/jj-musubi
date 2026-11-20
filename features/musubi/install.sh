#!/bin/sh
set -eu

arch=$(uname -m)
case "$arch" in
    x86_64|aarch64) ;;
    *) echo "jj-musubi has no Linux release for $arch" >&2; exit 1 ;;
esac

version=${VERSION:-latest}
releases=https://github.com/bos/jj-musubi/releases
if [ "$version" = latest ]; then
    sums_url=$releases/latest/download/SHA256SUMS
else
    if ! printf '%s\n' "$version" | grep -Eq '^[0-9]+\.[0-9]+\.[0-9]+$'; then
        echo "Expected a jj-musubi release version such as 0.47.1 or latest" >&2
        exit 1
    fi
    sums_url=$releases/download/v$version/SHA256SUMS
fi

if ! command -v curl >/dev/null || ! command -v ssh >/dev/null ||
    [ ! -s /etc/ssl/certs/ca-certificates.crt ]; then
    apt-get update
    DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        ca-certificates curl openssh-client
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cd "$work"

# Follow the latest-release redirect once, then fetch the archive from the same version.
curl -fsSL --retry 3 -o SHA256SUMS "$sums_url"
target=$arch-unknown-linux-musl
if [ "$version" = latest ]; then
    version=$(sed -n "s/^[0-9a-f]*  jj-musubi-\([0-9][0-9.]*\)-$target\.tar\.gz\$/\1/p" \
        SHA256SUMS)
    if [ -z "$version" ]; then
        echo "The latest jj-musubi release contains no archive for $target" >&2
        exit 1
    fi
fi
name=jj-musubi-$version-$target
archive=$name.tar.gz
curl -fsSL --retry 3 -o "$archive" "$releases/download/v$version/$archive"
awk -v archive="$archive" '$2 == archive' SHA256SUMS | sha256sum -c -
tar -xzf "$archive" "$name/musubi"
install -D -m 755 "$name/musubi" /usr/local/bin/musubi
