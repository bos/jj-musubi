#!/usr/bin/env bash
# Builds musubi against a checkout of jj instead of the release it pins, such as jj's main
# branch, so that changes to jj-lib that will break musubi show up before a release brings
# them. It rewrites the working copy: the jj-lib and jj-cli dependencies, the gix and prost
# requirements, which follow jj's, and the jj version the tests and the wire expect; the next
# build updates Cargo.lock to match. Run it from the workspace root, and `jj restore` those
# files afterwards. The checkout must lie outside this workspace, or cargo takes its crates
# for members of this one.
#
# Usage: use-jj-checkout.sh <jj checkout>
set -euo pipefail

jj=$(cd "$1" && pwd)

# The value of `key = "..."` on the first line of section in a manifest.
value() {
    sed -n "/^\[$2\]/,/^\[/s/^$3 = \"\([^\"]*\)\".*/\1/p" "$1" | head -n 1
}
# jj's requirement for a dependency, written either `dep = "x"` or `dep = { version = "x", ... }`.
requirement() {
    sed -n -e "s/^$1 = \"\([^\"]*\)\".*/\1/p" -e "s/^$1 = { version = \"\([^\"]*\)\".*/\1/p" \
        "$jj/Cargo.toml" | head -n 1
}
# Applies a perl substitution to a file, failing if it matches nothing.
rewrite() {
    if ! perl -pi -e "\$n += $2; END { exit !\$n }" "$1"; then
        echo "use-jj-checkout.sh: $1: no match for $2" >&2
        exit 1
    fi
}

version=$(value "$jj/Cargo.toml" workspace.package version)
gix=$(requirement gix)
prost=$(requirement prost)
if [[ -z $version || -z $gix || -z $prost ]]; then
    echo "use-jj-checkout.sh: can't read jj's version, gix or prost from $jj/Cargo.toml" >&2
    exit 1
fi

rewrite Cargo.toml "s|^jj-lib = \{ version = \"=[^\"]*\"|jj-lib = { version = \"=$version\", path = \"$jj/lib\"|"
rewrite Cargo.toml "s|^jj-cli = \{ version = \"=[^\"]*\"|jj-cli = { version = \"=$version\", path = \"$jj/cli\"|"
# jj's requirements: musubi decodes jj-lib's protobuf types with its prost, and builds one gix.
rewrite Cargo.toml "s|^gix = \{ version = \"=?[^\"]*\"|gix = { version = \"$gix\"|"
rewrite Cargo.toml "s|^prost = \"=?[^\"]*\"|prost = \"$prost\"|"
rewrite crates/musubi-testutil/src/lib.rs \
    "s|^pub const JJ_VERSION: &str = \"[^\"]*\";|pub const JJ_VERSION: &str = \"$version\";|"
rewrite crates/musubi-sync/src/wire.rs \
    "s|^pub const JJ_LIB_VERSION: &str = \"[^\"]*\";|pub const JJ_LIB_VERSION: &str = \"$version\";|"

echo "Using jj $version from $jj (gix $gix, prost $prost)"
