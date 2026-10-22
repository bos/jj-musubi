#!/bin/bash
# Builds the "git server" repositories the benchmark starts from, under $WORK/srv:
#   small.git  synthetic, 50 commits, and a week of 21 more
#   NAME.git   a copy of SOURCE, for each NAME=SOURCE argument: a local clone (a jj
#              repository's is read through jj), or a URL to clone the default branch of.
#              NAME is letters, digits and underscores.
# Each gets `main` as it was a week before its newest commit, with what came after at
# refs/bench/upstream, which bench.py's week phase brings in a day at a time; a 20-commit
# `feature` stack on main~1; and `marker` at feature~10. The sources are only read.
#
# Usage: setup_sources.sh [NAME=SOURCE ...], as in jj=$HOME/dev/jj git=https://github.com/git/git
set -euo pipefail
bench=$(cd "$(dirname "$0")" && pwd)
WORK=${MUSUBI_BENCH_DIR:-$bench/work}
export JJ_CONFIG=$bench/env/jjconfig.toml GIT_CONFIG_GLOBAL=$bench/env/gitconfig GIT_CONFIG_NOSYSTEM=1
for arg in "$@"; do
  name=${arg%%=*}
  case $arg in
    *=?*) ;;
    *) echo "expected NAME=SOURCE, not $arg" >&2; exit 2 ;;
  esac
  case $name in
    "" | small | *[!A-Za-z0-9_]*) echo "bad repository name: $name" >&2; exit 2 ;;
  esac
done
mkdir -p "$WORK"
cd "$WORK"
rm -rf srv tmp && mkdir -p srv tmp

export GIT_AUTHOR_DATE="2026-01-01T00:00:00Z" GIT_COMMITTER_DATE="2026-01-01T00:00:00Z"

# 1. Small synthetic repo, with three commits a day for the week after.
git init -q tmp/small-work
(
  cd tmp/small-work
  for i in $(seq 1 50); do
    mkdir -p src/m$((i % 5))
    printf 'line %s\n' $(seq 1 $((i * 3))) > src/m$((i % 5))/file$((i % 7)).txt
    echo "commit $i" >> README
    git add -A && git commit -q -m "small commit $i"
  done
  for d in $(seq 2 8); do
    for h in 08 16 23; do
      export GIT_AUTHOR_DATE="2026-01-0${d}T$h:00:00Z" GIT_COMMITTER_DATE="2026-01-0${d}T$h:00:00Z"
      echo "day $d hour $h" >> src/m$((d % 5))/week.txt
      git add -A && git commit -q -m "small upstream commit, day $d hour $h"
    done
  done
)
git clone -q --bare tmp/small-work srv/small.git
repos=(small)

# 2. Copies of real repositories. A jj repository is read through jj, and its HEAD may be
# detached, so `main` comes from its origin's.
copy() {
  local name=$1 src=${2/#\~/$HOME}
  if [ -d "$src/.jj" ]; then
    jj git clone --colocate "$src" "tmp/$name-src" >/dev/null 2>&1
    git clone -q --bare --no-local "tmp/$name-src" "srv/$name.git"
    if git -C "tmp/$name-src" rev-parse -q --verify refs/remotes/origin/main >/dev/null; then
      git -C "srv/$name.git" fetch -q "$WORK/tmp/$name-src" +refs/remotes/origin/main:refs/heads/main
    fi
  elif [ -d "$src" ]; then
    git clone -q --bare --no-local "$src" "srv/$name.git"
  else
    git clone -q --bare --single-branch "$src" "srv/$name.git"
  fi
  if ! git -C "srv/$name.git" rev-parse -q --verify refs/heads/main >/dev/null; then
    git -C "srv/$name.git" branch -m "$(git -C "srv/$name.git" symbolic-ref --short HEAD)" main
  fi
  repos+=("$name")
}
for arg in "$@"; do
  copy "${arg%%=*}" "${arg#*=}"
done

for r in "${repos[@]}"; do
  repo=srv/$r.git
  # Keep only main among the branches.
  git -C $repo for-each-ref --format='%(refname:short)' refs/heads | { grep -vx main || true; } | while read -r b; do
    git -C $repo branch -D "$b" >/dev/null
  done
  git -C $repo symbolic-ref HEAD refs/heads/main
  # Set main back a week; tags made during the week are left out.
  tip=$(git -C $repo rev-parse main)
  base=$(git -C $repo rev-list -1 --first-parent --before=$(( $(git -C $repo log -1 --format=%ct main) - 7 * 86400 )) main)
  if [ -z "$base" ]; then
    echo "$r: main has less than a week of history" >&2
    exit 1
  fi
  comm -23 <(git -C $repo tag --merged "$tip" | sort) <(git -C $repo tag --merged "$base" | sort) | while read -r t; do
    git -C $repo tag -d "$t" >/dev/null
  done
  git -C $repo update-ref refs/bench/upstream "$tip"
  git -C $repo update-ref refs/heads/main "$base"
  git clone -q $repo tmp/$r-work2
  (
    cd tmp/$r-work2
    git checkout -q -b feature main~1
    mkdir -p bench-feature
    for i in $(seq 1 20); do
      printf 'feature line %s\n' $(seq 1 $((i * 4))) > bench-feature/f$((i % 6)).txt
      git add -A && git commit -q -m "feature commit $i"
    done
    git branch marker feature~10
    git push -q origin feature marker
  )
  git -C $repo repack -adq
  echo "$r: $(git -C $repo rev-list --count --all) commits, $(git -C $repo count-objects -v | awk '/in-pack/{print $2}') objects, pack $(du -sh $repo/objects/pack | cut -f1), refs $(git -C $repo for-each-ref | wc -l), a week of $(git -C $repo rev-list --count main..refs/bench/upstream) commits"
done
rm -rf tmp
