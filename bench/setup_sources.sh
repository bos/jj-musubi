#!/bin/bash
# Builds the "git server" repositories the benchmark starts from, under $WORK/srv:
#   small.git  synthetic, 50 commits
#   jj.git     a copy of a local clone of jj ($JJ_SRC), if set
#   git.git    a copy of a local clone of git ($GIT_SRC), if set
# Each gets `main`, a 20-commit `feature` stack on main~1, and `marker` at feature~10.
# The sources are only read.
set -euo pipefail
bench=$(cd "$(dirname "$0")" && pwd)
WORK=${MUSUBI_BENCH_DIR:-$bench/work}
export JJ_CONFIG=$bench/env/jjconfig.toml GIT_CONFIG_GLOBAL=$bench/env/gitconfig GIT_CONFIG_NOSYSTEM=1
mkdir -p "$WORK"
cd "$WORK"
rm -rf srv tmp && mkdir -p srv tmp

export GIT_AUTHOR_DATE="2026-01-01T00:00:00Z" GIT_COMMITTER_DATE="2026-01-01T00:00:00Z"

# 1. Small synthetic repo.
git init -q tmp/small-work
(
  cd tmp/small-work
  for i in $(seq 1 50); do
    mkdir -p src/m$((i % 5))
    printf 'line %s\n' $(seq 1 $((i * 3))) > src/m$((i % 5))/file$((i % 7)).txt
    echo "commit $i" >> README
    git add -A && git commit -q -m "small commit $i"
  done
)
git clone -q --bare tmp/small-work srv/small.git
repos=(small)

# 2. Copies of real repositories. A jj repository is read through jj, and its HEAD may be
# detached, so `main` comes from its origin's.
copy() {
  local name=$1 src=$2
  if [ -d "$src/.jj" ]; then
    jj git clone --colocate "$src" "tmp/$name-src" >/dev/null 2>&1
    git clone -q --bare --no-local "tmp/$name-src" "srv/$name.git"
    if git -C "tmp/$name-src" rev-parse -q --verify refs/remotes/origin/main >/dev/null; then
      git -C "srv/$name.git" fetch -q "$WORK/tmp/$name-src" +refs/remotes/origin/main:refs/heads/main
    fi
  else
    git clone -q --bare --no-local "$src" "srv/$name.git"
  fi
  if ! git -C "srv/$name.git" rev-parse -q --verify refs/heads/main >/dev/null; then
    git -C "srv/$name.git" branch -m "$(git -C "srv/$name.git" symbolic-ref --short HEAD)" main
  fi
  repos+=("$name")
}
if [ -n "${JJ_SRC:-}" ]; then copy jj "$JJ_SRC"; fi
if [ -n "${GIT_SRC:-}" ]; then copy git "$GIT_SRC"; fi

for r in "${repos[@]}"; do
  repo=srv/$r.git
  # Keep only main among the branches.
  git -C $repo for-each-ref --format='%(refname:short)' refs/heads | { grep -vx main || true; } | while read -r b; do
    git -C $repo branch -D "$b" >/dev/null
  done
  git -C $repo symbolic-ref HEAD refs/heads/main
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
  echo "$r: $(git -C $repo rev-list --count --all) commits, $(git -C $repo count-objects -v | awk '/in-pack/{print $2}') objects, pack $(du -sh $repo/objects/pack | cut -f1), refs $(git -C $repo for-each-ref | wc -l)"
done
rm -rf tmp
