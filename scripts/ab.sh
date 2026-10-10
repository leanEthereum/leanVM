#!/usr/bin/env bash
# Proves a base and a head in turns on this machine, as bench.yml does for a PR, and prints what
# moved as the PR's comment would show it.
#
#   scripts/ab.sh [--base REF] [--rounds N] [--out DIR] [--testbed NAME] [--pr N] [--ci] BENCHMARK...
#
# A benchmark is a case of `proven()` in bins/leanvm/src/tracked.rs (`hash-50000-16thread`), proven by the
# CLI; a `benches/` target named in `target_of` below (`kernels`), run with `--json`; or `counts`,
# the exact counts counts.yml compares (`bench --cycles-only`, once a side). Each is built on both
# sides and run N times a side (`--rounds`, default `ROUNDS` or 5) in the order base, head, head,
# base, ... A base that cannot build or run one leaves the head's runs compared with nothing. The
# runs are saved as DIR/ab-<testbed>-<benchmark>/ab.json (bench.yml's artifact), the counts as
# DIR/counts/counts.json; DIR defaults to target/ab, the testbed to `local`, the PR to 1.
#
# Locally the head is the working tree, uncommitted changes included, and the base the merge-base
# with upstream/riscv-exploration (or origin/riscv-exploration, else HEAD^1), built in a temporary
# worktree into DIR/base-target, so neither the tree nor its build is touched. The comparison is
# then printed by main's .github/scripts/pr_comment.py, read from upstream/main or origin/main.
# With --ci (or GITHUB_ACTIONS=true), as bench.yml runs it: the head is the commit checked out,
# the base `--base` or else HEAD^1, checked out in place, and nothing is printed.
# The CI runs are capped at 16 GiB with no swap via a systemd user scope. After its timed
# rounds, leanxmss-100-1thread traces each runnable side once into trace-{base,head}.log.
#
# Needs git, python3 and cargo (or $CARGO).
set -euo pipefail

# The `benches/` targets, by benchmark name: package, target, then any build flags. Any other name is a CLI case.
target_of() {
  case $1 in
    flock-class-batch-16thread) echo leanvm class_batch ;;
    pcs-throughput-16thread) echo pcs throughput ;;
    blake2s-batch-16thread) echo primitives hash_throughput ;;
    kernels) echo primitives kernels ;;
  esac
}

# One measured pass a run, as the CLI's `--repeat 1 --cooldown 0`: the rounds are the repeats.
export BENCH_REPEAT=1 BENCH_COOLDOWN=0 FLOCK_N_LOG=18

cargo=${CARGO:-cargo}

say() { echo "ab: $*" >&2; }
die() { say "$*"; exit 1; }
warn() { if [ "$ci" = true ]; then echo "::warning::$*"; else say "warning: $*"; fi; }
usage() { sed -n '2,/^[^#]/s/^# \{0,1\}//p' "$0"; }

# The executable of the target named $1 among the artifacts cargo reports on stdin.
executable() {
  python3 -c '
import json, sys
for line in sys.stdin:
    m = json.loads(line)
    if m.get("reason") == "compiler-artifact" and m["target"]["name"] == sys.argv[1] and m.get("executable"):
        print(m["executable"])' "$1"
}

# Builds benchmark $1 in the current directory and copies its executable to $work/$2/$1.
build() {
  local name exe
  local -a target cmd
  read -ra target <<< "$(target_of "$1")"
  if [ ${#target[@]} -ge 2 ]; then
    name=${target[1]}
    cmd=(bench -p "${target[0]}" --bench "${target[1]}" --no-run "${target[@]:2}")
  else
    name=leanvm
    cmd=(build --release -p leanvm-cli)
  fi
  exe=$("$cargo" "${cmd[@]}" --message-format=json-render-diagnostics | executable "$name") && [ -n "$exe" ] || return
  mkdir -p "$work/$2"
  cp "$exe" "$work/$2/$1"
}

# Runs benchmark $1's side $2 once, printing its JSON.
run() {
  local exe=$work/$2/$1
  local -a scope=()
  if [ "$ci" = true ]; then scope=(systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0); fi
  if [ "$1" = counts ]; then
    ${scope[@]+"${scope[@]}"} "$exe" bench --cycles-only
  elif [ -n "$(target_of "$1")" ]; then
    ${scope[@]+"${scope[@]}"} "$exe" --json
  else
    ${scope[@]+"${scope[@]}"} "$exe" bench --only "$1" --repeat 1 --cooldown 0
  fi
}

# The run in file $1 as a line of runs.jsonl, with pool sizes kept as topology metadata, not timings.
# Fixed16 selections also require matching identifiers and measured pool size, never old default results.
wrap() {
  python3 -c '
import json, re, sys
results = json.load(open(sys.argv[1]))
if not isinstance(results, dict):
    sys.exit(1)
if sys.argv[4].endswith("-16thread"):
    if not results or any(
        re.search(r"-16thread(?:-(?:first|node))?$", name) is None
        or not isinstance(measures, dict)
        or not isinstance(measures.get("threads"), dict)
        or measures["threads"].get("value") != 16
        for name, measures in results.items()
    ):
        sys.exit(1)
topology = {}
for name, measures in results.items():
    pool = {
        key: measures.pop(key)["value"]
        for key in ("threads", "performance-threads", "efficiency-threads")
        if key in measures
    }
    if pool:
        topology[name] = pool
run = {"round": int(sys.argv[2]), "side": sys.argv[3], "results": results}
if topology:
    run["topology"] = topology
print(json.dumps(run, separators=(",", ":")))' "$@" 2> /dev/null
}

# Proves benchmark $1 in turns and saves the runs as ab.json.
prove() {
  local dir=$out/ab-$testbed-$1 has_base=false round side order line cpu
  if [ -x "$work/base/$1" ]; then has_base=true; fi
  mkdir -p "$dir"
  : > "$dir/runs.jsonl"
  for round in $(seq "$rounds"); do
    if [ $((round % 2)) = 1 ]; then order="base head"; else order="head base"; fi
    for side in $order; do
      if [ "$side" = base ] && [ "$has_base" = false ]; then continue; fi
      say "$1: round $round, $side"
      # A base that cannot run the benchmark at all (one the head adds, a base older than
      # `--only`, or a target whose base prints incompatible JSON) fails its first run, and the head's runs
      # are then compared with nothing: the comment shows them as new. Any other failure is fatal.
      if ! run "$1" "$side" > "$work/result.json" || ! line=$(wrap "$work/result.json" "$round" "$side" "$1"); then
        if [ "$side" = head ] || [ "$round" != 1 ]; then die "$1: the $side's run in round $round failed"; fi
        warn "the base cannot run $1: the PR's runs are compared with nothing"
        has_base=false
        continue
      fi
      echo "$line" >> "$dir/runs.jsonl"
      if [ "$ci" = true ]; then echo "$line"; fi
    done
  done
  cpu=$(lscpu 2> /dev/null | sed -n 's/^Model name: *//p' | head -n1) || true
  [ -n "$cpu" ] || cpu=$(sysctl -n machdep.cpu.brand_string 2> /dev/null) || true
  python3 -c '
import json, sys
pr, base, testbed, cpu, runs = sys.argv[1:]
runs = [json.loads(line) for line in open(runs)]
json.dump({"pr": int(pr), "base": base, "testbed": testbed, "cpu": cpu, "runs": runs}, sys.stdout, indent=2)' \
    "$pr" "$base" "$testbed" "$cpu" "$dir/runs.jsonl" > "$dir/ab.json"
  rm "$dir/runs.jsonl"
  if [ "$ci" = true ] && [ "$1" = leanxmss-100-1thread ]; then
    for side in base head; do
      if [ "$side" = base ] && [ "$has_base" = false ]; then continue; fi
      say "$1: tracing $side after the timed rounds"
      systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 \
        env LEANVM_NUM_THREADS=1 "$work/$side/$1" leanxmss --n 100 --repeat 1 --tracing \
        2>&1 | tee "$dir/trace-$side.log"
    done
  fi
}

# Counts both sides once and saves them as counts.json, counts.yml's artifact.
count() {
  rm -f "$out/counts/counts.json"
  say "counts: head"
  run counts head > "$work/counts-head.json" || die "the head cannot count"
  say "counts: base"
  if [ ! -x "$work/base/counts" ] || ! run counts base > "$work/counts-base.json"; then
    warn "the base cannot count: no counts compared"
    return
  fi
  mkdir -p "$out/counts"
  python3 -c '
import json, sys
pr, base, old, new = sys.argv[1:]
counts = {"base": json.load(open(old)), "head": json.load(open(new))}
json.dump({"pr": int(pr), "base": base, "counts": counts}, sys.stdout, indent=2)' \
    "$pr" "$base" "$work/counts-base.json" "$work/counts-head.json" > "$out/counts/counts.json"
}

# Prints the comparison with main's pr_comment.py, as the PR's comments would show it.
render() {
  local script=$work/pr_comment.py ref found=false body dirty="" counts="" b
  local -a files=()
  for b in "${benches[@]}"; do
    if [ "$b" != counts ]; then
      files+=("$out/ab-$testbed-$b/ab.json")
    elif [ -f "$out/counts/counts.json" ]; then
      counts=$out/counts/counts.json
    fi
  done
  for ref in upstream/main origin/main; do
    if git show "$ref:.github/scripts/pr_comment.py" > "$script" 2> /dev/null; then found=true && break; fi
  done
  if [ "$found" = false ]; then
    say "no .github/scripts/pr_comment.py on upstream/main or origin/main to print the comparison with: the runs are in $out"
    return
  fi
  [ -z "$(git status --porcelain)" ] || dirty=" plus the uncommitted changes"
  say "head: $head$dirty; base: $base"
  if [ -n "$counts" ]; then
    body=$(python3 "$script" counts "$head" "$counts" --dry-run)
    if [ -n "$body" ]; then echo "$body"; else say "no count changed"; fi
  fi
  if [ ${#files[@]} -gt 0 ]; then
    body=$(python3 "$script" bench "$head" "${files[@]}" --dry-run)
    if [ -n "$body" ]; then
      echo "$body"
    else
      say "nothing moved beyond pr_comment.py's threshold; every run is in:"
      printf '  %s\n' "${files[@]}" >&2
    fi
  fi
}

cleanup() {
  if [ "$on_base" = true ]; then git checkout --quiet --detach "$head"; fi
  rm -rf "$work"
  if [ -n "$worktree" ]; then git worktree prune; fi
}

main() {
  base="" rounds=${ROUNDS:-5} out=target/ab testbed=local pr=1 ci=${GITHUB_ACTIONS:-false}
  benches=()
  while [ $# -gt 0 ]; do
    case $1 in
      --base) base=${2:?--base needs a ref}; shift 2 ;;
      --rounds) rounds=${2:?--rounds needs a number}; shift 2 ;;
      --out) out=${2:?--out needs a directory}; shift 2 ;;
      --testbed) testbed=${2:?--testbed needs a name}; shift 2 ;;
      --pr) pr=${2:?--pr needs a number}; shift 2 ;;
      --ci) ci=true; shift ;;
      -h | --help) usage; exit 0 ;;
      -*) die "unknown option $1 (see --help)" ;;
      *) benches+=("$1"); shift ;;
    esac
  done
  [ ${#benches[@]} -gt 0 ] || { usage >&2; exit 2; }
  case $rounds in '' | *[!0-9]* | 0) die "--rounds must be a positive number" ;; esac
  case $pr in '' | *[!0-9]* | 0) die "--pr must be a positive number" ;; esac

  mkdir -p "$out"
  out=$(cd "$out" && pwd)
  cd "$(git rev-parse --show-toplevel)"
  head=$(git rev-parse HEAD)
  if [ -z "$base" ]; then
    base=HEAD^1
    if [ "$ci" = false ]; then
      for ref in upstream/riscv-exploration origin/riscv-exploration; do
        if git rev-parse --verify --quiet "$ref^{commit}" > /dev/null; then base=$(git merge-base HEAD "$ref") && break; fi
      done
    fi
  fi
  base=$(git rev-parse --verify "$base^{commit}")
  # The base builds outside this tree, where a rustup override for it would not apply.
  if [ "$ci" = false ] && [ -z "${RUSTUP_TOOLCHAIN:-}" ] && command -v rustup > /dev/null; then
    RUSTUP_TOOLCHAIN=$(rustup show active-toolchain | cut -d' ' -f1) && export RUSTUP_TOOLCHAIN
  fi

  work=$(mktemp -d "${TMPDIR:-/tmp}/ab.XXXXXX") worktree="" on_base=false
  trap cleanup EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM

  for b in "${benches[@]}"; do
    say "building the head's $b"
    build "$b" head || die "the head cannot build $b"
  done
  if [ "$ci" = true ]; then
    on_base=true
    git checkout --quiet --detach "$base"
    for b in "${benches[@]}"; do
      say "building the base's $b"
      build "$b" base || warn "the base cannot build $b"
    done
    git checkout --quiet --detach "$head"
    on_base=false
  else
    worktree=$work/tree
    git worktree add --quiet --detach "$worktree" "$base"
    (
      cd "$worktree"
      export CARGO_TARGET_DIR=$out/base-target
      for b in "${benches[@]}"; do
        say "building the base's $b"
        build "$b" base || warn "the base cannot build $b"
      done
    )
    git worktree remove --force "$worktree"
  fi

  for b in "${benches[@]}"; do
    if [ "$b" = counts ]; then count; else prove "$b"; fi
  done
  if [ "$ci" = false ]; then render; fi
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then main "$@"; fi
