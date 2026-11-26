#!/usr/bin/env bash
# Measures what a change to the verifier costs to re-prove: apply a patch in a copy of the tree, regenerate the image
# and the templates, rebuild, and report what changed, what was rebuilt (by module class, with CPU seconds) and what
# fails.
#
#   scripts/iterate.sh --init [REV]                 out/bench/base: REV (default HEAD) of formal/rv64mc,
#                                                   formal/Statement and crates/verifier, built warm from this
#                                                   project's .lake
#   scripts/iterate.sh PATCH [--label L] [--title T] [--jobs N] [--no-sweep] [--no-log]
#   scripts/iterate.sh --rebuild L [--jobs N]       the build and its report again in out/bench/L, after edits there
#
# PATCH is a unified diff against the repository root (crates/verifier, formal/Statement, formal/rv64mc/Rv64mc/...).
# A run copies out/bench/base to out/bench/L (sources and .lake/build copied, .lake/packages hard-linked), so the
# shared tree and its build are never touched; the copy's own regen.sh and type-layouts.sh run with VERIFIER_SRC at the
# copy's crates/verifier. The build runs `lake build Rv64mc` through a `lean` that records each module's CPU time
# (iterate.py), at most N (default 6) modules at once. Then `rv_sweep` on each changed template. The report is
# out/bench/L/meta/section.md and row.tsv, appended to notes/iteration-log.md and notes/iteration-bench.tsv.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/../.." && pwd)
bench=$here/out/bench
base=$bench/base
py=(python3 -I "$here/scripts/iterate.py")
jobs=6
TIMEFMT='%e %U %S %M %x'

copy_tree() { # SRC DST: a copy of a bench tree, .lake/packages hard-linked
  local src=$1 dst=$2
  mkdir -p "$dst/formal/rv64mc/.lake" "$dst/crates"
  cp -a "$src/crates/verifier" "$dst/crates/"
  cp -a "$src/formal/Statement" "$dst/formal/"
  local e
  for e in "$src/formal/rv64mc"/* "$src/formal/rv64mc"/.[!.]*; do
    [ -e "$e" ] && [ "$(basename "$e")" != .lake ] && cp -a "$e" "$dst/formal/rv64mc/"
  done
  cp -al "$src/formal/rv64mc/.lake/packages" "$dst/formal/rv64mc/.lake/"
  cp -a "$src/formal/rv64mc/.lake/build" "$dst/formal/rv64mc/.lake/"
}

build() { # TREE META: lake build Rv64mc with per-module records
  local tree=$1 meta=$2 sys
  sys=$(mktemp -d "$meta/sysroot.XXXXXX")
  local bin
  bin=$("${py[@]}" sysroot "$sys/root")
  : > "$meta/lean.tsv"
  echo "$jobs" > "$meta/jobs"
  (cd "$tree/formal/rv64mc" && ITER_BIN=$bin ITER_LOG=$meta/lean.tsv ITER_JOBS=$jobs LEAN_SYSROOT=$sys/root \
    LAKE_OVERRIDE_LEAN=true /usr/bin/time -f "$TIMEFMT" -o "$meta/build.time" \
    timeout 21600 lake build Rv64mc > "$meta/build.txt" 2>&1) || true
  rm -rf "$sys" "$meta"/slot*
}

if [ "${1:-}" = --init ]; then
  rev=${2:-HEAD}
  sha=$(git -C "$root" rev-parse --short=9 "$rev")
  rm -rf "$base"
  mkdir -p "$base/meta" "$base/formal/rv64mc/.lake" "$base/formal/Statement/.lake"
  git -C "$root" archive "$rev" formal/rv64mc formal/Statement crates/verifier | tar -x -C "$base"
  cp -al "$here/.lake/packages" "$base/formal/rv64mc/.lake/"
  cp -a "$here/.lake/build" "$base/formal/rv64mc/.lake/"
  cp -a "$root/formal/Statement/.lake/build" "$base/formal/Statement/.lake/"
  cp -a "$here/Rv64mc/Gen" "$here/Rv64mc/Gen.lean" "$base/formal/rv64mc/Rv64mc/"
  echo "$sha" > "$base/meta/sha"
  t=$base/formal/rv64mc
  (cd "$t" && VERIFIER_SRC=$base/crates/verifier /usr/bin/time -f "$TIMEFMT" -o "$base/meta/regen.time" \
    scripts/regen.sh > "$base/meta/regen.txt" 2>&1)
  (cd "$t" && VERIFIER_SRC=$base/crates/verifier /usr/bin/time -f "$TIMEFMT" -o "$base/meta/layouts.time" \
    scripts/type-layouts.sh > "$base/meta/layouts.txt" 2>&1)
  grep -E '^(changed|added|removed)	|^templates:' "$base/meta/regen.txt" > "$base/meta/templates.txt" || true
  build "$base" "$base/meta"
  "${py[@]}" report "$base/meta" base
  exit 0
fi

if [ "${1:-}" = --rebuild ]; then
  label=$2; shift 2
  [ "${1:-}" = --jobs ] && jobs=$2
  run=$bench/$label
  k=1
  while [ -e "$run/meta-rebuild$k" ]; do k=$((k + 1)); done
  meta=$run/meta-rebuild$k
  mkdir -p "$meta"
  cp "$run/meta/sha" "$meta/"
  build "$run" "$meta"
  "${py[@]}" report "$meta" "$label-rebuild$k"
  exit 0
fi

patch=$(realpath "$1"); shift
label=$(basename "$patch" .patch)
title=
sweep=1
log=1
while [ $# -gt 0 ]; do
  case $1 in
    --label) label=$2; shift ;;
    --title) title=$2; shift ;;
    --jobs) jobs=$2; shift ;;
    --no-sweep) sweep=0 ;;
    --no-log) log=0 ;;
    *) echo "usage: $0 PATCH [--label L] [--title T] [--jobs N] [--no-sweep] [--no-log]" >&2; exit 2 ;;
  esac
  shift
done
[ -d "$base/formal/rv64mc/.lake/build" ] || { echo "no $base: run $0 --init first" >&2; exit 1; }
run=$bench/$label
meta=$run/meta
rm -rf "$run"
copy_tree "$base" "$run"
mkdir -p "$meta"
cp "$base/meta/sha" "$meta/sha"
echo "${title:-$label}" > "$meta/title"
echo "$(basename "$patch")" > "$meta/patch"
t=$run/formal/rv64mc
cp "$t/out/gen.elf" "$meta/old.elf"
cp "$t/Rv64mc/Gen/Layouts.lean" "$meta/old-Layouts.lean"
if [ -s "$patch" ]; then
  patch -p1 -d "$run" --no-backup-if-mismatch -s < "$patch"
  lsdiff_files=$(grep -E '^\+\+\+ ' "$patch" | sed -E 's#^\+\+\+ [^/]*/##; s#\t.*##' | paste -sd, | sed 's/,/, /g')
else
  lsdiff_files="empty"
fi
echo "$lsdiff_files" > "$meta/patch-files"
(cd "$t" && VERIFIER_SRC=$run/crates/verifier /usr/bin/time -f "$TIMEFMT" -o "$meta/regen.time" \
  scripts/regen.sh > "$meta/regen.txt" 2>&1)
grep -E '^(changed|added|removed)	|^templates:' "$meta/regen.txt" > "$meta/templates.txt" || true
(cd "$t" && VERIFIER_SRC=$run/crates/verifier /usr/bin/time -f "$TIMEFMT" -o "$meta/layouts.time" \
  scripts/type-layouts.sh > "$meta/layouts.txt" 2>&1)
if cmp -s "$meta/old-Layouts.lean" "$t/Rv64mc/Gen/Layouts.lean"; then
  echo unchanged > "$meta/layouts-changed"
else
  n=$(diff "$meta/old-Layouts.lean" "$t/Rv64mc/Gen/Layouts.lean" | grep -c '^[<>]')
  echo "changed, $n lines" > "$meta/layouts-changed"
fi
python3 -I "$t/scripts/elf-diff.py" "$meta/old.elf" "$t/out/gen.elf" > "$meta/elf-diff.txt"
build "$run" "$meta"
[ $sweep = 1 ] && "${py[@]}" sweep "$t" "$meta"
"${py[@]}" report "$meta" "$label"
if [ $log = 1 ]; then
  [ -f "$here/notes/iteration-bench.tsv" ] || "${py[@]}" header > "$here/notes/iteration-bench.tsv"
  cat "$meta/row.tsv" >> "$here/notes/iteration-bench.tsv"
  { echo; cat "$meta/section.md"; } >> "$here/notes/iteration-log.md"
fi
