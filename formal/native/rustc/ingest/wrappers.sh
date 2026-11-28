#!/usr/bin/env bash
# Regenerate the small committed module wrappers from assembly and RustcIngest.Core's import graph.
# Usage, from anywhere: rustc/ingest/wrappers.sh [--check]
set -euo pipefail

case ${1:-} in
  "" | --check) ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
native=$(cd "$here/../.." && pwd)
generated=$(mktemp -d)
trap 'rm -rf "$generated"' EXIT
(
  cd "$native"
  lake build -q RustcIngest.Arm RustcIngest.X64 RustcIngest.Generate
  lake env lean --run cli/GenerateRustcWrappersArm.lean "$generated"
  lake env lean --run cli/GenerateRustcWrappersX64.lean "$generated"
)

status=0
for ns in NativeRustcArm NativeRustcX64 NativeRustcVmArm NativeRustcVmX64; do
  if [ "${1:-}" = --check ]; then
    diff -r -x Infix.lean "$generated/$ns/Code" "$native/$ns/Code" || status=1
    diff "$generated/$ns/Code.lean" "$native/$ns/Code.lean" || status=1
  else
    while IFS= read -r -d '' file; do
      if grep -Eq '^ingest_(arm|x64) ' "$file" && [ ! -f "$generated/${file#"$native/"}" ]; then
        rm "$file"
      fi
    done < <(find "$native/$ns/Code" -name '*.lean' -print0)
    find "$native/$ns/Code" -mindepth 1 -type d -empty -delete
    cp -R "$generated/$ns/Code/." "$native/$ns/Code/"
    cp "$generated/$ns/Code.lean" "$native/$ns/Code.lean"
  fi
done
if [ "$status" -eq 0 ]; then echo "ingestion wrappers up to date"; fi
exit "$status"
