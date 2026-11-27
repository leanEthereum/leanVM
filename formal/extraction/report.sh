#!/usr/bin/env bash
# What each extraction takes on trust, as Markdown: the Rust items left opaque (axioms in
# Assumptions/), the bodies Aeneas could not translate (`sorry` in Extraction/), and the
# pre-extraction patches; then the standard-library models every extraction shares.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
shopt -s nullglob

echo "| extraction | definitions | opaque Rust items | sorry | patches |"
echo "| --- | ---: | ---: | ---: | ---: |"
for lean in crates/*/proofs/*/lean crates/*/*/proofs/*/lean; do
  pkg=$(awk -F'"' '/^name = /{ print $2; exit }' "$lean/lakefile.toml")
  ext="$lean/$pkg/Extraction"
  asm="$lean/$pkg/Assumptions"
  defs=$(cat "$ext"/Types.lean "$ext"/Funs.lean | grep -cE '^(@\[[^]]*\] *)*(def|structure|inductive|instance) ' || true)
  axioms=$(cat "$asm"/*External.lean 2>/dev/null | grep -cE '^axiom ' || true)
  sorries=$(cat "$ext"/Types.lean "$ext"/Funs.lean | grep -cw sorry || true)
  patches=$(find "${lean%/lean}" -path '*/patches/*' -name '*.patch' | wc -l | tr -d ' ')
  echo "| \`${lean%/lean}\` | $defs | $axioms | $sorries | $patches |"
done

ext=formal/extraction/CoreModelsExt/CoreModelsExt
models=$(cat "$ext"/*.lean | grep -cE '^(@\[[^]]*\] *)*(def|opaque|abbrev|instance) ' || true)
opaques=$(cat "$ext"/*.lean | grep -cE '^opaque ' || true)
echo
echo "Shared standard-library models (CoreModelsExt): $models, of which $opaques opaque."
