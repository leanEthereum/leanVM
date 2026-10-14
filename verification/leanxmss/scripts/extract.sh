#!/usr/bin/env bash
# Regenerate `Leanxmss/Types.lean` and `Leanxmss/Funs.lean` from the guest's source: Charon, then Aeneas, then the
# closure patch (`patch_closures.py`).
#
# Needs `charon` and `aeneas` on `PATH`, at the versions the README pins, and Charon's Rust toolchain.
set -euo pipefail

here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(cd "$here/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The guest's manifest and source, verbatim, next to the SDK shim where its manifest expects `sdk/`.
mkdir -p "$work/programs/leanxmss/guest"
cp -r "$here/shim" "$work/sdk"
cp -r "$repo/programs/leanxmss/guest/"{Cargo.toml,Cargo.lock,src} "$work/programs/leanxmss/guest/"

(
    cd "$work/programs/leanxmss/guest"
    CARGO_TARGET_DIR="$work/target" charon cargo --preset aeneas \
        --opaque leanvm_guest \
        --start-from leanxmss::verify \
        --dest-file "$work/leanxmss.llbc" \
        -- --lib
)

aeneas -backend lean -split-files -use-lean-modules false -all-computable -no-progress-bar \
    -dest "$work/lean" "$work/leanxmss.llbc"

# The models are written by hand in `TypesExternal.lean` and `FunsExternal.lean`: the templates only list what they
# must define, so they are compared, not kept.
for f in Types Funs; do
    sed "s|$work/||g" "$work/lean/$f.lean" >"$here/Leanxmss/$f.lean"
done
python3 "$here/scripts/patch_closures.py" "$here/Leanxmss/Funs.lean"
for f in TypesExternal FunsExternal; do
    sed "s|$work/||g" "$work/lean/${f}_Template.lean" >"$here/Leanxmss/${f}_Template.lean.txt"
done
echo "Regenerated $here/Leanxmss/{Types,Funs}.lean; the external templates are in Leanxmss/*_Template.lean.txt"
