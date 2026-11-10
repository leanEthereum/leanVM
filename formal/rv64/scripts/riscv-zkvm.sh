#!/usr/bin/env bash
# Fetch riscv-zkvm at its pinned tag into .deps/riscv-zkvm and apply the one change Lean v4.35.0 needs: a do-element
# `assert` now parses as Lean's intrinsic-verification syntax, so the generated Sail code's calls to `Sail.assert` are
# written `«assert»`, the same function.
set -euo pipefail
cd "$(dirname "$0")/.."
TAG=v0.4.0
DIR=.deps/riscv-zkvm
if [ ! -d "$DIR" ]; then
  git clone --quiet https://github.com/Verified-zkEVM/riscv-zkvm "$DIR"
fi
git -C "$DIR" checkout --quiet "$TAG"
git -C "$DIR" checkout --quiet -B lean-v4.35.0
echo "leanprover/lean4:v4.35.0" > "$DIR/lean-toolchain"
grep -rlE '(^\s+|then |else )assert ' "$DIR/RiscvZkvm" | xargs -r sed -i -E 's/(^\s+|then |else )assert /\1«assert» /'
