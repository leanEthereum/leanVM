#!/usr/bin/env bash
# Vendor EthLib's leanSPHINCS test vectors at one commit.
#
#     crates/lean_sphincs/tests/lean_sphincs/ethlib/sync.sh <ethlib-commit>
#
# Replaces this directory's vectors with EthLib's `tests/cryptography/sphincs/` at that commit,
# checks every case against EthLib's SHA256SUMS, and records the commit. leanXMSS and
# leanSPHINCS are vendored from the same commit: run both crates' scripts with it.
set -euo pipefail

commit=${1:?usage: sync.sh <ethlib-commit>}
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

curl -fsSL "https://codeload.github.com/ethereum/EthLib/tar.gz/$commit" | tar -xz -C "$work"
src=$(echo "$work"/*/tests/cryptography/sphincs)
[ -d "$src" ] || { echo "no tests/cryptography/sphincs at $commit" >&2; exit 1; }
(cd "$src" && sha256sum --quiet -c SHA256SUMS)

find "$here" -mindepth 1 -maxdepth 1 ! -name sync.sh ! -name COMMIT -exec rm -rf {} +
cp -R "$src"/. "$here"/
echo "$commit" > "$here/COMMIT"
echo "vendored EthLib $commit sphincs: $(grep -vc '^#' "$here/SHA256SUMS") cases"
