#!/usr/bin/env bash
# Vendor EthLib's leanXMSS test vectors at one commit.
#
#     crates/lean_xmss/tests/lean_xmss/ethlib/sync.sh <ethlib-commit>
#
# Replaces this directory's vectors with EthLib's `tests/cryptography/xmss/` at that commit,
# checks every case against EthLib's SHA256SUMS, and records the commit. leanXMSS and
# leanSPHINCS are vendored from the same commit: run both crates' scripts with it.
set -euo pipefail

commit=${1:?usage: sync.sh <ethlib-commit>}
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

curl -fsSL "https://codeload.github.com/ethereum/EthLib/tar.gz/$commit" | tar -xz -C "$work"
src=$(echo "$work"/*/tests/cryptography/xmss)
[ -d "$src" ] || { echo "no tests/cryptography/xmss at $commit" >&2; exit 1; }
(cd "$src" && sha256sum --quiet -c SHA256SUMS)

find "$here" -mindepth 1 -maxdepth 1 ! -name sync.sh ! -name COMMIT -exec rm -rf {} +
cp -R "$src"/. "$here"/
echo "$commit" > "$here/COMMIT"
echo "vendored EthLib $commit xmss: $(grep -vc '^#' "$here/SHA256SUMS") cases"
