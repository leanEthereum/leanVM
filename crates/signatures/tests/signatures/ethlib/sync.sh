#!/usr/bin/env bash
# Vendor EthLib's leanXMSS test vectors at one commit.
#
#     crates/signatures/tests/signatures/ethlib/sync.sh <ethlib-commit>
#
# Replaces `xmss/` with EthLib's `tests/cryptography/xmss/` at that commit,
# checks every case against EthLib's SHA256SUMS, and records the commit.
set -euo pipefail

commit=${1:?usage: sync.sh <ethlib-commit>}
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# One archive of the whole repository at that commit, unpacked outside the tree.
curl -fsSL "https://codeload.github.com/ethereum/EthLib/tar.gz/$commit" | tar -xz -C "$work"
src=$(echo "$work"/*/tests/cryptography/xmss)
[ -d "$src" ] || { echo "no tests/cryptography/xmss at $commit" >&2; exit 1; }

# The digests EthLib pins must hold before anything is copied.
(cd "$src" && sha256sum --quiet -c SHA256SUMS)

rm -rf "$here/xmss"
cp -R "$src" "$here/xmss"
echo "$commit" > "$here/COMMIT"
echo "vendored EthLib $commit: $(wc -l < "$here/xmss/SHA256SUMS") cases"
