#!/usr/bin/env bash
# Vendor EthLib's leanXMSS and leanSPHINCS test vectors at one commit.
#
#     crates/signatures/tests/signatures/ethlib/sync.sh <ethlib-commit>
#
# Replaces `xmss/` and `sphincs/` with EthLib's `tests/cryptography/xmss/` and
# `tests/cryptography/sphincs/` at that commit, checks every case against
# EthLib's SHA256SUMS, and records the commit.
set -euo pipefail

commit=${1:?usage: sync.sh <ethlib-commit>}
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# One archive of the whole repository at that commit, unpacked outside the tree.
curl -fsSL "https://codeload.github.com/ethereum/EthLib/tar.gz/$commit" | tar -xz -C "$work"

for scheme in xmss sphincs; do
  src=$(echo "$work"/*/tests/cryptography/"$scheme")
  [ -d "$src" ] || { echo "no tests/cryptography/$scheme at $commit" >&2; exit 1; }

  # The digests EthLib pins must hold before anything is copied.
  (cd "$src" && sha256sum --quiet -c SHA256SUMS)

  rm -rf "${here:?}/$scheme"
  cp -R "$src" "$here/$scheme"
  echo "vendored EthLib $commit $scheme: $(wc -l < "$here/$scheme/SHA256SUMS") cases"
done

echo "$commit" > "$here/COMMIT"
