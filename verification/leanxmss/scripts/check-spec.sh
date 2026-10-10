#!/usr/bin/env bash
# Check that `Spec/` is the Ethereum XMSS specification's `Xmss` modules, verbatim, at the pinned commit.
set -euo pipefail

commit=d1331f02e308fe6d0aedda8601e4d5b0fc360318
here=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

git -C "$work" init -q
git -C "$work" fetch -q --depth 1 https://github.com/ethereum/cryptography-specs "$commit"
git -C "$work" checkout -q FETCH_HEAD
diff -r "$work/EthCryptographySpecs/Xmss" "$here/Spec/EthCryptographySpecs/Xmss"
diff "$work/EthCryptographySpecs/Xmss.lean" "$here/Spec/EthCryptographySpecs/Xmss.lean"
echo "Spec/ is ethereum/cryptography-specs@$commit, verbatim"
