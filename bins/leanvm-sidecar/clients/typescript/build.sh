#!/usr/bin/env bash
# Build the client into dist/: the mmap addon with the C compiler, the TypeScript with tsc.
# Needs Node's headers (they ship with Node; NODE_INCLUDE overrides where) and `npm install` for tsc.
set -euo pipefail
cd "$(dirname "$0")"
include=${NODE_INCLUDE:-$(node -p "require('path').resolve(process.execPath, '..', '..', 'include', 'node')")}
[[ -d node_modules ]] || npm install --no-audit --no-fund
mkdir -p dist
# An addon's N-API symbols resolve against the node binary when it is loaded.
if [[ $(uname) == Darwin ]]; then undefined=(-undefined dynamic_lookup); else undefined=(); fi
${CC:-cc} -O2 -Wall -Wextra -shared -fPIC "${undefined[@]}" -DNODE_GYP_MODULE_NAME=mmap -I"$include" mmap.c -o dist/mmap.node
npx tsc
