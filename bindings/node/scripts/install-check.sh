#!/bin/sh
# Installs a packed @kevaundray/lean-pq and one packed platform package into a fresh project, then
# runs scripts/smoke.js against the installed copy. Extra arguments go to smoke.js.
#
#   sh scripts/install-check.sh <lean-pq.tgz> <lean-pq-platform.tgz> [--aggregate]
set -eu

if [ "$#" -lt 2 ]; then
  echo "usage: $0 <lean-pq.tgz> <lean-pq-platform.tgz> [--aggregate]" >&2
  exit 2
fi

scripts=$(cd "$(dirname "$0")" && pwd)
root_tgz=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
platform_tgz=$(cd "$(dirname "$2")" && pwd)/$(basename "$2")
shift 2

# The root package must load its binary from the platform package, never from a bundled copy.
if tar -tzf "$root_tgz" | grep '\.node$'; then
  echo "$root_tgz must not contain a native binary" >&2
  exit 1
fi
if ! tar -tzf "$platform_tgz" | grep -q '^package/lean_pq_node\..*\.node$'; then
  echo "$platform_tgz does not contain lean_pq_node.<platform>.node" >&2
  exit 1
fi

project=$(mktemp -d)
trap 'rm -rf "$project"' EXIT
cp "$scripts/smoke.js" "$project/"
cd "$project"
npm init -y >/dev/null
npm install --no-audit --no-fund --ignore-scripts "$root_tgz" "$platform_tgz"
# The generated loader compares its baked-in version with the platform package's.
NAPI_RS_ENFORCE_VERSION_CHECK=1 node smoke.js "$@"
