#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
project_path=${LEAN_PATH:-}
unset LEAN_PATH
exec lean --run "$here/AxiomFootprint.lean" "$project_path" "$@"
