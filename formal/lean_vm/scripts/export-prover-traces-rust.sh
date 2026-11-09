#!/usr/bin/env bash
# The prover traces (`export-rust.sh traces`, which documents them).
# Usage: scripts/export-prover-traces-rust.sh <output dir> [--corpus]
exec "$(dirname "${BASH_SOURCE[0]}")/export-rust.sh" traces "$@"
