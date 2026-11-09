#!/usr/bin/env bash
# The verifier fixtures (`export-rust.sh fixtures`, which documents them).
# Usage: scripts/export-verifier-fixtures-rust.sh <output dir> [--corpus]
exec "$(dirname "${BASH_SOURCE[0]}")/export-rust.sh" fixtures "$@"
