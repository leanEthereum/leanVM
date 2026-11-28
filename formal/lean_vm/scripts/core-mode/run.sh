#!/usr/bin/env bash
# The core route's generators alone, in order: `regen-guest.sh`'s `core-mode` step, on a tree whose earlier steps are
# current. Any arguments go to `regen-guest.sh` (`--check`, `--jobs N`).
set -euo pipefail
exec "$(dirname "${BASH_SOURCE[0]}")/../regen-guest.sh" --from core-mode "$@"
