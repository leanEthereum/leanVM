#!/usr/bin/env bash
# On a machine that cannot push: pack the commits it made into a git bundle, to copy (scp) to a machine that can.
#
#   formal/rv64mc/campaign/transfer/export.sh <out.bundle> [branch...]
#
# Run anywhere inside the leanVM clone. With no branch named, it takes every local branch holding a commit that no
# remote-tracking branch has. The bundle holds only those commits (`--not --remotes`), so the receiving machine
# must have the remote's commits, which it does: it pushed them. Then, there: import-push.sh <bundle>.
set -euo pipefail
out=$1; shift
cd "$(git rev-parse --show-toplevel)"
branches=("$@")
if [ ${#branches[@]} -eq 0 ]; then
  while read -r b; do
    [ -n "$(git rev-list "$b" --not --remotes | head -1)" ] && branches+=("$b")
  done < <(git for-each-ref --format='%(refname:short)' refs/heads/)
fi
[ ${#branches[@]} -gt 0 ] || { echo "nothing to export: every local branch is on a remote-tracking branch" >&2; exit 1; }
git bundle create "$out" "${branches[@]}" --not --remotes
git bundle list-heads "$out"
for b in "${branches[@]}"; do echo "== $b"; git log --oneline "$b" --not --remotes | head -20; done
