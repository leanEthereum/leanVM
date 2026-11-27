#!/usr/bin/env bash
# On a machine that can push: fetch a bundle made by export.sh, show its commits, and push its branches to origin.
#
#   import-push.sh <bundle>            # fetch and show only
#   import-push.sh <bundle> --push     # then push every branch in it (fast-forward only)
#
# REPO is the leanVM clone to push from (default ~/leanEthereum/leanVM). The bundle's branches land in
# refs/remotes/handoff/<branch>; a push that is not a fast-forward of origin's branch is refused by git.
set -euo pipefail
bundle=$(readlink -f "$1"); push=${2:-}
cd "${REPO:-$HOME/leanEthereum/leanVM}"
git bundle verify -q "$bundle"
git fetch -q origin
git fetch -q "$bundle" 'refs/heads/*:refs/remotes/handoff/*'
for ref in $(git bundle list-heads "$bundle" | awk '{ sub("refs/heads/", "", $2); print $2 }'); do
  echo "== $ref"
  if git rev-parse -q --verify "origin/$ref" >/dev/null; then
    git log --oneline "origin/$ref..handoff/$ref"
  else
    echo "(new branch)"; git log --oneline -20 "handoff/$ref"
  fi
  [ "$push" = --push ] && git push origin "refs/remotes/handoff/$ref:refs/heads/$ref"
done
[ "$push" = --push ] || echo "fetched only; rerun with --push to push"
