#!/usr/bin/env bash
# lean_vm's Lake build kept between CI runs as a workflow artifact (`.github/workflows/lean.yml`).
#
#   tools/lake-artifact.sh restore      unpack the newest artifact of a push to main of this repository, or of this
#                                       pull request's own runs, whichever is newer; none found: a cold build
#   tools/lake-artifact.sh pack FILE    write the build to FILE (tar, zstd), and `pack=true` and the artifact's
#                                       `name` to $GITHUB_OUTPUT, unless the restored build was made from this very
#                                       `formal/` tree
#
# Not the Actions cache: that is 10 GB per repository, evicted least recently used first, and the Lean jobs alone
# saved more than that on each push to main, so lean_vm's build never survived until the next run. An artifact lives
# until its retention ends. Its name holds the toolchain's and the manifest's hash, so a build is restored only for
# the same packages. Lake trusts nothing restored: it compares every module's trace with its inputs.
#
# Environment: GH_TOKEN, GITHUB_REPOSITORY, GITHUB_REPOSITORY_ID, HEAD_REPO_ID and HEAD_REF (the pull request's head
# repository and branch; for a push, this repository and `main`), RUNNER_TEMP, GITHUB_OUTPUT.
set -euo pipefail
self=$(readlink -f "$0")
cd "$(git rev-parse --show-toplevel)"
# `v2`: builds packed before directories were kept lacked the packages' empty git directories (`refs/`), so git took
# a package for the enclosing repository and Lake's checkout of it rewrote this one's working tree.
name=lean-vm-lake-v2-$(cat formal/lean_vm/lean-toolchain formal/lean_vm/lake-manifest.json | sha256sum | cut -c1-16)
marker=formal/lean_vm/.lake/ci-formal-tree  # the `formal/` tree the packed build was made from

case ${1:-} in
restore)
  # A run's artifact counts only if that run is a push to main of this repository or this pull request's own
  # branch (its head repository too, so a fork cannot hand another branch a build).
  run=$(gh api --paginate "repos/$GITHUB_REPOSITORY/actions/artifacts?name=$name&per_page=100" --jq '.artifacts[]' |
    jq -rs --argjson repo "$GITHUB_REPOSITORY_ID" --argjson head "$HEAD_REPO_ID" --arg ref "$HEAD_REF" '
      [.[] | select(.expired | not)
       | select((.workflow_run.head_repository_id == $repo and .workflow_run.head_branch == "main")
                or (.workflow_run.head_repository_id == $head and .workflow_run.head_branch == $ref))]
      | max_by(.created_at) | .workflow_run.id // empty')
  if [ -z "$run" ]; then
    echo "no $name of main or of this branch: building from scratch"
    exit 0
  fi
  start=$SECONDS
  gh run download "$run" -R "$GITHUB_REPOSITORY" -n "$name" -D "$RUNNER_TEMP/lake-artifact"
  echo "downloaded run $run's $name ($(du -sh "$RUNNER_TEMP/lake-artifact" | cut -f1)) in $((SECONDS - start)) s"
  zstd -dc "$RUNNER_TEMP"/lake-artifact/lake.tar.zst | tar -xf -
  rm -rf "$RUNNER_TEMP/lake-artifact"
  echo "restored in $((SECONDS - start)) s, built from formal/ tree $(cat "$marker" 2>/dev/null || echo unknown)"
  ;;
pack)
  out=$2
  tree=$(git rev-parse HEAD:formal)
  if [ -f "$marker" ] && [ "$(cat "$marker")" = "$tree" ]; then
    echo "the restored build is this formal/ tree's: nothing new to keep"
    exit 0
  fi
  echo "$tree" > "$marker"
  start=$SECONDS
  # Mathlib's build comes from `lake exe cache get`, all but its compiled C objects, which the executables need.
  # Directories too (`--no-recursion`), empty ones included: a package's git repository needs its `refs/`.
  { find formal/lean_vm/.lake -path formal/lean_vm/.lake/packages/mathlib/.lake -prune -o \( -type f -o -type l -o -type d \) -print0
    find formal/lean_vm/.lake/packages/mathlib/.lake/build/ir -name '*.c.o.*' -print0 2>/dev/null || true
    for p in common Statement lean_xmss lean_sphincs lean_da; do
      if [ -d "formal/$p/.lake/build" ]; then find "formal/$p/.lake/build" \( -type f -o -type l -o -type d \) -print0; fi
    done; } | tar --null --no-recursion -T - -cf - | zstd -T0 -3 -q -o "$out"
  echo "packed $(du -h "$out" | cut -f1) in $((SECONDS - start)) s"
  echo pack=true >> "$GITHUB_OUTPUT"
  echo "name=$name" >> "$GITHUB_OUTPUT"
  ;;
*)
  sed -n 2,17p "$self"
  exit 2
  ;;
esac
