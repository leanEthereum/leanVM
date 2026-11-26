#!/usr/bin/env bash
# The Rust-to-Lean extraction of the crates that declare a hax scenario (crates/<crate>/hax.toml).
#
#   hax.sh setup               install the pinned cargo-hax, the charon and aeneas it resolves
#                              (hax.toml), and the Rust toolchain charon builds with
#   hax.sh extract [args]      regenerate every extraction; args go to `cargo hax extract`
#                              (scenario names, `-p <crate>`)
#   hax.sh check [args]        extract, then build every extraction in Lean and print what each
#                              takes on trust (report.sh); fails on a build error or a `sorry`
#   hax.sh patched <cmd...>    run a command on the patched source, e.g. `cargo test -p verifier`
#   hax.sh test                clippy and the tests of every patched crate, on the patched source:
#                              `cargo test -p <crate>`, or each line of patches/pre/tests as its args
#   hax.sh refresh [--from REV]  rebase the pre/ patches onto HEAD after the source changed under
#                              them: replay them as commits on the last first-parent commit they
#                              apply to (or REV), `git rebase` those onto HEAD, write them back
#   hax.sh refresh --continue  after resolving a conflict the rebase stopped on
#   hax.sh refresh --skip      drop the patch the rebase stopped on, its rewrite no longer needed
#   hax.sh refresh --abort     drop a refresh in progress
#
# A scenario's patches live in crates/<crate>/proofs/<scenario>/patches. Those in pre/ rewrite
# the Rust source, only for the length of `extract` or `patched`: the committed source never
# carries them. Before them goes the patch mechanical.py generates: the rewrites that recur all
# over the crates (tracing spans out, anonymous constants named). Those in post/ (a last resort)
# rewrite the generated Lean after every extraction.
# Each extraction is then wired into the workspace in formal/extraction (wire.py). Nothing an
# extraction writes is committed: the Lean packages and the workspace's lakefile are gitignored.
set -euo pipefail

# cargo-hax is installed from this commit of https://github.com/cryspen/hax (0.4.2 and later
# fixes); charon, aeneas and the Lean libraries are pinned in the root hax.toml.
HAX_REV=721d1a2710b1d7020a0b32de7291fe791885d215

root=$(git rev-parse --show-toplevel)
cd "$root"

# The extraction models the portable code paths, the same on every host: the hardware features
# the crates dispatch on are off (on x86-64 they are off by default, with `target-cpu=native`
# overridden), so each `cfg(target_feature)` choice takes its fallback. The tests run on these
# paths too, the ones the extraction and its patches describe.
case "$(uname -m)" in
  arm64 | aarch64) export RUSTFLAGS="-C target-feature=-aes,-sha2,-sha3" ;;
  *) export RUSTFLAGS="" ;;
esac
export RUSTDOCFLAGS="$RUSTFLAGS" # doctests build with these

usage() {
  awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"
  exit 2
}

setup() {
  if ! cargo hax --version 2>/dev/null | grep -q "${HAX_REV:0:10}"; then
    cargo install --locked --force --git https://github.com/cryspen/hax --rev "$HAX_REV" cargo-hax
  fi
  cargo hax tools install
  local version charon
  version=$(cargo hax tools show | awk '$1 == "charon" { print $2; exit }')
  charon="${XDG_CACHE_HOME:-$HOME/.cache}/hax/tools/charon/$version/charon"
  rustup toolchain install "$("$charon" toolchain-version)" --profile minimal \
    --component rustc-dev,llvm-tools,rust-src,miri # miri builds charon's full-MIR standard library
}

applied=()
revert() {
  for ((i = ${#applied[@]} - 1; i >= 0; i--)); do
    git apply -R "${applied[i]}"
  done
  applied=()
}

# The mechanical rewrites are a generated patch (mechanical.py), applied before the
# hand-written ones, so code that moves under them stales no patch.
strip_patch="$root/target/hax-mechanical.patch"

# The generator as commit $1 has it (the one its patches were written against), or else the
# working tree's: a path to run.
generator_at() {
  local copy="$root/target/hax-mechanical-$1.py"
  if git show "$1:formal/extraction/mechanical.py" >"$copy" 2>/dev/null; then
    echo "$copy"
  else
    rm -f "$copy"
    echo "$root/formal/extraction/mechanical.py"
  fi
}

apply_patches() {
  trap revert EXIT
  shopt -s nullglob
  mkdir -p "$root/target"
  python3 formal/extraction/mechanical.py >"$strip_patch"
  if [[ -s "$strip_patch" ]]; then
    git apply "$strip_patch"
    applied+=("$strip_patch")
  fi
  for patch in crates/*/proofs/*/patches/pre/*.patch crates/*/*/proofs/*/patches/pre/*.patch; do
    if ! git apply "$patch"; then
      echo "error: $patch no longer applies to the Rust source; run formal/extraction/hax.sh refresh" >&2
      exit 1
    fi
    applied+=("$patch")
  done
}

extract() {
  apply_patches
  rm -f crates/*/proofs/*/lean/aeneas-error.log crates/*/*/proofs/*/lean/aeneas-error.log
  cargo hax extract "$@"
  revert
  for patch in crates/*/proofs/*/patches/post/*.patch crates/*/*/proofs/*/patches/post/*.patch; do
    if ! git apply "$patch"; then
      echo "error: $patch no longer applies to the generated Lean; refresh it (formal/extraction/README.md)" >&2
      exit 1
    fi
  done
  python3 formal/extraction/wire.py
}

check() {
  extract "$@"
  (cd formal/extraction && lake exe cache get && lake build)
  if grep -rlw sorry crates/*/proofs/*/lean/*/Extraction crates/*/*/proofs/*/lean/*/Extraction 2>/dev/null; then
    echo "error: Aeneas left a \`sorry\` in the files above; formal/extraction/repair.py extract marks such items opaque" >&2
    exit 1
  fi
  proofs
  formal/extraction/report.sh
}

# The proofs about the extractions (formal/extraction/proofs/<crate>): they build, by nothing but
# proof, and their end theorem rests on the axioms its `axioms` file lists and no others.
proofs() {
  local dir
  for dir in formal/extraction/proofs/*/; do
    (cd "$dir" && lake build)
    if grep -rnwE 'sorry|admit|native_decide|bv_decide|axiom|set_option|unsafe|implemented_by' "$dir" --include='*.lean' --exclude-dir=.lake; then
      echo "error: an escape in $dir, above" >&2
      exit 1
    fi
    if ! (cd "$dir" && lake env lean Axioms.lean | tr -d '\n ' | diff - <(tr -d '\n ' < axioms)); then
      echo "error: the axioms of $dir's theorem are not those in ${dir}axioms" >&2
      exit 1
    fi
  done
}

patched() {
  [[ $# -gt 0 ]] || usage
  apply_patches
  "$@"
}

test_patched() {
  apply_patches
  local runs=() dir crate line
  for dir in crates/*/proofs/*/patches/pre crates/*/*/proofs/*/patches/pre; do
    local patches=("$dir"/*.patch)
    [[ ${#patches[@]} -gt 0 ]] || continue
    crate=$(basename "${dir%%/proofs/*}")
    cargo clippy --release -p "$crate" --all-targets -- -D warnings
    if [[ -f "$dir/tests" ]]; then
      while read -r line; do
        [[ -z "$line" || "$line" == \#* ]] || runs+=("$line")
      done < "$dir/tests"
    else
      runs+=("-p $crate")
    fi
  done
  # A suite several crates name (the verifier's checks against real proofs) runs once.
  local args
  while read -r -a args; do
    cargo test --release "${args[@]}"
  done < <(printf '%s\n' "${runs[@]}" | awk '!seen[$0]++')
}

# The pre/ patches, in the order apply_patches applies them.
pre_patches() {
  local patch
  for patch in crates/*/proofs/*/patches/pre/*.patch crates/*/*/proofs/*/patches/pre/*.patch; do
    [[ -e "$patch" ]] && echo "$patch"
  done
}

# Whether the pre/ patches of the working tree apply, in order, to commit $1: checked in a scratch
# index, so nothing is checked out.
patches_apply_at() {
  local index strip patch status=0
  index=$(mktemp)
  strip=$(mktemp)
  GIT_INDEX_FILE=$index git read-tree "$1"
  python3 "$(generator_at "$1")" --rev "$1" >"$strip"
  if [[ -s "$strip" ]] && ! GIT_INDEX_FILE=$index git apply --cached "$strip" 2>/dev/null; then
    status=1
  fi
  rm -f "$strip"
  [[ $status -eq 0 ]] || { rm -f "$index"; return 1; }
  while read -r patch; do
    if ! GIT_INDEX_FILE=$index git apply --cached "$patch" 2>/dev/null; then
      status=1
      break
    fi
  done < <(pre_patches)
  rm -f "$index"
  return $status
}

# A refresh replays the patches as commits in this worktree and rebases them there, so the
# working tree of the repository is never touched; $refresh_state records the commit they go onto.
refresh_tree="$root/target/hax-refresh"
refresh_state="$root/target/hax-refresh.onto"
# The replayed commits stay in the scratch worktree, so they carry a fixed identity.
scratch_git() {
  GIT_AUTHOR_NAME=hax-refresh GIT_AUTHOR_EMAIL=hax-refresh@localhost \
    GIT_COMMITTER_NAME=hax-refresh GIT_COMMITTER_EMAIL=hax-refresh@localhost \
    git -C "$refresh_tree" -c rerere.enabled=true -c rerere.autoUpdate=true -c commit.gpgsign=false \
    -c advice.mergeConflict=false -c advice.resolveConflict=false -c merge.conflictStyle=zdiff3 "$@"
}

refresh() {
  local from=""
  case "${1:-}" in
    --continue | --skip)
      [[ -e "$refresh_state" ]] || { echo "error: no refresh in progress" >&2; exit 1; }
      if [[ "$1" == --continue ]] && git -C "$refresh_tree" diff --cached --check | grep 'conflict marker' >&2; then
        echo "error: a staged file still has conflict markers; resolve them and git add it again" >&2
        exit 1
      fi
      GIT_EDITOR=true scratch_git rebase "$1" || refresh_stopped
      refresh_export
      return
      ;;
    --abort)
      git worktree remove --force "$refresh_tree" 2>/dev/null || true
      rm -f "$refresh_state"
      return
      ;;
    --from) from=$(git rev-parse --verify "${2:?--from takes a revision}^{commit}") ;;
    "") ;;
    *) usage ;;
  esac
  if [[ -e "$refresh_state" ]]; then
    echo "error: a refresh is in progress in $refresh_tree: hax.sh refresh --continue or --abort" >&2
    exit 1
  fi
  if [[ -n "$(git status --porcelain -- 'crates/*/proofs/*/patches/pre' 'crates/*/*/proofs/*/patches/pre')" ]]; then
    echo "error: commit or stash the changes to the patches first; refresh rewrites them" >&2
    exit 1
  fi
  local onto commit patch
  onto=$(git rev-parse HEAD)
  if [[ -z "$from" ]]; then
    while read -r commit; do
      if patches_apply_at "$commit"; then
        from=$commit
        break
      fi
    done < <(git rev-list --first-parent --max-count=200 HEAD)
    if [[ -z "$from" ]]; then
      echo "error: the patches apply to none of the last 200 first-parent commits; name one with --from" >&2
      exit 1
    fi
  fi
  if [[ "$from" == "$onto" ]]; then
    echo "every patch applies to HEAD: nothing to refresh"
    return
  fi
  echo "replaying the patches on $(git log -1 --format='%h %s' "$from"), then rebasing them onto HEAD"
  mkdir -p "$root/target"
  git worktree add --quiet --detach "$refresh_tree" "$from"
  # The generated strip is regenerated on each side rather than rebased: the hand-written
  # patches go from the strip of $from to the strip of HEAD.
  local strip_from strip_onto tip
  strip_from=$(scratch_strip_commit "$from" "$(generator_at "$from")")
  scratch_git checkout --quiet --detach "$strip_from"
  while read -r patch; do
    scratch_git apply --index "$root/$patch"
    scratch_git commit --quiet --no-verify -m "$patch"
  done < <(pre_patches)
  tip=$(git -C "$refresh_tree" rev-parse HEAD)
  strip_onto=$(scratch_strip_commit "$onto" "$root/formal/extraction/mechanical.py")
  echo "$strip_onto" >"$refresh_state"
  scratch_git checkout --quiet --detach "$tip"
  scratch_git rebase --quiet --onto "$strip_onto" "$strip_from" || refresh_stopped
  refresh_export
}

# A commit on $1 of the patch generator $2 makes, in the scratch worktree.
scratch_strip_commit() {
  scratch_git checkout --quiet --detach "$1"
  (cd "$refresh_tree" && python3 "$2" >"$strip_patch")
  if [[ -s "$strip_patch" ]]; then
    scratch_git apply --index "$strip_patch"
  fi
  scratch_git commit --quiet --no-verify --allow-empty -m "generated: mechanical.py"
  git -C "$refresh_tree" rev-parse HEAD
}

# The rebase stopped on a conflict. If rerere resolved every file from an earlier refresh, go
# on; otherwise say where it stopped, and how to go on.
refresh_stopped() {
  local patch stuck=""
  while [[ -d "$(git -C "$refresh_tree" rev-parse --git-path rebase-merge)" ]] &&
    [[ -z "$(git -C "$refresh_tree" diff --name-only --diff-filter=U)" ]]; do
    patch=$(git -C "$refresh_tree" rev-parse REBASE_HEAD)
    [[ "$patch" != "$stuck" ]] || break # --continue made no progress: the patch is now empty
    stuck=$patch
    echo "$(git -C "$refresh_tree" log -1 --format=%s REBASE_HEAD): resolved as before (rerere)"
    if GIT_EDITOR=true scratch_git rebase --continue; then
      return 0
    fi
  done
  patch=$(git -C "$refresh_tree" log -1 --format=%s REBASE_HEAD 2>/dev/null || echo "?")
  echo >&2
  echo "error: $patch conflicts with the new source, in:" >&2
  git -C "$refresh_tree" diff --name-only --diff-filter=U | sed 's/^/  /' >&2
  cat >&2 <<EOF
Resolve them in $refresh_tree: keep the source's new code with the patch's rewrite on it
(the resolution is remembered, by rerere), \`git add\` the files, and run hax.sh refresh --continue.
A patch whose rewrite the new source no longer needs (its code is gone): hax.sh refresh --skip.
A hunk in code the source deleted: take the source's side, \`git checkout --ours <file>\`.
EOF
  exit 1
}

# Write each rebased commit back as its patch; a patch whose commit the rebase dropped is
# already in the source, and goes.
refresh_export() {
  local onto commit patch kept=()
  onto=$(cat "$refresh_state")
  while read -r commit; do
    patch=$(git -C "$refresh_tree" log -1 --format=%s "$commit")
    git -C "$refresh_tree" diff --no-color --no-ext-diff --src-prefix=a/ --dst-prefix=b/ \
      "$commit^" "$commit" >"$root/$patch"
    kept+=("$patch")
  done < <(git -C "$refresh_tree" rev-list --reverse "$onto..HEAD")
  while read -r patch; do
    if [[ ! " ${kept[*]} " == *" $patch "* ]]; then
      rm "$patch"
      echo "dropped $patch: the source now does what it did"
    fi
  done < <(pre_patches)
  git worktree remove --force "$refresh_tree"
  rm -f "$refresh_state"
  echo "refreshed ${#kept[@]} patches; next, hax.sh extract and hax.sh test"
}

case "${1:-}" in
  setup) setup ;;
  refresh) shift; refresh "$@" ;;
  extract) shift; extract "$@" ;;
  check) shift; check "$@" ;;
  patched) shift; patched "$@" ;;
  test) test_patched ;;
  *) usage ;;
esac
