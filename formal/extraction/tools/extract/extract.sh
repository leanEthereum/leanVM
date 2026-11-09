#!/usr/bin/env bash
#
# Regenerate each extracted crate's Lean from the Rust in ../../crates, and check it.
# Ported from Plonky3-lean's script of the same name.
# The generated Lean is committed, so `lake build` alone checks the proofs.
#
#   0. check (never install) the pinned hax, charon, aeneas, Rust toolchain and Lean
#   1. apply the pre-extraction patches and `cargo check` the crates for the extraction target
#   2. run `cargo hax into lean` on each crate not in state `stub`
#   3. revert the pre-extraction patches, also on failure
#   4. check each hand-written Assumptions/*External.lean against aeneas's template, and install
#   5. apply the post-extraction patches
#   6. `lake build`, whose warnings must be exactly known-warnings.txt
#
# With --check, re-extraction must leave crates/*/extraction/ as committed.
#
# Usage:  tools/extract/extract.sh [--tools-only] [--check]
#
# Environment:
#   HAX_BIN      the cargo-hax to use (default: `cargo-hax` on PATH)
#   EXTRACT_DIR  scratch space (default: .lake/extract)

set -eu

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
RUST="$(cd "$ROOT/../.." && pwd)"
CONFIG="$HERE/config.py"
WORK="${EXTRACT_DIR:-$ROOT/.lake/extract}"

TOOLS_ONLY=0
CHECK=0
while [ "$#" -gt 0 ]; do
    case "$1" in
        --tools-only) TOOLS_ONLY=1 ;;
        --check) CHECK=1 ;;
        -h|--help) sed -n '2,/^set -eu/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
        *) echo "error: unknown argument '$1' (try --help)" >&2; exit 2 ;;
    esac
    shift
done

tc() { python3 -I "$CONFIG" toolchain "$1"; }
HAX_RELEASE="$(tc hax_release)"
HAX_COMMIT="$(tc hax_commit)"
if [ -n "$HAX_RELEASE" ]; then
    HAX_NAME="hax $HAX_RELEASE"
    HAX_INSTALL="cargo install --locked cargo-hax@$HAX_RELEASE --force"
    HAX_ID_RE="version=$HAX_RELEASE|commit=$HAX_COMMIT"
else
    HAX_NAME="hax at ${HAX_COMMIT:0:7}"
    HAX_INSTALL="cargo install --locked --git https://github.com/cryspen/hax --rev $HAX_COMMIT cargo-hax --force"
    HAX_ID_RE="commit=$HAX_COMMIT"
fi
EXPECT_CHARON="$(tc charon)"
EXPECT_AENEAS="$(tc aeneas)"
CHARON_TOOLCHAIN="$(tc rust_toolchain)"
CHARON_COMPONENTS="$(tc rust_components | tr ' ' ',')"
HAX_TARGET="$(tc target)"
EXTRACT_RUSTFLAGS="$(tc rustflags)"

# --- 0. tools -----------------------------------------------------------------------------------
echo "==> 0/6 tools"

missing() {   # missing <what> <install command>
    echo "error: $1 is missing. Install it (see docs/extracting.md):" >&2
    echo "       $2" >&2
    exit 1
}

for cmd in rustup cargo lake python3 patch git; do
    command -v "$cmd" >/dev/null 2>&1 || missing "'$cmd'" "see docs/extracting.md"
done

rustup target list --toolchain "$CHARON_TOOLCHAIN" --installed 2>/dev/null | grep -qx "$HAX_TARGET" \
    && rustup component list --toolchain "$CHARON_TOOLCHAIN" --installed 2>/dev/null | grep -q '^rustc-dev' \
    || missing "Rust $CHARON_TOOLCHAIN with $CHARON_COMPONENTS and $HAX_TARGET" \
        "rustup toolchain install $CHARON_TOOLCHAIN --profile minimal --component $CHARON_COMPONENTS --target $HAX_TARGET"
echo "    rust     $CHARON_TOOLCHAIN (for charon), target $HAX_TARGET"

HAX_BIN="${HAX_BIN:-cargo-hax}"
hax_id="$("$HAX_BIN" hax --version 2>/dev/null || true)"
if ! printf '%s\n' "$hax_id" | grep -qxE "$HAX_ID_RE"; then
    if [ -z "$hax_id" ]; then
        echo "error: $HAX_BIN not found." >&2
    else
        echo "error: $HAX_BIN is not $HAX_NAME ($(printf '%s\n' "$hax_id" | grep -m1 '^version=')):" >&2
    fi
    echo "       $HAX_INSTALL" >&2
    exit 1
fi
echo "    hax      $HAX_NAME ($(command -v "$HAX_BIN"))"

# hax resolves the pinned charon and aeneas, and has fetched them.
# The Lean pins must agree: the generated code and its libraries come from one aeneas build.
shown="$(cd "$RUST" && "$HAX_BIN" hax tools show)"
fetched="$("$HAX_BIN" hax tools list 2>/dev/null)"
for tool in "charon $EXPECT_CHARON" "aeneas $EXPECT_AENEAS"; do
    printf '%s\n' "$fetched" | awk -v t="${tool%% *}:" -v v="${tool#* }" \
        '$1 == t { in_t = 1; next } /^[a-z]+:$/ { in_t = 0 }
         in_t && $1 == v && /installed/ { found = 1 } END { exit !found }' \
        || missing "hax's ${tool%% *} ${tool#* }" "cargo hax tools install"
done

resolved() { printf '%s\n' "$shown" | awk -v t="$1" '$1 == t { print $2; exit }'; }
lake_rev() {   # the `rev` of the [[require]] named $1 in lakefile.toml
    awk -v n="$1" '/^\[\[require\]\]/ { hit = 0 }
                   $0 ~ "^name = \"" n "\"" { hit = 1 }
                   hit && /^rev = / { gsub(/"/, "", $3); print $3; exit }' "$ROOT/lakefile.toml"
}
pin_fail=0
check_pin() {   # check_pin <what> <actual> <expected>
    if [ "$2" != "$3" ]; then
        echo "error: $1 is '$2', expected '$3'." >&2
        pin_fail=1
    fi
}
check_pin "charon (cargo hax tools show)" "$(resolved charon)" "$EXPECT_CHARON"
check_pin "aeneas (cargo hax tools show)" "$(resolved aeneas)" "$EXPECT_AENEAS"
check_pin "lakefile.toml's aeneas rev" "$(lake_rev aeneas)" "$(resolved aeneas)"
check_pin "lakefile.toml's hax rev" "$(lake_rev hax)" "$(resolved hax-lean-lib)"
check_pin "lean-toolchain" "$(cat "$ROOT/lean-toolchain")" "$(resolved lean)"
if [ "$pin_fail" -ne 0 ]; then
    echo "       Look for a hax.toml above the repository, or move the pins in toolchain.toml," >&2
    echo "       lakefile.toml and lean-toolchain together (docs/extracting.md)." >&2
    exit 1
fi
echo "    charon   $EXPECT_CHARON, aeneas $EXPECT_AENEAS"
echo "    lean     $(cat "$ROOT/lean-toolchain")"

[ "$TOOLS_ONLY" = "0" ] || exit 0

# Crates to extract: every crate whose state is not `stub`.
CRATES="$(python3 -I "$CONFIG" crates | awk -F'|' '$3 != "stub"')"
if [ -z "$CRATES" ]; then
    echo "Nothing to extract: every crate is a stub."
    exit 0
fi

# --- the patch applier, shared by both phases -----------------------------------------------------
# `patch -F0` forbids fuzz, so context drift fails instead of applying somewhere plausible.
# Line-number offsets are tolerated.
PATCH_FLAGS="-p1 -F0 --no-backup-if-mismatch"

# Apply the ordered set listed in $1 in the root $2, all or nothing, recording each applied patch
# in $3 (or nowhere, if $3 is "").
apply_set() {
    local list="$1" root="$2" record="$3" pf
    if [ ! -s "$list" ]; then
        echo "    none"
        return 0
    fi
    while read -r pf; do
        if ! patch $PATCH_FLAGS --dry-run -d "$root" < "$pf" >/dev/null 2>&1; then
            echo "error: ${pf#"$ROOT"/} does not apply cleanly." >&2
            return 1
        fi
        patch $PATCH_FLAGS -d "$root" < "$pf" >/dev/null
        [ -z "$record" ] || echo "$pf" >> "$record"
        echo "    ${pf#"$ROOT"/crates/}"
    done < "$list"
}

# Reverted on EXIT, so an aborted run never leaves the crates modified.
# Exactly what was applied is reversed, in reverse order.
# Never `git checkout`, which would discard unrelated work.
PRE_RECORD="$(mktemp)"
PRE_LIST="$(mktemp)"
revert_pre_patches() {
    [ -s "$PRE_RECORD" ] || return 0
    local ok=1 pf
    for pf in $( (tail -r "$PRE_RECORD" 2>/dev/null || tac "$PRE_RECORD") ); do
        patch $PATCH_FLAGS -R -d "$RUST" < "$pf" >/dev/null || ok=0
    done
    : > "$PRE_RECORD"
    if [ "$ok" = "1" ]; then
        echo "    reverted pre-extraction patches"
    else
        echo "ERROR: could not revert the pre-extraction patches; the crates are left MODIFIED:" >&2
        echo "       inspect 'git status crates' before building." >&2
    fi
}
cleanup() { revert_pre_patches; rm -f "$PRE_RECORD" "$PRE_LIST"; }
trap cleanup EXIT

echo "==> 1/6 pre-extraction patches and cargo check ($HAX_TARGET, $EXTRACT_RUSTFLAGS)"
python3 -I "$CONFIG" pre-patches > "$PRE_LIST"
if [ -s "$PRE_LIST" ]; then
    echo "    WARNING: patching Rust source changes the artifact under verification." >&2
fi
apply_set "$PRE_LIST" "$RUST" "$PRE_RECORD"
packages="$(printf '%s\n' "$CRATES" | cut -d'|' -f1 | while read -r c; do
    printf -- '-p %s ' "$(python3 -I "$CONFIG" package "$c")"; done)"
# RUSTFLAGS replaces the repository's `-C target-cpu=native`, which names the host.
(cd "$RUST" && env RUSTUP_TOOLCHAIN="$CHARON_TOOLCHAIN" RUSTFLAGS="$EXTRACT_RUSTFLAGS" \
    CARGO_TARGET_DIR="$WORK/target-check" cargo check --quiet --target "$HAX_TARGET" $packages)
echo "    cargo check: ok"

echo "==> 2/6 extracting with hax (charon + aeneas, target $HAX_TARGET)"
# Each crate gets a fresh output directory, so a removed item cannot linger. aeneas exits
# non-zero on any translation error, and a partial file is not worth building.
rm -rf "$WORK/out"
printf '%s\n' "$CRATES" | while IFS='|' read -r crate lib state; do
    echo "    $crate ($state) -> $lib/Extraction/"
    out="$WORK/out/$crate"
    mkdir -p "$out"
    args="$(python3 -I "$CONFIG" charon-args "$crate")"
    src="$(python3 -I "$CONFIG" source "$crate")"
    (cd "$src" && RUSTFLAGS="$(python3 -I "$CONFIG" rustflags "$crate")" CARGO_TARGET_DIR="$WORK/target-hax" \
        "$HAX_BIN" hax into --output-dir "$out" lean --charon-args="$args" 2>&1 \
        | tee "$WORK/hax-$crate.log"; exit "${PIPESTATUS[0]}")
done

echo "==> 3/6 restoring the crates"
revert_pre_patches

echo "==> 4/6 checking each Assumptions/ against the regenerated templates; installing"
# aeneas writes a template of the declarations the generated code expects someone to supply.
# Each hand-written Assumptions/ file must declare exactly the template's names.
# `lake build` then checks their signatures.
# An `axiom` is refused: assumptions are `opaque` constants.
decl_names() {
    [ -f "$1" ] || return 0
    sed -nE 's/^(noncomputable )?(axiom|opaque|def|abbrev|structure|inductive|class) ([^ :({]+).*/\3/p' "$1" | sort -u
}
stub_fail=0
while IFS='|' read -r crate lib state; do
    gen="$WORK/out/$crate/$lib/Extraction"
    [ -d "$gen" ] || { echo "error: hax wrote no $lib/Extraction/ for $crate" >&2; exit 1; }
    for tpl in "$gen/"*External_Template.lean; do
        [ -e "$tpl" ] || continue
        stub="$(basename "$tpl" _Template.lean)"
        mine="$ROOT/crates/$crate/extraction/$lib/Assumptions/$stub.lean"
        rel="crates/$crate/extraction/$lib/Assumptions/$stub.lean"
        if [ ! -f "$mine" ]; then
            echo "error: $rel is missing. Write it from ${stub}_Template.lean, each hole an \`opaque\` constant." >&2
            stub_fail=1
        elif grep -qE '^axiom ' "$mine"; then
            echo "error: $rel states an axiom; make it an \`opaque\` constant." >&2
            stub_fail=1
        elif [ "$(decl_names "$tpl")" != "$(decl_names "$mine")" ]; then
            echo "error: $rel is out of date with the extraction:" >&2
            diff <(decl_names "$tpl") <(decl_names "$mine") \
                | sed -n 's/^< /         needed, not declared: /p; s/^> /         declared, no longer needed: /p' >&2
            stub_fail=1
        fi
    done
done <<< "$CRATES"
[ "$stub_fail" -eq 0 ] || exit 1
while IFS='|' read -r crate lib state; do
    dest="$ROOT/crates/$crate/extraction/$lib"
    rm -rf "$dest/Extraction" "$dest/Extraction.lean"
    mkdir -p "$dest/Extraction"
    cp "$WORK/out/$crate/$lib/Extraction"/*.lean "$dest/Extraction/"
    cp "$WORK/out/$crate/$lib/Extraction.lean" "$dest/Extraction.lean"
done <<< "$CRATES"
echo "    ok"

echo "==> 5/6 post-extraction patches (generated Lean)"
while IFS='|' read -r crate lib state; do
    list="$(mktemp)"
    ls "$ROOT/crates/$crate/patches/post/"[0-9]*.patch 2>/dev/null > "$list" || true
    apply_set "$list" "$ROOT/crates/$crate" ""
    rm -f "$list"
done <<< "$CRATES"

echo "==> 6/6 lake build"
(cd "$ROOT" && lake exe cache get >/dev/null 2>&1) || echo "note: 'lake exe cache get' failed" >&2
build_log="$(mktemp)"
if ! (cd "$ROOT" && lake build 2>&1 | tee "$build_log"; exit "${PIPESTATUS[0]}"); then
    echo "error: lake build failed. Fix the failing patch, or the Assumptions/ it names." >&2
    rm -f "$build_log"
    exit 1
fi
# Every warning must be listed, and every listed one must still occur, so the list cannot go stale.
# A warning is compared as `<file>: <message>`, without its position.
seen="$(sed -nE 's/^warning: ([^:]+):[0-9]+:[0-9]+: (.*)$/\1: \2/p' "$build_log" | sort -u)"
known="$(grep -v '^#' "$ROOT/known-warnings.txt" | sed '/^[[:space:]]*$/d' | sort -u)"
rm -f "$build_log"
new_w="$(comm -23 <(printf '%s\n' "$seen" | sed '/^$/d') <(printf '%s\n' "$known" | sed '/^$/d'))"
gone_w="$(comm -13 <(printf '%s\n' "$seen" | sed '/^$/d') <(printf '%s\n' "$known" | sed '/^$/d'))"
if [ -n "$new_w" ] || [ -n "$gone_w" ]; then
    [ -z "$new_w" ] || { echo "error: warnings not in known-warnings.txt:" >&2; printf '  %s\n' "$new_w" >&2; }
    [ -z "$gone_w" ] || { echo "error: known-warnings.txt lists warnings no longer printed:" >&2; printf '  %s\n' "$gone_w" >&2; }
    exit 1
fi

if [ "$CHECK" = "1" ]; then
    echo "==> check: re-extraction is byte-identical to the committed output"
    spec=':(glob)crates/*/extraction/**'
    if ! (cd "$ROOT" && git diff --quiet -- "$spec" \
            && [ -z "$(git ls-files --others --exclude-standard -- "$spec")" ]); then
        (cd "$ROOT" && git status --short -- "$spec") >&2
        echo "error: re-extraction changed the committed output above." >&2
        exit 1
    fi
    echo "    ok"
fi

echo "Done. The extraction type-checks, and so do the proofs about it."
