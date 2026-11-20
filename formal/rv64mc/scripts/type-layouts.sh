#!/usr/bin/env bash
# Writes Rv64mc/Gen/Layouts.lean: the layouts rustc gives the types layouts.txt names, for the guest as regen.sh builds
# it (the guest's sources and rustflags, the no_std copy of $VERIFIER_SRC, default crates/verifier, a fresh directory).
#
#   scripts/type-layouts.sh [--check]
#
# Two sources, both rustc's: `-Zprint-type-sizes` on a release build of the guest (the field names and offsets of
# alloc's types, which no module can name), and `#[rustc_dump_layout(debug)]` on an alias of each other type, added to
# a copy of its module and type-checked (sizes, field offsets, and an enum's tag and encoding, which
# `-Zprint-type-sizes` does not print). Neither changes a layout: they only print it.
# --check writes nothing and exits 1 if Layouts.lean would change.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
check=
case ${1:-} in
  --check) check=--check ;;
  "") ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac
mkdir -p "$here/out"
tmp=$(mktemp -d "$here/out/layouts.XXXXXX")
# LAYOUTS_KEEP=1 keeps the directory, to rerun `type-layouts.py gen` on its outputs.
[ -n "${LAYOUTS_KEEP:-}" ] || trap 'rm -rf "${tmp:?}"' EXIT
b=$tmp/guest
fresh() {
  rm -rf "$b/src" "$b/verifier-nostd"
  mkdir -p "$b"
  (cd "$here/guest" && cp -r .cargo Cargo.toml Cargo.lock build.rs link.x rust-toolchain.toml src "$b/")
  "$here/scripts/nostd-verifier.sh" "$b/verifier-nostd" >/dev/null
}
flags() {
  python3 -I -c 'import sys, tomllib
c = tomllib.load(open(sys.argv[1], "rb"))
print("\x1f".join(c["target"]["riscv64im-unknown-none-elf"]["rustflags"] + sys.argv[2:]))' "$b/.cargo/config.toml" "$@"
}
cargo_in() {
  (cd "$b" && CARGO_ENCODED_RUSTFLAGS=$1 CARGO_TARGET_DIR=$b/target timeout 1800 cargo "${@:2}")
}
fresh
cargo_in "$(flags -Z print-type-sizes)" build --release >"$tmp/pts.txt" 2>"$tmp/build.log" ||
  { tail -20 "$tmp/build.log"; exit 1; }
# Each check fails by design: every dumped layout is an error.
python3 -I "$here/scripts/type-layouts.py" probe "$here/layouts.txt" "$b/verifier-nostd/src" "$b/src/main.rs" lib
cargo_in "$(flags)" check --release -p verifier 2>"$tmp/dump.txt" && { echo "the probes printed nothing" >&2; exit 1; }
fresh
python3 -I "$here/scripts/type-layouts.py" probe "$here/layouts.txt" "$b/verifier-nostd/src" "$b/src/main.rs" main
cargo_in "$(flags)" check --release --bin verifier-rv64 2>>"$tmp/dump.txt" && { echo "the probes printed nothing" >&2; exit 1; }
python3 -I "$here/scripts/type-layouts.py" gen "$here/layouts.txt" "$b/verifier-nostd/src" "$b/src/main.rs" \
  "$tmp/pts.txt" "$tmp/dump.txt" "$here/Rv64mc/Gen/Layouts.lean" $check
