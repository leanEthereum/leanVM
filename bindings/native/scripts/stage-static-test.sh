#!/bin/sh
# Verify staging builds only the staticlib with cargo-zigbuild, combines the two Apple
# architectures for universal2, and preserves the target-specific layout.
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
tmp_dir=$(mktemp -d)
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

mkdir -p "$tmp_dir/bin"
cat > "$tmp_dir/bin/cargo-zigbuild" <<'EOF'
#!/bin/sh
set -eu

printf '%s\n' "$*" >> "$TEST_CALLS"

target=
while [ "$#" -gt 0 ]; do
    if [ "$1" = "--target" ]; then
        target=$2
        break
    fi
    shift
done

mkdir -p "$CARGO_TARGET_DIR/$target/release"
printf '%s' "$target" > "$CARGO_TARGET_DIR/$target/release/liblean_pq_native.a"
EOF
cat > "$tmp_dir/bin/lipo" <<'EOF'
#!/bin/sh
set -eu

printf 'lipo %s\n' "$*" >> "$TEST_CALLS"
test "$1" = "-create"
test "$2" = "-output"
cat "$4" "$5" > "$3"
EOF
chmod +x "$tmp_dir/bin/cargo-zigbuild" "$tmp_dir/bin/lipo"

stage() {
    target=$1
    archive_dir="$tmp_dir/$target"
    calls="$tmp_dir/$target.calls"

    CARGO_TARGET_DIR="$tmp_dir/target" \
        TEST_CALLS="$calls" \
        PATH="$tmp_dir/bin:$PATH" \
        sh "$script_dir/stage-static.sh" "$target" "$archive_dir"

    test -f "$archive_dir/liblean_pq_native.a"
}

expect_build() {
    calls=$1
    line=$2
    target=$3
    test "$(sed -n "${line}p" "$calls")" = \
        "rustc --manifest-path $(CDPATH= cd -- "$script_dir/.." && pwd)/Cargo.toml --release --target $target --crate-type staticlib"
}

for target in x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu x86_64-pc-windows-gnu; do
    stage "$target"
    test "$(wc -l < "$tmp_dir/$target.calls")" -eq 1
    expect_build "$tmp_dir/$target.calls" 1 "$target"
    test "$(cat "$tmp_dir/$target/liblean_pq_native.a")" = "$target"
done

stage universal2-apple-darwin
calls="$tmp_dir/universal2-apple-darwin.calls"
test "$(wc -l < "$calls")" -eq 3
expect_build "$calls" 1 x86_64-apple-darwin
expect_build "$calls" 2 aarch64-apple-darwin
sed -n '3p' "$calls" | grep -q '^lipo -create -output '
test "$(cat "$tmp_dir/universal2-apple-darwin/liblean_pq_native.a")" = "x86_64-apple-darwinaarch64-apple-darwin"
echo "stage-static checks passed"
