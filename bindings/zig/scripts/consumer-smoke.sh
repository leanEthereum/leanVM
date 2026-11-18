#!/bin/sh
# Prove a packaged tarball works as a dependency: a fresh project fetches it with
# `zig fetch --save`, imports the `lean_pq` module, and runs the README example.
set -eu

if [ "$#" -ne 1 ]; then
    echo "usage: $0 PACKAGE_TARBALL" >&2
    exit 64
fi

tarball=$(CDPATH= cd -- "$(dirname -- "$1")" && pwd)/$(basename -- "$1")
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
readme="$script_dir/../README.md"
project=$(mktemp -d)
trap 'rm -rf "$project"' EXIT

cd "$project"
zig init >/dev/null
rm -f src/root.zig
zig fetch --save=lean_pq "$tarball"

cat > build.zig <<'EOF'
const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const lean_pq = b.dependency("lean_pq", .{ .target = target, .optimize = optimize });
    const exe = b.addExecutable(.{
        .name = "consumer",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "lean_pq", .module = lean_pq.module("lean_pq") }},
        }),
    });
    b.installArtifact(exe);
}
EOF

# The README's example is the program: it asserts its own results.
sed -n '/^## Example$/,/^## /p' "$readme" | sed -n '/^```zig$/,/^```$/p' | sed '1d;$d' > src/main.zig
test -s src/main.zig

zig build -Doptimize=ReleaseSafe
./zig-out/bin/consumer
echo "consumer built and ran against $(basename -- "$tarball")"
