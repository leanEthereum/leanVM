const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const native_dir = b.option(
        []const u8,
        "native-dir",
        "Directory containing liblean_pq_native.a (default: the archive bundled for the target)",
    );

    const lean_pq = b.addModule("lean_pq", .{
        .root_source_file = b.path("src/lean_pq.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });
    lean_pq.addIncludePath(b.path("include"));
    lean_pq.addLibraryPath(nativePath(b, target.result, native_dir));
    lean_pq.linkSystemLibrary("lean_pq_native", .{ .preferred_link_mode = .static });
    lean_pq.linkSystemLibrary("m", .{});
    if (target.result.os.tag == .linux) {
        lean_pq.linkSystemLibrary("dl", .{});
        lean_pq.linkSystemLibrary("pthread", .{});
        lean_pq.linkSystemLibrary("unwind", .{});
    } else if (target.result.os.tag == .macos) {
        lean_pq.linkFramework("Foundation", .{});
    } else if (target.result.os.tag == .windows) {
        // The Rust standard library's imports (`--print native-static-libs`), its unwinder, and the
        // API set that exports WaitOnAddress/WakeByAddress*, which the archive's own import stubs do
        // not always satisfy at link time. Zig's Windows distribution has no `synchronization.def`.
        for ([_][]const u8{ "kernel32", "ntdll", "userenv", "ws2_32", "dbghelp", "api-ms-win-core-synch-l1-2-0", "unwind" }) |name| {
            lean_pq.linkSystemLibrary(name, .{});
        }
    }

    const tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/lean_pq_test.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "lean_pq", .module = lean_pq }},
        }),
    });
    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run Zig binding tests");
    test_step.dependOn(&run_tests.step);
}

/// The directory to link `liblean_pq_native.a` from: `-Dnative-dir` when given, otherwise the
/// archive a release package bundles for the target.
fn nativePath(b: *std.Build, target: std.Target, native_dir: ?[]const u8) std.Build.LazyPath {
    if (native_dir) |dir| {
        return if (std.fs.path.isAbsolute(dir)) .{ .cwd_relative = dir } else b.path(dir);
    }
    const bundled = bundledNativeDir(target) orelse std.debug.panic(
        "lean_pq bundles no native archive for {s}-{s}-{s}; pass -Dnative-dir",
        .{ @tagName(target.cpu.arch), @tagName(target.os.tag), @tagName(target.abi) },
    );
    return b.path(bundled);
}

fn bundledNativeDir(target: std.Target) ?[]const u8 {
    return switch (target.os.tag) {
        .linux => if (!target.abi.isGnu()) null else switch (target.cpu.arch) {
            .x86_64 => "native/x86_64-linux-gnu",
            .aarch64 => "native/aarch64-linux-gnu",
            else => null,
        },
        .macos => switch (target.cpu.arch) {
            .x86_64, .aarch64 => "native/universal-macos",
            else => null,
        },
        // A MinGW archive; `x86_64-windows-gnu` is Zig's native target on Windows.
        .windows => if (target.abi.isGnu() and target.cpu.arch == .x86_64) "native/x86_64-windows-gnu" else null,
        else => null,
    };
}
