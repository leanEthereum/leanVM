const std = @import("std");
const builtin = @import("builtin");
const lpq = @import("lean_pq");

const message: lpq.Message = [_]u8{0x42} ** 32;
const other_message: lpq.Message = [_]u8{0x43} ** 32;

test "leanXMSS signs and verifies" {
    var key = try lpq.XmssSecretKey.fromSeed([_]u8{1} ** 32);
    defer key.deinit();
    const public_key = try key.publicKey();
    try key.prepare(7);
    const signature = try key.sign(message, 7);

    try lpq.xmssVerify(public_key, message, &signature);
    try std.testing.expectError(error.InvalidSignature, lpq.xmssVerify(public_key, other_message, &signature));
}

test "leanSPHINCS signs and verifies" {
    const seed: lpq.Seed = [_]u8{2} ** 32;
    var key = try lpq.SphincsSecretKey.fromSeed(seed);
    defer key.deinit();
    try std.testing.expectEqual(seed, try key.toBytes());
    const public_key = try key.publicKey();
    const signature = try key.sign(message);

    try lpq.sphincsVerify(public_key, message, &signature);
    try std.testing.expectError(error.InvalidSignature, lpq.sphincsVerify(public_key, other_message, &signature));
}

test "leanXMSS key loads from its tree cache" {
    const allocator = std.testing.allocator;
    const seed: lpq.Seed = [_]u8{6} ** 32;
    var key = try lpq.XmssSecretKey.fromSeed(seed);
    defer key.deinit();
    try key.prepare(3);
    const cache = try key.cacheToBytes(allocator);
    defer allocator.free(cache);

    const public_key = try key.publicKey();
    var loaded = try lpq.XmssSecretKey.fromCacheBytes(seed, public_key, cache);
    defer loaded.deinit();
    try std.testing.expectEqual(public_key, try loaded.publicKey());
    const signature = try loaded.sign(message, 3);
    try std.testing.expectEqual(try key.sign(message, 3), signature);
    try lpq.xmssVerify(public_key, message, &signature);

    try std.testing.expectError(error.NativeFailure, lpq.XmssSecretKey.fromCacheBytes(seed, public_key, cache[1..]));
    const tampered = try allocator.dupe(u8, cache);
    defer allocator.free(tampered);
    tampered[0] ^= 1;
    try std.testing.expectError(error.NativeFailure, lpq.XmssSecretKey.fromCacheBytes(seed, public_key, tampered));
    var other = try lpq.XmssSecretKey.fromSeed([_]u8{7} ** 32);
    defer other.deinit();
    try std.testing.expectError(error.NativeFailure, lpq.XmssSecretKey.fromCacheBytes(seed, try other.publicKey(), cache));
}

test "secret keys round trip through bytes" {
    var xmss = try lpq.XmssSecretKey.generate();
    defer xmss.deinit();
    var xmss_restored = try lpq.XmssSecretKey.fromBytes(&try xmss.toBytes());
    defer xmss_restored.deinit();
    try std.testing.expectEqual(try xmss.publicKey(), try xmss_restored.publicKey());

    var sphincs = try lpq.SphincsSecretKey.generate();
    defer sphincs.deinit();
    const sphincs_bytes = try sphincs.toBytes();
    var sphincs_restored = try lpq.SphincsSecretKey.fromBytes(&sphincs_bytes);
    defer sphincs_restored.deinit();
    try std.testing.expectEqual(try sphincs.publicKey(), try sphincs_restored.publicKey());
    try std.testing.expectEqual(sphincs_bytes, try sphincs_restored.toBytes());
}

test "VRF key opens its slots" {
    const seed: lpq.Seed = [_]u8{9} ** 32;
    var key = try lpq.VrfKey.init(seed, 100, 200);
    defer key.deinit();
    var expected_root: lpq.VrfRoot = undefined;
    _ = try std.fmt.hexToBytes(&expected_root, "c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45");

    const root = try key.root();
    try std.testing.expectEqual(expected_root, root);

    const proof = try key.proof(150);
    try lpq.vrfVerify(root, 150, &proof);
    try std.testing.expectError(error.InvalidSignature, lpq.vrfVerify(root, 151, &proof));
    try lpq.vrfVerify(root, 100, &try key.proof(100));
    try lpq.vrfVerify(root, 199, &try key.proof(199));

    try std.testing.expectError(error.NativeFailure, key.proof(99));
    try std.testing.expectError(error.NativeFailure, key.proof(200));
    try std.testing.expectError(error.NativeFailure, lpq.VrfKey.init(seed, 5, 5));
    try std.testing.expectError(error.NativeFailure, lpq.VrfKey.init(seed, 0, (1 << 31) + 1));
}

test "VRF key loads from its cache" {
    const allocator = std.testing.allocator;
    const seed: lpq.Seed = [_]u8{9} ** 32;
    var key = try lpq.VrfKey.init(seed, 100, 200);
    defer key.deinit();
    const cache = try key.cacheToBytes(allocator);
    defer allocator.free(cache);

    var root: lpq.VrfRoot = undefined;
    _ = try std.fmt.hexToBytes(&root, "c7e3eaa5a1af5e528e56beb589b4d1c579f5fb8939ddd7f6b1ce2141bc096b45");
    var loaded = try lpq.VrfKey.fromCacheBytes(seed, root, cache);
    defer loaded.deinit();
    const reencoded = try loaded.cacheToBytes(allocator);
    defer allocator.free(reencoded);
    try std.testing.expectEqualSlices(u8, cache, reencoded);
    try lpq.vrfVerify(root, 150, &try loaded.proof(150));

    try std.testing.expectError(error.NativeFailure, lpq.VrfKey.fromCacheBytes(seed, root, cache[0 .. cache.len - 1]));
    try std.testing.expectError(error.NativeFailure, lpq.VrfKey.fromCacheBytes(seed, [_]u8{0} ** 32, cache));
}

fn requiredEnv(name: []const u8, meaning: []const u8) ![]const u8 {
    return std.testing.environ.getPosix(name) orelse {
        std.debug.print("set {s} to {s}\n", .{ name, meaning });
        return error.MissingEnvironmentVariable;
    };
}

fn expectLastError(expected: []const u8) !void {
    const reason = try lpq.lastError(std.testing.allocator);
    defer std.testing.allocator.free(reason);
    try std.testing.expectEqualStrings(expected, reason);
}

fn expectKnownProver(sidecar: *const lpq.Sidecar) !void {
    const prover = try sidecar.prover(std.testing.allocator);
    defer std.testing.allocator.free(prover);
    try std.testing.expect(std.mem.eql(u8, prover, "experimental") or std.mem.eql(u8, prover, "stable"));
}

test "aggregates recursively and round trips through bytes" {
    if (builtin.os.tag == .windows) return error.SkipZigTest;
    const allocator = std.testing.allocator;
    var sidecar = try lpq.Sidecar.connect(try requiredEnv("LEANVM_SIDECAR_SOCKET", "the socket of a running leanvm-sidecar"));
    defer sidecar.deinit();
    try expectKnownProver(&sidecar);

    var xmss_key = try lpq.XmssSecretKey.fromSeed([_]u8{3} ** 32);
    defer xmss_key.deinit();
    var sphincs_key = try lpq.SphincsSecretKey.fromSeed([_]u8{4} ** 32);
    defer sphincs_key.deinit();
    var extra_key = try lpq.XmssSecretKey.fromSeed([_]u8{5} ** 32);
    defer extra_key.deinit();
    const xmss_public_key = try xmss_key.publicKey();
    const sphincs_public_key = try sphincs_key.publicKey();
    const extra_public_key = try extra_key.publicKey();

    var xmss_leaf = try sidecar.aggregate(&.{}, &.{.{
        .public_key = xmss_public_key,
        .message = message,
        .signature = try xmss_key.sign(message, 0),
    }}, &.{});
    defer xmss_leaf.deinit();
    var sphincs_leaf = try sidecar.aggregate(&.{}, &.{}, &.{.{
        .public_key = sphincs_public_key,
        .message = message,
        .signature = try sphincs_key.sign(message),
    }});
    defer sphincs_leaf.deinit();
    var root = try sidecar.aggregate(&.{ &xmss_leaf, &sphincs_leaf }, &.{.{
        .public_key = extra_public_key,
        .message = other_message,
        .signature = try extra_key.sign(other_message, 0),
    }}, &.{});
    defer root.deinit();

    const encoded = try root.toBytes(allocator);
    defer allocator.free(encoded);

    const xmss_claim: lpq.Claim = .{ .public_key = xmss_public_key, .message = message };
    const extra_claim: lpq.Claim = .{ .public_key = extra_public_key, .message = other_message };
    const sphincs_claim: lpq.Claim = .{ .public_key = sphincs_public_key, .message = message };

    // The receiver lists the claims in any order; a repeated claim counts once.
    var restored = try sidecar.verify(encoded, &.{ extra_claim, xmss_claim, extra_claim }, &.{sphincs_claim});
    defer restored.deinit();

    var expected_xmss = [_]lpq.Claim{ xmss_claim, extra_claim };
    std.mem.sortUnstable(lpq.Claim, &expected_xmss, {}, claimLessThan);
    const xmss_claims = try restored.xmssClaims(allocator);
    defer allocator.free(xmss_claims);
    try std.testing.expectEqualSlices(lpq.Claim, &expected_xmss, xmss_claims);

    const sphincs_claims = try restored.sphincsClaims(allocator);
    defer allocator.free(sphincs_claims);
    try std.testing.expectEqualSlices(lpq.Claim, &.{sphincs_claim}, sphincs_claims);

    // The getters' claims are exactly what verifying needs.
    var reread = try sidecar.verify(encoded, xmss_claims, sphincs_claims);
    defer reread.deinit();
    const reencoded = try reread.toBytes(allocator);
    defer allocator.free(reencoded);
    try std.testing.expectEqualSlices(u8, encoded, reencoded);

    // The same proof does not prove any other claim set.
    const other_sphincs_claim: lpq.Claim = .{ .public_key = sphincs_public_key, .message = other_message };
    try std.testing.expectError(error.NativeFailure, sidecar.verify(encoded, &.{xmss_claim}, &.{sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, sidecar.verify(encoded, &.{ xmss_claim, extra_claim }, &.{}));
    try std.testing.expectError(error.NativeFailure, sidecar.verify(encoded, &.{ xmss_claim, extra_claim }, &.{other_sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, sidecar.verify(encoded, &.{ xmss_claim, extra_claim }, &.{ sphincs_claim, other_sphincs_claim }));
    try std.testing.expectError(error.NativeFailure, sidecar.verify(encoded, &.{ xmss_claim, extra_claim, sphincs_claim }, &.{sphincs_claim}));

    const tampered = try allocator.dupe(u8, encoded);
    defer allocator.free(tampered);
    tampered[tampered.len / 2] ^= 1;
    try std.testing.expectError(error.NativeFailure, sidecar.verify(tampered, &.{ xmss_claim, extra_claim }, &.{sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, sidecar.verify(encoded[0 .. encoded.len - 1], &.{ xmss_claim, extra_claim }, &.{sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, sidecar.verify(&.{}, &.{ xmss_claim, extra_claim }, &.{sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, sidecar.aggregate(&.{}, &.{}, &.{}));
}

test "starts and stops its own sidecar" {
    if (builtin.os.tag == .windows) return error.SkipZigTest;
    const allocator = std.testing.allocator;
    const binary = try requiredEnv("LEANVM_SIDECAR_BIN", "a leanvm-sidecar executable");
    // Short, as macOS limits a socket path to 104 bytes, and missing, so `start` creates it private.
    var id: [4]u8 = undefined;
    std.testing.io.random(&id);
    const directory = try std.fmt.allocPrint(allocator, "{s}/lpq-{x}", .{
        std.testing.environ.getPosix("TMPDIR") orelse "/tmp",
        std.mem.readInt(u32, &id, .little),
    });
    defer allocator.free(directory);
    defer std.Io.Dir.cwd().deleteTree(std.testing.io, directory) catch {};
    const socket = try std.fs.path.join(allocator, &.{ directory, "s.sock" });
    defer allocator.free(socket);

    var started = try lpq.Sidecar.start(binary, socket, 2);
    defer started.deinit();
    try expectKnownProver(&started);
    // Bytes that are no proof: the sidecar answers that they prove nothing.
    try std.testing.expectError(error.NativeFailure, started.verify(&.{0}, &.{}, &.{}));
    try expectLastError("the aggregate does not prove the given claims");

    // Closing it stops the sidecar.
    try started.close();
    try started.close();
    try std.testing.expectError(error.NativeFailure, started.verify(&.{0}, &.{}, &.{}));
    try expectLastError("the sidecar is closed");
    try std.testing.expectError(error.NativeFailure, lpq.Sidecar.connect(socket));
}

test "the sidecar needs Unix sockets" {
    if (builtin.os.tag != .windows) return error.SkipZigTest;
    const unsupported = "the leanVM sidecar needs Unix sockets, which this platform lacks";
    try std.testing.expectError(error.NativeFailure, lpq.Sidecar.connect("sidecar.sock"));
    try expectLastError(unsupported);
    try std.testing.expectError(error.NativeFailure, lpq.Sidecar.start("leanvm-sidecar.exe", "sidecar.sock", 0));
    try expectLastError(unsupported);
}

fn claimLessThan(_: void, a: lpq.Claim, b: lpq.Claim) bool {
    return std.mem.order(u8, std.mem.asBytes(&a), std.mem.asBytes(&b)) == .lt;
}
