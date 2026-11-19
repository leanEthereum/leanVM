const std = @import("std");
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

test "aggregates recursively and round trips through bytes" {
    const allocator = std.testing.allocator;
    try lpq.setup();

    var xmss_key = try lpq.XmssSecretKey.fromSeed([_]u8{3} ** 32);
    defer xmss_key.deinit();
    var sphincs_key = try lpq.SphincsSecretKey.fromSeed([_]u8{4} ** 32);
    defer sphincs_key.deinit();
    var extra_key = try lpq.XmssSecretKey.fromSeed([_]u8{5} ** 32);
    defer extra_key.deinit();
    const xmss_public_key = try xmss_key.publicKey();
    const sphincs_public_key = try sphincs_key.publicKey();
    const extra_public_key = try extra_key.publicKey();

    var xmss_leaf = try lpq.Aggregate.create(&.{}, &.{.{
        .public_key = xmss_public_key,
        .message = message,
        .signature = try xmss_key.sign(message, 0),
    }}, &.{});
    defer xmss_leaf.deinit();
    var sphincs_leaf = try lpq.Aggregate.create(&.{}, &.{}, &.{.{
        .public_key = sphincs_public_key,
        .message = message,
        .signature = try sphincs_key.sign(message),
    }});
    defer sphincs_leaf.deinit();
    var root = try lpq.Aggregate.create(&.{ &xmss_leaf, &sphincs_leaf }, &.{.{
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
    var restored = try lpq.Aggregate.fromBytes(encoded, &.{ extra_claim, xmss_claim, extra_claim }, &.{sphincs_claim});
    defer restored.deinit();

    var expected_xmss = [_]lpq.Claim{ xmss_claim, extra_claim };
    std.mem.sortUnstable(lpq.Claim, &expected_xmss, {}, claimLessThan);
    const xmss_claims = try restored.xmssClaims(allocator);
    defer allocator.free(xmss_claims);
    try std.testing.expectEqualSlices(lpq.Claim, &expected_xmss, xmss_claims);

    const sphincs_claims = try restored.sphincsClaims(allocator);
    defer allocator.free(sphincs_claims);
    try std.testing.expectEqualSlices(lpq.Claim, &.{sphincs_claim}, sphincs_claims);

    // The getters' claims are exactly what decoding needs.
    var reread = try lpq.Aggregate.fromBytes(encoded, xmss_claims, sphincs_claims);
    defer reread.deinit();
    const reencoded = try reread.toBytes(allocator);
    defer allocator.free(reencoded);
    try std.testing.expectEqualSlices(u8, encoded, reencoded);

    // The same proof does not prove any other claim set.
    const other_sphincs_claim: lpq.Claim = .{ .public_key = sphincs_public_key, .message = other_message };
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.fromBytes(encoded, &.{xmss_claim}, &.{sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.fromBytes(encoded, &.{ xmss_claim, extra_claim }, &.{}));
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.fromBytes(encoded, &.{ xmss_claim, extra_claim }, &.{other_sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.fromBytes(encoded, &.{ xmss_claim, extra_claim }, &.{ sphincs_claim, other_sphincs_claim }));
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.fromBytes(encoded, &.{ xmss_claim, extra_claim, sphincs_claim }, &.{sphincs_claim}));

    const tampered = try allocator.dupe(u8, encoded);
    defer allocator.free(tampered);
    tampered[tampered.len / 2] ^= 1;
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.fromBytes(tampered, &.{ xmss_claim, extra_claim }, &.{sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.fromBytes(encoded[0 .. encoded.len - 1], &.{ xmss_claim, extra_claim }, &.{sphincs_claim}));
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.fromBytes(&.{}, &.{ xmss_claim, extra_claim }, &.{sphincs_claim}));
}

test "aggregating nothing fails" {
    try std.testing.expectError(error.NativeFailure, lpq.Aggregate.create(&.{}, &.{}, &.{}));
}

fn claimLessThan(_: void, a: lpq.Claim, b: lpq.Claim) bool {
    return std.mem.order(u8, std.mem.asBytes(&a), std.mem.asBytes(&b)) == .lt;
}
