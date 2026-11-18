//! Safe Zig bindings for leanVM's post-quantum signatures and their recursive aggregation.
//!
//! leanXMSS is stateful: a key signs at `2^32` leaf indices, and must never sign two different
//! messages at the same leaf index. leanSPHINCS is stateless: a key signs at most `2^30` messages.
//! Public keys and messages are 32 bytes; signatures are fixed-size byte arrays. Secret keys and
//! aggregates own native handles: call `deinit` exactly once on each.
const std = @import("std");

const c = @cImport({
    @cInclude("lean_pq_native.h");
});

pub const message_len = 32;
pub const public_key_len = 32;
pub const seed_len = 32;
pub const xmss_secret_key_len = 32;
pub const xmss_signature_len = 2404;
pub const sphincs_secret_key_len = 32;
pub const sphincs_signature_len = 7740;
/// The most child aggregates one `Aggregate.create` call accepts.
pub const max_children = 16;

pub const PublicKey = [public_key_len]u8;
pub const Message = [message_len]u8;
pub const Seed = [seed_len]u8;
pub const XmssSignature = [xmss_signature_len]u8;
pub const SphincsSignature = [sphincs_signature_len]u8;

pub const Error = error{
    /// The native library reported a checked error; `lastError` has its message.
    NativeFailure,
    /// The native library caught a panic; `lastError` has its message.
    NativePanic,
    InvalidNativeStatus,
    InvalidNativeEncoding,
    /// The signature does not verify; `lastError` has the reason.
    InvalidSignature,
    TooManyChildren,
};

/// A raw leanXMSS signature input to `Aggregate.create`. Its layout is the native record.
pub const XmssSignedMessage = extern struct {
    public_key: PublicKey,
    message: Message,
    signature: XmssSignature,
};

/// A raw leanSPHINCS signature input to `Aggregate.create`. Its layout is the native record.
pub const SphincsSignedMessage = extern struct {
    public_key: PublicKey,
    message: Message,
    signature: SphincsSignature,
};

/// A `(public key, message)` pair an aggregate attests. Its layout is the native record.
pub const Claim = extern struct {
    public_key: PublicKey,
    message: Message,
};

comptime {
    std.debug.assert(@sizeOf(XmssSignedMessage) == 2468);
    std.debug.assert(@sizeOf(SphincsSignedMessage) == 7804);
    std.debug.assert(@sizeOf(Claim) == 64);
}

/// Moves the one-time guest build ahead of the first proof. Optional and idempotent.
pub fn setup() Error!void {
    try checkStatus(c.lpq_setup());
}

/// Copies the calling thread's last native error message.
pub fn lastError(allocator: std.mem.Allocator) (Error || std.mem.Allocator.Error)![]u8 {
    var output: c.lpq_buffer = .{ .data = null, .len = 0 };
    try checkStatus(c.lpq_last_error(&output));
    return takeBuffer(allocator, output);
}

pub const XmssSecretKey = struct {
    handle: *c.lpq_xmss_secret_key,

    /// A fresh key from the operating system's randomness.
    pub fn generate() Error!XmssSecretKey {
        var output: ?*c.lpq_xmss_secret_key = null;
        try checkStatus(c.lpq_xmss_secret_key_generate(&output));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    /// The seed is the key's entire secret material: never derive another key from it.
    pub fn fromSeed(seed: Seed) Error!XmssSecretKey {
        return fromBytes(&seed);
    }

    pub fn fromBytes(data: []const u8) Error!XmssSecretKey {
        var output: ?*c.lpq_xmss_secret_key = null;
        try checkStatus(c.lpq_xmss_secret_key_from_bytes(bytesPtr(data), data.len, &output));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    pub fn deinit(self: *XmssSecretKey) void {
        c.lpq_xmss_secret_key_destroy(self.handle);
        self.* = undefined;
    }

    /// SECRET KEY MATERIAL: the seed.
    pub fn toBytes(self: *const XmssSecretKey) Error![xmss_secret_key_len]u8 {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_xmss_secret_key_to_bytes(self.handle, &output));
        return takeFixed(xmss_secret_key_len, output);
    }

    pub fn publicKey(self: *const XmssSecretKey) Error!PublicKey {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_xmss_secret_key_public_key(self.handle, &output));
        return takeFixed(public_key_len, output);
    }

    /// Builds the bottom tree `leaf_index` falls in ahead of signing there.
    pub fn prepare(self: *const XmssSecretKey, leaf_index: u32) Error!void {
        try checkStatus(c.lpq_xmss_secret_key_prepare(self.handle, leaf_index));
    }

    /// Never sign two different messages at the same `leaf_index`.
    pub fn sign(self: *const XmssSecretKey, message: Message, leaf_index: u32) Error!XmssSignature {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_xmss_secret_key_sign(self.handle, &message, message.len, leaf_index, &output));
        return takeFixed(xmss_signature_len, output);
    }
};

/// Returns `error.InvalidSignature` when `signature` is not `public_key`'s signature of `message`.
pub fn xmssVerify(public_key: PublicKey, message: Message, signature: *const XmssSignature) Error!void {
    try checkVerification(c.lpq_xmss_verify(&public_key, public_key.len, &message, message.len, signature, signature.len));
}

pub const SphincsSecretKey = struct {
    handle: *c.lpq_sphincs_secret_key,

    /// A fresh key from the operating system's randomness.
    pub fn generate() Error!SphincsSecretKey {
        var output: ?*c.lpq_sphincs_secret_key = null;
        try checkStatus(c.lpq_sphincs_secret_key_generate(&output));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    /// The seed is the key's entire secret material: never derive another key from it.
    pub fn fromSeed(seed: Seed) Error!SphincsSecretKey {
        var output: ?*c.lpq_sphincs_secret_key = null;
        try checkStatus(c.lpq_sphincs_secret_key_from_seed(&seed, seed.len, &output));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    pub fn fromBytes(data: []const u8) Error!SphincsSecretKey {
        var output: ?*c.lpq_sphincs_secret_key = null;
        try checkStatus(c.lpq_sphincs_secret_key_from_bytes(bytesPtr(data), data.len, &output));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    pub fn deinit(self: *SphincsSecretKey) void {
        c.lpq_sphincs_secret_key_destroy(self.handle);
        self.* = undefined;
    }

    /// SECRET KEY MATERIAL: the seed.
    pub fn toBytes(self: *const SphincsSecretKey) Error![sphincs_secret_key_len]u8 {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_sphincs_secret_key_to_bytes(self.handle, &output));
        return takeFixed(sphincs_secret_key_len, output);
    }

    pub fn publicKey(self: *const SphincsSecretKey) Error!PublicKey {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_sphincs_secret_key_public_key(self.handle, &output));
        return takeFixed(public_key_len, output);
    }

    pub fn sign(self: *const SphincsSecretKey, message: Message) Error!SphincsSignature {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_sphincs_secret_key_sign(self.handle, &message, message.len, &output));
        return takeFixed(sphincs_signature_len, output);
    }
};

/// Returns `error.InvalidSignature` when `signature` is not `public_key`'s signature of `message`.
pub fn sphincsVerify(public_key: PublicKey, message: Message, signature: *const SphincsSignature) Error!void {
    try checkVerification(c.lpq_sphincs_verify(&public_key, public_key.len, &message, message.len, signature, signature.len));
}

/// A verified proof that each listed public key signed its message.
pub const Aggregate = struct {
    handle: *c.lpq_aggregate,

    /// Verifies the raw signatures, then proves the union of their claims and the children's.
    /// Runs one proof at a time per process. Children are neither consumed nor retained.
    pub fn create(
        children: []const *const Aggregate,
        xmss: []const XmssSignedMessage,
        sphincs: []const SphincsSignedMessage,
    ) Error!Aggregate {
        if (children.len > max_children) return error.TooManyChildren;
        var handles: [max_children]?*c.lpq_aggregate = undefined;
        for (children, handles[0..children.len]) |child, *handle| handle.* = child.handle;

        var output: ?*c.lpq_aggregate = null;
        try checkStatus(c.lpq_aggregate_create(
            if (children.len == 0) null else &handles,
            children.len,
            bytesPtr(std.mem.sliceAsBytes(xmss)),
            xmss.len,
            bytesPtr(std.mem.sliceAsBytes(sphincs)),
            sphincs.len,
            &output,
        ));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    /// Decodes a proof and verifies that it proves exactly `xmss_claims` and `sphincs_claims`.
    /// The encoding is the proof alone: send the claims alongside it, or rebuild them on the
    /// receiving side. Claims may come in any order; a repeated claim counts once. Fails with
    /// `error.NativeFailure` for malformed bytes or any other claim set.
    pub fn fromBytes(data: []const u8, xmss_claims: []const Claim, sphincs_claims: []const Claim) Error!Aggregate {
        var output: ?*c.lpq_aggregate = null;
        try checkStatus(c.lpq_aggregate_from_bytes(
            bytesPtr(data),
            data.len,
            bytesPtr(std.mem.sliceAsBytes(xmss_claims)),
            xmss_claims.len,
            bytesPtr(std.mem.sliceAsBytes(sphincs_claims)),
            sphincs_claims.len,
            &output,
        ));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    pub fn deinit(self: *Aggregate) void {
        c.lpq_aggregate_destroy(self.handle);
        self.* = undefined;
    }

    /// The proof alone, without its claims. The caller owns the returned slice.
    pub fn toBytes(self: *const Aggregate, allocator: std.mem.Allocator) (Error || std.mem.Allocator.Error)![]u8 {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_aggregate_to_bytes(self.handle, &output));
        return takeBuffer(allocator, output);
    }

    /// The leanXMSS claims, strictly sorted. The caller owns the returned slice.
    pub fn xmssClaims(self: *const Aggregate, allocator: std.mem.Allocator) (Error || std.mem.Allocator.Error)![]Claim {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_aggregate_xmss_claims(self.handle, &output));
        return takeClaims(allocator, output);
    }

    /// The leanSPHINCS claims, strictly sorted. The caller owns the returned slice.
    pub fn sphincsClaims(self: *const Aggregate, allocator: std.mem.Allocator) (Error || std.mem.Allocator.Error)![]Claim {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_aggregate_sphincs_claims(self.handle, &output));
        return takeClaims(allocator, output);
    }
};

fn checkStatus(status: i32) Error!void {
    return switch (status) {
        0 => {},
        1 => error.NativeFailure,
        2 => error.NativePanic,
        else => error.InvalidNativeStatus,
    };
}

fn checkVerification(status: i32) Error!void {
    return switch (status) {
        0 => {},
        1 => error.InvalidSignature,
        2 => error.NativePanic,
        else => error.InvalidNativeStatus,
    };
}

fn nativeBytes(buffer: c.lpq_buffer) Error![]const u8 {
    const data = buffer.data orelse {
        if (buffer.len == 0) return &.{};
        return error.InvalidNativeEncoding;
    };
    return data[0..buffer.len];
}

fn takeBuffer(allocator: std.mem.Allocator, buffer: c.lpq_buffer) (Error || std.mem.Allocator.Error)![]u8 {
    const data = try nativeBytes(buffer);
    defer freeBuffer(buffer);
    return allocator.dupe(u8, data);
}

fn takeFixed(comptime len: usize, buffer: c.lpq_buffer) Error![len]u8 {
    const data = try nativeBytes(buffer);
    defer freeBuffer(buffer);
    if (data.len != len) return error.InvalidNativeEncoding;
    return data[0..len].*;
}

fn takeClaims(allocator: std.mem.Allocator, buffer: c.lpq_buffer) (Error || std.mem.Allocator.Error)![]Claim {
    const data = try nativeBytes(buffer);
    defer freeBuffer(buffer);
    if (data.len % @sizeOf(Claim) != 0) return error.InvalidNativeEncoding;
    const claims = try allocator.alloc(Claim, data.len / @sizeOf(Claim));
    @memcpy(std.mem.sliceAsBytes(claims), data);
    return claims;
}

fn freeBuffer(buffer: c.lpq_buffer) void {
    if (buffer.data) |data| c.lpq_buffer_free(data, buffer.len);
}

fn bytesPtr(data: []const u8) ?[*]const u8 {
    return if (data.len == 0) null else data.ptr;
}
