//! Safe Zig bindings for leanXMSS and leanSPHINCS signatures, their recursive aggregation, and
//! the VRF tree of the consensus `pq` feature.
//!
//! leanXMSS is stateful: a key signs at `2^32` leaf indices, and must never sign two different
//! messages at the same leaf index. leanSPHINCS is stateless: a key signs at most `2^30` messages.
//! Public keys and messages are 32 bytes; signatures are fixed-size byte arrays. Secret keys, VRF
//! keys and aggregates own native handles: call `deinit` exactly once on each.
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
pub const vrf_root_len = 32;
/// The slot's secret, then its leaf's 31 siblings.
pub const vrf_proof_len = 1024;
/// The most child aggregates one `Aggregate.create` call accepts.
pub const max_children = 16;

pub const PublicKey = [public_key_len]u8;
pub const Message = [message_len]u8;
pub const Seed = [seed_len]u8;
pub const XmssSignature = [xmss_signature_len]u8;
pub const SphincsSignature = [sphincs_signature_len]u8;
pub const VrfRoot = [vrf_root_len]u8;
pub const VrfProof = [vrf_proof_len]u8;

pub const Error = error{
    /// The native library reported a checked error; `lastError` has its message.
    NativeFailure,
    /// The native library caught a panic; `lastError` has its message.
    NativePanic,
    InvalidNativeStatus,
    InvalidNativeEncoding,
    /// The signature or VRF proof does not verify; `lastError` has the reason.
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

/// Starts the prover on `threads` threads (0: one per core). Fails if the prover already runs
/// with another count.
pub fn setup(threads: usize) Error!void {
    try checkStatus(c.lpq_setup(threads));
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

    /// Loads a key from its seed, its public key and the bytes of `cacheToBytes`, building no
    /// tree. The cache is checked against the public key.
    pub fn fromCacheBytes(seed: Seed, public_key: PublicKey, cache: []const u8) Error!XmssSecretKey {
        var output: ?*c.lpq_xmss_secret_key = null;
        try checkStatus(c.lpq_xmss_secret_key_from_cache_bytes(&seed, seed.len, &public_key, public_key.len, bytesPtr(cache), cache.len, &output));
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

    /// The trees the key holds, without any secret. The caller owns the returned slice.
    pub fn cacheToBytes(self: *const XmssSecretKey, allocator: std.mem.Allocator) (Error || std.mem.Allocator.Error)![]u8 {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_xmss_secret_key_cache_to_bytes(self.handle, &output));
        return takeBuffer(allocator, output);
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

/// A VRF key: a seed and its slots `[start, end)`, which fix the root, so keep both.
pub const VrfKey = struct {
    handle: *c.lpq_vrf_key,

    /// Builds the key, hashing every slot. `error.NativeFailure` if the range is empty or ends
    /// past `2^31`.
    pub fn init(seed: Seed, start: u32, end: u32) Error!VrfKey {
        var output: ?*c.lpq_vrf_key = null;
        try checkStatus(c.lpq_vrf_key_new(&seed, seed.len, start, end, &output));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    /// Rebuilds a key from its seed, its root and a cache from `cacheToBytes`, without hashing the
    /// range. `error.NativeFailure` if the cache is malformed or does not lead to `expected_root`.
    pub fn fromCacheBytes(seed: Seed, expected_root: VrfRoot, cache: []const u8) Error!VrfKey {
        var output: ?*c.lpq_vrf_key = null;
        try checkStatus(c.lpq_vrf_key_from_cache_bytes(&seed, seed.len, &expected_root, expected_root.len, bytesPtr(cache), cache.len, &output));
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    pub fn deinit(self: *VrfKey) void {
        c.lpq_vrf_key_destroy(self.handle);
        self.* = undefined;
    }

    /// Encodes the key's cache: its range and cached layer, no secret. The caller owns the slice.
    pub fn cacheToBytes(self: *const VrfKey, allocator: std.mem.Allocator) (Error || std.mem.Allocator.Error)![]u8 {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_vrf_key_cache_to_bytes(self.handle, &output));
        return takeBuffer(allocator, output);
    }

    pub fn root(self: *const VrfKey) Error!VrfRoot {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_vrf_key_root(self.handle, &output));
        return takeFixed(vrf_root_len, output);
    }

    /// The proof of `slot`. `error.NativeFailure` outside the range.
    pub fn proof(self: *const VrfKey, slot: u32) Error!VrfProof {
        var output: c.lpq_buffer = .{ .data = null, .len = 0 };
        try checkStatus(c.lpq_vrf_key_proof(self.handle, slot, &output));
        return takeFixed(vrf_proof_len, output);
    }
};

/// `error.InvalidSignature` if `proof` does not open `slot` under `root`.
pub fn vrfVerify(root: VrfRoot, slot: u64, proof: *const VrfProof) Error!void {
    try checkVerification(c.lpq_vrf_verify(&root, root.len, slot, proof, proof.len));
}

/// A verified proof that each listed public key signed its message.
pub const Aggregate = struct {
    handle: *c.lpq_aggregate,

    /// Verifies the raw signatures, then proves the union of their claims and the children's.
    /// At least one input is required. Children are neither consumed nor retained.
    pub fn create(
        children: []const *const Aggregate,
        xmss: []const XmssSignedMessage,
        sphincs: []const SphincsSignedMessage,
    ) Error!Aggregate {
        return createWith(children, xmss, sphincs, null);
    }

    /// `create`, but the result proves exactly `xmss_claims` and `sphincs_claims`, in any order, a
    /// repeat counting once; each must be one the inputs cover.
    pub fn createOnly(
        children: []const *const Aggregate,
        xmss: []const XmssSignedMessage,
        sphincs: []const SphincsSignedMessage,
        xmss_claims: []const Claim,
        sphincs_claims: []const Claim,
    ) Error!Aggregate {
        return createWith(children, xmss, sphincs, .{ xmss_claims, sphincs_claims });
    }

    fn createWith(
        children: []const *const Aggregate,
        xmss: []const XmssSignedMessage,
        sphincs: []const SphincsSignedMessage,
        only: ?struct { []const Claim, []const Claim },
    ) Error!Aggregate {
        if (children.len > max_children) return error.TooManyChildren;
        var handles: [max_children]?*c.lpq_aggregate = undefined;
        for (children, handles[0..children.len]) |child, *handle| handle.* = child.handle;
        const children_ptr: [*c]const ?*c.lpq_aggregate = if (children.len == 0) null else &handles;
        const xmss_ptr = bytesPtr(std.mem.sliceAsBytes(xmss));
        const sphincs_ptr = bytesPtr(std.mem.sliceAsBytes(sphincs));

        var output: ?*c.lpq_aggregate = null;
        if (only) |claims| {
            try checkStatus(c.lpq_aggregate_create_only(
                children_ptr,
                children.len,
                xmss_ptr,
                xmss.len,
                sphincs_ptr,
                sphincs.len,
                bytesPtr(std.mem.sliceAsBytes(claims[0])),
                claims[0].len,
                bytesPtr(std.mem.sliceAsBytes(claims[1])),
                claims[1].len,
                &output,
            ));
        } else {
            try checkStatus(c.lpq_aggregate_create(children_ptr, children.len, xmss_ptr, xmss.len, sphincs_ptr, sphincs.len, &output));
        }
        return .{ .handle = output orelse return error.InvalidNativeEncoding };
    }

    /// Verifies that a proof from `Aggregate.toBytes` proves exactly `xmss_claims` and
    /// `sphincs_claims`. Claims may come in any order; a repeated claim counts once. Fails with
    /// `error.NativeFailure` for malformed bytes or any other claim set.
    pub fn fromBytes(
        data: []const u8,
        xmss_claims: []const Claim,
        sphincs_claims: []const Claim,
    ) Error!Aggregate {
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
