# lean-pq Zig bindings

Safe Zig bindings for post-quantum signatures, their recursive aggregation, and a VRF:

- **leanXMSS**: stateful. A key signs at `2^32` leaf indices; never sign two different messages at the same leaf index.
- **leanSPHINCS**: stateless. A key signs at most `2^30` messages; signing is deterministic.
- **VRF**: the consensus `pq` feature's VRF tree, pruned to the slots a validator proposes in.

Public keys and messages are `[32]u8`; signatures are `[2404]u8` (leanXMSS) and `[7740]u8` (leanSPHINCS). VRF roots are `[32]u8` and proofs `[1024]u8`. `XmssSecretKey`, `SphincsSecretKey`, `VrfKey`, and `Aggregate` own native handles: call `deinit` exactly once on each. Slices returned by `VrfKey.cacheToBytes`, `Aggregate.toBytes`, `xmssClaims`, and `sphincsClaims` belong to the caller's allocator.

The binding links the Rust bridge's static `liblean_pq_native.a` for the target, which release packages bundle for Linux x86_64 and aarch64 (glibc), macOS (universal) and Windows x86_64 (MinGW).

## Install

Each GitHub release attaches `lean-pq-zig-<version>.tar.gz`, a Zig package with the native archives bundled. Zig 0.16 or newer:

<!-- x-release-please-start-version -->
```sh
version=0.12.0
zig fetch --save=lean_pq "https://github.com/leanEthereum/leanVM/releases/download/bindings-v$version/lean-pq-zig-$version.tar.gz"
```
<!-- x-release-please-end -->

Then import the module in `build.zig`:

```zig
const lean_pq = b.dependency("lean_pq", .{ .target = target, .optimize = optimize });
exe.root_module.addImport("lean_pq", lean_pq.module("lean_pq"));
```

The package picks the bundled archive for the build target. For any other target, build `liblean_pq_native.a` yourself and pass its directory as `-Dnative-dir=...`.

On Windows the bundled archive targets the GNU ABI, `x86_64-windows-gnu`, which is Zig's native target there, so a plain `zig build` works; Zig supplies the MinGW-w64 libc. The MSVC ABI (`-Dtarget=x86_64-windows-msvc`) is not bundled.

## Build from source

Staging the archive needs Zig 0.15.2 (for `cargo-zigbuild`'s Apple cross builds); building the binding needs Zig 0.16 or newer. On Linux x86_64:

```sh
rustup target add x86_64-unknown-linux-gnu
cargo install cargo-zigbuild --locked
sh bindings/native/scripts/stage-static.sh x86_64-unknown-linux-gnu bindings/zig/.native
cd bindings/zig
zig build test -Dnative-dir=.native
```

For Linux aarch64, stage `aarch64-unknown-linux-gnu`; for macOS, stage `universal2-apple-darwin` on macOS after adding both Apple Rust targets; for Windows, stage `x86_64-pc-windows-gnu` (cross-builds from Linux). `scripts/package.sh` assembles a release package from staged archives, and `scripts/consumer-smoke.sh` proves one works as a `zig fetch` dependency.

## Example

```zig
const std = @import("std");
const lpq = @import("lean_pq");

pub fn main() !void {
    const allocator = std.heap.page_allocator;
    const message: lpq.Message = [_]u8{0x42} ** 32;

    var xmss_key = try lpq.XmssSecretKey.fromSeed([_]u8{0x01} ** 32);
    defer xmss_key.deinit();
    const xmss_signature = try xmss_key.sign(message, 7);
    try lpq.xmssVerify(try xmss_key.publicKey(), message, &xmss_signature);

    var sphincs_key = try lpq.SphincsSecretKey.fromSeed([_]u8{0x02} ** 32);
    defer sphincs_key.deinit();
    const sphincs_signature = try sphincs_key.sign(message);
    try lpq.sphincsVerify(try sphincs_key.publicKey(), message, &sphincs_signature);

    // The seed and the slot range fix the VRF root: keep both. Building the key hashes every leaf of the range.
    var vrf_key = try lpq.VrfKey.init([_]u8{0x03} ** 32, 1000, 2000);
    defer vrf_key.deinit();
    const vrf_root = try vrf_key.root();
    try lpq.vrfVerify(vrf_root, 1500, &try vrf_key.proof(1500));

    var leaf = try lpq.Aggregate.create(&.{}, &.{.{
        .public_key = try xmss_key.publicKey(),
        .message = message,
        .signature = xmss_signature,
    }}, &.{.{
        .public_key = try sphincs_key.publicKey(),
        .message = message,
        .signature = sphincs_signature,
    }});
    defer leaf.deinit();
    var root = try lpq.Aggregate.create(&.{&leaf}, &.{}, &.{});
    defer root.deinit();

    // The encoding is the proof alone; the receiver supplies the claims it expects.
    const encoded = try root.toBytes(allocator);
    defer allocator.free(encoded);
    var received = try lpq.Aggregate.fromBytes(encoded, &.{.{
        .public_key = try xmss_key.publicKey(),
        .message = message,
    }}, &.{.{
        .public_key = try sphincs_key.publicKey(),
        .message = message,
    }});
    defer received.deinit();
    const claims = try received.xmssClaims(allocator);
    defer allocator.free(claims);
    std.debug.assert(claims.len == 1);
}
```

Verification failures, of signatures and VRF proofs, return `error.InvalidSignature`; other native errors return `error.NativeFailure` or `error.NativePanic`, and `lastError` copies the message.

leanXMSS keys are stateful: persist your own durable high-water leaf index alongside `XmssSecretKey.toBytes()` and advance it before publishing a signature. Secret key bytes are secret material: the leanXMSS or leanSPHINCS seed.

`Aggregate.create` verifies every raw signature before proving and runs one proof at a time per process; one aggregation takes seconds and over a gigabyte of memory. `Aggregate.toBytes` encodes the proof alone, without its claims: send the claims alongside it, or let the receiver rebuild them. `Aggregate.fromBytes(data, xmss_claims, sphincs_claims)` verifies that the proof proves exactly those claims, in any order with a repeated claim counted once, and fails with `error.NativeFailure` for malformed bytes or any other claim set; so every `Aggregate` value is proven, and `xmssClaims` and `sphincsClaims` return the claims, strictly sorted, in the slice type `fromBytes` takes. `setup()` moves the one-time guest build ahead of the first proof; calling it is optional and idempotent.

`VrfKey.init(seed, start, end)` is the VRF tree of `seed` with leaves for the slots `[start, end)`, and fails for an empty range or one ending past `2^31`. It hashes every leaf of the range once and keeps about `sqrt(end - start)` of the tree's nodes. `root()` is the root to register, and `proof(slot)` is the slot's leaf and its 31 siblings, hashing about `3 sqrt(end - start)` nodes; `vrfVerify(root, slot, &proof)` checks it, counting only the slot's 31 low bits. A slot outside the range has no proof.

`VrfKey.cacheToBytes(allocator)` returns the range and the cached layer, about `32 sqrt(end - start)` bytes that hold no secret, and `VrfKey.fromCacheBytes(seed, cache)` loads a key from them in place of hashing every leaf of the range again, failing with `error.NativeFailure` for bytes that do not encode a range and its layer. The cache is not checked, and a wrong one gives a wrong root and proofs that do not verify: compare the loaded key's `root()` with the registered root before revealing a proof.
