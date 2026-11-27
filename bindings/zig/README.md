# lean-pq Zig bindings

Zig bindings for leanXMSS and leanSPHINCS signatures, their recursive aggregation, and the consensus VRF tree.

## Install

Needs Zig 0.16+.

<!-- x-release-please-start-version -->
```sh
version=0.19.1
zig fetch --save=lean_pq "https://github.com/leanEthereum/leanVM/releases/download/bindings-v$version/lean-pq-zig-$version.tar.gz"
```
<!-- x-release-please-end -->

In `build.zig`:

```zig
const lean_pq = b.dependency("lean_pq", .{ .target = target, .optimize = optimize });
exe.root_module.addImport("lean_pq", lean_pq.module("lean_pq"));
```

Prebuilt for Linux x86_64 and aarch64 (glibc), macOS (universal) and Windows `x86_64-windows-gnu` (not MSVC). For any other target, pass `-Dnative-dir=DIR` holding your own `liblean_pq_native.a`.

## Example

```zig
const std = @import("std");
const lpq = @import("lean_pq");

pub fn main() !void {
    const message: lpq.Message = [_]u8{0x42} ** 32;

    var xmss_key = try lpq.XmssSecretKey.fromSeed([_]u8{0x01} ** 32);
    defer xmss_key.deinit();
    const xmss_signature = try xmss_key.sign(message, 7);
    try lpq.xmssVerify(try xmss_key.publicKey(), message, &xmss_signature);

    var sphincs_key = try lpq.SphincsSecretKey.fromSeed([_]u8{0x02} ** 32);
    defer sphincs_key.deinit();
    const sphincs_signature = try sphincs_key.sign(message);
    try lpq.sphincsVerify(try sphincs_key.publicKey(), message, &sphincs_signature);

    var vrf_key = try lpq.VrfKey.init([_]u8{0x03} ** 32, 1000, 2000);
    defer vrf_key.deinit();
    const vrf_root = try vrf_key.root();
    try lpq.vrfVerify(vrf_root, 1500, &try vrf_key.proof(1500));
}
```

- leanXMSS keys are stateful: store your own leaf index next to `XmssSecretKey.toBytes()` and never sign two different messages at the same index.
- leanSPHINCS keys are stateless and deterministic, and sign at most `2^30` messages.
- `XmssSecretKey.cacheToBytes(allocator)` returns the key's trees, which are not secret; `XmssSecretKey.fromCacheBytes(seed, public_key, cache)` loads the key from them instead of rebuilding them, checking them against the public key.
- Call `deinit` exactly once on every `XmssSecretKey`, `SphincsSecretKey`, `VrfKey` and `Aggregate`. Returned slices belong to the allocator you pass.
- A bad signature or VRF proof returns `error.InvalidSignature`; for other errors, `lastError` returns the message.

## Aggregate

With the keys and signatures above:

```zig
const allocator = std.heap.page_allocator;

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
```

- `Aggregate.create` verifies raw signatures first and takes at most `max_children` (16) children, which it neither consumes nor retains.
- `Aggregate.createOnly` takes the claims the result proves too, in any order; each must be one the inputs cover.
- `toBytes` is the proof alone: send the claims (`xmssClaims`, `sphincsClaims`) alongside it.
- `Aggregate.fromBytes` takes the claims in any order (a repeat counts once) and fails with `error.NativeFailure` for any other set, so every `Aggregate` is proven.
- `setup(threads)` fails if the prover already runs with another thread count. See [Proving](https://github.com/leanEthereum/leanVM/tree/main/bindings#proving).
- A process forked after the prover started cannot aggregate.

## VRF

A key is a 32-byte seed and the slots `[start, end)`, with `end <= 2^31`: both fix the root, so keep both. Building it hashes every slot of the range once; a proof then costs about `3 sqrt(R)` hashes for `R` slots. A proof is 1024 bytes: the slot's secret, then its leaf's 31 siblings, which reveal no other secret. An empty range, a range past `2^31` and a slot outside the range fail with `error.NativeFailure`.

`cacheToBytes(allocator)` encodes the key's cache, its range and cached layer (about `32 sqrt(R)` bytes, no secret), and `VrfKey.fromCacheBytes(seed, root, cache)` rebuilds the key from its seed and that cache without hashing the range, failing if the cache does not lead to `root`.

## Build from source

Needs Rust, [Zig](https://ziglang.org/) 0.15.2 to stage the archive, and Zig 0.16+ to build. From the repository root, on Linux x86_64:

```sh
rustup target add x86_64-unknown-linux-gnu
rustup component add llvm-tools
cargo install cargo-zigbuild --locked
sh bindings/native/scripts/stage-static.sh x86_64-unknown-linux-gnu bindings/zig/.native
cd bindings/zig && zig build test -Dnative-dir=.native
```

Other platforms stage `aarch64-unknown-linux-gnu`, `universal2-apple-darwin` (on macOS, with both Apple Rust targets) or `x86_64-pc-windows-gnu`.

Then pass that directory as `-Dnative-dir`, or as an absolute `.@"native-dir"` to `b.dependency`.

## License

MIT or Apache-2.0, at your option.
