# lean-pq for .NET

.NET bindings for the leanXMSS and leanSPHINCS post-quantum signatures, their aggregation into one proof, and the consensus VRF tree.

## Install

NuGet, `Ethereum.LeanPq`, .NET 10. The namespace is `Ethereum.PostQuantum`.

<!-- x-release-please-start-version -->
```sh
dotnet add package Ethereum.LeanPq --version 0.19.1
```
<!-- x-release-please-end -->

- The package bundles the native library for Linux x64 and arm64 (glibc 2.17+), macOS x64 and arm64, and Windows x64; x64 needs AVX2 and PCLMULQDQ.
- `LEAN_PQ_NATIVE_PATH=FILE` loads another build instead of the bundled one.

## Sign and verify

```csharp
using Ethereum.PostQuantum;

using XmssSecretKey xmss = XmssSecretKey.FromSeed(seed32);
using SphincsSecretKey sphincs = SphincsSecretKey.FromSeed(otherSeed32);

byte[] xmssSignature = xmss.Sign(message32, 7); // at leaf index 7
bool xmssValid = LeanPq.XmssVerify(xmss.GetPublicKey(), message32, xmssSignature);

byte[] sphincsSignature = sphincs.Sign(message32);
bool sphincsValid = LeanPq.SphincsVerify(sphincs.GetPublicKey(), message32, sphincsSignature);
```

- Public keys and messages are 32 bytes; signatures are 2404 (leanXMSS) or 7740 (leanSPHINCS) bytes. Byte inputs are `ReadOnlySpan<byte>`, so arrays, slices and stack buffers all work.
- `XmssSecretKey`, `SphincsSecretKey`, `VrfKey` and `Aggregate` are `IDisposable`: use `using`. A call on a disposed one throws `ObjectDisposedException`.
- leanXMSS is stateful: a key has `2^32` leaf indices, and must never sign two messages at the same one. Persist a high-water leaf index next to the key and advance it before publishing a signature. `Prepare(leafIndex)` builds a leaf's signing state ahead of time, and `SetBottomTreeCacheSize(size)` sets how many recently used bottom trees the key keeps, 8 by default.
- leanSPHINCS is stateless and deterministic; a key signs at most `2^30` messages.
- `ToBytes()` is the key's 32-byte seed, which is secret; `FromBytes` restores the key.
- `CacheToBytes()` returns the key's trees, which are not secret; `XmssSecretKey.FromCacheBytes(seed, publicKey, cache)` loads the key from them instead of rebuilding them, checking them against the public key.
- A public key, message, seed or root that is not 32 bytes throws `ArgumentException`; other invalid input, including malformed keys, caches and signatures, throws `LeanPqException` or fails verification.

## VRF

```csharp
using Ethereum.PostQuantum;

using VrfKey key = VrfKey.FromSeed(seed32, 1000, 2000);
byte[] root = key.GetRoot();
bool valid = LeanPq.VrfVerify(root, 1500, key.GetProof(1500));
```

A key is a 32-byte seed and the slots `[start, end)`, with `end <= 2^31`: both fix the root, so keep both. Building it hashes every slot of the range once; a proof then costs about `3 sqrt(R)` hashes for `R` slots. A proof is 1024 bytes: the slot's secret, then its leaf's 31 siblings, which reveal no other secret. An empty range, a range past `2^31` and a slot outside the range throw `LeanPqException`.

`CacheToBytes()` encodes the key's cache, its range and cached layer (about `32 sqrt(R)` bytes, no secret), and `VrfKey.FromCacheBytes(seed, root, cache)` rebuilds the key from its seed and that cache without hashing the range, failing if the cache does not lead to `root`.

## Aggregate

```csharp
using Ethereum.PostQuantum;

using XmssSecretKey xmss = XmssSecretKey.FromSeed(seed32);
using SphincsSecretKey sphincs = SphincsSecretKey.FromSeed(otherSeed32);

using Aggregate leaf = LeanPq.Aggregate(
    [],
    [new SignedMessage(xmss.GetPublicKey(), message32, xmss.Sign(message32, 7))],
    [new SignedMessage(sphincs.GetPublicKey(), message32, sphincs.Sign(message32))]);
using Aggregate root = LeanPq.Aggregate([leaf], [], []);
using Aggregate received = Aggregate.FromBytes(root.ToBytes(), root.GetXmssClaims(), root.GetSphincsClaims());
IReadOnlyList<SignatureClaim> xmssClaims = received.GetXmssClaims();
```

- `LeanPq.Aggregate(children, xmss, sphincs)` verifies raw signatures before proving and takes at most 16 children, which stay owned by the caller. The result proves the union of their claims.
- `LeanPq.AggregateOnly(children, xmss, sphincs, xmssClaims, sphincsClaims)` proves exactly the given claims, in any order; each must be one the inputs cover.
- `ToBytes()` is the proof alone: send the claims alongside it, or let the receiver rebuild them.
- `Aggregate.FromBytes(bytes, xmssClaims, sphincsClaims)` accepts exactly those claims, in any order (a repeat counts once), and throws `LeanPqException` otherwise. `GetXmssClaims()` and `GetSphincsClaims()` are sorted.
- `LeanPq.Setup` throws `LeanPqException` if the prover already runs with another thread count. See [Proving](https://github.com/leanEthereum/leanVM/tree/main/bindings#proving).

## Build and test

Needs the .NET 10 SDK and Rust. From the repository root:

```sh
dotnet test bindings/dotnet/Ethereum.LeanPq.slnx
```

The build compiles the native library itself. Packing the release package is in [RELEASING.md](../RELEASING.md#nuget).

## License

MIT OR Apache-2.0
