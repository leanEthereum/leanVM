# lean-pq for Java

Java bindings for the leanXMSS and leanSPHINCS post-quantum signatures, their aggregation into one proof, and the consensus VRF tree.

## Install

Maven Central, `io.github.crate-crypto:lean-pq`, JDK 25. Gradle (Kotlin DSL):

<!-- x-release-please-start-version -->
```kotlin
implementation("io.github.crate-crypto:lean-pq:0.17.0")
```
<!-- x-release-please-end -->

Maven:

<!-- x-release-please-start-version -->
```xml
<dependency>
  <groupId>io.github.crate-crypto</groupId>
  <artifactId>lean-pq</artifactId>
  <version>0.17.0</version>
</dependency>
```
<!-- x-release-please-end -->

- The module is `org.ethereum.leanpq`. Grant it native access: `java --enable-native-access=org.ethereum.leanpq`, or `--enable-native-access=ALL-UNNAMED` on the class path.
- The jar bundles the native library for Linux x86_64 and aarch64 (glibc 2.17+), macOS x86_64 and arm64, and Windows x86_64; x86_64 needs AVX2 and PCLMULQDQ.
- It is extracted under `java.io.tmpdir`, which must allow executable mappings (on Windows, under `%LOCALAPPDATA%\lean-pq\native`). `-Dlean.pq.native.path=FILE` loads another build instead.

## Sign and verify

```java
import org.ethereum.leanpq.*;

try (XmssSecretKey xmss = XmssSecretKey.fromSeed(seed32);
     SphincsSecretKey sphincs = SphincsSecretKey.fromSeed(otherSeed32)) {
    byte[] xmssSig = xmss.sign(message32, 7); // at leaf index 7
    boolean xmssValid = LeanPq.xmssVerify(xmss.publicKey(), message32, xmssSig);

    byte[] sphincsSig = sphincs.sign(message32);
    boolean sphincsValid = LeanPq.sphincsVerify(sphincs.publicKey(), message32, sphincsSig);
}
```

- Public keys and messages are 32 bytes; signatures are 2404 (leanXMSS) or 7740 (leanSPHINCS) bytes.
- `XmssSecretKey`, `SphincsSecretKey`, `VrfKey` and `Aggregate` are `AutoCloseable`: use try-with-resources.
- leanXMSS is stateful: a key has `2^32` leaf indices, and must never sign two messages at the same one. Persist a high-water leaf index next to the key and advance it before publishing a signature. `prepare(leafIndex)` builds a leaf's signing state ahead of time.
- leanSPHINCS is stateless and deterministic; a key signs at most `2^30` messages.
- `toBytes()` is the key's 32-byte seed, which is secret; `fromBytes` restores the key.
- `cacheToBytes()` returns the key's trees, which are not secret; `XmssSecretKey.fromCacheBytes(seed, publicKey, cache)` loads the key from them instead of rebuilding them, checking them against the public key.

## VRF

```java
import org.ethereum.leanpq.*;

try (VrfKey key = VrfKey.fromSeed(seed32, 1000, 2000)) {
    byte[] root = key.root();
    boolean valid = LeanPq.vrfVerify(root, 1500, key.proof(1500));
}
```

A key is a 32-byte seed and the slots `[start, end)`, with `end <= 2^31`: both fix the root, so keep both. Building it hashes every slot of the range once; a proof then costs about `3 sqrt(R)` hashes for `R` slots. A proof is 1024 bytes: the slot's secret, then its leaf's 31 siblings, which reveal no other secret. An empty range, a range past `2^31` and a slot outside the range throw `LeanPqException`.

`cacheToBytes()` encodes the key's cache, its range and cached layer (about `32 sqrt(R)` bytes, no secret), and `VrfKey.fromCacheBytes(seed, root, cache)` rebuilds the key from its seed and that cache without hashing the range, failing if the cache does not lead to `root`.

## Aggregate

```java
import java.util.List;
import org.ethereum.leanpq.*;

try (XmssSecretKey xmss = XmssSecretKey.fromSeed(seed32);
     SphincsSecretKey sphincs = SphincsSecretKey.fromSeed(otherSeed32);
     Aggregate leaf = LeanPq.aggregate(
         List.of(),
         List.of(new SignedMessage(xmss.publicKey(), message32, xmss.sign(message32, 7))),
         List.of(new SignedMessage(sphincs.publicKey(), message32, sphincs.sign(message32))));
     Aggregate root = LeanPq.aggregate(List.of(leaf), List.of(), List.of());
     Aggregate received = Aggregate.fromBytes(root.toBytes(), root.xmssClaims(), root.sphincsClaims())) {
    List<SignatureClaim> xmssClaims = received.xmssClaims();
}
```

- `aggregate(children, xmss, sphincs)` verifies raw signatures before proving and takes at most 16 children. The result proves the union of their claims.
- `aggregateOnly(children, xmss, sphincs, xmssClaims, sphincsClaims)` proves exactly the given claims, in any order; each must be one the inputs cover.
- `toBytes()` is the proof alone: send the claims alongside it, or let the receiver rebuild them.
- `Aggregate.fromBytes(bytes, xmssClaims, sphincsClaims)` accepts exactly those claims, in any order, and throws `LeanPqException` otherwise. `xmssClaims()` and `sphincsClaims()` are sorted.
- `setup` throws `LeanPqException` if the prover already runs with another thread count. See [Proving](https://github.com/leanEthereum/leanVM/tree/main/bindings#proving).

## Build and test

Needs JDK 25, Gradle 9.1 or newer and Rust. From the repository root:

```sh
gradle -p bindings/java test
```

The test task builds the native library itself. Building the release jar is in [RELEASING.md](../RELEASING.md#maven-central).

## License

MIT OR Apache-2.0
