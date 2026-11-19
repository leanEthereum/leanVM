# lean-pq Java bindings

Java 25 bindings for post-quantum signatures, their aggregation, and the consensus VRF:

- **leanXMSS**: stateful. A key signs at unsigned 32-bit leaf indices; never sign two different messages at the same leaf index.
- **leanSPHINCS**: stateless. A key is its 32-byte seed, signs at most 2^30 messages, and signs deterministically.
- **VRF**: the consensus `pq` feature's VRF tree, pruned to the slots a validator proposes in.

Public keys and messages are 32 bytes; signatures are `byte[]` of 2404 (leanXMSS) or 7740 (leanSPHINCS) bytes. An `Aggregate` proves that each listed public key signed its message, across both schemes, and can absorb earlier aggregates.

The API is the named module `org.ethereum.leanpq`, built on the Foreign Function & Memory API. `XmssSecretKey`, `SphincsSecretKey`, `VrfKey` and `Aggregate` are `AutoCloseable`: use try-with-resources.

## Install

Published on Maven Central as `io.github.crate-crypto:lean-pq`; it needs JDK 25.

Gradle (Kotlin DSL):

<!-- x-release-please-start-version -->
```kotlin
dependencies {
    implementation("io.github.crate-crypto:lean-pq:0.12.0")
}
```
<!-- x-release-please-end -->

Maven:

<!-- x-release-please-start-version -->
```xml
<dependency>
  <groupId>io.github.crate-crypto</groupId>
  <artifactId>lean-pq</artifactId>
  <version>0.12.0</version>
</dependency>
```
<!-- x-release-please-end -->

## Native-access permission

A modular application grants the module native access:

```sh
java --enable-native-access=org.ethereum.leanpq ...
```

On the class path, use `--enable-native-access=ALL-UNNAMED`.

## Native library

The jar bundles the native library for:

| Platform | Resource in the jar |
| --- | --- |
| Linux x86_64, glibc 2.17 or newer (CPU with AVX2 and PCLMULQDQ) | `org/ethereum/leanpq/native/linux-x86_64/liblean_pq_native.so` |
| Linux aarch64, glibc 2.17 or newer | `org/ethereum/leanpq/native/linux-aarch64/liblean_pq_native.so` |
| macOS arm64 and x86_64 (one universal library; x86_64 needs AVX2 and PCLMULQDQ) | `org/ethereum/leanpq/native/macos-universal/liblean_pq_native.dylib` |
| Windows x86_64 (Windows 10 or newer; CPU with AVX2 and PCLMULQDQ) | `org/ethereum/leanpq/native/windows-x86_64/lean_pq_native.dll` |

On Linux and macOS, first use copies the library into a new owner-only directory under `java.io.tmpdir`, loads it, and deletes the copy; that directory must allow executable mappings. Windows cannot delete a loaded DLL, so there the library is installed once per build as `%LOCALAPPDATA%\lean-pq\native\<SHA-256 of the DLL>\lean_pq_native.dll` and reused by later JVMs only while its bytes match the jar's copy; a missing or different file is rewritten atomically. Each release adds one directory there, which can be deleted while no JVM uses it. The DLL is built for `x86_64-pc-windows-gnu` and imports only DLLs that ship with Windows, so it needs no Visual C++ or MinGW runtime. Other platforms, including musl-based Linux and Windows on arm64, fail with an error naming the platform.

To load a different build instead, set `-Dlean.pq.native.path=/path/to/liblean_pq_native.so` (or `.dylib`, or `lean_pq_native.dll`) before first use; the bundled libraries are then ignored. Build one with `cargo build --release -p lean-pq-native` in `bindings/` (the library lands in `bindings/target/release`).

## Build and test

Requirements: JDK 25, Gradle 9.1 or newer, and Rust (stable toolchain). From the repository root:

```sh
gradle -p bindings/java test
```

The test task builds the shared `lean_pq_native` library in release mode and passes its path as `-Dlean.pq.native.path`. One aggregation takes seconds and over a gigabyte of memory.

`gradle -p bindings/java jar` bundles the freshly built host library only. To bundle prebuilt libraries instead, pass `-PleanPqNativeDir=DIR`, where `DIR/<platform>/` holds the library for each platform in the table above; `scripts/build-native.sh <platform> DIR` builds one (the Linux builds need [Zig 0.15.2](https://ziglang.org/download/) and `cargo install cargo-zigbuild`, the macOS build needs a Mac, and the Windows build needs Windows with Git Bash, the `x86_64-pc-windows-gnu` Rust target and MinGW-w64's `gcc` and `objdump` on `PATH`). Local builds have version `0.0.0-SNAPSHOT`; `-Pversion=X.Y.Z` overrides it.

`scripts/consumer-smoke.sh [GRADLE_ARGS...]` publishes the jar to a throwaway Maven repository and signs, verifies and aggregates through it from a fresh modular project, with the bundled library (set `GRADLE` if Gradle is not on `PATH`). CI runs it on Linux x86_64, the release workflow on every bundled platform.

## Releasing

`.github/workflows/bindings-release.yml` publishes on every `bindings-vX.Y.Z` tag: `java-native` builds and checks each platform's library, and `java-publish` bundles all four in the jar, runs the consumer smoke against it, then signs and uploads it to the Central Portal, releasing it once the Portal validates the deployment. A version can be published only once.

One-time setup, with the `io.github.crate-crypto` namespace verified on [central.sonatype.com](https://central.sonatype.com/publishing/namespaces):

1. Generate a Portal user token: sign in to the Central Portal, open <https://central.sonatype.com/usertoken>, press **Generate User Token**, and copy the username and password it shows once.
2. Generate a signing key and publish its public half:

   ```sh
   gpg --quick-generate-key "lean-pq release signing <maintainer@example.org>" rsa4096 sign 2y
   gpg --list-secret-keys --keyid-format long    # note the 40-hex-digit fingerprint
   gpg --armor --export FINGERPRINT > lean-pq-signing.asc
   ```

   Upload `lean-pq-signing.asc` at <https://keys.openpgp.org/upload> and confirm the verification e-mail so the key is published with its identity (or `gpg --keyserver keys.openpgp.org --send-keys FINGERPRINT`, then request verification on that site). Central looks the key up there to check signatures.
3. Export the private key, ASCII-armored:

   ```sh
   gpg --armor --export-secret-keys FINGERPRINT
   ```

4. Add the repository secrets (Settings → Secrets and variables → Actions):

   | Secret | Value |
   | --- | --- |
   | `MAVEN_CENTRAL_USERNAME` | the user token's username |
   | `MAVEN_CENTRAL_PASSWORD` | the user token's password |
   | `SIGNING_KEY` | the whole exported private key, including the `BEGIN`/`END` lines |
   | `SIGNING_PASSWORD` | the key's passphrase |

The workflow passes them to the [`com.vanniktech.maven.publish`](https://vanniktech.github.io/gradle-maven-publish-plugin/central/) Gradle plugin as `ORG_GRADLE_PROJECT_mavenCentralUsername`, `ORG_GRADLE_PROJECT_mavenCentralPassword`, `ORG_GRADLE_PROJECT_signingInMemoryKey` and `ORG_GRADLE_PROJECT_signingInMemoryKeyPassword`. Builds without `signingInMemoryKey` skip signing. Before the key expires, extend it with `gpg --quick-set-expire FINGERPRINT 2y`, upload the public key again, and update `SIGNING_KEY`.

## Sign and verify

```java
import org.ethereum.leanpq.*;

try (XmssSecretKey xmss = XmssSecretKey.fromSeed(seed32);
     SphincsSecretKey sphincs = SphincsSecretKey.fromSeed(otherSeed32)) {
    byte[] xmssSignature = xmss.sign(message32, 7);
    boolean xmssValid = LeanPq.xmssVerify(xmss.publicKey(), message32, xmssSignature);

    byte[] sphincsSignature = sphincs.sign(message32);
    boolean sphincsValid = LeanPq.sphincsVerify(sphincs.publicKey(), message32, sphincsSignature);
}
```

leanXMSS keys are stateful: persist your own durable high-water leaf index alongside `XmssSecretKey.toBytes()` and advance it before publishing a signature. `prepare(leafIndex)` builds the signing state ahead of time. Secret-key bytes are secret material: the key's 32-byte seed.

## VRF

```java
import org.ethereum.leanpq.*;

// The seed and the range [1000, 2000) fix the root: keep both.
try (VrfKey key = VrfKey.fromSeed(seed32, 1000, 2000)) {
    byte[] root = key.root();
    boolean valid = LeanPq.vrfVerify(root, 1500, key.proof(1500));
}
```

`fromSeed` hashes every leaf of the range once and keeps about sqrt(end - start) nodes of the tree, so `proof(slot)` is cheap: keep the key open for as long as the validator proposes from it. A range must be nonempty and end at most at 2^31, and a slot outside it has no proof, both failing with `LeanPqException`. A proof is 1024 bytes, the leaf then its 31 siblings, and `vrfVerify` counts only the slot's 31 low bits, as the consensus specifications do.

`cacheToBytes()` returns the range and the layer of the tree a key keeps, which hold no secret, and `VrfKey.fromCacheBytes(seed, cache)` loads a key from them, hashing about sqrt(end - start) nodes in place of every leaf of the range. The cache is not checked, and a wrong one gives a wrong root, so compare `root()` with the registered root before revealing a proof.

## Aggregation

`LeanPq.aggregate(children, xmss, sphincs)` verifies every raw signature before proving, accepts at most 16 children, and runs one proof at a time per process. `toBytes()` encodes the proof alone: send the claims alongside it, or let the receiver rebuild them, as Ethereum does from its validator bitfields. `Aggregate.fromBytes(bytes, xmssClaims, sphincsClaims)` verifies the proof against exactly the claims you pass, in any order (a repeated claim counts once), and throws `LeanPqException` for any other set of claims or bytes that are not a proof, so every `Aggregate` is proven. `LeanPq.setup()` moves the one-time guest build ahead of the first proof; calling it is optional and idempotent.

```java
import java.util.List;
import org.ethereum.leanpq.*;

try (Aggregate leaf = LeanPq.aggregate(
         List.of(),
         List.of(new SignedMessage(xmss.publicKey(), message32, xmss.sign(message32, 7))),
         List.of(new SignedMessage(sphincs.publicKey(), message32, sphincs.sign(message32))));
     Aggregate root = LeanPq.aggregate(List.of(leaf), List.of(), List.of());
     // The bytes are the proof alone: the receiver supplies the claims it expects.
     Aggregate received = Aggregate.fromBytes(
         root.toBytes(),
         List.of(new SignatureClaim(xmss.publicKey(), message32)),
         List.of(new SignatureClaim(sphincs.publicKey(), message32)))) {
    List<SignatureClaim> xmssClaims = received.xmssClaims();
    List<SignatureClaim> sphincsClaims = received.sphincsClaims();
}
```
