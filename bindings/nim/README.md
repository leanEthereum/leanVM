# lean-pq Nim bindings

Nim bindings for leanXMSS and leanSPHINCS signatures, their recursive aggregation, and the consensus VRF tree.

## Install

Needs Nim 2.2.12+. In your `.nimble`:

<!-- x-release-please-start-version -->
```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.17.0"
```
<!-- x-release-please-end -->

Or from the command line:

<!-- x-release-please-start-version -->
```sh
nimble install "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.17.0"
```
<!-- x-release-please-end -->

With [nimbus-build-system](https://github.com/status-im/nimbus-build-system), vendor the tag as a submodule and add `--path:"vendor/leanVM/bindings/nim"` to `config.nims`:

<!-- x-release-please-start-version -->
```sh
git submodule add https://github.com/leanEthereum/leanVM vendor/leanVM
git -C vendor/leanVM checkout bindings-v0.17.0
```
<!-- x-release-please-end -->

The package depends on [`results`](https://github.com/arnetheduck/nim-results); with nimbus-build-system, vendor it too.

The first build downloads the prebuilt archive with curl, for Linux x86_64 and aarch64 (glibc), macOS (universal) and Windows x86_64 (MinGW-w64 gcc, not `--cc:vcc`), so no Rust is needed. For other targets or offline builds, pass `-d:leanPqNativeDir=DIR` holding your own `liblean_pq_native.a`.

## Example

```nim
import lean_pq

proc main() =
  var
    message: LeanPqMessage
    seed: LeanPqSeed
  message[0] = 0x42
  seed[0] = 0x01

  let
    xmssKey = XmssSecretKey.fromSeed(seed).expect("key")
    xmssPublicKey = xmssKey.publicKey().expect("public key")
    xmssSignature = xmssKey.sign(message, 7).expect("signature")
  doAssert xmssVerify(xmssPublicKey, message, xmssSignature)

  let
    sphincsKey = SphincsSecretKey.generate().expect("key")
    sphincsPublicKey = sphincsKey.publicKey().expect("public key")
    sphincsSignature = sphincsKey.sign(message).expect("signature")
  doAssert sphincsVerify(sphincsPublicKey, message, sphincsSignature)

  seed[0] = 0x03
  let
    vrfKey = VrfKey.init(seed, 1000, 2000).expect("key")
    vrfRoot = vrfKey.root().expect("root")
  doAssert vrfVerify(vrfRoot, 1500, vrfKey.proof(1500).expect("proof"))

  # Handles are freed when collected; `close` frees them now.
  xmssKey.close()
  doAssert xmssKey.sign(message, 8).isErr()

main()
```

- leanXMSS keys are stateful: store your own leaf index next to `XmssSecretKey.toBytes()` and never sign two different messages at the same index.
- leanSPHINCS keys are stateless and deterministic, and sign at most `2^30` messages.
- `XmssSecretKey.cacheToBytes()` returns the key's trees, which are not secret; `XmssSecretKey.fromCacheBytes(seed, publicKey, cache)` loads the key from them instead of rebuilding them, checking them against the public key.
- Fallible calls return `Result[T, string]` from [`results`](https://github.com/arnetheduck/nim-results); verification returns `bool`. Modules are `{.push raises: [], gcsafe.}` and build under `--mm:refc` and `--mm:orc`.
- Every later call on a closed value returns an error. Do not `close` a value while another thread uses it.

## Aggregate

With the keys and signatures above:

```nim
let
  leaf = LeanPqAggregate.init(
    xmss = [XmssSignedMessage(
      publicKey: xmssPublicKey, message: message, signature: xmssSignature)],
    sphincs = [SphincsSignedMessage(
      publicKey: sphincsPublicKey, message: message, signature: sphincsSignature)],
  ).expect("leaf")
  root = LeanPqAggregate.init([leaf]).expect("root")
  encoded = root.toBytes().expect("bytes")
  received = LeanPqAggregate.fromBytes(
    encoded,
    [LeanPqClaim(publicKey: xmssPublicKey, message: message)],
    [LeanPqClaim(publicKey: sphincsPublicKey, message: message)],
  ).expect("verifies")
doAssert received.xmssClaims().expect("claims").len == 1
```

- `LeanPqAggregate.init` verifies raw signatures first and takes at most `MaxAggregateChildren` (16) children, which it neither consumes nor closes.
- `LeanPqAggregate.initOnly` takes the claims the result proves too, in any order; each must be one the inputs cover.
- `toBytes` is the proof alone: send the claims (`xmssClaims`, `sphincsClaims`) alongside it.
- `LeanPqAggregate.fromBytes` takes the claims in any order (a repeat counts once) and fails for any other set, so every `LeanPqAggregate` is proven.
- `leanPqSetup(threads)` fails if the prover already runs with another thread count. See [Proving](https://github.com/leanEthereum/leanVM/tree/main/bindings#proving).
- A process forked after the prover started cannot aggregate.

## VRF

A key is a 32-byte seed and the slots `start ..< stop`, with `stop <= 2^31`: both fix the root, so keep both. Building it hashes every slot of the range once; a proof then costs about `3 sqrt(R)` hashes for `R` slots. A proof is 1024 bytes: the slot's secret, then its leaf's 31 siblings, which reveal no other secret. An empty range, a range past `2^31` and a slot outside the range return an error.

`cacheToBytes()` encodes the key's cache, its range and cached layer (about `32 sqrt(R)` bytes, no secret), and `VrfKey.fromCacheBytes(seed, root, cache)` rebuilds the key from its seed and that cache without hashing the range, failing if the cache does not lead to `root`.

## Build from source

Needs Rust and [Zig](https://ziglang.org/) 0.15.2. From the repository root, on Linux x86_64:

```sh
rustup target add x86_64-unknown-linux-gnu
rustup component add llvm-tools
cargo install cargo-zigbuild --locked
sh bindings/native/scripts/stage-static.sh x86_64-unknown-linux-gnu bindings/nim/native/x86_64-linux-gnu
cd bindings/nim && nimble test
```

Other platforms stage `aarch64-unknown-linux-gnu` into `native/aarch64-linux-gnu`, `universal2-apple-darwin` into `native/universal-macos` (on macOS), and `x86_64-pc-windows-gnu` into `native/x86_64-windows-gnu`.

Then build your program with `-d:leanPqNativeDir=DIR`, the absolute path of that directory.

## License

MIT or Apache-2.0, at your option.
