# lean-pq Nim bindings

Nim bindings for leanXMSS and leanSPHINCS signatures and their recursive aggregation.

## Install

Needs Nim 2.2.12+. In your `.nimble`:

<!-- x-release-please-start-version -->
```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.12.0"
```
<!-- x-release-please-end -->

Or from the command line:

<!-- x-release-please-start-version -->
```sh
nimble install "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.12.0"
```
<!-- x-release-please-end -->

With [nimbus-build-system](https://github.com/status-im/nimbus-build-system), vendor the tag as a submodule and add `--path:"vendor/leanVM/bindings/nim"` to `config.nims`:

<!-- x-release-please-start-version -->
```sh
git submodule add https://github.com/leanEthereum/leanVM vendor/leanVM
git -C vendor/leanVM checkout bindings-v0.12.0
```
<!-- x-release-please-end -->

The first build downloads the prebuilt archive with curl, for Linux x86_64 and aarch64 (glibc), macOS (universal) and Windows x86_64 (MinGW-w64 gcc, not `--cc:vcc`), so signing and verifying need no Rust. For other targets or offline builds, pass `-d:leanPqNativeDir=DIR` holding your own `liblean_pq_native.a`.

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

  # Handles are freed when collected; `close` frees them now.
  xmssKey.close()
  doAssert xmssKey.sign(message, 8).isErr()

main()
```

- leanXMSS keys are stateful: store your own leaf index next to `XmssSecretKey.toBytes()` and never sign two different messages at the same index.
- leanSPHINCS keys are stateless and deterministic, and sign at most `2^30` messages.
- Fallible calls return `Result[T, string]` from [`results`](https://github.com/arnetheduck/nim-results); verification returns `bool`. Modules are `{.push raises: [], gcsafe.}` and build under `--mm:refc` and `--mm:orc`.
- Every later call on a closed value returns an error. Do not `close` a value while another thread uses it.

## Aggregate

Aggregation runs in a leanVM sidecar, on Linux and macOS: see [the sidecar](../README.md#sidecar). With the keys and signatures above:

```nim
let
  sidecar = LeanPqSidecar.connect("/home/me/.leanvm/sidecar.sock").expect("sidecar")
  leaf = sidecar.aggregate(
    xmss = [XmssSignedMessage(
      publicKey: xmssPublicKey, message: message, signature: xmssSignature)],
    sphincs = [SphincsSignedMessage(
      publicKey: sphincsPublicKey, message: message, signature: sphincsSignature)],
  ).expect("leaf")
  root = sidecar.aggregate([leaf]).expect("root")
  encoded = root.toBytes().expect("bytes")
  received = sidecar.verify(
    encoded,
    [LeanPqClaim(publicKey: xmssPublicKey, message: message)],
    [LeanPqClaim(publicKey: sphincsPublicKey, message: message)],
  ).expect("verifies")
doAssert received.xmssClaims().expect("claims").len == 1
sidecar.close()
```

- `aggregate` verifies raw signatures first and takes at most `MaxAggregateChildren` (16) children, which it neither consumes nor closes.
- `toBytes` is the proof alone: send the claims (`xmssClaims`, `sphincsClaims`) alongside it.
- `verify` takes the claims in any order (a repeat counts once) and fails for any other set, so every `LeanPqAggregate` is proven.
- `LeanPqSidecar.start(binaryPath, socketPath, threads = 0)` launches a sidecar instead (`threads` 0: one per core). `prover()` returns `experimental` or `stable`.
- Calls on one `LeanPqSidecar` run one at a time. `close` disconnects and stops a sidecar `start` launched.

## Build from source

Needs Rust and [Zig](https://ziglang.org/) 0.15.2. From the repository root, on Linux x86_64:

```sh
rustup target add x86_64-unknown-linux-gnu
cargo install cargo-zigbuild --locked
sh bindings/native/scripts/stage-static.sh x86_64-unknown-linux-gnu bindings/nim/native/x86_64-linux-gnu
cd bindings/nim && nimble test
```

Other platforms stage `aarch64-unknown-linux-gnu` into `native/aarch64-linux-gnu`, `universal2-apple-darwin` into `native/universal-macos` (on macOS), and `x86_64-pc-windows-gnu` into `native/x86_64-windows-gnu`.

Aggregation tests connect to the sidecar at `LEANVM_SIDECAR_SOCKET` and start one from `LEANVM_SIDECAR_BIN`.

## License

MIT or Apache-2.0, at your option.
