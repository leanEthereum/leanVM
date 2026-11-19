# lean-pq Nim bindings

Nim bindings for post-quantum signatures and their recursive aggregation:

- **leanXMSS**: stateful. A key signs at `2^32` leaf indices; never sign two different messages at the same leaf index.
- **leanSPHINCS**: stateless. A key signs at most `2^30` messages; signing is deterministic.

The bindings follow the [Status Nim style guide](https://status-im.github.io/nim-style-guide/). Every module is `{.push raises: [], gcsafe.}`, fallible calls return `Result[T, string]` from [`results`](https://github.com/arnetheduck/nim-results), and verification returns `bool`. They build with Nim 2.2.12 or newer under both `--mm:refc` and `--mm:orc`, and the tests compile with `--styleCheck:error` and a strict `warningAsError` and `hintAsError` set.

Public keys and messages are `array[32, byte]`; signatures are `array[2404, byte]` (leanXMSS) and `array[7740, byte]` (leanSPHINCS). `XmssSecretKey`, `SphincsSecretKey`, `LeanPqSidecar` and `LeanPqAggregate` are references to native handles. The garbage collector frees each handle once nothing refers to it, and `close` frees it at once; every later call on a closed value returns an error.

The binding links the Rust bridge's static `liblean_pq_native.a` for the target. Each release attaches it for Linux x86_64 and aarch64 (glibc), macOS (universal) and Windows x86_64 (MinGW-w64 gcc, Nim's default Windows compiler), and the package's first build downloads it with curl.

## Install

The package is `bindings/nim` at the tag `bindings-v<version>` and needs no Rust toolchain. Nim 2.2.12 or newer, with Nimble:

<!-- x-release-please-start-version -->
```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.12.0"
```
<!-- x-release-please-end -->

or, from the command line:

<!-- x-release-please-start-version -->
```sh
nimble install "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.12.0"
```
<!-- x-release-please-end -->

With [nimbus-build-system](https://github.com/status-im/nimbus-build-system), vendor the repository at the same tag as a submodule and add `--path:"vendor/leanVM/bindings/nim"` to the build's `config.nims`:

<!-- x-release-please-start-version -->
```sh
git submodule add https://github.com/leanEthereum/leanVM vendor/leanVM
git -C vendor/leanVM checkout bindings-v0.12.0
```
<!-- x-release-please-end -->

The package depends on `results`.

The package picks the release archive for the build target. For any other target, or to build without network access, build `liblean_pq_native.a` yourself and pass its directory with `-d:leanPqNativeDir=DIR`. On Windows the release archive targets the GNU ABI; the MSVC compiler (`--cc:vcc`) is not supported.

## Build from source

Stage the static archive for your platform in the directory the package links from, then run the tests, which build with both memory managers. On Linux x86_64:

```sh
rustup target add x86_64-unknown-linux-gnu
cargo install cargo-zigbuild --locked
sh bindings/native/scripts/stage-static.sh x86_64-unknown-linux-gnu bindings/nim/native/x86_64-linux-gnu
cd bindings/nim
nimble test
```

`stage-static.sh` needs [Zig](https://ziglang.org/) 0.15.2 for `cargo-zigbuild`. Each platform stages its archive from one Rust target:

| Rust target | Package directory |
| --- | --- |
| `x86_64-unknown-linux-gnu` | `native/x86_64-linux-gnu` |
| `aarch64-unknown-linux-gnu` | `native/aarch64-linux-gnu` |
| `universal2-apple-darwin` (on macOS) | `native/universal-macos` |
| `x86_64-pc-windows-gnu` | `native/x86_64-windows-gnu` |

The aggregation tests prove through the sidecar listening on `LEANVM_SIDECAR_SOCKET`, and one starts its own from the executable at `LEANVM_SIDECAR_BIN`; on Windows they only check that the sidecar is unsupported. `scripts/stage-release.sh` stages the archives a release attaches, and `scripts/consumer-smoke.sh` proves the package works as a Nimble dependency without Rust.

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

leanXMSS keys are stateful: persist your own durable high-water leaf index alongside `XmssSecretKey.toBytes()` and advance it before publishing a signature. Secret key bytes are secret material, the leanXMSS or leanSPHINCS seed; wipe your copies when done.

Do not `close` a value while another thread uses it.

## Aggregate

Aggregation runs in a leanVM sidecar, a process of its own on Linux and macOS: see [the sidecar](../README.md#sidecar) for how to get and run it.

`LeanPqSidecar.connect(socketPath)` connects to a running sidecar; `LeanPqSidecar.start(binaryPath, socketPath)` launches one, waits until it listens and connects, and `close` (or collection) stops it. Calls on one `LeanPqSidecar` run one at a time, and a broken connection is reopened on the next call. On Windows `connect` and `start` return an error. With the keys and signatures of the example above:

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

# The encoding is the proof alone: the receiver supplies the claims it expects.
let
  encoded = root.toBytes().expect("bytes")
  expectedXmss = [LeanPqClaim(publicKey: xmssPublicKey, message: message)]
  expectedSphincs = [LeanPqClaim(publicKey: sphincsPublicKey, message: message)]
  received = sidecar.verify(encoded, expectedXmss, expectedSphincs).expect("verifies")
doAssert received.xmssClaims().expect("claims") == @expectedXmss
doAssert sidecar.verify(encoded, expectedXmss).isErr()
```

- `aggregate` verifies every raw signature before proving, and takes at most `MaxAggregateChildren` (16) children, which it neither consumes nor closes.
- `LeanPqAggregate.toBytes` encodes the proof alone, without its claims: send the claims alongside it, or let the receiver rebuild them.
- `verify(bytes, xmssClaims, sphincsClaims)` checks the proof against exactly the given claims, in any order with a repeated claim counting once, and fails for any other claim set, so every `LeanPqAggregate` value is proven. `xmssClaims` and `sphincsClaims` return the claims strictly sorted, in the form `verify` takes.
