# lean-pq Go bindings

Go bindings for leanXMSS and leanSPHINCS signatures, their recursive aggregation, and the consensus VRF.

## Install

<!-- x-release-please-start-version -->
```sh
go get leanvm.org/go@v0.16.0
```
<!-- x-release-please-end -->

Prebuilt for linux/amd64 and linux/arm64 (glibc), darwin/amd64 and darwin/arm64, and windows/amd64: signing and verifying need no Rust.

Needs Go 1.24+ with cgo (`CGO_ENABLED=1`) and a C compiler: gcc or clang on Linux, the Xcode command line tools on macOS, [MinGW-w64](https://www.mingw-w64.org/) gcc on Windows (not MSVC).

## Example

```go
package main

import (
    "log"

    leanpq "leanvm.org/go"
)

func main() {
    message := [32]byte{0x42}

    xmssKey, err := leanpq.XmssSecretKeyFromSeed([32]byte{0x01})
    if err != nil {
        log.Fatal(err)
    }
    defer xmssKey.Close()
    xmssPublicKey, err := xmssKey.PublicKey()
    if err != nil {
        log.Fatal(err)
    }
    xmssSignature, err := xmssKey.Sign(message, 7)
    if err != nil {
        log.Fatal(err)
    }
    if err := leanpq.XmssVerify(xmssPublicKey, message, xmssSignature); err != nil {
        log.Fatal(err)
    }

    sphincsKey, err := leanpq.SphincsSecretKeyFromSeed([32]byte{0x02})
    if err != nil {
        log.Fatal(err)
    }
    defer sphincsKey.Close()
    sphincsPublicKey, err := sphincsKey.PublicKey()
    if err != nil {
        log.Fatal(err)
    }
    sphincsSignature, err := sphincsKey.Sign(message)
    if err != nil {
        log.Fatal(err)
    }
    if err := leanpq.SphincsVerify(sphincsPublicKey, message, sphincsSignature); err != nil {
        log.Fatal(err)
    }
    log.Print("signed and verified with leanXMSS and leanSPHINCS")
}
```

- leanXMSS keys are stateful: store your own leaf index next to `XmssSecretKey.Bytes()` and never sign two different messages at the same index.
- leanSPHINCS keys are stateless and deterministic, and sign at most 2^30 messages.
- `CacheBytes()` returns an `XmssSecretKey`'s trees, which are not secret; `XmssSecretKeyFromCacheBytes(seed, publicKey, cache)` loads the key from them instead of rebuilding them, checking them against the public key.

## VRF

```go
vrfKey, err := leanpq.VrfKeyFromSeed([32]byte{0x03}, 1000, 2000)
if err != nil {
    log.Fatal(err)
}
defer vrfKey.Close()
root, err := vrfKey.Root()
if err != nil {
    log.Fatal(err)
}
proof, err := vrfKey.Proof(1500)
if err != nil {
    log.Fatal(err)
}
if err := leanpq.VrfVerify(root, 1500, proof); err != nil {
    log.Fatal(err)
}
```

A key is a 32-byte seed and the slots `[start, end)`, with `end <= 2^31`: both fix the root, so keep both. Building it hashes every slot of the range once; a proof then costs about `3 sqrt(R)` hashes for `R` slots. A proof is 1024 bytes: the slot's secret, then its leaf's 31 siblings, which reveal no other secret. An empty range, a range past `2^31` and a slot outside the range return an error.

`CacheBytes()` encodes the key's cache, its range and cached layer (about `32 sqrt(R)` bytes, no secret), and `VrfKeyFromCacheBytes(seed, root, cache)` rebuilds the key from its seed and that cache without hashing the range, failing if the cache does not lead to `root`.

## Aggregate

Aggregation runs in a leanVM sidecar, on Linux and macOS: see [the sidecar](../README.md#sidecar). With the keys and signatures above:

```go
sidecar, err := leanpq.ConnectSidecar("/home/me/.leanvm/sidecar.sock")
if err != nil {
    log.Fatal(err)
}
defer sidecar.Close()

leaf, err := sidecar.Aggregate(
    nil,
    []leanpq.XmssSignedMessage{{PublicKey: xmssPublicKey, Message: message, Signature: xmssSignature}},
    []leanpq.SphincsSignedMessage{{PublicKey: sphincsPublicKey, Message: message, Signature: sphincsSignature}},
)
if err != nil {
    log.Fatal(err)
}
defer leaf.Close()
root, err := sidecar.Aggregate([]*leanpq.Aggregate{leaf}, nil, nil)
if err != nil {
    log.Fatal(err)
}
defer root.Close()

encoded, err := root.Bytes()
if err != nil {
    log.Fatal(err)
}
received, err := sidecar.Verify(
    encoded,
    []leanpq.Claim{{PublicKey: xmssPublicKey, Message: message}},
    []leanpq.Claim{{PublicKey: sphincsPublicKey, Message: message}},
)
if err != nil {
    log.Fatal(err)
}
defer received.Close()
```

- `Aggregate` verifies raw signatures first and takes at most 16 children, which it neither consumes nor closes.
- `Bytes()` is the proof alone: send the claims (`XmssClaims()`, `SphincsClaims()`) alongside it.
- `Verify` takes the claims in any order (a repeat counts once) and rejects any other set, so every `Aggregate` is proven.
- Verifying an aggregate also needs the sidecar.
- `StartSidecar(binaryPath, socketPath, threads)` launches a sidecar instead, on a socket in a private directory such as `~/.leanvm/run/sidecar.sock` (`threads` 0: one per core). `Prover()` returns `experimental` or `stable`; both make the same proofs.
- A `Sidecar` is safe for concurrent use. A sidecar serves at most 16 connections, so share one `Sidecar` per process.
- `Close` stops a sidecar `StartSidecar` launched at once, failing calls in progress, then closes the connection; later calls fail.

## Build from source

Needs Rust and [Zig](https://ziglang.org/) 0.15.2. From the repository root, on Linux x86_64:

```sh
rustup target add x86_64-unknown-linux-gnu
rustup component add llvm-tools
cargo install cargo-zigbuild --locked
sh bindings/native/scripts/stage-static.sh x86_64-unknown-linux-gnu bindings/go/internal/native/linux_amd64
cd bindings/go && go test ./...
```

Other platforms stage `aarch64-unknown-linux-gnu` into `linux_arm64`, `universal2-apple-darwin` into `darwin_universal` (on macOS, with both Apple Rust targets), and `x86_64-pc-windows-gnu` into `windows_amd64`.

Aggregation tests connect to the sidecar at `LEANVM_SIDECAR_SOCKET` and start one from `LEANVM_SIDECAR_BIN`.

## License

MIT or Apache-2.0, at your option.
