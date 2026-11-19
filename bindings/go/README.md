# lean-pq Go bindings

Go bindings for leanXMSS and leanSPHINCS signatures and their recursive aggregation, over a Rust static archive that cgo links into the program. The API exposes Go values with `Close` methods, never C pointers.

## Install

Each release publishes `leanvm.org/go` with the native archives built in, so `go get` needs no Rust toolchain:

<!-- x-release-please-start-version -->
```sh
go get leanvm.org/go@v0.12.0
```
<!-- x-release-please-end -->

Requirements:

- Go 1.24 or newer with cgo enabled (`CGO_ENABLED=1`)
- A C compiler for the target platform: gcc or clang on Linux, the Xcode command line tools on macOS, and [MinGW-w64](https://www.mingw-w64.org/) gcc on PATH on Windows (cgo does not use MSVC)

Supported platforms:

| `GOOS`/`GOARCH` | Bundled archive |
| --- | --- |
| `linux/amd64` | `internal/native/linux_amd64` (glibc) |
| `linux/arm64` | `internal/native/linux_arm64` (glibc) |
| `darwin/amd64`, `darwin/arm64` | `internal/native/darwin_universal` |
| `windows/amd64` | `internal/native/windows_amd64` (MinGW-w64) |

Build tags select the archive, which cgo links statically. The archives are never committed: a checkout needs the source build below.

## Source build and test

From the repository root, with [Zig](https://ziglang.org/) 0.15.2 installed, stage the Linux amd64 archive and test:

```sh
rustup target add x86_64-unknown-linux-gnu
cargo install cargo-zigbuild --locked
sh bindings/native/scripts/stage-static.sh x86_64-unknown-linux-gnu bindings/go/internal/native/linux_amd64
cd bindings/go
go test ./...
```

The aggregation test proves recursively: expect seconds per proof and over a gigabyte of memory.

Each platform stages its archive from one Rust target:

| Rust target | Go native-asset directory |
| --- | --- |
| `x86_64-unknown-linux-gnu` | `linux_amd64` |
| `aarch64-unknown-linux-gnu` | `linux_arm64` |
| `universal2-apple-darwin` | `darwin_universal` |
| `x86_64-pc-windows-gnu` | `windows_amd64` |

The universal macOS build requires both `x86_64-apple-darwin` and `aarch64-apple-darwin` Rust targets and runs on macOS so `cargo-zigbuild` can use the installed SDK.

`scripts/assemble-module.sh` builds the published module's proxy files from the release archives, and `scripts/consumer-smoke.sh` proves it works through `go get` without Rust. A release attaches the files to its GitHub release, and the Website workflow serves every release's files from `leanvm.org/goproxy`, which `leanvm.org/go`'s `go-import` tag names.

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

    leaf, err := leanpq.AggregateSignatures(
        nil,
        []leanpq.XmssSignedMessage{{PublicKey: xmssPublicKey, Message: message, Signature: xmssSignature}},
        []leanpq.SphincsSignedMessage{{PublicKey: sphincsPublicKey, Message: message, Signature: sphincsSignature}},
    )
    if err != nil {
        log.Fatal(err)
    }
    defer leaf.Close()
    root, err := leanpq.AggregateSignatures([]*leanpq.Aggregate{leaf}, nil, nil)
    if err != nil {
        log.Fatal(err)
    }
    defer root.Close()

    encoded, err := root.Bytes() // the proof alone: send the claims alongside it
    if err != nil {
        log.Fatal(err)
    }
    xmssClaims, err := root.XmssClaims()
    if err != nil {
        log.Fatal(err)
    }
    sphincsClaims, err := root.SphincsClaims()
    if err != nil {
        log.Fatal(err)
    }
    // Decodes the proof and verifies it proves exactly these claims.
    received, err := leanpq.AggregateFromBytes(encoded, xmssClaims, sphincsClaims)
    if err != nil {
        log.Fatal(err)
    }
    defer received.Close()
    log.Printf("leanXMSS claims: %x", xmssClaims)
}
```

leanXMSS keys are stateful: persist your own durable high-water leaf index alongside `XmssSecretKey.Bytes()` and never sign two different messages at the same leaf index. leanSPHINCS keys are stateless and deterministic: `SphincsSecretKey.Bytes()` is the 32-byte seed, and a key signs at most 2^30 messages.

`XmssSecretKey.CacheBytes()` returns the trees a key holds, which are not secret, and `XmssSecretKeyFromCacheBytes(seed, publicKey, cache)` loads a key from them in place of building the trees, which is what key generation spends its time on. The cache is checked against the public key.

`Aggregate.Bytes()` encodes the proof alone, not its claims: send `XmssClaims()` and `SphincsClaims()` alongside it, or have the receiver rebuild the claims it expects. `AggregateFromBytes(bytes, xmssClaims, sphincsClaims)` verifies the proof against exactly those claims, given in any order with a repeated claim counted once, and rejects any other claim set. `AggregateSignatures` verifies every raw signature before proving, so every `Aggregate` is proven. `Setup` moves the one-time setup ahead of the first proof; calling it is optional.
