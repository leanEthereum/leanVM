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
LEANVM_SIDECAR_SOCKET=~/.leanvm/sidecar.sock LEANVM_SIDECAR_BIN=/path/to/leanvm-sidecar go test ./...
```

The aggregation tests prove through the sidecar listening on `LEANVM_SIDECAR_SOCKET`, and one of them starts its own from `LEANVM_SIDECAR_BIN`; on Windows they only check that connecting fails.

Each platform stages its archive from one Rust target:

| Rust target | Go native-asset directory |
| --- | --- |
| `x86_64-unknown-linux-gnu` | `linux_amd64` |
| `aarch64-unknown-linux-gnu` | `linux_arm64` |
| `universal2-apple-darwin` | `darwin_universal` |
| `x86_64-pc-windows-gnu` | `windows_amd64` |

The universal macOS build requires both `x86_64-apple-darwin` and `aarch64-apple-darwin` Rust targets and runs on macOS so `cargo-zigbuild` can use the installed SDK.

`scripts/assemble-module.sh` builds the published module's proxy files from the release archives, and `scripts/consumer-smoke.sh` proves it works through `go get` without Rust, by running the example below. A release attaches the files to its GitHub release, and the Website workflow serves every release's files from `leanvm.org/goproxy`, which `leanvm.org/go`'s `go-import` tag names.

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

leanXMSS keys are stateful: persist your own durable high-water leaf index alongside `XmssSecretKey.Bytes()` and never sign two different messages at the same leaf index. leanSPHINCS keys are stateless and deterministic: `SphincsSecretKey.Bytes()` is the 32-byte seed, and a key signs at most 2^30 messages.

## Aggregation

Aggregation runs in a leanVM sidecar, a separate process on Linux and macOS: see [the bindings README](../README.md#sidecar) to get and run it. `ConnectSidecar(socketPath)` connects to a running sidecar; `StartSidecar(binaryPath, socketPath)` launches one, and `Close` stops it. A `Sidecar` is safe for concurrent use.

Continuing the example above:

```go
home, err := os.UserHomeDir()
if err != nil {
    log.Fatal(err)
}
sidecar, err := leanpq.ConnectSidecar(filepath.Join(home, ".leanvm", "sidecar.sock"))
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

encoded, err := root.Bytes() // the proof alone: send the claims alongside it
if err != nil {
    log.Fatal(err)
}
// The receiver supplies the claims it expects; Verify checks the proof proves exactly these.
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

- `Sidecar.Aggregate` verifies every raw signature before proving, and accepts at most 16 children.
- `Aggregate.Bytes()` encodes the proof alone, not its claims: send `XmssClaims()` and `SphincsClaims()` alongside it, or have the receiver rebuild the claims it expects.
- `Sidecar.Verify(bytes, xmssClaims, sphincsClaims)` checks the proof against exactly those claims, given in any order with a repeated claim counted once, and rejects any other claim set, so every `Aggregate` is proven.
