# Bindings

leanXMSS and leanSPHINCS signatures, and their aggregation into one proof, for Python, Node.js, Java, Go, Zig and Nim.

Signing and verifying signatures run in your process. Aggregating runs in a [sidecar](#sidecar), a separate process the bindings start or connect to. An aggregate's bytes are the proof only: send its claims (public key, message) alongside it.

## Install

| Language | Package | Prebuilt for |
| --- | --- | --- |
| [Python](python/README.md) ≥ 3.11 | `py-lean-pq` on PyPI | Linux x86_64/aarch64 (glibc, musl), macOS arm64, Windows x86_64 |
| [Node.js](node/README.md) ≥ 18.17 | `@kevaundray/lean-pq` on npm | Linux x64/arm64 (glibc, musl), macOS x64/arm64, Windows x64 |
| [Java](java/README.md) 25 | `io.github.crate-crypto:lean-pq` on Maven Central | Linux x86_64/aarch64, macOS x86_64/arm64, Windows x86_64 |
| [Go](go/README.md) ≥ 1.24 | `leanvm.org/go` | Linux amd64/arm64, macOS amd64/arm64, Windows amd64 |
| [Zig](zig/README.md) ≥ 0.16 | tarball on each GitHub release | Linux x86_64/aarch64, macOS x86_64/aarch64, Windows x86_64 |
| [Nim](nim/README.md) ≥ 2.2.12 | `bindings/nim` at tag `bindings-vX.Y.Z` | Linux x86_64/aarch64, macOS x86_64/arm64, Windows x86_64 |

On x86_64, the CPU needs AVX2 and PCLMULQDQ.

<!-- x-release-please-start-version -->
```sh
pip install py-lean-pq==0.12.0
npm install @kevaundray/lean-pq@0.12.0
go get leanvm.org/go@v0.12.0
version=0.12.0
zig fetch --save=lean_pq "https://github.com/leanEthereum/leanVM/releases/download/bindings-v$version/lean-pq-zig-$version.tar.gz"
```

Java (Gradle):

```kotlin
implementation("io.github.crate-crypto:lean-pq:0.12.0")
```

Nim (`.nimble`):

```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.12.0"
```
<!-- x-release-please-end -->

Each language's README has the details (Go needs cgo, Java needs `--enable-native-access`).

### Rust

Use `lean_vm` directly, and build in release with `RUSTFLAGS="-C target-cpu=native"`:

```toml
[dependencies]
lean_vm = { git = "https://github.com/leanEthereum/leanVM.git", features = ["experimental_prover"] }
```

## Sidecar

`leanvm-sidecar` proves and verifies aggregates in a process of its own; the bindings talk to it over a Unix socket, so aggregation works on Linux and macOS, not on Windows. Use the sidecar of the same release as the bindings.

Download it (Linux needs glibc 2.35 or newer):

<!-- x-release-please-start-version -->
```sh
# leanvm-sidecar-x86_64-linux, leanvm-sidecar-aarch64-linux or leanvm-sidecar-aarch64-macos
curl -fsSLo leanvm-sidecar https://github.com/leanEthereum/leanVM/releases/download/bindings-v0.12.0/leanvm-sidecar-x86_64-linux
chmod +x leanvm-sidecar
```
<!-- x-release-please-end -->

Or build it for this machine's CPU, which proves faster (needs Rust):

<!-- x-release-please-start-version -->
```sh
RUSTFLAGS="-C target-cpu=native" cargo install --locked --git https://github.com/leanEthereum/leanVM --tag bindings-v0.12.0 leanvm-sidecar --features experimental_prover
```
<!-- x-release-please-end -->

Then either run it yourself and connect to it:

```sh
mkdir -p -m 700 ~/.leanvm
./leanvm-sidecar --socket ~/.leanvm/sidecar.sock
```

It warms up, then creates the socket and serves; connect with `Sidecar.connect("<home>/.leanvm/sidecar.sock")`. Keep it running, for example as a service; `--threads N` caps its threads.

Or let your program launch it: `Sidecar.start("./leanvm-sidecar", "/tmp/leanvm/sidecar.sock")` starts it, waits until it listens, and stops it when the `Sidecar` is closed or the program exits.

[`bins/leanvm-sidecar`](../bins/leanvm-sidecar/README.md) documents the sidecar itself.

## Build from source

Needs Rust. The aggregation tests need a running sidecar (`cargo build --release -p leanvm-sidecar --features experimental_prover` from the repository root, then run it as above) in `LEANVM_SIDECAR_SOCKET`, and its binary in `LEANVM_SIDECAR_BIN`. From the repository root:

| Binding | Build and test |
| --- | --- |
| [Python](python/README.md) | `cd bindings/python && uv run --extra dev pytest tests/` |
| [Node.js](node/README.md) | `cd bindings/node && npm ci && npm run build && npm test` |
| [Java](java/README.md) | `gradle -p bindings/java test` |
| [Go](go/README.md), [Zig](zig/README.md), [Nim](nim/README.md) | build the static library first, as each README shows |
| [`lean-pq`](rust/README.md), the Rust core all of them wrap | `cd bindings && cargo test --release -p lean-pq` |

## Releases

Merging the release pull request that release-please keeps open tags `bindings-vX.Y.Z` and publishes every package. See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or [MIT license](../LICENSE-MIT) at your option.
