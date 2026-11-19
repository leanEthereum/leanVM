# Bindings

leanXMSS and leanSPHINCS signatures, and their aggregation into one proof, for Python, Node.js, Java, Go, Zig and Nim.

An aggregate's bytes are the proof only: send its claims (public key, message) alongside it.

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
pip install py-lean-pq==0.11.1
npm install @kevaundray/lean-pq@0.11.1
go get leanvm.org/go@v0.11.1
zig fetch --save=lean_pq https://github.com/leanEthereum/leanVM/releases/download/bindings-v0.11.1/lean-pq-zig-0.11.1.tar.gz
```

Java (Gradle):

```kotlin
implementation("io.github.crate-crypto:lean-pq:0.11.1")
```

Nim (`.nimble`):

```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.11.1"
```
<!-- x-release-please-end -->

Each language's README has the details (Go needs cgo, Java needs `--enable-native-access`).

### Rust

Use `lean_vm` directly, and build in release with `RUSTFLAGS="-C target-cpu=native"`:

```toml
[dependencies]
lean_vm = { git = "https://github.com/leanEthereum/leanVM.git", features = ["experimental_prover"] }
```

## Build from source

Needs Rust. From the repository root:

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
