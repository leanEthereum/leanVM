# Bindings

leanXMSS and leanSPHINCS signatures and their aggregation, for Python, Node.js, Java, Go, Zig and Nim.

- Signing and verifying run in your process, on every platform.
- Aggregating runs in the [sidecar](#sidecar), a separate process (Linux and macOS).
- An aggregate's bytes are the proof only: send its claims (public key, message) alongside.

## Install

| Language | Package | Prebuilt for |
| --- | --- | --- |
| [Python](python/README.md) 3.11+ | `py-lean-pq` (PyPI) | Linux x86_64/aarch64 (glibc, musl), macOS arm64, Windows x86_64 |
| [Node.js](node/README.md) 18.17+ | `@kevaundray/lean-pq` (npm) | Linux x64/arm64 (glibc, musl), macOS x64/arm64, Windows x64 |
| [Java](java/README.md) 25 | `io.github.crate-crypto:lean-pq` (Maven Central) | Linux x86_64/aarch64, macOS x86_64/arm64, Windows x86_64 |
| [Go](go/README.md) 1.24+ | `leanvm.org/go` | Linux amd64/arm64, macOS amd64/arm64, Windows amd64 |
| [Zig](zig/README.md) 0.16+ | tarball on each GitHub release | Linux x86_64/aarch64, macOS x86_64/aarch64, Windows x86_64 |
| [Nim](nim/README.md) 2.2.12+ | `bindings/nim` at tag `bindings-vX.Y.Z` | Linux x86_64/aarch64, macOS x86_64/arm64, Windows x86_64 |

x86_64 needs AVX2 and PCLMULQDQ.

<!-- x-release-please-start-version -->
```sh
pip install py-lean-pq==0.12.0
npm install @kevaundray/lean-pq@0.12.0
go get leanvm.org/go@v0.12.0
version=0.12.0
zig fetch --save=lean_pq "https://github.com/leanEthereum/leanVM/releases/download/bindings-v$version/lean-pq-zig-$version.tar.gz"
```

```kotlin
implementation("io.github.crate-crypto:lean-pq:0.12.0") // Java, Gradle
```

```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.12.0" # Nim, .nimble
```
<!-- x-release-please-end -->

Rust: depend on `lean_vm` directly and build with `RUSTFLAGS="-C target-cpu=native"`:

```toml
lean_vm = { git = "https://github.com/leanEthereum/leanVM.git", features = ["experimental_prover"] }
```

## Sidecar

`leanvm-sidecar` proves and verifies aggregates; the bindings reach it over a Unix socket. Proving is performance critical, so build it from source for the machine that runs it (needs Rust), at the same release as the bindings:

<!-- x-release-please-start-version -->
```sh
RUSTFLAGS="-C target-cpu=native" cargo install --locked --git https://github.com/leanEthereum/leanVM --tag bindings-v0.12.0 leanvm-sidecar --features experimental_prover
```
<!-- x-release-please-end -->

This installs `~/.cargo/bin/leanvm-sidecar`. Then either:

- **Run it** (for example as a service) and `Sidecar.connect("<home>/.leanvm/sidecar.sock")`:
  ```sh
  mkdir -p -m 700 ~/.leanvm && leanvm-sidecar --socket ~/.leanvm/sidecar.sock
  ```
- **Launch it from code**: `Sidecar.start("<home>/.cargo/bin/leanvm-sidecar", "/tmp/leanvm/sidecar.sock", threads)` waits until it is ready; closing the `Sidecar`, or the program exiting, stops it.

`threads` (or `--threads`) caps its threads; 0 means one per core. [`bins/leanvm-sidecar`](../bins/leanvm-sidecar/README.md) documents the sidecar itself.

## Build and test

Needs Rust. Aggregation tests read a running sidecar's socket from `LEANVM_SIDECAR_SOCKET` and its binary from `LEANVM_SIDECAR_BIN` (build it with `cargo build --release -p leanvm-sidecar --features experimental_prover` at the repository root).

| Binding | Command, from the repository root |
| --- | --- |
| [Python](python/README.md) | `cd bindings/python && uv run --extra dev pytest tests/` |
| [Node.js](node/README.md) | `cd bindings/node && npm ci && npm run build && npm test` |
| [Java](java/README.md) | `gradle -p bindings/java test` |
| [Go](go/README.md), [Zig](zig/README.md), [Nim](nim/README.md) | stage the static library first (see each README) |
| [`lean-pq`](rust/README.md), the Rust core all of them wrap | `cd bindings && cargo test --release -p lean-pq` |

## Releases

Merging the release pull request that release-please keeps open tags `bindings-vX.Y.Z` and publishes every package: see [CHANGELOG.md](CHANGELOG.md) and [RELEASING.md](RELEASING.md).

## License

MIT or Apache-2.0, at your option: [LICENSE-MIT](../LICENSE-MIT), [LICENSE-APACHE](../LICENSE-APACHE).
