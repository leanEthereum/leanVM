# Bindings

leanXMSS and leanSPHINCS signatures, their aggregation, and the consensus VRF tree, for Python, Node.js, Java, Go, Zig and Nim.

- Signing and verifying signatures run in your process, on every platform.
- Aggregating, and verifying aggregates, run in the [sidecar](#sidecar), a separate process (Linux and macOS).
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
pip install py-lean-pq==0.16.0
npm install @kevaundray/lean-pq@0.16.0
go get leanvm.org/go@v0.16.0
version=0.16.0
zig fetch --save=lean_pq "https://github.com/leanEthereum/leanVM/releases/download/bindings-v$version/lean-pq-zig-$version.tar.gz"
```

```kotlin
implementation("io.github.crate-crypto:lean-pq:0.16.0") // Java, Gradle
```

```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.16.0" # Nim, .nimble
```
<!-- x-release-please-end -->

Rust: depend on `lean_vm` directly and build with `RUSTFLAGS="-C target-cpu=native"`:

```toml
lean_vm = { git = "https://github.com/leanEthereum/leanVM.git", features = ["experimental_prover"] }
```

## Sidecar

`leanvm-sidecar` proves and verifies aggregates; the bindings reach it over a Unix socket. Proving is performance critical, so build it from source for the machine that runs it, at the same release as the bindings (a sidecar of another release is not detected, and its proofs are rejected). It needs a recent stable Rust, a C compiler and `make`:

<!-- x-release-please-start-version -->
```sh
RUSTFLAGS="-C target-cpu=native" cargo install --locked --git https://github.com/leanEthereum/leanVM --tag bindings-v0.16.0 leanvm-sidecar --features experimental_prover
```
<!-- x-release-please-end -->

This installs `~/.cargo/bin/leanvm-sidecar`; `leanvm-sidecar --version` prints its release. Then either:

- **Run it** (for example as a service) and `Sidecar.connect("<home>/.leanvm/sidecar.sock")`:
  ```sh
  mkdir -p -m 700 ~/.leanvm && leanvm-sidecar --socket ~/.leanvm/sidecar.sock
  ```
- **Launch it from code**: `Sidecar.start("<home>/.cargo/bin/leanvm-sidecar", "<home>/.leanvm/run/sidecar.sock", threads)` waits until it is ready. Closing the `Sidecar`, dropping it, or the program exiting stops it (a forked child still running keeps it alive). Its socket directory must be private: `start` creates it with mode 0700, and refuses one others can write to.

- `threads` (or `--threads`) caps its threads; 0 means one per core.
- A sidecar serves at most 16 connections: share one `Sidecar` per process. Its calls run one at a time, and a forked child opens its own connection.
- On Linux, a C or Nim program should ignore `SIGPIPE`, so a sidecar that dies fails the call instead of killing the program.
- [`bins/leanvm-sidecar`](../bins/leanvm-sidecar/README.md) documents the sidecar itself.

## Build and test

Needs Rust. Aggregation tests read a running sidecar's socket from `LEANVM_SIDECAR_SOCKET` and its binary from `LEANVM_SIDECAR_BIN`; from the repository root, this builds and starts one and sets both:

```sh
cargo build --release -p leanvm-sidecar --features experimental_prover
export $(sh bindings/scripts/start-sidecar.sh target/release/leanvm-sidecar ~/.leanvm/test)
```

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
