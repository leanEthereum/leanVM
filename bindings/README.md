# Bindings

leanXMSS and leanSPHINCS signatures, their aggregation, and the consensus VRF tree, for Python, Node.js, Java, .NET, Go, Zig and Nim.

An aggregate's bytes are the proof only: send its claims (public key, message) alongside.

## Install

| Language | Package | Prebuilt for |
| --- | --- | --- |
| [Python](python/README.md) 3.11+ | `py-lean-pq` (PyPI) | Linux x86_64/aarch64 (glibc, musl), macOS arm64, Windows x86_64 |
| [Node.js](node/README.md) 18.17+ | `@kevaundray/lean-pq` (npm) | Linux x64/arm64 (glibc, musl), macOS x64/arm64, Windows x64 |
| [Java](java/README.md) 25 | `io.github.crate-crypto:lean-pq` (Maven Central) | Linux x86_64/aarch64, macOS x86_64/arm64, Windows x86_64 |
| [.NET](dotnet/README.md) 10 | `Ethereum.LeanPq` (NuGet) | Linux x64/arm64 (glibc), macOS x64/arm64, Windows x64 |
| [Go](go/README.md) 1.24+ | `leanvm.org/go` | Linux amd64/arm64, macOS amd64/arm64, Windows amd64 |
| [Zig](zig/README.md) 0.16+ | tarball on each GitHub release | Linux x86_64/aarch64, macOS x86_64/aarch64, Windows x86_64 |
| [Nim](nim/README.md) 2.2.12+ | `bindings/nim` at tag `bindings-vX.Y.Z` | Linux x86_64/aarch64, macOS x86_64/arm64, Windows x86_64 |

x86_64 needs AVX2 and PCLMULQDQ.

<!-- x-release-please-start-version -->
```sh
pip install py-lean-pq==0.19.1
npm install @kevaundray/lean-pq@0.19.1
dotnet add package Ethereum.LeanPq --version 0.19.1
go get leanvm.org/go@v0.19.1
version=0.19.1
zig fetch --save=lean_pq "https://github.com/leanEthereum/leanVM/releases/download/bindings-v$version/lean-pq-zig-$version.tar.gz"
```

```kotlin
implementation("io.github.crate-crypto:lean-pq:0.19.1") // Java, Gradle
```

```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.19.1" # Nim, .nimble
```
<!-- x-release-please-end -->

Rust: depend on `lean_vm` directly, build with `RUSTFLAGS="-C target-cpu=native"` and install jemalloc as [`crates/allocator`](../crates/allocator/src/lib.rs) does:

```toml
lean_vm = { git = "https://github.com/leanEthereum/leanVM.git", features = ["experimental_prover"] }
```

## Proving

- Prebuilt packages hold the prover once per CPU tier and run the fastest one the CPU supports, except Python, Java and .NET on Windows. A source build gets the tiers with `RUSTC_WRAPPER` set to the checkout's `scripts/tier-rustc` (not on Windows), or matches them with `RUSTFLAGS="-C target-cpu=native"` on the proving machine.
- `setup(threads)`, before the first aggregation, starts the prover with `threads` threads (0: one per physical core); it fails above the machine's parallelism. Proofs run one at a time per process.
- When the build leaves a faster tier unused on this CPU, the first aggregation prints a warning on stderr, which `LEANVM_TIER` set to the tier it names silences.
- Except on Windows, the Rust code allocates with jemalloc, which keeps freed pages: a process that aggregated keeps its peak memory.

## Build and test

Needs Rust.

| Binding | Command, from the repository root |
| --- | --- |
| [Python](python/README.md) | `cd bindings/python && uv run --extra dev pytest tests/` |
| [Node.js](node/README.md) | `cd bindings/node && npm ci && npm run build && npm test` |
| [Java](java/README.md) | `gradle -p bindings/java test` |
| [.NET](dotnet/README.md) | `dotnet test bindings/dotnet/Ethereum.LeanPq.slnx` |
| [Go](go/README.md), [Zig](zig/README.md), [Nim](nim/README.md) | stage the static library first (see each README) |
| [`lean-pq`](rust/README.md), the Rust core all of them wrap | `cd bindings && cargo test --release -p lean-pq` |

## Releases

The package version follows the API. `PROTOCOL_VERSION` (`protocolVersion()` or `ProtocolVersion` in some languages) is separate: proofs and signatures interoperate only between packages with the same one. Changing it bumps at least the minor version.

Merging the release pull request that release-please keeps open tags `bindings-vX.Y.Z` and publishes every package: see [CHANGELOG.md](CHANGELOG.md) and [RELEASING.md](RELEASING.md).

## License

MIT or Apache-2.0, at your option: [LICENSE-MIT](../LICENSE-MIT), [LICENSE-APACHE](../LICENSE-APACHE).
