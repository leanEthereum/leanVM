# lean-pq bindings

Bindings for stateful **leanXMSS**, stateless **leanSPHINCS**, and recursive aggregation of both into one proof. Every binding wraps the Rust facade [`lean-pq`](rust/README.md), which keeps the proving parameters internal.

An encoded aggregate is the proof alone. Its claims, the (public key, message) pairs it proves, travel separately: a receiver decodes the proof together with the claims it expects, and decoding fails unless the proof proves exactly those.

## Install

Each `bindings-vX.Y.Z` release publishes every package at `X.Y.Z`. Prebuilt packages need no Rust toolchain.

| Language | Package | Prebuilt for |
| --- | --- | --- |
| [Python](python/README.md) ≥ 3.11 | `py-lean-pq` on PyPI | Linux x86_64/aarch64 (glibc, musl), macOS arm64, Windows x86_64 |
| [Node.js](node/README.md) ≥ 18.17 | `@kevaundray/lean-pq` on npm | Linux x64/arm64 (glibc, musl), macOS x64/arm64, Windows x64 |
| [Java](java/README.md) 25 | `io.github.crate-crypto:lean-pq` on Maven Central | Linux x86_64/aarch64 (glibc 2.17+), macOS x86_64/arm64, Windows x86_64 |
| [Go](go/README.md) ≥ 1.24 | `leanvm.org/go` | Linux amd64/arm64 (glibc), macOS amd64/arm64, Windows amd64 |
| [Zig](zig/README.md) ≥ 0.16 | package attached to each GitHub release | Linux x86_64/aarch64 (glibc), macOS x86_64/aarch64, Windows x86_64 |
| [Nim](nim/README.md) ≥ 2.2.12 | Nimble package `lean_pq`, `bindings/nim` at tag `bindings-vX.Y.Z` | Linux x86_64/aarch64 (glibc), macOS x86_64/arm64, Windows x86_64 (MinGW) |
| [Rust](rust/README.md) | `lean-pq` from git | built from source |

The x86_64 builds require a CPU with AVX2 and PCLMULQDQ.

### Python

<!-- x-release-please-start-version -->
```sh
pip install py-lean-pq==0.11.1
```
<!-- x-release-please-end -->

### Node.js

<!-- x-release-please-start-version -->
```sh
npm install @kevaundray/lean-pq@0.11.1
```
<!-- x-release-please-end -->

npm installs the binary for your platform through an optional dependency; installing with `--omit=optional` leaves the package unable to load.

### Java

Gradle (Kotlin DSL):

<!-- x-release-please-start-version -->
```kotlin
implementation("io.github.crate-crypto:lean-pq:0.11.1")
```
<!-- x-release-please-end -->

Maven:

<!-- x-release-please-start-version -->
```xml
<dependency>
  <groupId>io.github.crate-crypto</groupId>
  <artifactId>lean-pq</artifactId>
  <version>0.11.1</version>
</dependency>
```
<!-- x-release-please-end -->

The jar bundles the native library for each platform. Run with `--enable-native-access=org.ethereum.leanpq`.

### Go

<!-- x-release-please-start-version -->
```sh
go get leanvm.org/go@v0.11.1
```
<!-- x-release-please-end -->

The module, served from leanvm.org, links a bundled static library through cgo, so it needs `CGO_ENABLED=1` and a C compiler: gcc or clang on Linux, the Xcode command line tools on macOS, and MinGW-w64 gcc on Windows.

### Zig

<!-- x-release-please-start-version -->
```sh
version=0.11.1
zig fetch --save=lean_pq "https://github.com/leanEthereum/leanVM/releases/download/bindings-v$version/lean-pq-zig-$version.tar.gz"
```
<!-- x-release-please-end -->

Then add the module in `build.zig`:

```zig
const lean_pq = b.dependency("lean_pq", .{ .target = target, .optimize = optimize });
exe.root_module.addImport("lean_pq", lean_pq.module("lean_pq"));
```

On Windows the bundled archive targets Zig's default `x86_64-windows-gnu` ABI.

### Nim

In your `.nimble` file:

<!-- x-release-please-start-version -->
```nim
requires "https://github.com/leanEthereum/leanVM?subdir=bindings/nim#bindings-v0.11.1"
```
<!-- x-release-please-end -->

The first build downloads the target's native archive from the release; the tag also works as a nimbus-build-system `vendor/` submodule.

### Rust

The crate is not on crates.io, as the crates it builds on are not:

<!-- x-release-please-start-version -->
```toml
[dependencies]
lean-pq = { git = "https://github.com/leanEthereum/leanVM.git", tag = "bindings-v0.11.1" }
```
<!-- x-release-please-end -->

## Build from source

Every binding builds against the crates in the same checkout. The bindings are their own Cargo workspace, excluded from the root one: run cargo from `bindings/` or below, so that [`bindings/.cargo/config.toml`](.cargo/config.toml) replaces the root's `target-cpu=native` with the portable baseline. Commands without a directory run from the repository root:

| Binding | Local build and test | Prerequisites |
| --- | --- | --- |
| [Python](python/README.md) | `uv run --extra dev maturin develop --release`, then `uv run --extra dev pytest tests/` in `bindings/python` | Rust, uv |
| [Node.js](node/README.md) | `npm ci && npm run build && npm test` in `bindings/node` | Rust, Node.js 18.17+ |
| [Java](java/README.md) | `gradle -p bindings/java test` | Rust, JDK 25, Gradle 9.1+ |
| [Go](go/README.md) | stage the static archive (below), then `go test ./...` in `bindings/go` | Rust, Go 1.24+, cgo, Zig, `cargo-zigbuild` |
| [Zig](zig/README.md) | stage the static archive (below), then `zig build test -Dnative-dir=…` in `bindings/zig` | Rust, Zig 0.16+, `cargo-zigbuild` |
| [Nim](nim/README.md) | stage the static archive (below) in `bindings/nim/native/<target>`, then `nimble test` in `bindings/nim` | Rust, Nim 2.2.12+, `cargo-zigbuild` |
| [Rust](rust/README.md) | `cargo test --release -p lean-pq` in `bindings` | Rust |

Go, Zig and Nim link a static archive for the build target. For Linux x86_64:

```sh
rustup target add x86_64-unknown-linux-gnu
cargo install cargo-zigbuild --locked
sh bindings/native/scripts/stage-static.sh x86_64-unknown-linux-gnu bindings/go/internal/native/linux_amd64
```

Zig takes the same archive's directory as `-Dnative-dir`; the Go and Nim READMEs list the directory for each platform.

Python and Node.js wrap the Rust facade directly. Java, Go, Zig and Nim go through the internal [`bindings/native`](native/README.md) crate, a private C ABI that Java loads through FFM and the others link as a static archive; it is not a supported C binding.

## Releases

[release-please](https://github.com/googleapis/release-please) keeps a release pull request open from the conventional commits on `main` that touch `bindings/` (pull requests touching `bindings/` need a conventional title). Merging it bumps the version everywhere it appears, including the install instructions above, and tags `bindings-vX.Y.Z`. That tag runs `.github/workflows/bindings-release.yml`, which builds and tests every package on each platform before publishing it. See [CHANGELOG.md](CHANGELOG.md).

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or [MIT license](../LICENSE-MIT) at your option.
