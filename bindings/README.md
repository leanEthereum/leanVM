# lean-pq bindings

Language bindings for [leanVM](https://github.com/leanEthereum/leanVM)'s post-quantum signatures:
stateful **leanXMSS**, stateless **leanSPHINCS**, and zkVM-backed recursive aggregation of both into
one proof. Every binding wraps the safe Rust facade in [`bindings/rust`](rust/README.md), which
builds the leanVM crates of this repository and keeps the proving parameters internal.

An encoded aggregate is leanVM's proof alone. Its claims, the (public key, message) pairs it proves,
travel separately: a receiver decodes the proof together with the claims it expects, and decoding
fails unless the proof proves exactly those.

## Install

Every package is released together from one version: each `bindings-vX.Y.Z` release publishes all
of them at `X.Y.Z`. Prebuilt packages need no Rust toolchain.

| Language | Package | Prebuilt for |
| --- | --- | --- |
| [Python](python/README.md) ≥ 3.11 | `py-lean-pq` on PyPI | Linux x86_64/aarch64 (glibc, musl), macOS arm64, Windows x86_64 |
| [Node.js](node/README.md) ≥ 18.17 | `@kevaundray/lean-pq` on npm | Linux x64/arm64 (glibc, musl), macOS x64/arm64, Windows x64 |
| [Java](java/README.md) 25 | `io.github.crate-crypto:lean-pq` on Maven Central | Linux x86_64/aarch64 (glibc 2.17+), macOS x86_64/arm64, Windows x86_64 |
| [Go](go/README.md) ≥ 1.24 | `github.com/leanEthereum/leanVM/bindings/go` | Linux amd64/arm64 (glibc), macOS amd64/arm64, Windows amd64 |
| [Zig](zig/README.md) ≥ 0.16 | package attached to each GitHub release | Linux x86_64/aarch64 (glibc), macOS x86_64/aarch64, Windows x86_64 |
| [Nim](nim/README.md) ≥ 2.2.12 | Nimble package `lean_pq` at tag `bindings/nim/vX.Y.Z` | Linux x86_64/aarch64 (glibc), macOS x86_64/arm64, Windows x86_64 (MinGW) |
| [Rust](rust/README.md) | `lean-pq` from this repository (git) | built from source |

The x86_64 builds require a CPU with AVX2 and PCLMULQDQ.

### Python

<!-- x-release-please-start-version -->
```sh
pip install py-lean-pq==0.11.0
```
<!-- x-release-please-end -->

### Node.js

<!-- x-release-please-start-version -->
```sh
npm install @kevaundray/lean-pq@0.11.0
```
<!-- x-release-please-end -->

npm installs the binary for your platform through an optional dependency; installing with
`--omit=optional` leaves the package unable to load.

### Java

Gradle (Kotlin DSL):

<!-- x-release-please-start-version -->
```kotlin
implementation("io.github.crate-crypto:lean-pq:0.11.0")
```
<!-- x-release-please-end -->

Maven:

<!-- x-release-please-start-version -->
```xml
<dependency>
  <groupId>io.github.crate-crypto</groupId>
  <artifactId>lean-pq</artifactId>
  <version>0.11.0</version>
</dependency>
```
<!-- x-release-please-end -->

The jar bundles the native library for each platform. Run with
`--enable-native-access=org.ethereum.leanpq`.

### Go

<!-- x-release-please-start-version -->
```sh
go get github.com/leanEthereum/leanVM/bindings/go@v0.11.0
```
<!-- x-release-please-end -->

The module links a bundled static library through cgo, so it needs `CGO_ENABLED=1` and a C
compiler: gcc or clang on Linux, the Xcode command line tools on macOS, and MinGW-w64 gcc on
Windows.

### Zig

<!-- x-release-please-start-version -->
```sh
version=0.11.0
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
requires "https://github.com/leanEthereum/leanVM#bindings/nim/v0.11.0"
```
<!-- x-release-please-end -->

The tag holds the package with its native archives built in, and also works as a
nimbus-build-system `vendor/` submodule. The bindings are `Result`-based and `raises: []`, and
build with `--mm:refc` and `--mm:orc`.

### Rust

The crate is not on crates.io because the leanVM crates it builds are not published there:

<!-- x-release-please-start-version -->
```toml
[dependencies]
lean-pq = { git = "https://github.com/leanEthereum/leanVM.git", tag = "bindings-v0.11.0" }
```
<!-- x-release-please-end -->

## Build from source

Clone the repository and follow each binding's README; every binding builds against the leanVM
crates in the same checkout. The bindings are their own Cargo workspace, `bindings/Cargo.toml`,
excluded from the root one: run cargo from `bindings/` (or below), so that
[`bindings/.cargo/config.toml`](.cargo/config.toml) replaces the root's `target-cpu=native` with the
portable baseline. Commands below without a directory run from the repository root. Building needs
Rust, plus the language toolchain:

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

Zig takes the same archive's directory as `-Dnative-dir`; the Go and Nim READMEs list the directory
for each platform.

Each binding uses a language-native wrapper around the Rust implementation. The internal
[`bindings/native`](native/README.md) crate supplies a private C-shaped Rust ABI for
managed wrappers: Java consumes it through the Foreign Function & Memory API, while Go, Zig and
Nim link its static archive. It is not a separate, supported C binding.

## Releases

[release-please](https://github.com/googleapis/release-please) keeps a release pull request open
from the conventional commits on `main` that touch `bindings/` (pull requests touching `bindings/`
need a conventional title). Merging it bumps the version everywhere it appears, including the
install instructions above, and tags `bindings-vX.Y.Z`. That tag runs
`.github/workflows/bindings-release.yml`, which builds and tests every package on each platform
before publishing it. See [CHANGELOG.md](CHANGELOG.md). Versions up to 0.11.0 were released from
[ethereum/lean-pq-bindings](https://github.com/ethereum/lean-pq-bindings) as `vX.Y.Z`.

## License

Licensed under either of [Apache License, Version 2.0](../LICENSE-APACHE) or [MIT license](../LICENSE-MIT)
at your option.
