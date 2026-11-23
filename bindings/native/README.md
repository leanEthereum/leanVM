# lean-pq-native

The internal C ABI (`lpq_*`) that the Java, Go, Zig and Nim bindings call. It is not a supported or versioned C API.

- Java loads its `cdylib` through FFM; Go, Zig and Nim link its `staticlib`.
- [`include/lean_pq_native.h`](include/lean_pq_native.h) declares every function, handle and byte format.
- `scripts/stage-static.sh` builds one Rust target's static archive with `cargo zigbuild` and stages it for Go, Zig and Nim, without the LLVM bitcode that Go refuses since Go 1.27 (`scripts/strip-archive.sh`, which needs `rustup component add llvm-tools`).
