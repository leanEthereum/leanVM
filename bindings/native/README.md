# Internal native bridge

`lean-pq-native` is the private Rust bridge of the Java, Go, Zig and Nim bindings: a `cdylib` Java loads through FFM and a `staticlib` the others link, owning the opaque handles and buffers behind the `lpq_*` ABI in [`include/lean_pq_native.h`](include/lean_pq_native.h).

- Java loads its `cdylib` through FFM; Go, Zig and Nim link its `staticlib`.
- [`include/lean_pq_native.h`](include/lean_pq_native.h) declares every function, handle and byte format.
- `scripts/stage-static.sh` builds one Rust target's static archive with `cargo zigbuild` and stages it for Go, Zig and Nim, without the LLVM bitcode that Go refuses since Go 1.27 (`scripts/strip-archive.sh`, which needs `rustup component add llvm-tools`).
- On Unix it installs jemalloc, configured for proving by `allocator`, as Rust's global allocator: the host language's allocator is untouched.
