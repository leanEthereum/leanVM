# Internal native bridge

`lean-pq-native` is a private Rust bridge for managed-language bindings in this repository. It produces a `cdylib` for Java FFM and a `staticlib` for Go cgo, and owns the opaque Rust handles and buffers behind the `lpq_*` ABI declared in [`include/lean_pq_native.h`](include/lean_pq_native.h).

It is consumed by the Java 25 FFM, Go cgo, Zig and Nim bindings. This crate and header are internal: they are not a supported or versioned general-purpose C API. `scripts/stage-static.sh` uses `cargo zigbuild` to build and stage one explicit Rust target's static archive for Go, Zig and Nim builds and release packaging.

The bridge's byte encodings are likewise private: raw-signature inputs to `lpq_aggregate_create` are concatenated fixed-width `public key (32) | message (32) | signature` records (2468 bytes for leanXMSS, 7804 for leanSPHINCS), and claims, both those `lpq_aggregate_from_bytes` checks a proof against and those the claim getters return, are concatenated 64-byte `public key | message` records. Language wrappers use them only to talk to the bridge; they are not public serialization formats. The one public encoding is an aggregate's: `lpq_aggregate_to_bytes` returns leanVM's own proof encoding, which carries no claims.
