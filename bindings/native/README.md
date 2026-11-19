# Internal native bridge

`lean-pq-native` is the private Rust bridge of the Java, Go, Zig and Nim bindings: a `cdylib` Java loads through FFM and a `staticlib` the others link, owning the opaque handles and buffers behind the `lpq_*` ABI in [`include/lean_pq_native.h`](include/lean_pq_native.h).

Neither the crate nor the header is a supported or versioned C API. `scripts/stage-static.sh` builds one Rust target's static archive with `cargo zigbuild` and stages it for the Go, Zig and Nim builds and releases.

The bridge's byte encodings are likewise private: raw-signature inputs to `lpq_sidecar_aggregate` are concatenated fixed-width `public key (32) | message (32) | signature` records (2468 bytes for leanXMSS, 7804 for leanSPHINCS), and claims, both those `lpq_sidecar_verify` checks a proof against and those the claim getters return, are concatenated 64-byte `public key | message` records. The one public encoding is an aggregate's: `lpq_aggregate_to_bytes` returns the proof's own encoding, which carries no claims.
