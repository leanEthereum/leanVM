# lean-pq

The Rust facade that the Python, Node.js, Java, Go, Zig and Nim bindings wrap: leanXMSS and leanSPHINCS signatures, and their aggregation through a leanVM sidecar. It is internal and unpublished; Rust code uses [`lean_vm`](../README.md#install) directly.

## Sign and verify

```rust
use lean_pq::{sphincs, xmss};

let message = [0x42; 32];

let xmss_key = xmss::SecretKey::from_seed([0x01; 32]);
let signature = xmss_key.sign(&message, 7);
xmss_key.public_key().verify(&message, &signature)?;

let sphincs_key = sphincs::SecretKey::from_seed([0x02; 32]);
let signature = sphincs_key.sign(&message);
sphincs_key.public_key().verify(&message, &signature)?;
# Ok::<(), lean_pq::Error>(())
```

- Public keys, messages and secret keys (a seed) are 32 bytes.
- leanXMSS is stateful: a key has `2^32` leaf indices and must never sign two messages at the same one. Persist a high-water leaf index next to the key and advance it before publishing a signature.
- leanSPHINCS is stateless; a key signs at most `2^30` messages.

## Aggregate

Aggregation runs in a leanVM sidecar, a separate process (Linux and macOS): see [the sidecar](../README.md#sidecar).

```rust,no_run
use lean_pq::{sphincs, xmss, Sidecar};

let sidecar = Sidecar::connect("/home/me/.leanvm/sidecar.sock")?;
// or: Sidecar::start("leanvm-sidecar", "/tmp/leanvm/sidecar.sock", 0)?, which launches one
let message = [0x42; 32];
let xmss_key = xmss::SecretKey::from_seed([0x01; 32]);
let sphincs_key = sphincs::SecretKey::from_seed([0x02; 32]);

let leaf = sidecar.aggregate(
    &[],
    &[(xmss_key.public_key(), message, xmss_key.sign(&message, 7))],
    &[(sphincs_key.public_key(), message, sphincs_key.sign(&message))],
)?;
let root = sidecar.aggregate(&[&leaf], &[], &[])?;

let received = sidecar.verify(&root.to_bytes(), &root.xmss_claims(), &root.sphincs_claims())?;
assert_eq!(received.xmss_claims(), root.xmss_claims());
# Ok::<(), lean_pq::Error>(())
```

- `aggregate` verifies raw signatures before proving and takes at most `MAX_CHILDREN` (16) children. The result proves the union of their claims.
- `to_bytes` is the proof alone: send the claims alongside it, or let the receiver rebuild them.
- `verify` accepts exactly the claims passed, in any order, and fails otherwise.
- `Sidecar::start` with `threads` 0 uses one thread per core; dropping the `Sidecar` stops a sidecar it launched. `prover()` is `experimental` or `stable`, which make the same proofs.
- Calls run one at a time; a broken connection is reopened on the next call. In a forked child, connect again.

## Build and test

From `bindings/`:

```sh
cargo test --release -p lean-pq
```

The aggregation tests use the sidecar listening on `LEANVM_SIDECAR_SOCKET`, and start one from the executable at `LEANVM_SIDECAR_BIN`.

## License

MIT OR Apache-2.0
