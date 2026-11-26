# lean-pq

The Rust facade that the Python, Node.js, Java, Go, Zig and Nim bindings wrap: leanXMSS and leanSPHINCS signatures, their aggregation, and the consensus VRF tree. It is internal and unpublished; Rust code uses [`lean_vm`](../README.md#install) directly.

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
- `xmss::SecretKey::cache_to_bytes()` returns the key's trees, which are not secret; `xmss::SecretKey::from_cache_bytes(seed, &public_key, &cache)` loads the key from them instead of rebuilding them, checking them against the public key.

## VRF

```rust
use lean_pq::vrf;

let key = vrf::Key::new([0x03; 32], 1000..2000)?;
let root = key.root();
vrf::verify(&root, 1500, &key.proof(1500)?)?;
# Ok::<(), lean_pq::Error>(())
```

A key is a 32-byte seed and the slots `[start, end)`, with `end <= 2^31`: both fix the root, so keep both. Building it hashes every slot of the range once; a proof then costs about `3 sqrt(R)` hashes for `R` slots. A proof is 1024 bytes: the slot's secret, then its leaf's 31 siblings, which reveal no other secret. An empty range, a range past `2^31` and a slot outside the range are errors.

`Key::cache_to_bytes()` encodes the key's cache, its range and cached layer (about `32 sqrt(R)` bytes, no secret), and `Key::from_cache_bytes(seed, &root, &cache)` rebuilds the key from its seed and that cache without hashing the range, failing if the cache does not lead to `root`.

## Aggregate

Aggregation is the default `aggregation` feature; without it the crate only signs, verifies and builds VRF trees.

```rust,no_run
use lean_pq::{aggregate, sphincs, xmss, Aggregate};

let message = [0x42; 32];
let xmss_key = xmss::SecretKey::from_seed([0x01; 32]);
let sphincs_key = sphincs::SecretKey::from_seed([0x02; 32]);

let leaf = aggregate(
    &[],
    &[(xmss_key.public_key(), message, xmss_key.sign(&message, 7))],
    &[(sphincs_key.public_key(), message, sphincs_key.sign(&message))],
)?;
let root = aggregate(&[&leaf], &[], &[])?;

let received = Aggregate::from_bytes(&root.to_bytes(), &root.xmss_claims(), &root.sphincs_claims())?;
assert_eq!(received.xmss_claims(), root.xmss_claims());
# Ok::<(), lean_pq::Error>(())
```

- `aggregate` verifies raw signatures before proving and takes at most `MAX_CHILDREN` (16) children. The result proves the union of their claims.
- `aggregate_only` takes the claims the result proves too, in any order; each must be one the inputs cover.
- `to_bytes` is the proof alone: send the claims alongside it, or let the receiver rebuild them.
- `Aggregate::from_bytes` accepts exactly the claims passed, in any order, and fails otherwise.
- `setup(threads)`: see [Proving](../README.md#proving). A process forked after the prover started cannot aggregate.

## Build and test

From `bindings/`:

```sh
cargo test --release -p lean-pq
```

## License

MIT OR Apache-2.0
