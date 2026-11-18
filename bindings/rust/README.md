# lean-pq

Safe Rust bindings for [leanVM](https://github.com/leanEthereum/leanVM)'s post-quantum signatures and their aggregation.

- **leanXMSS** is synchronized: a key signs at `2^32` leaf indices, one message per leaf index.
- **leanSPHINCS** is stateless: a key signs at most `2^30` messages, with no state kept between them.
- **Aggregation** proves many signatures of both schemes in one recursive leanVM proof.

Public keys and messages are 32 bytes in both schemes.

## Install

The crate is not on crates.io: it depends on leanVM by git revision.

<!-- x-release-please-start-version -->
```toml
[dependencies]
lean-pq = { git = "https://github.com/ethereum/lean-pq-bindings.git", tag = "v0.11.0" }
```
<!-- x-release-please-end -->

Build in release mode: debug builds of leanVM prove far slower.

Aggregation is the default `aggregation` feature, which pulls in leanVM's prover and verifier. To
only sign and verify, add `default-features = false` to the dependency: the crate then builds from
leanVM's `lean_xmss` and `lean_sphincs` crates alone, and `aggregate`, `setup`, `Aggregate` and
`MAX_CHILDREN` are not compiled.

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

A leanXMSS key keeps no record of the leaf indices it used.

Persist a durable high-water leaf index next to the key's bytes, and advance it before publishing a signature.

Secret key bytes are secret material: in both schemes they are the key's 32-byte seed.

## Aggregate

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

// The bytes are the proof alone: the receiver supplies the claims it expects.
let received = Aggregate::from_bytes(
    &root.to_bytes(),
    &[(xmss_key.public_key(), message)],
    &[(sphincs_key.public_key(), message)],
)?;
assert_eq!(received.xmss_claims(), root.xmss_claims());
# Ok::<(), lean_pq::Error>(())
```

- Aggregation verifies every raw signature before proving, and runs one proof at a time per process.
- An encoded aggregate is the proof alone, as leanVM encodes it. Send the claims alongside it, or
  let the receiver rebuild them, as Ethereum does from its validator bitfields.
- `Aggregate::from_bytes` verifies the proof against exactly the claims you pass, in any order;
  any other set of claims fails. Every aggregate value is proven.
- The first proof starts leanVM's prover pool and builds the aggregation guest; call `setup()` to
  pay that earlier.

## License

MIT OR Apache-2.0
