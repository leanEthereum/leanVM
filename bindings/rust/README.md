# lean-pq

The safe Rust facade that the Python, Node.js, Java, Go, Zig and Nim bindings wrap, with the proving parameters fixed. It is internal to the bindings: Rust code depends on `lean_vm` directly (see the bindings README).

- **leanXMSS** is synchronized: a key signs at `2^32` leaf indices, one message per leaf index.
- **leanSPHINCS** is stateless: a key signs at most `2^30` messages, with no state kept between them.
- **Aggregation** proves many signatures of both schemes in one recursive leanVM proof, through a leanVM sidecar.

Public keys and messages are 32 bytes in both schemes.

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

A leanXMSS key keeps no record of the leaf indices it used: persist a durable high-water leaf index next to the key's bytes, and advance it before publishing a signature. Secret key bytes are secret material, the key's 32-byte seed in both schemes.

## Aggregate

A leanVM sidecar proves and verifies aggregates in a process of its own; run it first (see [`bins/leanvm-sidecar`](../../bins/leanvm-sidecar/README.md)), then connect to its socket. Unix only: on Windows, `Sidecar::connect` fails.

```rust,no_run
use lean_pq::{sphincs, xmss, Sidecar};

let sidecar = Sidecar::connect("/home/me/.leanvm/sidecar.sock")?;
let message = [0x42; 32];
let xmss_key = xmss::SecretKey::from_seed([0x01; 32]);
let sphincs_key = sphincs::SecretKey::from_seed([0x02; 32]);

let leaf = sidecar.aggregate(
    &[],
    &[(xmss_key.public_key(), message, xmss_key.sign(&message, 7))],
    &[(sphincs_key.public_key(), message, sphincs_key.sign(&message))],
)?;
let root = sidecar.aggregate(&[&leaf], &[], &[])?;

// The bytes are the proof alone: the receiver supplies the claims it expects.
let received = sidecar.verify(
    &root.to_bytes(),
    &[(xmss_key.public_key(), message)],
    &[(sphincs_key.public_key(), message)],
)?;
assert_eq!(received.xmss_claims(), root.xmss_claims());
# Ok::<(), lean_pq::Error>(())
```

- `aggregate` verifies every raw signature before proving. The sidecar proves one request at a time.
- An encoded aggregate is the proof alone: send the claims alongside it, or let the receiver rebuild them, as Ethereum does from its validator bitfields.
- `verify` checks the proof against exactly the claims you pass, in any order; any other set of claims fails. Every aggregate value is proven or verified.
- A broken connection is reopened on the next call.

## License

MIT OR Apache-2.0
