# py-lean-pq

Python bindings for post-quantum signatures and their aggregation, over the Rust facade `lean-pq`:

- **leanXMSS**: stateful hash-based signatures, `2^32` leaf indices per key.
- **leanSPHINCS**: stateless hash-based signatures.
- **Aggregation**: a recursive proof that every listed public key signed its message. Aggregates can be combined into larger aggregates.
- **VRF**: the consensus `pq` feature's VRF tree, pruned to the slots a validator proposes in.

Public keys and messages are 32 bytes. Signatures are plain fixed-length `bytes` (2404 for leanXMSS, 7740 for leanSPHINCS). Errors raise `LeanPqError`; a seed, secret key, message, public key, signature, VRF root, or VRF proof of the wrong length raises `ValueError`. Key generation, signing, verification, aggregation, aggregate decoding, and building a VRF key or proof release the GIL.

Requires Python >= 3.11. Wheels are built for Linux (x86_64, aarch64; glibc + musl), macOS arm64, and Windows x86_64. The Windows wheels link the C runtime statically, so they need no Visual C++ redistributable. x86_64 wheels require a CPU with AVX2 and PCLMULQDQ.

## Install

<!-- x-release-please-start-version -->
```bash
pip install py-lean-pq==0.12.0
```
<!-- x-release-please-end -->

Other languages: see the [bindings README](https://github.com/leanEthereum/leanVM/tree/main/bindings#install).

## leanXMSS

```python
import py_lean_pq as lpq

key = lpq.XmssSecretKey.from_seed(b"\x01" * 32)  # or XmssSecretKey.generate()
message = b"\x42" * 32

key.prepare(5)  # optional: build the bottom tree for leaf 5 ahead of time
signature = key.sign(message, 5)
lpq.xmss_verify(key.public_key, message, signature)  # raises LeanPqError if invalid

restored = lpq.XmssSecretKey.from_bytes(key.to_bytes())
```

leanXMSS keys are stateful: never sign two different messages at the same leaf index. Persist your own durable high-water leaf index alongside `XmssSecretKey.to_bytes()` (the key's seed, secret material) and advance it before publishing a signature.

## leanSPHINCS

A key is its 32-byte seed and signs at most `2^30` messages. Signing is deterministic.

```python
key = lpq.SphincsSecretKey.from_seed(b"\x02" * 32)  # or SphincsSecretKey.generate()
signature = key.sign(message)
lpq.sphincs_verify(key.public_key, message, signature)

restored = lpq.SphincsSecretKey.from_bytes(key.to_bytes())
assert restored.public_key == key.public_key
```

## VRF

A key is a 32-byte seed and a range of slots `[start, end)`, with `end <= 2^31`: both fix the root, so keep both.

```python
key = lpq.VrfKey.from_seed(b"\x03" * 32, 1000, 2000)  # hashes every leaf of the range
root = key.root()  # 32 bytes, the validator's VRF root

proof = key.proof(1500)  # 1024 bytes: the leaf, then its 31 siblings
lpq.vrf_verify(root, 1500, proof)  # raises LeanPqError if invalid
```

`from_seed` hashes every leaf of the range once and keeps about `sqrt(R)` nodes for a range of `R` slots; `proof` then hashes about `3 sqrt(R)` nodes. A slot outside the key's range, an empty range, or one ending past `2^31` raises `LeanPqError`. `vrf_verify`, like the consensus specifications, checks only the 31 low bits of the slot.

## Aggregation

`aggregate` proves raw `(public_key, message, signature)` tuples of either scheme together with up to 16 child aggregates. The result's claims are the union of its inputs' claims. Raw signatures are verified before proving.

```python
xmss_key = lpq.XmssSecretKey.from_seed(b"\x05" * 32)
sphincs_key = lpq.SphincsSecretKey.from_seed(b"\x06" * 32)
first, second = b"\x11" * 32, b"\x22" * 32

left = lpq.aggregate(xmss=[(xmss_key.public_key, first, xmss_key.sign(first, 0))])
right = lpq.aggregate(sphincs=[(sphincs_key.public_key, second, sphincs_key.sign(second))])
root = lpq.aggregate(
    children=[left, right],
    xmss=[(xmss_key.public_key, second, xmss_key.sign(second, 1))],
)

# The encoding is the proof alone: send the claims alongside it, or let the
# receiver rebuild the claims it expects.
proof = root.to_bytes()
received = lpq.Aggregate.from_bytes(proof, root.xmss_claims, root.sphincs_claims)
assert received.sphincs_claims == [(sphincs_key.public_key, second)]
```

Every `Aggregate` value has been proven or verified. `Aggregate.from_bytes(data, xmss_claims=(), sphincs_claims=())` takes the `(public_key, message)` pairs the receiver expects and verifies the proof against exactly them: they may come in any order and a duplicate counts once, but a proof of any other claim set raises `LeanPqError`. `xmss_claims` and `sphincs_claims` return the claims as sorted lists of `(public_key, message)` tuples.

`aggregate` and `Aggregate.from_bytes` build the aggregation guest on first use; call `setup()`, which is idempotent, to pay that cost earlier. Proving is serialized process-wide and takes seconds and over a gigabyte of memory. `setup()` and the first `aggregate` also start the prover's threads, which a forked child does not inherit: in a child forked after that, `aggregate` raises `LeanPqError`, so give `multiprocessing` the `spawn` or `forkserver` start method.

## Development

```bash
uv run --extra dev pytest tests/ -v
uv run --extra dev python -m mypy.stubtest py_lean_pq --allowlist stubtest_allowlist.txt
```

## License

MIT OR Apache-2.0
