# py-lean-pq

Python bindings for the leanXMSS and leanSPHINCS post-quantum signatures, their aggregation into one proof, and the consensus VRF tree.

## Install

<!-- x-release-please-start-version -->
```bash
pip install py-lean-pq==0.19.1
```
<!-- x-release-please-end -->

Python 3.11 or newer. Wheels for Linux x86_64 and aarch64 (glibc, musl), macOS arm64 and Windows x86_64; x86_64 needs AVX2 and PCLMULQDQ.

## Sign and verify

```python
import py_lean_pq as lpq

message = b"\x42" * 32

xmss_key = lpq.XmssSecretKey.from_seed(b"\x01" * 32)  # or XmssSecretKey.generate()
xmss_sig = xmss_key.sign(message, 7)  # at leaf index 7
lpq.xmss_verify(xmss_key.public_key, message, xmss_sig)  # raises LeanPqError if invalid

sphincs_key = lpq.SphincsSecretKey.from_seed(b"\x02" * 32)
sphincs_sig = sphincs_key.sign(message)
lpq.sphincs_verify(sphincs_key.public_key, message, sphincs_sig)
```

- Public keys and messages are 32 bytes; signatures are 2404 (leanXMSS) or 7740 (leanSPHINCS) bytes.
- leanXMSS is stateful: a key has `2^32` leaf indices, and must never sign two messages at the same one. Persist a high-water leaf index next to the key and advance it before publishing a signature. `prepare(leaf_index)` builds a leaf's signing state ahead of time, and `set_bottom_tree_cache_size(size)` sets how many recently used bottom trees the key keeps, 8 by default.
- leanSPHINCS is stateless and deterministic; a key signs at most `2^30` messages.
- `to_bytes()` is the key's 32-byte seed, which is secret; `from_bytes` restores the key.
- `cache_to_bytes()` returns the key's trees, which are not secret; `XmssSecretKey.from_cache_bytes(seed, public_key, cache)` loads the key from them instead of rebuilding them, checking them against the public key.
- Failures raise `LeanPqError`, inputs of the wrong length `ValueError`. Every call that signs, verifies or aggregates releases the GIL.

## Aggregate

```python
leaf = lpq.aggregate(
    xmss=[(xmss_key.public_key, message, xmss_sig)],
    sphincs=[(sphincs_key.public_key, message, sphincs_sig)],
)
root = lpq.aggregate(children=[leaf])
proof = root.to_bytes()

received = lpq.Aggregate.from_bytes(proof, root.xmss_claims, root.sphincs_claims)
```

- `aggregate(children=(), xmss=(), sphincs=())` verifies raw signatures before proving and takes at most 16 children. The result proves the union of their claims, or with `xmss_claims` or `sphincs_claims` exactly those claims, in any order, each one the inputs cover; an omitted list means none.
- `to_bytes()` is the proof alone: send the claims alongside it, or let the receiver rebuild them.
- `Aggregate.from_bytes(data, xmss_claims=(), sphincs_claims=())` accepts exactly those `(public_key, message)` claims, in any order, and raises `LeanPqError` otherwise. `xmss_claims` and `sphincs_claims` are sorted lists.
- `setup` raises `LeanPqError` if the prover already runs with another thread count. See [Proving](https://github.com/leanEthereum/leanVM/tree/main/bindings#proving).
- A process forked after the prover started cannot aggregate: give `multiprocessing` the `spawn` or `forkserver` start method.

## VRF

```python
key = lpq.VrfKey.from_seed(b"\x03" * 32, 1000, 2000)  # hashes every leaf of the range
root = key.root()  # 32 bytes, the validator's VRF root

proof = key.proof(1500)  # 1024 bytes: the secret, then its leaf's 31 siblings
lpq.vrf_verify(root, 1500, proof)  # raises LeanPqError if invalid
```

A key is a 32-byte seed and the slots `[start, end)`, with `end <= 2^31`: both fix the root, so keep both. Building it hashes every slot of the range once; a proof then costs about `3 sqrt(R)` hashes for `R` slots. A proof is 1024 bytes: the slot's secret, then its leaf's 31 siblings, which reveal no other secret. An empty range, a range past `2^31` and a slot outside the range raise `LeanPqError`.

`cache_to_bytes()` encodes the key's cache, its range and cached layer (about `32 sqrt(R)` bytes, no secret), and `VrfKey.from_cache_bytes(seed, root, cache)` rebuilds the key from its seed and that cache without hashing the range. It raises `ValueError` if the cache is malformed or does not lead to `root`.

## Build and test

Needs Rust and [uv](https://docs.astral.sh/uv/). From `bindings/python`:

```bash
uv run --extra dev pytest tests/ -v
uv run --extra dev python -m mypy.stubtest py_lean_pq --allowlist stubtest_allowlist.txt
```

## License

MIT OR Apache-2.0
