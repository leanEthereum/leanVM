# py-lean-pq

Python bindings for the leanXMSS and leanSPHINCS post-quantum signatures and their aggregation into one proof.

## Install

<!-- x-release-please-start-version -->
```bash
pip install py-lean-pq==0.13.1
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
- leanXMSS is stateful: a key has `2^32` leaf indices, and must never sign two messages at the same one. Persist a high-water leaf index next to the key and advance it before publishing a signature. `prepare(leaf_index)` builds a leaf's signing state ahead of time.
- leanSPHINCS is stateless and deterministic; a key signs at most `2^30` messages.
- `to_bytes()` is the key's 32-byte seed, which is secret; `from_bytes` restores the key.
- Failures raise `LeanPqError`, inputs of the wrong length `ValueError`. Every call that signs, verifies or reaches the sidecar releases the GIL.

## Aggregate

Aggregation runs in a leanVM sidecar, a separate process (Linux and macOS): see [the sidecar](https://github.com/leanEthereum/leanVM/tree/main/bindings#sidecar).

```python
import os

with lpq.Sidecar.connect(os.path.expanduser("~/.leanvm/sidecar.sock")) as sidecar:
    # or: lpq.Sidecar.start(binary, socket, threads=0), which launches one
    leaf = sidecar.aggregate(
        xmss=[(xmss_key.public_key, message, xmss_sig)],
        sphincs=[(sphincs_key.public_key, message, sphincs_sig)],
    )
    root = sidecar.aggregate(children=[leaf])
    proof = root.to_bytes()

    received = sidecar.verify(proof, root.xmss_claims, root.sphincs_claims)
```

- `aggregate(children=(), xmss=(), sphincs=())` verifies raw signatures before proving and takes at most 16 children. The result proves the union of their claims.
- `to_bytes()` is the proof alone: send the claims alongside it, or let the receiver rebuild them.
- `verify(data, xmss_claims, sphincs_claims)` accepts exactly those `(public_key, message)` claims, in any order, and raises `LeanPqError` otherwise. `xmss_claims` and `sphincs_claims` are sorted lists.
- `Sidecar.start` uses one thread per core for `threads=0`. `close()`, or the `Sidecar` being garbage collected, stops the sidecar it launched, failing a call in progress. `sidecar.prover` is `experimental` or `stable`, which make the same proofs.
- Share one `Sidecar` per process (a sidecar serves at most 16 connections); it is thread-safe, and its calls run one at a time. A forked child opens its own connection.

## Build and test

Needs Rust and [uv](https://docs.astral.sh/uv/). From `bindings/python`:

```bash
uv run --extra dev pytest tests/ -v
uv run --extra dev python -m mypy.stubtest py_lean_pq --allowlist stubtest_allowlist.txt
```

The aggregation tests use the sidecar listening on `LEANVM_SIDECAR_SOCKET`, and start one from the executable at `LEANVM_SIDECAR_BIN`.

## License

MIT OR Apache-2.0
