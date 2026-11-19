# py-lean-pq

Python bindings for post-quantum signatures and their aggregation, over the Rust facade `lean-pq`:

- **leanXMSS**: stateful hash-based signatures, `2^32` leaf indices per key.
- **leanSPHINCS**: stateless hash-based signatures.
- **Aggregation**: a recursive proof that every listed public key signed its message. Aggregates can be combined into larger aggregates.

Public keys and messages are 32 bytes. Signatures are plain fixed-length `bytes` (2404 for leanXMSS, 7740 for leanSPHINCS). Errors raise `LeanPqError`; a seed, secret key, message, public key, or signature of the wrong length raises `ValueError`. Key generation, signing, verification and sidecar calls release the GIL.

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

## Aggregation

Aggregation runs in a leanVM sidecar, a separate process that proves and verifies (Linux and macOS). [The bindings README](https://github.com/leanEthereum/leanVM/tree/main/bindings#sidecar) says how to get and run it. Then connect to its socket, or let `Sidecar.start` launch it:

```python
sidecar = lpq.Sidecar.connect(os.path.expanduser("~/.leanvm/sidecar.sock"))
# or: sidecar = lpq.Sidecar.start("./leanvm-sidecar", "/tmp/leanvm/sidecar.sock"), stopped by close()

xmss_key = lpq.XmssSecretKey.from_seed(b"\x05" * 32)
sphincs_key = lpq.SphincsSecretKey.from_seed(b"\x06" * 32)
first, second = b"\x11" * 32, b"\x22" * 32

left = sidecar.aggregate(xmss=[(xmss_key.public_key, first, xmss_key.sign(first, 0))])
right = sidecar.aggregate(sphincs=[(sphincs_key.public_key, second, sphincs_key.sign(second))])
root = sidecar.aggregate(
    children=[left, right],
    xmss=[(xmss_key.public_key, second, xmss_key.sign(second, 1))],
)

# The encoding is the proof alone: send the claims alongside it, or let the
# receiver rebuild the claims it expects.
proof = root.to_bytes()
received = sidecar.verify(proof, root.xmss_claims, root.sphincs_claims)
assert received.sphincs_claims == [(sphincs_key.public_key, second)]
sidecar.close()
```

- `aggregate` proves raw `(public_key, message, signature)` tuples of either scheme together with up to 16 child aggregates; the result's claims are the union of its inputs' claims. Raw signatures are verified before proving.
- `verify(data, xmss_claims=(), sphincs_claims=())` checks the proof against exactly the `(public_key, message)` pairs the receiver expects, in any order, a duplicate counting once; any other claim set raises `LeanPqError`. Every `Aggregate` value has been proven or verified.
- `xmss_claims` and `sphincs_claims` return the claims as sorted lists of `(public_key, message)` tuples.
- A `Sidecar` is a context manager, safe to share between threads; its calls run one at a time. In a forked child, connect again.

## Development

```bash
uv run --extra dev pytest tests/ -v
uv run --extra dev python -m mypy.stubtest py_lean_pq --allowlist stubtest_allowlist.txt
```

The aggregation tests need a running sidecar's socket in `LEANVM_SIDECAR_SOCKET` and its binary in `LEANVM_SIDECAR_BIN`.

## License

MIT OR Apache-2.0
