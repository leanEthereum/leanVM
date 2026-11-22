# @kevaundray/lean-pq

Node.js bindings for the leanXMSS and leanSPHINCS post-quantum signatures, their aggregation into one proof, and the consensus VRF tree.

## Install

<!-- x-release-please-start-version -->
```sh
npm install @kevaundray/lean-pq@0.16.0
```
<!-- x-release-please-end -->

Node.js 18.17 or newer. Prebuilt for Linux x64 and arm64 (glibc 2.17+, musl), macOS x64 and arm64 and Windows x64; x64 needs AVX2 and PCLMULQDQ. The binary comes as an optional dependency, so `--omit=optional` leaves the package unable to load.

## Sign and verify

```js
const lpq = require('@kevaundray/lean-pq')

const message = Buffer.alloc(32, 0x42)

const xmssKey = await lpq.XmssSecretKey.fromSeed(Buffer.alloc(32, 1)) // or XmssSecretKey.generate()
const xmssSig = await xmssKey.sign(message, 7) // at leaf index 7
lpq.xmssVerify(xmssKey.publicKey, message, xmssSig) // throws if invalid

const sphincsKey = await lpq.SphincsSecretKey.fromSeed(Buffer.alloc(32, 2))
const sphincsSig = await sphincsKey.sign(message)
lpq.sphincsVerify(sphincsKey.publicKey, message, sphincsSig)
```

- Public keys and messages are 32-byte `Buffer`s; signatures are 2404 (leanXMSS) or 7740 (leanSPHINCS) bytes.
- Creating a key, `prepare`, `sign` and every sidecar call return Promises and run off the event loop; `xmssVerify` and `sphincsVerify` are synchronous.
- leanXMSS is stateful: a key has `2^32` leaf indices, and must never sign two messages at the same one. Persist a high-water leaf index next to the key and advance it before publishing a signature. `prepare(leafIndex)` builds a leaf's signing state ahead of time.
- leanSPHINCS is stateless and deterministic; a key signs at most `2^30` messages.
- `toBytes()` is the key's 32-byte seed, which is secret; `fromBytes` restores the key.
- `cacheToBytes()` returns the key's trees, which are not secret; `XmssSecretKey.fromCacheBytes(seed, publicKey, cache)` loads the key from them instead of rebuilding them, checking them against the public key.

## VRF

```js
// The seed and the range fix the root: keep both.
const vrfKey = await lpq.VrfKey.fromSeed(Buffer.alloc(32, 3), 1000, 2000)
const root = vrfKey.root()
lpq.vrfVerify(root, 1500, vrfKey.proof(1500)) // throws if invalid
```

A key is a 32-byte seed and the slots `[start, end)`, with `end <= 2^31`: both fix the root, so keep both. Building it hashes every slot of the range once; a proof then costs about `3 sqrt(R)` hashes for `R` slots. A proof is 1024 bytes: the slot's secret, then its leaf's 31 siblings, which reveal no other secret. Building returns a Promise, which rejects for an empty range or one past `2^31`; `proof` throws for a slot outside the range. `vrfVerify` takes the slot as a number up to `Number.MAX_SAFE_INTEGER`.

`cacheToBytes()` encodes the key's cache, its range and cached layer (about `32 sqrt(R)` bytes, no secret), and `VrfKey.fromCacheBytes(seed, root, cache)` rebuilds the key from its seed and that cache without hashing the range. It returns a Promise, which rejects if the cache is malformed or does not lead to `root`.

## Aggregate

Aggregation runs in a leanVM sidecar, a separate process (Linux and macOS): see [the sidecar](https://github.com/leanEthereum/leanVM/tree/main/bindings#sidecar).

```js
const os = require('os')

const sidecar = await lpq.Sidecar.connect(`${os.homedir()}/.leanvm/sidecar.sock`)
// or: await lpq.Sidecar.start(binary, socket, threads), which launches one

const leaf = await sidecar.aggregate({
  xmss: [{ publicKey: xmssKey.publicKey, message, signature: xmssSig }],
  sphincs: [{ publicKey: sphincsKey.publicKey, message, signature: sphincsSig }],
})
const root = await sidecar.aggregate({ children: [leaf] })
const proof = root.toBytes()

const received = await sidecar.verify(proof, { xmss: root.xmssClaims, sphincs: root.sphincsClaims })
await sidecar.close()
```

- `aggregate({ children, xmss, sphincs })` verifies raw signatures before proving and takes at most 16 children. The result proves the union of their claims.
- `toBytes()` is the proof alone: send the claims alongside it, or let the receiver rebuild them.
- `verify(data, { xmss, sphincs })` accepts exactly those `{ publicKey, message }` claims, in any order, and rejects otherwise; an omitted list means none. `xmssClaims` and `sphincsClaims` are sorted.
- `Sidecar.start` uses one thread per core when `threads` is 0 or omitted. `close()`, or the `Sidecar` being garbage collected, stops the sidecar it launched, failing a call in progress. `sidecar.prover` is `experimental` or `stable`, which make the same proofs.
- Share one `Sidecar` per process: a sidecar serves at most 16 connections.
- Calls on one `Sidecar` run one at a time.

## Build and test

Needs Node.js 18.17 or newer and Rust. From `bindings/node`:

```sh
npm ci
npm run build
npm test
```

The aggregation tests use the sidecar listening on `LEANVM_SIDECAR_SOCKET`, and start one from the executable at `LEANVM_SIDECAR_BIN`. Publishing is in [RELEASING.md](../RELEASING.md#npm).

## License

MIT OR Apache-2.0
