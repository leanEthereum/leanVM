# lean-pq Node.js bindings

Node.js bindings for leanXMSS and leanSPHINCS post-quantum signatures and their recursive aggregation, built with `napi-rs` over the Rust facade `lean-pq`.

- **leanXMSS** is stateful: a key signs at `2^32` leaf indices; never sign two different messages at the same leaf index.
- **leanSPHINCS** is stateless: a key signs at most `2^30` messages, and signing is deterministic.

Public keys and messages are 32-byte `Buffer`s; signatures are `Buffer`s of 2404 (leanXMSS) or 7740 (leanSPHINCS) bytes. Key generation, preparation, signing, setup, aggregation, and aggregate decoding return Promises so their native work does not block the JavaScript event loop.

## Install

<!-- x-release-please-start-version -->
```sh
npm install @kevaundray/lean-pq@0.11.1
```
<!-- x-release-please-end -->

npm installs a prebuilt binary through a per-platform optional dependency, so installing needs no Rust toolchain. Prebuilt binaries cover Node.js 18.17 or later on:

| Platform                 | Package                              |
| ------------------------ | ------------------------------------ |
| Linux x64, glibc 2.17+   | `@kevaundray/lean-pq-linux-x64-gnu`    |
| Linux arm64, glibc 2.17+ | `@kevaundray/lean-pq-linux-arm64-gnu`  |
| Linux x64, musl          | `@kevaundray/lean-pq-linux-x64-musl`   |
| Linux arm64, musl        | `@kevaundray/lean-pq-linux-arm64-musl` |
| macOS x64                | `@kevaundray/lean-pq-darwin-x64`       |
| macOS arm64              | `@kevaundray/lean-pq-darwin-arm64`     |
| Windows x64              | `@kevaundray/lean-pq-win32-x64-msvc`   |

The x64 binaries require a CPU with AVX2 and PCLMULQDQ. The Windows binary links the C runtime statically, so it needs no Visual C++ redistributable. Installing with `--omit=optional` or `--no-optional` skips the binary and leaves the package unable to load.

## Sign and verify

```js
const lpq = require('@kevaundray/lean-pq')

const message = Buffer.alloc(32, 0x42)

const xmssKey = await lpq.XmssSecretKey.fromSeed(Buffer.alloc(32, 1))
const xmssSignature = await xmssKey.sign(message, 7)
lpq.xmssVerify(xmssKey.publicKey, message, xmssSignature) // throws if invalid

const sphincsKey = await lpq.SphincsSecretKey.fromSeed(Buffer.alloc(32, 2))
const sphincsSignature = await sphincsKey.sign(message)
lpq.sphincsVerify(sphincsKey.publicKey, message, sphincsSignature)
```

Persist your own durable high-water leaf index alongside a leanXMSS key's `toBytes()` and advance it before publishing a signature. `toBytes()` is secret material: the key's 32-byte seed. `XmssSecretKey.prepare(leafIndex)` builds the bottom tree a leaf index falls in ahead of signing there; a key keeps the 8 bottom trees it used last.

## Aggregation

`aggregate` verifies every raw signature before proving and runs one proof at a time per process. `setup()` moves the one-time guest build ahead of the first proof; calling it is optional and idempotent.

An aggregate's encoding is the proof alone, without its claims: send the claims alongside it, or let the receiver rebuild them. `Aggregate.fromBytes(data, { xmss, sphincs })` verifies the proof against exactly the claims you give it and rejects any other claim set, so every `Aggregate` is proven. The claims may come in any order, a repeated claim counts once, and an omitted list means no claims of that scheme.

```js
const leaf = await lpq.aggregate({
  xmss: [{ publicKey: xmssKey.publicKey, message, signature: xmssSignature }],
  sphincs: [{ publicKey: sphincsKey.publicKey, message, signature: sphincsSignature }],
})
const root = await lpq.aggregate({ children: [leaf] })

const received = await lpq.Aggregate.fromBytes(root.toBytes(), {
  xmss: [{ publicKey: xmssKey.publicKey, message }],
  sphincs: [{ publicKey: sphincsKey.publicKey, message }],
})
received.xmssClaims // [{ publicKey: xmssKey.publicKey, message }]
received.sphincsClaims // [{ publicKey: sphincsKey.publicKey, message }]
```

One aggregation takes seconds and over a gigabyte of memory.

## Development

Install Node.js 18.17 or later and Rust, then run:

```sh
cd bindings/node
npm ci
npm run build
npm test
```

`npm/` holds the per-platform package manifests. `napi create-npm-dirs` generates them from `package.json`'s `napi.targets`; rerun it and commit the result after changing the targets.

## Releasing

Each `bindings-vX.Y.Z` tag publishes `@kevaundray/lean-pq` and every platform package at `X.Y.Z` through `.github/workflows/bindings-release.yml`:

1. `node-build` stamps the version and builds one addon per target.
2. `node-package` fills the platform packages, sets the root package's `optionalDependencies` with `napi pre-publish --skip-optional-publish`, and packs every tarball.
3. `node-test` installs the root and platform tarball on each platform and signs, verifies and aggregates through them (`scripts/install-check.sh`).
4. `node-publish` publishes the platform packages, then the root package, with npm trusted publishing. npm adds provenance automatically. Versions already on npm are skipped, so a failed run can be re-dispatched on the same tag: `gh workflow run bindings-release.yml --ref bindings-vX.Y.Z`.

CI checks the packaging without publishing: it packs the root and Linux x64 packages, installs both tarballs into a fresh project, and runs `scripts/smoke.js` against them. To run it locally after `npm run build`:

```sh
pack=$(mktemp -d)
cp lean_pq_node.linux-x64-gnu.node npm/linux-x64-gnu/
npm pack --ignore-scripts --pack-destination "$pack"
npm pack --ignore-scripts --pack-destination "$pack" ./npm/linux-x64-gnu
sh scripts/install-check.sh "$pack/kevaundray-lean-pq-0.0.0-dev.tgz" \
  "$pack/kevaundray-lean-pq-linux-x64-gnu-0.0.0-dev.tgz" --aggregate
```

### One-time npm setup

npm can attach a trusted publisher only to a package that already exists, so the first release publishes the eight packages with a short-lived token, and later releases use trusted publishing. A platform package added later, such as `@kevaundray/lean-pq-win32-x64-msvc`, goes through the same steps on the first release that includes it; `node-package` warns about every package not yet on npm. Packages up to 0.11.1 were published from `ethereum/lean-pq-bindings`: point their trusted publishers at `leanEthereum/leanVM` (step 4) before the next release.

1. From the npm account that owns the `@kevaundray` scope, create a **granular access token** on npmjs.com (**Access Tokens → Generate New Token → Granular Access Token**) with read and write access to packages, a short expiry such as 7 days, and no other permissions. If your account requires two-factor authentication for publishing, allow the token to bypass it; CI cannot answer a 2FA prompt.
2. Store it as a repository secret:

   ```sh
   gh secret set NPM_TOKEN -R leanEthereum/leanVM
   ```

3. Cut a release. `node-publish` tries trusted publishing first, falls back to the token, and publishes `@kevaundray/lean-pq` and the seven platform packages with provenance.
4. Add a trusted publisher to each of the eight packages, on npmjs.com under the package's **Settings → Trusted publishing**, or with npm 11.15 or later:

   ```sh
   npm trust github <package> --repo leanEthereum/leanVM --file bindings-release.yml --env npm --allow-publish --yes
   ```

   The fields are repository `leanEthereum/leanVM`, workflow `bindings-release.yml`, environment `npm`, with `npm publish` allowed.
5. Delete the secret and revoke the token, then set each package's **Settings → Publishing access** to "Require two-factor authentication and disallow tokens":

   ```sh
   gh secret delete NPM_TOKEN -R leanEthereum/leanVM
   ```

