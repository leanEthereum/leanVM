# Changelog

## [0.16.0](https://github.com/leanEthereum/leanVM/compare/bindings-v0.15.0...bindings-v0.16.0) (2026-11-20)


### Features

* VRF tree, with pruning + with a cached middle layer ([#805](https://github.com/leanEthereum/leanVM/issues/805)) ([c38f2ba](https://github.com/leanEthereum/leanVM/commit/c38f2bac8ec30f1ab1d6e5d55908be2377abdc77))


### Bug Fixes

* staged native archives carry no LLVM bitcode, which Go 1.27 refuses ([41ca15b](https://github.com/leanEthereum/leanVM/commit/41ca15b4fd3c5830fca434ec2f78aa49a709d80d))

## [0.15.0](https://github.com/leanEthereum/leanVM/compare/bindings-v0.14.0...bindings-v0.15.0) (2026-11-20)


### ⚠ BREAKING CHANGES

* leanXMSS keys store 2^8 nodes per tree and cache 4 bottom trees (at most 20 KiB of cache per key)

### Features

* leanXMSS keys store 2^8 nodes per tree and cache 4 bottom trees (at most 20 KiB of cache per key) ([3c48956](https://github.com/leanEthereum/leanVM/commit/3c48956771ac909669b7ee54110170dbb6f21339))

## [0.14.0](https://github.com/leanEthereum/leanVM/compare/bindings-v0.13.1...bindings-v0.14.0) (2026-11-20)


### Features

* leanXMSS keys store 2^10 nodes per tree, and load from their tree cache ([#802](https://github.com/leanEthereum/leanVM/issues/802)) ([5b43139](https://github.com/leanEthereum/leanVM/commit/5b43139d50272f996ca884669b1d51555af1f35d))

## [0.13.1](https://github.com/leanEthereum/leanVM/compare/bindings-v0.13.0...bindings-v0.13.1) (2026-11-20)


### Bug Fixes

* add leanvm-sidecar --version ([8895fd1](https://github.com/leanEthereum/leanVM/commit/8895fd13d33acd90192f5d3ccc2f11f2332ce72e))

## [0.13.0](https://github.com/leanEthereum/leanVM/compare/bindings-v0.12.0...bindings-v0.13.0) (2026-11-19)


### ⚠ BREAKING CHANGES

* aggregate(), setup() and Aggregate.from_bytes are replaced by Sidecar.aggregate and Sidecar.verify on a running leanvm-sidecar (Unix only); the C ABI's aggregate calls take a sidecar handle.

### Features

* bindings: aggregate/verify through a leanVM sidecar instead of in-process ([#804](https://github.com/leanEthereum/leanVM/issues/804)) ([dbd30ec](https://github.com/leanEthereum/leanVM/commit/dbd30ec2c6f2475b4e996994f80b1ee5404ea1c2))

## [0.12.0](https://github.com/leanEthereum/leanVM/compare/bindings-v0.11.1...bindings-v0.12.0) (2026-11-19)


### ⚠ BREAKING CHANGES

* the Go module is leanvm.org/go, the Nim package is bindings/nim at tag bindings-vX.Y.Z (`?subdir=bindings/nim`), and an aggregate from 0.11.x and one from 0.12.0 reject each other.

### Features

* move the bindings into leanVM ([#789](https://github.com/leanEthereum/leanVM/issues/789)) ([39acb3f](https://github.com/leanEthereum/leanVM/commit/39acb3fe0c19586767075733496cb5ee6d7ce3c1))

## [0.11.1](https://github.com/ethereum/lean-pq-bindings/compare/v0.11.0...v0.11.1) (2026-11-19)


### Bug Fixes

* **go:** read native error messages on the failing call's OS thread ([#52](https://github.com/ethereum/lean-pq-bindings/issues/52)) ([d7a77e8](https://github.com/ethereum/lean-pq-bindings/commit/d7a77e8ad042d97b21eca8722e573dc22aaffe53))


### Performance Improvements

* aggregate with leanVM's experimental prover ([#54](https://github.com/ethereum/lean-pq-bindings/issues/54)) ([142a54a](https://github.com/ethereum/lean-pq-bindings/commit/142a54a627c94d1cc0bce2942bcba0234aaa34a1))

## [0.11.0](https://github.com/ethereum/lean-pq-bindings/compare/v0.10.1...v0.11.0) (2026-11-18)


### ⚠ BREAKING CHANGES

* update leanVM to 28368657 with proof-only aggregates ([#53](https://github.com/ethereum/lean-pq-bindings/issues/53))

### Features

* **nim:** add Nim bindings with Nimble packaging ([#50](https://github.com/ethereum/lean-pq-bindings/issues/50)) ([1663509](https://github.com/ethereum/lean-pq-bindings/commit/1663509ec6b503bf9c267da1e2d313ee77c6c12a))
* update leanVM to 28368657 with proof-only aggregates ([#53](https://github.com/ethereum/lean-pq-bindings/issues/53)) ([9b6dcd3](https://github.com/ethereum/lean-pq-bindings/commit/9b6dcd3c1465f93597cba514f78ce63e9287a59d))

## [0.10.1](https://github.com/ethereum/lean-pq-bindings/compare/v0.10.0...v0.10.1) (2026-11-16)


### Bug Fixes

* **zig:** link the Windows synchronization library ([#48](https://github.com/ethereum/lean-pq-bindings/issues/48)) ([a6e3827](https://github.com/ethereum/lean-pq-bindings/commit/a6e382705f8ac41bc8ccbf97131508bb824f1996))

## [0.10.0](https://github.com/ethereum/lean-pq-bindings/compare/v0.9.0...v0.10.0) (2026-11-16)


### ⚠ BREAKING CHANGES

* update leanVM to 5e3ade21 for its FIPS 205 leanSPHINCS layout ([#45](https://github.com/ethereum/lean-pq-bindings/issues/45))

### Features

* update leanVM to 5e3ade21 for its FIPS 205 leanSPHINCS layout ([#45](https://github.com/ethereum/lean-pq-bindings/issues/45)) ([1b8f279](https://github.com/ethereum/lean-pq-bindings/commit/1b8f2792499af2ffb438da6cf7cc8de43263c332))

## [0.9.0](https://github.com/ethereum/lean-pq-bindings/compare/v0.8.0...v0.9.0) (2026-11-04)


### ⚠ BREAKING CHANGES

* update leanVM to ed7d2b9 and its new leanSPHINCS ([#44](https://github.com/ethereum/lean-pq-bindings/issues/44))

### Features

* **rust:** expose the leanXMSS lifetime as xmss::LOG_LIFETIME ([#42](https://github.com/ethereum/lean-pq-bindings/issues/42)) ([0cc7bc6](https://github.com/ethereum/lean-pq-bindings/commit/0cc7bc6c7de965ce166498546b2a549dac65ca1d))
* update leanVM to ed7d2b9 and its new leanSPHINCS ([#44](https://github.com/ethereum/lean-pq-bindings/issues/44)) ([f262172](https://github.com/ethereum/lean-pq-bindings/commit/f262172eb107ebaa102938d958f27e6aad571270))

## [0.8.0](https://github.com/ethereum/lean-pq-bindings/compare/v0.7.0...v0.8.0) (2026-10-28)


### ⚠ BREAKING CHANGES

* **rust:** rebuild the Rust facade with typed errors ([#39](https://github.com/ethereum/lean-pq-bindings/issues/39))

### Features

* **rust:** make leanVM aggregation an optional default feature ([#41](https://github.com/ethereum/lean-pq-bindings/issues/41)) ([39cd44b](https://github.com/ethereum/lean-pq-bindings/commit/39cd44bd9bbe558b946abea257a6b77750cc6620))


### Code Refactoring

* **rust:** rebuild the Rust facade with typed errors ([#39](https://github.com/ethereum/lean-pq-bindings/issues/39)) ([03d576e](https://github.com/ethereum/lean-pq-bindings/commit/03d576ec7b958d03ffc963a5ecb6b86d64a19bf0))

## [0.7.0](https://github.com/ethereum/lean-pq-bindings/compare/v0.6.2...v0.7.0) (2026-10-27)


### Features

* Windows x86-64 for every binding, and a Go module that needs no Rust ([#37](https://github.com/ethereum/lean-pq-bindings/issues/37)) ([5d6313c](https://github.com/ethereum/lean-pq-bindings/commit/5d6313c4e76184ac3f390f6b90e99aab23644d3c))

## [0.6.2](https://github.com/ethereum/lean-pq-bindings/compare/v0.6.1...v0.6.2) (2026-10-27)


### Documentation

* **python:** point to the Node.js, Java, and Zig packages ([b33080e](https://github.com/ethereum/lean-pq-bindings/commit/b33080ea8477e03a77ca764e778a13c908f9e15c))

## [0.6.1](https://github.com/ethereum/lean-pq-bindings/compare/v0.6.0...v0.6.1) (2026-10-26)


### Miscellaneous Chores

* **python:** link the changelog from the PyPI page ([9534b44](https://github.com/ethereum/lean-pq-bindings/commit/9534b447de26e14114a4dc6cb6250adac3a2a634))

## [0.6.0](https://github.com/ethereum/lean-pq-bindings/compare/v0.4.0...v0.6.0) (2026-10-26)


### ⚠ BREAKING CHANGES

* the Claim/slot, Signature, MultiClaimProof, and merge APIs are replaced by leanXMSS/leanSPHINCS secret keys, byte signatures, and Aggregate. The PyPI package is now py-lean-pq.
* replace Python bindings with safe facade ([#10](https://github.com/ethereum/lean-pq-bindings/issues/10))

### Features

* add Java 25 bindings ([#12](https://github.com/ethereum/lean-pq-bindings/issues/12)) ([3690a76](https://github.com/ethereum/lean-pq-bindings/commit/3690a7628c0148f61419c4f3de189880e6f356f7))
* rename to lean-pq and port bindings to upstream leanVM ([c7edcc4](https://github.com/ethereum/lean-pq-bindings/commit/c7edcc46a55d4525c862f6eba89d76c6f4726fcb))
* replace Python bindings with safe facade ([#10](https://github.com/ethereum/lean-pq-bindings/issues/10)) ([4a0f276](https://github.com/ethereum/lean-pq-bindings/commit/4a0f27634d94633a756fac7639a67a4e353df31b))

## [0.4.0](https://github.com/ethereum/py-lean-multisig/compare/v0.3.0...v0.4.0) (2026-05-08)


### Features

* Fix license line formatting in README.md ([#7](https://github.com/ethereum/py-lean-multisig/issues/7)) ([18bbc35](https://github.com/ethereum/py-lean-multisig/commit/18bbc3598a59281a8e966570b01ce935ea9836a3))

## [0.3.0](https://github.com/kevaundray/py-lean-multisig/compare/v0.2.0...v0.3.0) (2026-05-06)


### Features

* use basic binary encoding with signature and public key ([188c183](https://github.com/kevaundray/py-lean-multisig/commit/188c183f45a38c7975fa842f934fd0d26acb68db))

## [0.2.0](https://github.com/kevaundray/py-lean-multisig/compare/v0.0.1...v0.2.0) (2026-05-06)


### Features

* trigger release please ([4896bdf](https://github.com/kevaundray/py-lean-multisig/commit/4896bdf2d5b42b31dcc7197a532676e88dc7c5b5))


### Bug Fixes

* typo ([864ded7](https://github.com/kevaundray/py-lean-multisig/commit/864ded7a7849c753317037619373a4d736a913cb))


### Miscellaneous Chores

* release 0.2.0 ([d0c57d0](https://github.com/kevaundray/py-lean-multisig/commit/d0c57d09c7383d5e252ec3d07b777c54ce903f91))
