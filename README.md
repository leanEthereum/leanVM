<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">minimal hash-based zkVM, for post-quantum Ethereum</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
</p>

<table align="center">
  <tr>
    <td><a href="#leanxmss-aggregation">leanXMSS aggregation</a></td>
    <td align="right"><b>2000/s</b></td>
  </tr>
  <tr>
    <td><a href="#leansphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>690/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>6,9 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>135 ms</b></td>
  </tr>
  <tr>
    <td><a href="#proving-keccak">proving KECCAK</a></td>
    <td align="right"><b>870K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>8,2M/s</b></td>
  </tr>
</table>

## security

leanVM is designed for security:

 * 125-bit ROM (62-bit QROM) soundness
 * no proximity gap conjecture
 * end-to-end formal verification
 * a traditional hash function (Keccak-256)

## work in progress

- leanVM is not yet stable
- Formal statements are still under review
- The Lean statements only describe the spec. Proving the Rust implem is faithful to the spec is still WIP.

**leanVM is not (yet) production ready.**

## two provers

In the short term, we provide two Rust implementations of the prover, `stable` (for readability and safety) and `experimental` (includes the latest optimizations). There will eventually be a single prover in this repo.

## bindings

Python, Node.js, Java, Go, Zig and Nim bindings for leanXMSS, leanSPHINCS and their aggregation, released together as `bindings-vX.Y.Z` ([releases](https://github.com/leanEthereum/leanVM/releases?q=bindings&expanded=true)):

| language | package |
| --- | --- |
| Python | [`py-lean-pq`](https://pypi.org/project/py-lean-pq/) on PyPI |
| Node.js | [`@kevaundray/lean-pq`](https://www.npmjs.com/package/@kevaundray/lean-pq) on npm |
| Java | [`io.github.crate-crypto:lean-pq`](https://central.sonatype.com/artifact/io.github.crate-crypto/lean-pq) on Maven Central |
| Go | [`leanvm.org/go`](https://pkg.go.dev/leanvm.org/go) |
| Zig | `lean-pq-zig-X.Y.Z.tar.gz` attached to each [`bindings-vX.Y.Z` release](https://github.com/leanEthereum/leanVM/releases?q=bindings&expanded=true) |
| Nim | [`bindings/nim`](bindings/nim/README.md) at tag `bindings-vX.Y.Z` |

Install commands and supported platforms are in [`bindings/README.md`](bindings/README.md). Rust code uses `lean_vm` directly.

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM, CPU only, i.e. no metal GPU)

### leanXMSS aggregation

The leanXMSS parameters are specified in [leanXMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanXMSS.pdf), with a [security proof in Lean 4](formal/statement.tex). **This is not the definitive parameter set.**

```bash
cargo leanvm-bench --prover experimental aggregate --xmss 1400 --log-inv-rate 2 --repeat 3
```

```
aggregation, 1,400 leanXMSS signatures
  cycles (VM steps)           : 1,142,142 = 2^20.123
    details                   : KECCAK 2^17.994 (22.9%)  XOR 2^17.981 (22.7%)  DEREF 2^17.88 (21.1%)  SET 2^17.37 (14.8%)  MUL 2^17.236 (13.5%)  JUMP 2^15.81 (5.0%)  MEMORY 2^20.847  BYTECODE 2^18.683  TOTAL_COMMITTED 2^24.889
  proof size                  : 203.1 KiB
  proof stream                : 2062 F128 scalars (32.2 KiB), Merkle openings 170.5 KiB
  proving time                : 0.535 s ± 1.6%      peak memory 3.577 GiB
  per signature               : 2,619.255 signatures/s
  verifying                   : 6.812 ms
```

### leanSPHINCS aggregation

The leanSPHINCS parameters are specified in [leanSPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanSPHINCS.pdf), with a [security proof in Lean 4](formal/statement.tex). **This is not the definitive parameter set.**

```bash
cargo leanvm-bench --prover experimental aggregate --sphincs 500 --log-inv-rate 1 --repeat 3
```

```
aggregation, 500 leanSPHINCS signatures
  cycles (VM steps)           : 2,753,776 = 2^21.393
    details                   : XOR 2^19.752 (32.1%)  MUL 2^19.42 (25.5%)  SET 2^19.394 (25.0%)  KECCAK 2^17.976 (9.4%)  DEREF 2^17.233 (5.6%)  JUMP 2^16.058 (2.5%)  MEMORY 2^21.807  BYTECODE 2^18.683  TOTAL_COMMITTED 2^25.651
  proof size                  : 287.6 KiB
  proof stream                : 2094 F128 scalars (32.7 KiB), Merkle openings 254.5 KiB
  proving time                : 0.623 s ± 3.9%      peak memory 3.971 GiB
  per signature               : 802.368 signatures/s
  verifying                   : 7.328 ms
```

### data availability

```bash
cargo leanvm-bench --prover experimental aggregate --blobs 32 --log-inv-rate 1 --repeat 3
```

```
aggregation, 32 blobs
  cycles (VM steps)           : 2,572,005 = 2^21.294
    details                   : XOR 2^20.063 (42.6%)  DEREF 2^19.321 (25.5%)  MUL 2^19.248 (24.2%)  SET 2^16.776 (4.4%)  KECCAK 2^16.088 (2.7%)  JUMP 2^14.096 (0.7%)  MEMORY 2^21.874  BYTECODE 2^18.683  TOTAL_COMMITTED 2^25.66
  proof size                  : 289.9 KiB
  proof stream                : 2080 F128 scalars (32.5 KiB), Merkle openings 257.0 KiB
  proving time                : 0.451 s ± 1.9%      peak memory 2.802 GiB
  blob throughput             : 70.915 blobs/s, 8.864 MiB/s
  verifying                   : 7.489 ms
```

### recursion

```bash
cargo leanvm-bench --prover experimental recursion --n 16 --xmss-per-leaf 1400 --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 3
```

```
recursion 16→1, over leaves of 1,400 leanXMSS signatures, leaf rate = 1/4, recursion rate = 1/2
  cycles (VM steps)           : 3,052,041 = 2^21.541
    details                   : MUL 2^20.007 (34.5%)  XOR 2^19.78 (29.5%)  DEREF 2^19.487 (24.1%)  SET 2^17.311 (5.3%)  KECCAK 2^16.673 (3.4%)  JUMP 2^16.554 (3.2%)  MEMORY 2^21.935  BYTECODE 2^18.683  TOTAL_COMMITTED 2^25.768
  proof size                  : 295.5 KiB
  proof stream                : 2080 F128 scalars (32.5 KiB), Merkle openings 262.6 KiB
  proving time                : 0.538 s ± 5.4%      peak memory 3.367 GiB
  verifying                   : 13.104 ms
```

### Proving KECCAK

```bash
KECCAK_N_LOG=20 BENCH_REPEAT=3 cargo bench -p experimental_keccak_gkr --bench hash_batch
```

```
Keccak GKR batch proving, 1,048,576 permutations, a state committed every 12 rounds
  witness                         :     63.4 ms ± 19.3%    5.3%
  commit                          :    117.5 ms ± 3.6%    9.7%
  output claim                    :     12.3 ms ± 4.0%    1.0%
  layers and openings             :    903.7 ms ± 2.7%   74.9%
  pcs opening                     :    109.7 ms ± 0.8%    9.1%
  ------------------------------------------
  prove TOTAL (witness included)  :   1206.6 ms ± 2.1%
  verify                          :      2.7 ms
  throughput                      :        869,028 permutations/s ± 2.1%
  proof size                      :       281.4 KiB  (1722 scalars, 254.5 KiB of Merkle openings)
```

### Fibonacci

```bash
cargo leanvm-bench --prover experimental fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,036,016
    details                   : MUL 2^20.937 (98.6%)  DEREF 2^13.774 (0.7%)  SET 2^13.288 (0.5%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.956  BYTECODE 2^10.014  TOTAL_COMMITTED 2^24.48
  proof size                  : 265.7 KiB
  proving                     : 0.206 s ± 7.2%   9,859,859 cycles/s      peak memory 1.112 GiB
  verifying                   : 2.978 ms
```

## SNARK machinery

- 128-bit binary field (degree-2 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187), using [affine combiners](https://eprint.iacr.org/2026/2863)
- [Hashcaster 2](https://github.com/levs57/hashcaster2) proving Keccak via GKR and RMFE
- Hotwire (Dao, Thaler and Wambsgans): tables linked by one-hot pointers, after [Twist and Shout](https://eprint.iacr.org/2025/105)
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))

## FV Credits:

- [leanerVM](https://github.com/Verified-zkEVM/leanerVM) by [Nicolas Schleicher](https://github.com/scaraven) and others
- [leanDA FV](https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746) by [Benedikt Wagner](https://github.com/b-wagn)
- [VCVio](https://github.com/Verified-zkEVM/VCVio), [ArkLib](https://github.com/Verified-zkEVM/ArkLib), [CompPoly](https://github.com/Verified-zkEVM/CompPoly), (Verified zk(E)VM) [Clean](https://github.com/Verified-zkEVM/clean) (zksecurity)