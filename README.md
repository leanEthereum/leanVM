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
    <td align="right"><b>1600/s</b></td>
  </tr>
  <tr>
    <td><a href="#leansphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>500/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>3,2 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>140 ms</b></td>
  </tr>
  <tr>
    <td><a href="#proving-keccak">proving KECCAK</a></td>
    <td align="right"><b>800K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>7,6M/s</b></td>
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

Install commands, supported platforms and the sidecar that aggregation needs are in [`bindings/README.md`](bindings/README.md). Rust code uses `lean_vm` directly.

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM, CPU only, i.e. no metal GPU)

### leanXMSS aggregation

The leanXMSS parameters are specified in [leanXMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanXMSS.pdf), with a [security proof in Lean 4](formal/statement.tex). **This is not the definitive parameter set.**

```bash
cargo leanvm-bench --prover experimental aggregate --xmss 1400 --log-inv-rate 2 --repeat 3
```

```
aggregation, 1,400 leanXMSS signatures
  cycles (VM steps)           : 1,147,761 = 2^20.13
    details                   : XOR 2^17.999 (22.8%)  KECCAK 2^17.994 (22.7%)  MUL 2^17.855 (20.7%)  SET 2^17.365 (14.7%)  DEREF 2^17.3 (14.1%)  JUMP 2^15.81 (5.0%)  MEMORY 2^21.081  BYTECODE 2^18.812  TOTAL_COMMITTED 2^25.589
  proof size                  : 209.4 KiB
  proving time                : 0.885 s ± 0.8%      peak memory 4.995 GiB
  per signature               : 1,581.591 signatures/s
  verifying                   : 4.522 ms
```

### leanSPHINCS aggregation

The leanSPHINCS parameters are specified in [leanSPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanSPHINCS.pdf), with a [security proof in Lean 4](formal/statement.tex). **This is not the definitive parameter set.**

```bash
cargo leanvm-bench --prover experimental aggregate --sphincs 500 --log-inv-rate 1 --repeat 3
```

```
aggregation, 500 leanSPHINCS signatures
  cycles (VM steps)           : 2,757,351 = 2^21.395
    details                   : XOR 2^19.755 (32.1%)  MUL 2^19.435 (25.7%)  SET 2^19.391 (24.9%)  KECCAK 2^17.976 (9.3%)  DEREF 2^17.195 (5.4%)  JUMP 2^16.058 (2.5%)  MEMORY 2^22.043  BYTECODE 2^18.812  TOTAL_COMMITTED 2^26.422
  proof size                  : 294.1 KiB
  proving time                : 0.986 s ± 0.4%      peak memory 4.574 GiB
  per signature               : 507.34 signatures/s
  verifying                   : 5.341 ms
```

### data availability

```bash
cargo leanvm-bench --prover experimental aggregate --blobs 32 --log-inv-rate 1 --repeat 3
```

```
aggregation, 32 blobs
  cycles (VM steps)           : 2,602,234 = 2^21.311
    details                   : XOR 2^20.063 (42.1%)  MUL 2^19.392 (26.4%)  DEREF 2^19.25 (24.0%)  SET 2^16.717 (4.1%)  KECCAK 2^16.088 (2.7%)  JUMP 2^14.14 (0.7%)  MEMORY 2^21.88  BYTECODE 2^18.801  TOTAL_COMMITTED 2^26.291
  proof size                  : 289.8 KiB
  proving time                : 0.643 s ± 2.6%      peak memory 4.28 GiB
  blob throughput             : 49.757 blobs/s, 6.22 MiB/s
  verifying                   : 5.466 ms
```

### recursion

```bash
cargo leanvm-bench --prover experimental recursion --n 2 --xmss-per-leaf 1400 --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 3
```

```
recursion 2→1, over leaves of 1,400 leanXMSS signatures, leaf rate = 1/4, recursion rate = 1/2
  cycles (VM steps)           : 431,087 = 2^18.718
    details                   : MUL 2^17.185 (34.6%)  XOR 2^16.726 (25.1%)  DEREF 2^16.641 (23.7%)  SET 2^15.409 (10.1%)  JUMP 2^13.797 (3.3%)  KECCAK 2^13.747 (3.2%)  MEMORY 2^19.394  BYTECODE 2^18.812  TOTAL_COMMITTED 2^23.611
  proof size                  : 270.5 KiB
  proving time                : 0.146 s ± 3.9%      peak memory 0.917 GiB
  verifying                   : 6.921 ms
```

### Proving KECCAK

```bash
KECCAK_N_LOG=20 BENCH_REPEAT=3 cargo bench -p experimental_keccak_gkr --bench hash_batch
```

```
Keccak GKR batch proving, 1,048,576 permutations, a state committed every 12 rounds
  witness                         :     63.8 ms ± 12.0%    5.1%
  commit                          :    116.1 ms ± 0.4%    9.2%
  output claim                    :     12.2 ms ± 1.8%    1.0%
  layers and openings             :    932.2 ms ± 1.2%   74.1%
  pcs opening                     :    133.7 ms ± 0.9%   10.6%
  ------------------------------------------
  prove TOTAL (witness included)  :   1258.1 ms ± 0.7%
  verify                          :      2.7 ms
  throughput                      :        833,488 permutations/s ± 0.7%
  proof size                      :       281.3 KiB  (1722 scalars, 254.4 KiB of Merkle openings)
```

### Fibonacci

```bash
cargo leanvm-bench --prover experimental fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,040,016
    details                   : MUL 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.959  BYTECODE 2^10.017  TOTAL_COMMITTED 2^25.014
  proof size                  : 262.6 KiB
  proving                     : 0.267 s ± 2.1%   7,641,814 cycles/s      peak memory 1.733 GiB
  verifying                   : 3.85 ms
```

## SNARK machinery

- 128-bit binary field (degree-2 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187), using [affine combiners](https://eprint.iacr.org/2026/2863)
- [Hashcaster 2](https://github.com/levs57/hashcaster2) proving Keccak via GKR and RMFE
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))

## FV Credits:

- [leanerVM](https://github.com/Verified-zkEVM/leanerVM) by [Nicolas Schleicher](https://github.com/scaraven) and others
- [leanDA FV](https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746) by [Benedikt Wagner](https://github.com/b-wagn)
- [VCVio](https://github.com/Verified-zkEVM/VCVio), [ArkLib](https://github.com/Verified-zkEVM/ArkLib), [CompPoly](https://github.com/Verified-zkEVM/CompPoly), (Verified zk(E)VM) [Clean](https://github.com/Verified-zkEVM/clean) (zksecurity)