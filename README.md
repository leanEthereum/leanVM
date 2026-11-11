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
    <td align="right"><b>1400/s</b></td>
  </tr>
  <tr>
    <td><a href="#leansphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>470/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>2,8 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>150 ms</b></td>
  </tr>
  <tr>
    <td><a href="#hashing">proving KECCAK</a></td>
    <td align="right"><b>560K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>7M/s</b></td>
  </tr>
</table>

## security

leanVM is designed for security:

 * 128-bit ROM (64-bit QROM) soundness
 * no proximity gap conjecture
 * end-to-end formal verification
 * a traditional hash function (Keccak-256)

## work in progress

- leanVM is not yet stable
- Formal statements are still under review
- The Lean statements only describe the spec. Proving the Rust implem is faithful to the spec is still WIP.

**leanVM is not (yet) production ready.**

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM, CPU only, i.e. no metal GPU)

### leanXMSS aggregation

The leanXMSS parameters are specified in [leanXMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanXMSS.pdf), with a [security proof in Lean 4](formal/statement.tex). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --xmss 1400 --log-inv-rate 2 --repeat 3
```

```
aggregation, 1,400 leanXMSS signatures
  cycles (VM steps)           : 1,143,916 = 2^20.126
    details                   : XOR 2^18 (22.9%)  KECCAK 2^17.994 (22.8%)  MUL 2^17.856 (20.7%)  SET 2^17.348 (14.6%)  DEREF 2^17.281 (13.9%)  JUMP 2^15.811 (5.0%)  MEMORY 2^21.079  BYTECODE 2^18.513  TOTAL_COMMITTED 2^25.745
  proof size                  : 246.8 KiB
  proving time                : 0.964 s ± 4.5%      peak memory 5.42 GiB
  per signature               : 1,452.435 signatures/s
  verifying                   : 5.872 ms
```

### leanSPHINCS aggregation

The leanSPHINCS parameters are specified in [leanSPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanSPHINCS.pdf), with a [security proof in Lean 4](formal/statement.tex). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --sphincs 500 --log-inv-rate 1 --repeat 3
```

```
aggregation, 500 leanSPHINCS signatures
  cycles (VM steps)           : 2,756,127 = 2^21.394
    details                   : XOR 2^19.755 (32.1%)  MUL 2^19.436 (25.7%)  SET 2^19.392 (25.0%)  KECCAK 2^17.976 (9.4%)  DEREF 2^17.175 (5.4%)  JUMP 2^16.058 (2.5%)  MEMORY 2^22.043  BYTECODE2^18.902  TOTAL_COMMITTED 2^26.629
  proof size                  : 347.9 KiB
  proving time                : 1.06 s ± 1.1%      peak memory 6.179 GiB
  per signature               : 471.496 signatures/s
  verifying                   : 6.966 ms
```

### data availability

```bash
cargo leanvm aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 3,019,625 = 2^21.526
    details                   : XOR 2^20.098 (37.2%)  MUL 2^19.811 (30.5%)  DEREF 2^19.201 (20.0%)  JUMP 2^18.052 (9.0%)  SET 2^16.056 (2.3%)  KECCAK 2^15.088 (1.2%)  MEMORY 2^21.799  BYTECODE2^18.902  TOTAL_COMMITTED 2^26.496
  proof size                  : 339.6 KiB
  proving time                : 0.699 s ± 2.3%      peak memory 5.6 GiB
  blob throughput             : 22.905 blobs/s, 2.863 MiB/s
  verifying                   : 6.858 ms
```

### recursion

```bash
cargo leanvm recursion --n 2 --xmss-per-leaf 1400 --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 3
```

```
recursion 2→1, over leaves of 1,400 leanXMSS signatures, leaf rate = 1/4, recursion rate = 1/2
  cycles (VM steps)           : 460,415 = 2^18.813
    details                   : MUL 2^17.272 (34.4%)  XOR 2^16.961 (27.7%)  DEREF 2^16.57 (21.1%)  SET 2^15.18 (8.1%)  JUMP 2^14.683 (5.7%)  KECCAK 2^13.761 (3.0%)  MEMORY 2^19.476  BYTECODE 2^18.513  TOTAL_COMMITTED 2^23.845
  proof size                  : 321.5 KiB
  proving time                : 0.154 s ± 3.2%      peak memory 1.119 GiB
  verifying                   : 8.684 ms
```

### Proving KECCAK

```bash
cargo leanvm hash --log-n 17 --repeat 3
```

```
Keccak GKR batch proving, 131,072 permutations, a state committed every 12 rounds
  witness                         :     11.1 ms ± 28.9%    4.8%
  commit                          :     18.5 ms ± 10.5%    8.0%
  output claim                    :      2.4 ms ± 17.5%    1.0%
  layers and openings             :    179.7 ms ± 1.1%   77.3%
  pcs opening                     :     20.7 ms ± 11.7%    8.9%
  ------------------------------------------
  prove TOTAL (witness included)  :    232.4 ms ± 1.1%
  verify                          :      3.2 ms
  throughput                      :        563,994 permutations/s ± 1.1%
  proof size                      :       267.1 KiB  (1562 scalars, 230.4 KiB of Merkle openings)
```

### Fibonacci

```bash
cargo leanvm fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,040,016
    details                   : MUL 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.959  BYTECODE 2^10.017  TOTAL_COMMITTED2^25.261
  proof size                  : 308.1 KiB
  proving                     : 0.289 s ± 6.3%   7,064,777 cycles/s      peak memory 2.32 GiB
  verifying                   : 4.831 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Hashcaster 2](https://github.com/levs57/hashcaster2) proving Keccak via GKR and RMFE
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))

## FV Credits:

- [leanerVM](https://github.com/Verified-zkEVM/leanerVM) by [Nicolas Schleicher](https://github.com/scaraven) and others
- [leanDA FV](https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746) by [Benedikt Wagner](https://github.com/b-wagn)
- [VCVio](https://github.com/Verified-zkEVM/VCVio), [ArkLib](https://github.com/Verified-zkEVM/ArkLib), [CompPoly](https://github.com/Verified-zkEVM/CompPoly), (Verified zk(E)VM) [Clean](https://github.com/Verified-zkEVM/clean) (zksecurity)