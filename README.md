<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">minimal hash-based zkVM, for post-quantum Ethereum</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="./python-verifier/verifier.py"><img src="https://img.shields.io/badge/verifier-python-yellow?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

<table align="center">
  <tr>
    <td><a href="#leanxmss-aggregation">leanXMSS aggregation</a></td>
    <td align="right"><b>1200/s</b></td>
  </tr>
  <tr>
    <td><a href="#leansphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>850/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>2,3 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>0.30s</b></td>
  </tr>
  <tr>
    <td><a href="#hashing">hash compressions</a></td>
    <td align="right"><b>540K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>5,7M/s</b></td>
  </tr>
</table>

## security

leanVM is designed for security:

 * 128-bit ROM (64-bit QROM) soundness
 * no proximity gap conjecture
 * end-to-end formal verification
 * a traditional hash function

**warning**: Formal verification is [in progress](https://github.com/Verified-zkEVM/leanerVM). leanVM is not (yet) production ready.

## work in progress

Expect leanVM to change significantly:

* **hash**: Keccak-256 is a placeholder: SHA2, BLAKE2s and BLAKE3 are actively considered.
* **ISA**: A migration from leanISA to RISC-V (rv64im) is planned.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM)

**note**: The Metal GPU was not used.

### leanXMSS aggregation

The leanXMSS parameters are specified in [leanXMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanXMSS.pdf), with a [(ROM) security proof in Lean 4](formal/lean_xmss/LeanXmss/Statement.lean). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --xmss 1400 --log-inv-rate 1 --repeat 3
```

**note**: The output below was measured on the single-layer XMSS over Keccak-256 that leanXMSS replaced. leanXMSS over Keccak-256 has not been measured yet.

```
aggregation, 1,400 leanXMSS signatures
  cycles (VM steps)           : 1,569,406 = 2^20.582
    details                   : XOR 2^18.675 (26.7%)  SET 2^18.179 (18.9%)  MUL 2^18.13 (18.3%)  KECCAK 2^17.994 (16.6%)  DEREF 2^17.559 (12.3%)  JUMP 2^16.788 (7.2%)  MEMORY 2^23.109  BYTECODE 2^18.474  TOTAL_COMMITTED 2^26.845
  proof size                  : 363.0 KiB
  proving time                : 1.172 s ± 0.8%      peak memory 11.562 GiB
  per signature               : 1,194.859 signatures/s
  verifying                   : 8.778 ms
```

### leanSPHINCS aggregation

The leanSPHINCS parameters are specified in [leanSPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanSPHINCS.pdf), with a [(ROM) security proof in Lean 4](formal/lean_sphincs/README.md). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --sphincs 975 --log-inv-rate 1 --repeat 3
```

```
aggregation, 975 leanSPHINCS signatures
  cycles (VM steps)           : 1,774,523 = 2^20.759
    details                   : XOR 2^18.916 (27.9%)  SET 2^18.533 (21.4%)  MUL 2^18.192 (16.9%)  KECCAK 2^17.993 (14.7%)  DEREF 2^17.75 (12.4%)  JUMP 2^16.871 (6.8%)  MEMORY 2^22.769  BYTECODE 2^18.494  TOTAL_COMMITTED 2^26.375
  proof size                  : 334.8 KiB
  proving time                : 1.15 s ± 2.6%      peak memory 10.32 GiB
  per signature               : 848.003 signatures/s
  verifying                   : 8.827 ms
```

### data availability

```bash
cargo leanvm aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 3,197,416 = 2^21.608
    details                   : XOR 2^20.223 (38.3%)  MUL 2^19.895 (30.5%)  DEREF 2^19.132 (18.0%)  JUMP 2^18.297 (10.1%)  SET 2^15.904 (1.9%)  KECCAK 2^15.324 (1.3%)  MEMORY 2^21.939  BYTECODE 2^18.494  TOTAL_COMMITTED 2^26.5
  proof size                  : 342.0 KiB
  proving time                : 0.875 s ± 2.6%      peak memory 9.858 GiB
  blob throughput             : 18.286 blobs/s, 2.286 MiB/s
  verifying                   : 14.482 ms
```

### recursion

```bash
cargo leanvm recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 leanXMSS signatures
  cycles (VM steps)           : 544,979 = 2^19.056
    details                   : MUL 2^17.631 (37.2%)  XOR 2^17.186 (27.4%)  DEREF 2^16.85 (21.7%)  SET 2^15.226 (7.0%)  JUMP 2^14.532 (4.3%)  KECCAK 2^13.63 (2.3%)  MEMORY 2^19.79  BYTECODE 2^18.474  TOTAL_COMMITTED 2^24.039
  proof size                  : 216.7 KiB
  proving time                : 0.302 s ± 2.8%      peak memory 8.96 GiB
  verifying                   : 9.814 ms
```

### hashing

```bash
cargo leanvm hash --log-n 17 --repeat 3
```

```
Keccak GKR batch proving, 131,072 permutations, a state committed every 12 rounds
  witness                         :      9.7 ms ± 31.2%    4.0%
  commit                          :     17.2 ms ± 20.8%    7.1%
  output claim                    :      2.2 ms ± 21.8%    0.9%
  layers and openings             :    184.2 ms ± 2.0%   76.0%
  pcs opening                     :     29.0 ms ± 6.6%   12.0%
  ------------------------------------------
  prove TOTAL (witness included)  :    242.3 ms ± 2.2%
  verify                          :      5.0 ms
  throughput                      :        541,034 permutations/s ± 2.2%
  proof size                      :       290.2 KiB  (1562 scalars, 253.6 KiB of Merkle openings)
```

### Fibonacci

```bash
cargo leanvm fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,040,016
    details                   : MUL 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY2^20.959  BYTECODE 2^10.017  TOTAL_COMMITTED 2^25.261
  proof size                  : 311.2 KiB
  proving                     : 0.353 s ± 7.3%   5,772,886 cycles/s      peak memory 3.331 GiB
  verifying                   : 7.356 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Hashcaster 2](https://github.com/levs57/hashcaster2) proving Keccak via GKR and RMFE
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
