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
    <td align="right"><b>1,2K/s</b></td>
  </tr>
  <tr>
    <td><a href="#leansphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>875/s</b></td>
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
    <td><a href="#hashing">proving KECCAK</a></td>
    <td align="right"><b>540K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>5,8M/s</b></td>
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

```
aggregation, 1,400 leanXMSS signatures
  cycles (VM steps)           : 1,569,406 = 2^20.582
    details                   : XOR 2^18.675 (26.7%)  SET 2^18.179 (18.9%)  MUL 2^18.13 (18.3%)  KECCAK 2^17.994 (16.6%)  DEREF 2^17.559 (12.3%)  JUMP 2^16.788 (7.2%)  MEMORY 2^23.109  BYTECODE 2^18.473  TOTAL_COMMITTED 2^26.801
  proof size                  : 358.5 KiB
  proving time                : 1.175 s ± 0.8%      peak memory 11.152 GiB
  per signature               : 1,191.353 signatures/s
  verifying                   : 7.43 ms
```

### leanSPHINCS aggregation

The leanSPHINCS parameters are specified in [leanSPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanSPHINCS.pdf), with a [(ROM) security proof in Lean 4](formal/lean_sphincs/README.md). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --sphincs 975 --log-inv-rate 1 --repeat 3
```

```
aggregation, 975 leanSPHINCS signatures
  cycles (VM steps)           : 1,774,523 = 2^20.759
    details                   : XOR 2^18.916 (27.9%)  SET 2^18.533 (21.4%)  MUL 2^18.192 (16.9%)  KECCAK 2^17.993 (14.7%)  DEREF 2^17.75 (12.4%)  JUMP 2^16.871 (6.8%)  MEMORY 2^22.769  BYTECODE 2^18.473  TOTAL_COMMITTED 2^26.313
  proof size                  : 330.8 KiB
  proving time                : 1.113 s ± 2.7%      peak memory 9.118 GiB
  per signature               : 875.984 signatures/s
  verifying                   : 7.458 ms
```

### data availability

```bash
cargo leanvm aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 3,197,416 = 2^21.608
    details                   : XOR 2^20.223 (38.3%)  MUL 2^19.895 (30.5%)  DEREF 2^19.132 (18.0%)  JUMP 2^18.297 (10.1%)  SET 2^15.904 (1.9%)  KECCAK 2^15.324 (1.3%)  MEMORY 2^21.939  BYTECODE 2^18.473  TOTAL_COMMITTED 2^26.486
  proof size                  : 337.1 KiB
  proving time                : 0.854 s ± 3.5%      peak memory 9.737 GiB
  blob throughput             : 18.737 blobs/s, 2.342 MiB/s
  verifying                   : 12.07 ms
```

### recursion

```bash
cargo leanvm recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 leanXMSS signatures
  cycles (VM steps)           : 542,311 = 2^19.049
    details                   : MUL 2^17.622 (37.2%)  XOR 2^17.183 (27.4%)  DEREF 2^16.841 (21.6%)  SET 2^15.217 (7.0%)  JUMP 2^14.527 (4.4%)  KECCAK 2^13.63 (2.3%)  MEMORY 2^19.782  BYTECODE 2^18.473  TOTAL_COMMITTED 2^24.02
  proof size                  : 218.1 KiB
  proving time                : 0.303 s ± 0.6%      peak memory 8.69 GiB
  verifying                   : 9.195 ms
```

### Proving KECCAK

```bash
cargo leanvm hash --log-n 17 --repeat 3
```

```
Keccak GKR batch proving, 131,072 permutations, a state committed every 12 rounds
  witness                         :     16.8 ms ± 10.9%    6.9%
  commit                          :     17.5 ms ± 26.4%    7.2%
  output claim                    :      2.1 ms ± 16.9%    0.9%
  layers and openings             :    178.5 ms ± 2.5%   73.5%
  pcs opening                     :     28.0 ms ± 8.0%   11.5%
  ------------------------------------------
  prove TOTAL (witness included)  :    242.9 ms ± 2.3%
  verify                          :      4.1 ms
  throughput                      :        539,619 permutations/s ± 2.3%
  proof size                      :       290.2 KiB  (1562 scalars, 253.6 KiB of Merkle openings)
```

### Fibonacci

```bash
cargo leanvm fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,040,016
    details                   : MUL 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.959  BYTECODE 2^10.017  TOTAL_COMMITTED 2^25.261
  proof size                  : 312.2 KiB
  proving                     : 0.352 s ± 4.1%   5,795,076 cycles/s      peak memory 3.332 GiB
  verifying                   : 5.767 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Hashcaster 2](https://github.com/levs57/hashcaster2) proving Keccak via GKR and RMFE
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
