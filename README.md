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
    <td align="right"><b>1130/s</b></td>
  </tr>
  <tr>
    <td><a href="#leansphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>720/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>2 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>0.34s</b></td>
  </tr>
  <tr>
    <td><a href="#hashing">hash compressions</a></td>
    <td align="right"><b>500K/s</b></td>
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
cargo leanvm aggregate --xmss 900 --log-inv-rate 1 --repeat 3
```

**note**: The output below was measured on the single-layer XMSS over Keccak-256 that leanXMSS replaced. leanXMSS over Keccak-256 has not been measured yet.

```
aggregation, 1,290 leanXMSS signatures
  cycles (VM steps)           : 1,487,899 = 2^20.505
    details                   : XOR 2^18.519 (25.2%)  SET 2^18.157 (19.6%)  MUL 2^18.105 (19.0%)  SHA3 2^17.876 (16.2%)  DEREF 2^17.556 (13.0%)  JUMP 2^16.677 (7.0%)  MEMORY 2^22.98  BYTECODE 2^18.457  TOTAL_COMMITTED 2^26.358
  proof size                  : 331.4 KiB
  proving time                : 1.133 s ± 2.9%      peak memory 10.466 GiB
  per signature               : 1,138.502 signatures/s
  verifying                   : 15.971 ms
```

### leanSPHINCS aggregation

The leanSPHINCS parameters are specified in [leanSPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanSPHINCS.pdf), with a [(ROM) security proof in Lean 4](formal/lean_sphincs/README.md). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --sphincs 850 --log-inv-rate 1 --repeat 3
```

```
aggregation, 850 leanSPHINCS signatures
  cycles (VM steps)           : 1,547,938 = 2^20.562
    details                   : XOR 2^18.704 (27.6%)  SET 2^18.283 (20.6%)  MUL 2^18.025 (17.2%)  SHA3 2^17.8 (14.7%)  DEREF 2^17.624 (13.0%)  JUMP 2^16.679 (6.8%)  MEMORY 2^22.561  BYTECODE 2^18.457  TOTAL_COMMITTED 2^26.358
  proof size                  : 332.7 KiB
  proving time                : 1.174 s ± 2.6%      peak memory 10.31 GiB
  per signature               : 723.809 signatures/s
  verifying                   : 16.149 ms
```

### data availability

```bash
cargo leanvm aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 3,192,288 = 2^21.606
    details                   : XOR 2^20.201 (37.8%)  MUL 2^19.908 (30.8%)  DEREF 2^19.142 (18.1%)  JUMP 2^18.298 (10.1%)  SET 2^15.903 (1.9%)  SHA3 2^15.332 (1.3%)  MEMORY 2^21.939  BYTECODE 2^18.457  TOTAL_COMMITTED 2^26.496
  proof size                  : 341.3 KiB
  proving time                : 0.939 s ± 2.3%      peak memory 9.957 GiB
  blob throughput             : 17.039 blobs/s, 2.13 MiB/s
  verifying                   : 27.377 ms
```

### recursion

```bash
cargo leanvm recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 leanXMSS signatures
  cycles (VM steps)           : 622,501 = 2^19.248
    details                   : MUL 2^17.818 (37.1%)  DEREF 2^17.293 (25.8%)  XOR 2^17.175 (23.8%)  SET 2^15.454 (7.2%)  JUMP 2^14.624 (4.1%)  SHA3 2^13.641 (2.1%)  MEMORY 2^19.906  BYTECODE 2^18.457  TOTAL_COMMITTED 2^24.19
  proof size                  : 222.6 KiB
  proving time                : 0.344 s ± 3.9%      peak memory 11.808 GiB
  verifying                   : 14.703 ms
```

### hashing

```bash
cargo leanvm hash --log-n 17 --repeat 3
```

```
Keccak GKR batch proving, 131,072 permutations, a state committed every 12 rounds
  witness                         :      6.9 ms ± 2.5%    2.7%
  commit                          :     14.8 ms ± 4.2%    5.7%
  layers and openings             :    199.7 ms ± 1.9%   77.0%
  pcs opening                     :     31.8 ms ± 2.6%   12.3%
  ------------------------------------------
  prove TOTAL (witness included)  :    259.5 ms ± 1.7%
  verify                          :     11.2 ms
  throughput                      :        505,176 permutations/s ± 1.7%
  proof size                      :       290.2 KiB  (1562 scalars, 253.6 KiB of Merkle openings)
```

### Fibonacci

```bash
cargo leanvm fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,128,384
    details                   : MUL 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.96  BYTECODE 2^11.352  TOTAL_COMMITTED 2^25.262
  proof size                  : 311.5 KiB
  proving                     : 0.371 s ± 6.0%   5,742,525 cycles/s      peak memory 3.611 GiB
  verifying                   : 19.091 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
