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
    <td><a href="#xmss-aggregation">leanXMSS aggregation</a></td>
    <td align="right"><b>1.65K/s</b></td>
  </tr>
  <tr>
    <td><a href="#sphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>626/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>2 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>0.27s</b></td>
  </tr>
  <tr>
    <td><a href="#hashing">hash compressions</a></td>
    <td align="right"><b>480K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">cheap cycles</a></td>
    <td align="right"><b>6,2M/s</b></td>
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

* **hash**: SHA3 is a placeholder: SHA2, BLAKE2s and BLAKE3 are actively considered.
* **ISA**: A migration from leanISA to RISC-V (rv64im) is planned.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM)

**note**: The Metal GPU was not used.

### XMSS aggregation

The XMSS parameters are specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf), with a [(ROM) security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/xmss/XmssSecurity/Statement.lean). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --xmss 900 --log-inv-rate 1 --repeat 3
```

```
aggregation, 900 XMSS signatures
  cycles (VM steps)           : 1,143,237 = 2^20.125
    details                   : DEREF 2^18.079 (24.2%)  SET 2^17.831 (20.4%)  MUL 2^17.771 (19.6%)  XOR 2^17.315 (14.3%) SHA3 2^16.925 (10.9%)  JUMP 2^16.897 (10.7%)  MEMORY 2^21.885  BYTECODE 2^18.453  TOTAL_COMMITTED 2^25.577
  proof size                  : 331.4 KiB
  proving time                : 0.628 s ± 2.3%      peak memory 6.084 GiB
  per signature               : 1,433.505 signatures/s
  verifying                   : 15.352 ms
```

### SPHINCS aggregation

The SPHINCS parameters are specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/SPHINCS.pdf), with a [(ROM) security proof in Lean 4](formal/sphincs/README.md). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --sphincs 850 --log-inv-rate 1 --repeat 3
```

```
aggregation, 850 SPHINCS signatures
  cycles (VM steps)           : 1,781,990 = 2^20.765
    details                   : XOR 2^18.713 (24.1%)  SET 2^18.696 (23.8%)  MUL 2^18.569 (21.8%)  SHA3 2^17.821 (13.0%)JUMP 2^17.267 (8.9%)  DEREF 2^17.189 (8.4%)  MEMORY 2^22.604  BYTECODE 2^18.453  TOTAL_COMMITTED 2^26.388
  proof size                  : 333.9 KiB
  proving time                : 1.198 s ± 6.0%      peak memory 10.787 GiB
  per signature               : 709.623 signatures/s
  verifying                   : 16.091 ms
```

### data availability

```bash
cargo leanvm aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 3,188,912 = 2^21.605
    details                   : XOR 2^20.201 (37.8%)  MUL 2^19.908 (30.9%)  DEREF 2^19.142 (18.1%)  JUMP 2^18.299 (10.1%)  SET 2^15.805 (1.8%)  SHA3 2^15.332 (1.3%)  MEMORY 2^21.938  BYTECODE 2^18.453  TOTAL_COMMITTED 2^26.496
  proof size                  : 339.9 KiB
  proving time                : 0.945 s ± 1.9%      peak memory 10.002 GiB
  blob throughput             : 16.937 blobs/s, 2.117 MiB/s
  verifying                   : 27.696 ms
```

### recursion

```bash
cargo leanvm recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 498,888 = 2^18.928
    details                   : MUL 2^17.563 (38.8%)  XOR 2^17.055 (27.3%)  DEREF 2^16.664 (20.8%)  SET 2^14.885 (6.1%)JUMP 2^14.522 (4.7%)  SHA3 2^13.473 (2.3%)  MEMORY 2^19.688  BYTECODE 2^18.453  TOTAL_COMMITTED 2^24.011
  proof size                  : 217.9 KiB
  proving time                : 0.326 s ± 1.7%      peak memory 6.84 GiB
  verifying                   : 14.478 ms
```

### hashing

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 KECCAK_N_LOG=17 cargo bench -p keccak_gkr --bench hash_batch
```

```
Keccak GKR batch proving, 131,072 permutations, a state committed every 12 rounds
  witness                         :     11.1 ms ± 29.1%    4.3%
  commit                          :     18.0 ms ± 11.7%    6.9%
  layers and openings             :    190.0 ms ± 1.2%   73.0%
  pcs opening                     :     33.9 ms ± 6.2%   13.0%
  ------------------------------------------
  prove TOTAL (witness included)  :    260.4 ms ± 2.5%
  verify                          :     10.9 ms
  throughput                      :        503,422 permutations/s ± 2.5%
  proof size                      :       291.2 KiB  (1562 scalars, 254.6 KiB of Merkle openings)
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
