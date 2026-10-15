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
    <td align="right"><b>295/s</b></td>
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

The XMSS parameters are specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf), with a [(ROM) security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/xmss/XmssSecurity/Statement.lean).

```bash
cargo leanvm aggregate --xmss 900 --log-inv-rate 1 --repeat 3
```

```
aggregation, 900 XMSS signatures
  cycles (VM steps)           : 1,049,883 = 2^20.002
    details                   : MUL 2^17.9 (23.3%)  DEREF 2^17.879 (23.0%)  SET 2^17.367 (16.1%)  XOR 2^17.315 (15.5%)  SHA3 2^16.925 (11.9%)  JUMP 2^16.719 (10.3%)  MEMORY 2^22.263  BYTECODE 2^17.963  TOTAL_COMMITTED 2^25.901
  proof size                  : 353.5 KiB
  proving time                : 0.743 s ± 5.4%      peak memory 6.973 GiB
  per signature               : 1,211.978 signatures/s
  verifying                   : 14.897 ms
```

### SPHINCS aggregation

The SPHINCS parameters are specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/SPHINCS.pdf), with a [(ROM) security proof in Lean 4](https://github.com/leanEthereum/leanMultisig/blob/main/formal/sphincs/SphincsSecurity/Statement.lean).

```bash
cargo leanvm aggregate --sphincs 245 --log-inv-rate 1 --repeat 3
```

```
aggregation, 245 SPHINCS signatures
  cycles (VM steps)           : 2,131,611 = 2^21.024
    details                   : XOR 2^18.951 (23.8%)  MUL 2^18.93 (23.4%)  SET 2^18.845 (22.1%)  DEREF 2^18.711 (20.1%)  BLAKE2S 2^16.992 (6.1%)  JUMP 2^16.543 (4.5%)  MEMORY 2^21.46  BYTECODE 2^17.737  TOTAL_COMMITTED 2^26.301
  proof size                  : 299.9 KiB
  proving time                : 0.831 s ± 3.6%      peak memory 9.275 GiB
  per signature               : 294.783 signatures/s
  verifying                   : 5.225 ms
```

### data availability

```bash
cargo leanvm aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 3,188,403 = 2^21.604
    details                   : XOR 2^20.201 (37.8%)  MUL 2^19.908 (30.9%)  DEREF 2^19.141 (18.1%)  JUMP 2^18.299 (10.1%)  SET 2^15.799 (1.8%)  SHA3 2^15.332 (1.3%)  MEMORY 2^21.938  BYTECODE 2^17.963  TOTAL_COMMITTED 2^26.492
  proof size                  : 339.1 KiB
  proving time                : 0.981 s ± 1.7%      peak memory 9.639 GiB
  blob throughput             : 16.306 blobs/s, 2.038 MiB/s
  verifying                   : 26.782 ms
```

### recursion

```bash
cargo leanvm recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 502,045 = 2^18.937
    details                   : MUL 2^17.574 (38.9%)  XOR 2^17.063 (27.3%)  DEREF 2^16.678 (20.9%)  SET 2^14.881 (6.0%)  JUMP 2^14.531 (4.7%)  SHA3 2^13.477 (2.3%)  MEMORY 2^19.691  BYTECODE 2^17.963  TOTAL_COMMITTED 2^23.989
  proof size                  : 237.9 KiB
  proving time                : 0.285 s ± 2.2%      peak memory 8.032 GiB
  verifying                   : 13.241 ms
```

### hashing

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 KECCAK_N_LOG=17 cargo bench -p keccak_gkr --bench hash_batch
```

```
Keccak GKR batch proving, 131,072 permutations, a state committed every 12 rounds
  witness                         :     12.0 ms ± 28.3%    3.7%
  commit                          :     18.9 ms ± 28.3%    5.8%
  layers and openings             :    252.7 ms ± 1.2%   77.9%
  pcs opening                     :     33.6 ms ± 6.9%   10.4%
  ------------------------------------------
  prove TOTAL (witness included)  :    324.3 ms ± 4.0%
  verify                          :     10.8 ms
  throughput                      :        404,137 permutations/s ± 4.0%
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
  proving                     : 0.382 s ± 4.5%   5,564,661 cycles/s      peak memory 3.616 GiB
  verifying                   : 19.01 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
