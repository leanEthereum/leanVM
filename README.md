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
    <td align="right"><b>1.35K/s</b></td>
  </tr>
  <tr>
    <td><a href="#leansphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>850/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>2 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>0.29s</b></td>
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

* **hash**: BLAKE2s is a placeholder. SHA2, SHA3, BLAKE3 are actively considered.
* **ISA**: A migration from leanISA to RISC-V (rv64im) is planned.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM)

**note**: The Metal GPU was not used.

### leanXMSS aggregation

The leanXMSS parameters are specified in [leanXMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanXMSS.pdf), with a [(ROM) security proof in Lean 4](formal/lean_xmss/LeanXmss/Statement.lean). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --xmss 1290 --log-inv-rate 1 --repeat 3
```

```
aggregation, 1,290 leanXMSS signatures
  cycles (VM steps)           : 1,336,043 = 2^20.35
    details                   : SET 2^18.207 (22.7%)  BLAKE2S 2^17.992 (19.5%)  MUL 2^17.943 (18.9%)  XOR2^17.866 (17.9%)  DEREF 2^17.437 (13.3%)  JUMP 2^16.672 (7.8%)  MEMORY 2^21.125  BYTECODE 2^17.961  TOTAL_COMMITTED 2^26.672
  proof size                  : 318.4 KiB
  proving time                : 0.947 s ± 0.8%      peak memory 15.46 GiB
  per signature               : 1,362.468 signatures/s
  verifying                   : 5.387 ms
```

### leanSPHINCS aggregation

The leanSPHINCS parameters are specified in [leanSPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanSPHINCS.pdf), with a [(ROM) security proof in Lean 4](formal/lean_sphincs/README.md). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --sphincs 850 --log-inv-rate 1 --repeat 3
```

```
aggregation, 850 leanSPHINCS signatures
  cycles (VM steps)           : 1,870,199 = 2^20.835
    details                   : SET 2^18.992 (27.9%)  XOR 2^18.696 (22.7%)  MUL 2^18.208 (16.2%)  BLAKE2S2^17.998 (14.0%)  DEREF 2^17.879 (12.9%)  JUMP 2^16.855 (6.3%)  MEMORY 2^21.403  BYTECODE 2^17.961  TOTAL_COMMITTED 2^26.775
  proof size                  : 325.8 KiB
  proving time                : 1 s ± 3.9%      peak memory 16.102 GiB
  per signature               : 850.082 signatures/s
  verifying                   : 5.113 ms
```

### data availability

```bash
cargo leanvm aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 2,989,506 = 2^21.511
    details                   : MUL 2^19.899 (32.7%)  XOR 2^19.809 (30.7%)  DEREF 2^19.138 (19.3%)  JUMP 2^18.299 (10.8%)  SET 2^16.787 (3.8%)  BLAKE2S 2^16.295 (2.7%)  MEMORY 2^21.695  BYTECODE 2^17.737 TOTAL_COMMITTED 2^26.695
  proof size                  : 324.0 KiB
  proving time                : 0.986 s ± 11.1%      peak memory 12.534 GiB
  blob throughput             : 16.235 blobs/s, 2.029 MiB/s
  verifying                   : 6.573 ms
```

### recursion

```bash
cargo leanvm recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 leanXMSS signatures
  cycles (VM steps)           : 598,600 = 2^19.191
    details                   : MUL 2^17.876 (40.2%)  DEREF 2^17.089 (23.3%)  XOR 2^16.799 (19.0%)  SET 2^15.955 (10.6%)  JUMP 2^14.505 (3.9%)  BLAKE2S 2^14.127 (3.0%)  MEMORY 2^19.555  BYTECODE 2^17.965  TOTAL_COMMITTED 2^24.533
  proof size                  : 200.5 KiB
  proving time                : 0.293 s      peak memory 14.69 GiB
  verifying                   : 6.2 ms
```

### hashing

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo bench -p flock --bench hash_batch
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     34.8 ms ± 26.8%   6.1%
  commit                          :    102.2 ms ± 1.3%   17.8%
  zerocheck                       :    244.9 ms ± 7.5%   42.6%
  lincheck                        :     20.2 ms ± 3.4%    3.5%
  pcs opening                     :    172.3 ms ± 1.3%   30.0%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    539.7 ms ± 3.3%   93.9%
  verify                          :      2.0 ms
  throughput                      :        485,765 compressions/s ± 3.3%
  (~2416.7 leanXMSS/s equivalent at 201 compressions/signature)
```

### Fibonacci

```bash
cargo leanvm fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,880
    details                   : MUL 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR 2^10.966 (0.1%)  MEMORY 2^20.96  BYTECODE 2^11.352  TOTAL_COMMITTED 2^25.26
  proof size                  : 286.0 KiB
  proving                     : 0.344 s ± 4.6%   6,181,087 cycles/s      peak memory 5.199 GiB
  verifying                   : 2.218 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
