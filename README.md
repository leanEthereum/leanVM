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
    <td align="right"><b>1700/s</b></td>
  </tr>
  <tr>
    <td><a href="#leansphincs-aggregation">leanSPHINCS aggregation</a></td>
    <td align="right"><b>540/s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">leanDA commitment</a></td>
    <td align="right"><b>3,1 MiB/s</b></td>
  </tr>
</table>
<table align="center">
  <tr>
    <td><a href="#recursion">2-to-1 recursion</a></td>
    <td align="right"><b>150 ms</b></td>
  </tr>
  <tr>
    <td><a href="#hashing">proving KECCAK</a></td>
    <td align="right"><b>800K/s</b></td>
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
cargo leanvm aggregate --xmss 1400 --log-inv-rate 2 --repeat 3
```

```
aggregation, 1,400 leanXMSS signatures
  cycles (VM steps)           : 1,150,164 = 2^20.133
    details                   : XOR 2^17.999 (22.8%)  KECCAK 2^17.994 (22.7%)  MUL 2^17.855 (20.6%)  SET 2^17.386 (14.9%)  DEREF 2^17.3 (14.0%)  JUMP 2^15.81 (5.0%)  MEMORY 2^21.083  BYTECODE 2^18.961  TOTAL_COMMITTED 2^25.589
  proof size                  : 207.7 KiB
  proving time                : 0.821 s ± 2.3%      peak memory 5.054 GiB
  per signature               : 1,704.896 signatures/s
  verifying                   : 4.996 ms
```

### leanSPHINCS aggregation

The leanSPHINCS parameters are specified in [leanSPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanSPHINCS.pdf), with a [(ROM) security proof in Lean 4](formal/lean_sphincs/README.md). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --sphincs 500 --log-inv-rate 1 --repeat 3
```

```
aggregation, 500 leanSPHINCS signatures
  cycles (VM steps)           : 2,759,754 = 2^21.396
    details                   : XOR 2^19.755 (32.1%)  MUL 2^19.435 (25.7%)  SET 2^19.396 (25.0%)  KECCAK 2^17.976 (9.3%)  DEREF 2^17.195 (5.4%)  JUMP 2^16.058 (2.5%)  MEMORY 2^22.044  BYTECODE 2^18.961  TOTAL_COMMITTED 2^26.422
  proof size                  : 293.5 KiB
  proving time                : 0.93 s ± 2.5%      peak memory 4.582 GiB
  per signature               : 537.824 signatures/s
  verifying                   : 5.783 ms
```

### data availability

```bash
cargo leanvm aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 3,023,242 = 2^21.528
    details                   : XOR 2^20.098 (37.1%)  MUL 2^19.811 (30.4%)  DEREF 2^19.206 (20.0%)  JUMP 2^18.052 (9.0%)  SET 2^16.093 (2.3%)  KECCAK 2^15.088 (1.2%)  MEMORY 2^21.8  BYTECODE 2^18.961  TOTAL_COMMITTED 2^26.306
  proof size                  : 287.7 KiB
  proving time                : 0.631 s ± 2.7%      peak memory 4.276 GiB
  blob throughput             : 25.373 blobs/s, 3.172 MiB/s
  verifying                   : 6.166 ms
```

### recursion

```bash
cargo leanvm recursion --n 2 --xmss-per-leaf 1400 --leaf-log-inv-rate 2 --log-inv-rate 1 --repeat 3
```

```
recursion 2→1, over leaves of 1,400 leanXMSS signatures, leaf rate = 1/4, recursion rate = 1/2
  cycles (VM steps)           : 441,348 = 2^18.752
    details                   : MUL 2^17.227 (34.7%)  XOR 2^16.761 (25.2%)  DEREF 2^16.663 (23.5%)  SET 2^15.478 (10.3%)  JUMP 2^13.811 (3.3%)  KECCAK 2^13.686 (3.0%)  MEMORY 2^19.394  BYTECODE 2^18.961  TOTAL_COMMITTED 2^23.611
  proof size                  : 269.5 KiB
  proving time                : 0.159 s ± 6.9%      peak memory 0.912 GiB
  verifying                   : 7.908 ms
```

### Proving KECCAK

```bash
cargo leanvm hash --log-n 20 --repeat 3
```

```
Keccak GKR batch proving, 1,048,576 permutations, a state committed every 12 rounds
  witness                         :     67.7 ms ± 1.7%    5.2%
  commit                          :    119.5 ms ± 5.0%    9.2%
  output claim                    :     12.3 ms ± 1.2%    0.9%
  layers and openings             :    950.2 ms ± 1.2%   73.1%
  pcs opening                     :    150.7 ms ± 4.8%   11.6%
  ------------------------------------------
  prove TOTAL (witness included)  :   1300.4 ms ± 1.5%
  verify                          :      3.0 ms
  throughput                      :        806,326 permutations/s ± 1.5%
  proof size                      :       281.8 KiB  (1770 scalars, 254.1 KiB of Merkle openings)
```

### Fibonacci

```bash
cargo leanvm fibonacci --n 4000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 4,000,000
  cycles (VM steps)           : 4,080,016
    details                   : MUL 2^21.944 (98.9%)  SET 2^14.288 (0.5%)  DEREF 2^13.967 (0.4%)  JUMP 2^11.967 (0.1%)  XOR 2^11.966 (0.1%)  MEMORY 2^21.959  BYTECODE 2^10.017  TOTAL_COMMITTED 2^26.013
  proof size                  : 274.0 KiB
  proving                     : 0.501 s ± 4.2%   8,136,972 cycles/s      peak memory 3.54 GiB
  verifying                   : 4.104 ms
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Hashcaster 2](https://github.com/levs57/hashcaster2) proving Keccak via GKR and RMFE
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
