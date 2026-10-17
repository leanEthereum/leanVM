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
    <td align="right"><b>770/s</b></td>
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

* **hash**: BLAKE2s is a placeholder. SHA2, SHA3, BLAKE3 are actively considered.
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
  cycles (VM steps)           : 995,578 = 2^19.925
    details                   : DEREF 2^17.878 (24.2%)  MUL 2^17.689 (21.2%)  SET 2^17.425 (17.7%)  BLAKE2S 2^16.989 (13.1%)  XOR 2^16.979 (13.0%)  JUMP 2^16.722 (10.9%)  MEMORY 2^20.674  BYTECODE 2^17.737  TOTAL_COMMITTED 2^25.801
  proof size                  : 317.4 KiB
  proving time                : 0.545 s ± 1.5%      peak memory 7.385 GiB
  per signature               : 1,651.687 signatures/s
  verifying                   : 3.977 ms
```

### SPHINCS aggregation

The SPHINCS parameters are specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/SPHINCS.pdf), with a [(ROM) security proof in Lean 4](formal/sphincs/README.md). **This is not the definitive parameter set.**

```bash
cargo leanvm aggregate --sphincs 850 --log-inv-rate 1 --repeat 3
```

```
aggregation, 850 SPHINCS signatures
  cycles (VM steps)           : 2,040,659 = 2^20.961
    details                   : SET 2^19.186 (29.2%)  XOR 2^18.694 (20.8%)  MUL 2^18.605 (19.5%)  BLAKE2S 2^17.998 (12.8%)  DEREF 2^17.625 (9.9%)  JUMP 2^17.266 (7.7%)  MEMORY 2^21.475  BYTECODE 2^17.982 TOTAL_COMMITTED 2^26.849
  proof size                  : 331.9 KiB
  proving time                : 1.04 s ± 2.1%      peak memory 14.013 GiB
  per signature               : 817.658 signatures/s
  verifying                   : 5.048 ms
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
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 562,737 = 2^19.102
    details                   : MUL 2^17.823 (41.2%)  DEREF 2^16.964 (22.7%)  XOR 2^16.728 (19.3%)  SET 2^15.77 (9.9%)  JUMP 2^14.486 (4.1%)  BLAKE2S 2^13.932 (2.8%)  MEMORY 2^19.481  BYTECODE 2^17.737  TOTAL_COMMITTED 2^24.086
  proof size                  : 190.2 KiB
  proving time                : 0.272 s ± 5.3%      peak memory 8.388 GiB
  verifying                   : 3.457 ms
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
  (~3373.4 XMSS/s equivalent at 144 compressions/signature)
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

## Clean circuits on binary Spartan

[`crates/binary_spartan`](crates/binary_spartan) proves R1CS over GF(2) exported from [Clean](https://github.com/Verified-zkEVM/clean) circuits, in leanVM's binary field, following BinarySpartan ([ePrint 2026/1656](https://eprint.iacr.org/2026/1656)). A Clean circuit is one block `(A_0, B_0, C_0)` and a proof covers `2^n_log` instances of it (SIMD R1CS, `A = I ⊗ A_0`). It reuses flock and pcs rather than reimplementing them: flock's zerocheck is the outer sumcheck, flock's lincheck (generalized here from `C_0 = I` to a general `C_0` through `LincheckCircuit::c_is_identity`, with BLAKE2s proofs unchanged) the inner one, and the packed witness is committed and opened with ring switching into stacked WHIR. Public bits are bound by strided opening claims on each instance's public words. The lincheck terminal needs `uᵀ(A_0 + αB_0 + α²C_0)w`: the verifier computes it from the sparse block, or checks a SPARK proof of it (`--spark`), which is what a recursive verifier would use. SPARK is adapted to characteristic 2: round polynomials are sent at 0, 1 and ∞, timestamps are `g^t` so an increment is a multiplication, and the memory-checking grand products run on leanVM's GKR. It applies to the block only, so its cost does not grow with the batch. The verifier is [`verifier::binary_spartan`](crates/verifier/src/binary_spartan.rs), on the same zerocheck, lincheck replay, ring switching, GKR and WHIR code that verifies leanVM proofs; the CLI is [`bins/binary-spartan`](bins/binary-spartan) (`cargo binary-spartan prove <circuit.r1cs> <witness.bin> [--spark] [--self-check] [--repeat N]`).

[`examples/clean-binary`](examples/clean-binary) exports one BLAKE2s compression as a Clean circuit over GF(2) (`clean/Gf2/Blake2s.lean`): 15,520 constraints, 16,289 signals (1,024 public: `h`, `m` and the output), 1.1M nonzeros, a 2^14 block like flock's hand-written circuit. Each adder witnesses only its sum bits: with `c_i = x_i ⊕ y_i ⊕ s_i` the carry recurrence becomes the single product `(y_i ⊕ s_i)(x_i ⊕ s_i) = c_{i+1} ⊕ c_i`, so every adder output is materialized at 31 signals and rows. XOR outputs stay linear, except the `b` words of rounds 2, 4 and 6, which are witnessed to bound how far the linear forms grow. Witnessing carries and sums both gives a 2^15 block with far fewer nonzeros (180k), which halves SPARK's cost but doubles the committed witness; flock avoids the choice by walking its XOR DAG instead of storing matrices. The build checks the circuit against Rust's `flock::hash::blake2s_compress` on three vectors.

```bash
cd examples/clean-binary
(cd clean && lake exe cache get)
bash run.sh 8192    # instances (compressions) per proof
```

`run.sh` exports the block R1CS and a batch witness from Lean (`lake exe clean_export r1cs|witness`), then proves and verifies in both modes (`binary-spartan prove --self-check`), confirming rejection of a flipped public bit, mutated proof bytes and, with SPARK, a mutated SPARK scalar. The new gadgets have no Lean soundness proofs; they are checked against the reference vectors and every constraint is checked on the generated witness. No zero-knowledge claim.
