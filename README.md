<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">Minimal hash-based zkVM, for a Post-Quantum Ethereum.</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="./python-verifier/verifier.py"><img src="https://img.shields.io/badge/verifier-python-yellow?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

<table align="center">
  <tr>
    <td><a href="#xmss-aggregation">XMSS aggregation</a></td>
    <td align="right"><b>1,200 XMSS/s</b></td>
  </tr>
  <tr>
    <td><a href="#sphincs-aggregation">SPHINCS aggregation</a></td>
    <td align="right"><b>280 SPHINCS/s</b></td>
  </tr>
  <tr>
    <td><a href="#recursion">Recursion 2 → 1</a></td>
    <td align="right"><b>0.29 s</b></td>
  </tr>
  <tr>
    <td><a href="#data-availability">Data availability</a></td>
    <td align="right"><b>16 blobs/s</b></td>
  </tr>
</table>

Warning: not (yet) production ready.

leanVM was originally designed over the [KoalaBear prime](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458), still available in the [koalabear](https://github.com/leanEthereum/leanVM/tree/koalabear) branch; it is now using binary fields and BLAKE2s.

# Benchmarks

Machine: Mac M4 Max

### XMSS aggregation

The XMSS parameters are specified in [XMSS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/XMSS.pdf).

```bash
cargo run --release -- aggregate --xmss 900 --log-inv-rate 1 --repeat 3
```

```
aggregation, 900 XMSS signatures
  cycles (VM steps)           : 1,573,849 = 2^20.586
    details                   : DEREF 2^18.947 (32.1%)  SET 2^18.528 (24.0%)  MUL 2^18.259 (19.9%)  BLAKE2S 2^16.989 (8.3%) XOR 2^16.979 (8.2%)  JUMP 2^16.839 (7.4%)  MEMORY 2^21.305  TOTAL_COMMITTED 2^26.195
  proof size                  : 295.4 KiB
  proving time                : 0.749 s ± 2.1%      peak memory 8.769 GiB
  per signature               : 1,201.795 signatures/s
  verifying                   : 3.799 ms
```

### SPHINCS aggregation

The SPHINCS parameters are specified in [SPHINCS.pdf](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/SPHINCS.pdf).

```bash
cargo run --release -- aggregate --sphincs 245 --log-inv-rate 1 --repeat 3
```

```
aggregation, 245 SPHINCS signatures
  cycles (VM steps)           : 2,132,425 = 2^21.024
    details                   : XOR 2^18.951 (23.8%)  MUL 2^18.93 (23.4%)  SET 2^18.847 (22.1%)  DEREF 2^18.711 (20.1%)  BLAKE2S 2^16.992 (6.1%)  JUMP 2^16.543 (4.5%)  MEMORY 2^21.564  TOTAL_COMMITTED 2^26.301
  proof size                  : 300.1 KiB
  proving time                : 0.861 s ± 1.5%      peak memory 9.348 GiB
  per signature               : 284.603 signatures/s
  verifying                   : 3.841 ms
```

### Recursion


```bash
cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
```

```
recursion 2→1, over leaves of 900 XMSS signatures
  cycles (VM steps)           : 570,113 = 2^19.121
    details                   : MUL 2^17.838 (41.1%)  DEREF 2^16.988 (22.8%)  XOR 2^16.747 (19.3%)  SET 2^15.79 (9.9%)  JUMP 2^14.488 (4.0%)  BLAKE2S 2^13.978 (2.8%)  MEMORY 2^19.507  TOTAL_COMMITTED 2^24.086
  proof size                  : 191.3 KiB
  proving time                : 0.287 s ± 15.9%      peak memory 10.124 GiB
  verifying                   : 4.121 ms
```

### Data Availability


```bash
cargo run --release -- aggregate --blobs 16 --log-inv-rate 1 --repeat 3
```

```
aggregation, 16 blobs
  cycles (VM steps)           : 2,989,506 = 2^21.511
    details                   : MUL 2^19.899 (32.7%)  XOR 2^19.809 (30.7%)  DEREF 2^19.138 (19.3%)  JUMP 2^18.299 (10.8%)  SET 2^16.787 (3.8%)  BLAKE2S 2^16.295 (2.7%)  MEMORY 2^21.696  TOTAL_COMMITTED 2^26.695
  proof size                  : 322.4 KiB
  proving time                : 0.998 s ± 0.9%      peak memory 12.646 GiB
  blob throughput             : 16.032 blobs/s, 2.004 MiB/s
  verifying                   : 6.659 ms
```

### Fibonacci


```bash
cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (in the exponent, i.e. modulo 2^64 - 1), N = 2,000,000
  cycles (VM steps)           : 2,127,880
    details                   : MUL 2^20.944 (98.9%)  SET 2^13.288 (0.5%)  DEREF 2^12.967 (0.4%)  JUMP 2^10.968 (0.1%)  XOR2^10.966 (0.1%)  MEMORY 2^20.96  TOTAL_COMMITTED 2^25.26
  proof size                  : 285.4 KiB
  proving                     : 0.391 s ± 1.1%   5,442,734 cycles/s      peak memory 5.203 GiB
  verifying                   : 2.092 ms
```

### Batch proving BLAKE2s

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo test --release --package flock --test batch_proving_hashes -- hash_batch_prove_verify --exact --nocapture --include-ignored
```

```
Flock BLAKE2s batch proving, 262,144 compressions (2^18 slots)
  setup (preprocessing, excluded) :      0.0 ms
  witness-gen                     :     64.6 ms ± 7.8%   10.6%
  commit                          :    101.2 ms ± 0.4%   16.6%
  zerocheck                       :    238.3 ms ± 3.9%   39.0%
  lincheck                        :     20.3 ms ± 12.2%   3.3%
  pcs opening                     :    186.0 ms ± 2.9%   30.5%
  other                           :      0.0 ms           0.0%
  ------------------------------------------
  prove TOTAL (witness excluded)  :    545.8 ms ± 1.1%   89.4%
  verify                          :      1.9 ms
  throughput                      :        480,319 compressions/s ± 1.1%
  (~3289.9 XMSS/s equivalent at 146 compressions/signature)
```

## Security

- 128-bit (LDR Johnson, no proximity gaps conjecture)

## Snark machinery

- Binary field of 192 bits (tower of degree 3 over the 64 bit field)
- PCS: [WHIR](https://eprint.iacr.org/2024/1586) (aka [Ligerito](https://eprint.iacr.org/2025/1187))
- Proving BLAKE2s by [Flock](https://github.com/succinctlabs/flock/tree/main)
- RingSwitching, M3 arithmetisation, (and more) by [Binius](https://github.com/IrreducibleOSS/binius) / [Binius64](https://github.com/binius-zk/binius64) (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
