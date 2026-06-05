<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./misc/images/banner.svg">
</p>

Minimal hash-based zkVM, for a Post-Quantum Ethereum.

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/spec-latest/minimal_zkVM.pdf"><img src="https://img.shields.io/badge/Documentation-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="crates/lean_compiler/zkDSL.md"><img src="https://img.shields.io/badge/zkDSL%20reference-7c3aed?style=for-the-badge&logo=markdown&logoColor=white" alt="zkDSL reference"></a>
  <a href="crates/lean_prover/python-verifier/verifier.py"><img src="https://img.shields.io/badge/Python%20verifier-d97706?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

## Proving System


- multilinear with [WHIR](https://eprint.iacr.org/2024/1586.pdf), allowing polynomial stacking (reducing proof size)
- [SuperSpartan](https://eprint.iacr.org/2023/552.pdf), with [AIR-specific optimizations](https://solvable.group/posts/super-air/#fnref:1)
- [Logup](https://eprint.iacr.org/2023/1284.pdf), with a system of buses similar to [OpenVM](https://openvm.dev/whitepaper.pdf)

The VM design is inspired by the famous [Cairo paper](https://eprint.iacr.org/2021/1063.pdf).


## Benchmarks

Machine: M4 Max 48GB (CPU only)

*Expect incoming perf improvements.*

### XMSS aggregation

```bash
cargo run --release -- xmss --n-signatures 1550 --log-inv-rate 1
```

| WHIR rate | Proven Regime         | Proximity Gaps Conjecture |
| --------- | --------------------- | ------------------------- |
| 1/2       | 1453 XMSS/s - 344 KiB | 1500 XMSS/s - 178 KiB     |
| 1/4       | 1058 XMSS/s - 229 KiB | 1065 XMSS/s - 127 KiB     |


(Proving throughput - proof size)

### Recursion

Aggregating together n previously aggregated signatures, each containing 700 XMSS.


```bash
cargo run --release -- recursion --n 2 --log-inv-rate 2
```


| n   | WHIR rate | Proven Regime               | Proximity Gaps Conjecture   |
| --- | --------- | --------------------------- | --------------------------- |
| 1   | 1/2       | 0.22s = 1 x 0.22s - 285 KiB | 0.15s = 1 x 0.15s - 143 KiB |
| 1   | 1/4       | 0.24s = 1 x 0.24s - 189 KiB | 0.18s = 1 x 0.18s - 98 KiB  |
| 2   | 1/2       | 0.52s = 2 x 0.26s - 282 KiB | 0.33s = 2 x 0.16s - 159 KiB |
| 2   | 1/4       | 0.45s = 2 x 0.23s - 198 KiB | 0.33s = 2 x 0.16s - 102 KiB |
| 3   | 1/2       | 0.7s = 3 x 0.23s - 317 KiB  | 0.47s = 3 x 0.16s - 151 KiB |
| 3   | 1/4       | 0.67s = 3 x 0.22s - 191 KiB | 0.43s = 3 x 0.14s - 111 KiB |
| 4   | 1/2       | 1.02s = 4 x 0.26s - 309 KiB | 0.61s = 4 x 0.15s - 168 KiB |
| 4   | 1/4       | 0.85s = 4 x 0.21s - 208 KiB | 0.62s = 4 x 0.15s - 109 KiB |


(time for n->1 recursive aggregation - proof size)

### Bonus: unbounded recursive aggregation

```bash
cargo run --release -- fancy-aggregation
```

![Recursive aggregation](./misc/images/fancy-aggregation.png)

(Proven regime)

## Security

### snark

≈ 124 bits of provable security, given by Johnson bound + degree 5 extension of koala-bear. (128 bits requires bigger hash digests (8 koalabears ≈ 248 bits) -> TODO). In the benchmarks, we also display performance with conjectured security, even though leanVM targets the proven regime by default.

### XMSS

Currently, we use an [XMSS](crates/xmss/xmss.md) with hash digests of 4 field elements ≈ 124 bits. Tweaks and public parameters ensure domain separation. An analysis in the ROM (resp. QROM), inspired by the section 3.1 of [Tight adaptive reprogramming in the QROM](https://arxiv.org/pdf/2010.15103) would lead to ≈ 124 (resp. 62) bits of classical (resp. quantum) security. Going to 128 / 64 bits of classical / quantum security, i.e. NIST level 1 (in the ROM/QROM), is an ongoing effort. It requires either:
- hash digests of 5 field elements (drawback: we need to double the hash chain length from 8 to 16 if we want to stay below one IPv6 MTU = 1280 bytes)
- a new prime, close to 32 bits (typically p = 125.2^25 + 1) or 64 bits ([goldilocks](https://2π.com/22/goldilocks/))

It's important to mention that a security analysis in the ROM / QROM is not the most conservative. In particular, [eprint 2025/055](https://eprint.iacr.org/2025/055.pdf)'s security proof holds in the standard model (at the cost of bigger hash digests): the implementation is available in the [leanSig](https://github.com/leanEthereum/leanSig) repository. A compatible version of leanVM can be found in the [devnet4](https://github.com/leanEthereum/leanVM/tree/devnet4) branch.

## Credits

- [Plonky3](https://github.com/Plonky3/Plonky3) for its various performant crates
- [whir-p3](https://github.com/tcoratger/whir-p3): a Plonky3-compatible WHIR implementation
- [Whirlaway](https://github.com/TomWambsgans/Whirlaway): Multilinear snark for AIR + minimal zkVM


