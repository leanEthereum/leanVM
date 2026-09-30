<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">minimal hash-based zkVM</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
  <a href="./python-verifier/verifier.py"><img src="https://img.shields.io/badge/verifier-python-yellow?style=for-the-badge&logo=python&logoColor=white" alt="Python verifier"></a>
</p>

<table align="center">
  <tr>
    <td><a href="#hashing">hash compressions</a></td>
    <td align="right"><b>480K/s</b></td>
  </tr>
  <tr>
    <td><a href="#fibonacci">RISC-V cycles</a></td>
    <td align="right"><b>1.6M/s</b></td>
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
* **ISA**: leanVM proves RISC-V (rv64im) plus one custom instruction, the BLAKE2s compression. A run is one proof; continuations, for runs whose witness exceeds one commitment, are planned.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## programs

A program is a guest: a `no_std` Rust program built for `riscv64im-unknown-none-elf` against the SDK in [`sdk`](./sdk/src/lib.rs). Its `main` does all its I/O: `leanvm_guest::read::<T>()` takes the next value from the advice (a region of memory the prover fills, which the statement says nothing about), in place with no copy or decoding, and `leanvm_guest::commit(&value)` makes a value public. The run's output is the BLAKE2s digest of everything committed, in order, which a verifier recomputes from the public values. Everything else in a guest is ordinary Rust. The SDK's linker script fixes the memory map. Each program lives in its own folder, `programs/<name>/guest`, a standalone package that `cargo build --release` builds there (a nightly toolchain, for `-Zbuild-std`); a program whose advice takes work to make also has a host, `programs/<name>/host`, its code off the VM. `programs/build.sh` builds every guest and refreshes its checked-in `programs/<name>/<name>.elf`; then prove and verify a run:

```bash
cargo leanvm guest programs/preimage/preimage.elf --advice 5,0x6f6c6c6568
```

The statement a proof makes is the program (an ELF file) and its four output words, the digest of what it committed; everything a guest reads from its advice it has to check itself, which is what makes a proof a proof of knowledge (`preimage` commits the digest of a message only the prover has).

## benchmarks

**machine**: M4 Max MacBook Pro (12 performance cores, 4 efficiency cores, 48GB RAM)

**note**: The Metal GPU was not used.

### Fibonacci

```bash
cargo leanvm fibonacci --n 2000000 --log-inv-rate 1 --repeat 3
```

```
Fibonacci (modulo 2^64), N = 2,000,000
  cycles (VM steps)           : 2,097,208
    details                   : ALU 2^20.934 (100.0%)  TOTAL_COMMITTED 2^26.395
  proof size                  : 337.5 KiB
  proving                     : 1.281 s ± 1.2%   1,636,564 cycles/s      peak memory 11.6 GiB
  verifying                   : 6.186 ms
```

### BLAKE2s in plain Rust

The `blake2s` guest is the hash function written in ordinary Rust, compiled by `rustc` for `riscv64im-unknown-none-elf` (`programs/blake2s`): 10,000 bytes, 157 compressions, a mix of arithmetic, shifts, loads and stores.

```bash
cargo leanvm guest programs/blake2s/blake2s.elf --advice 10000 --repeat 3 --cooldown 2
```

```
programs/blake2s/blake2s.elf
  advice                      : 1 words
  output                      : [8f9fc3d71d84c0cc, 515c979fa65679e8, 9ffc0e1e022efcc7, cef54d0c06836e56]
  cycles (VM steps)           : 1,015,824
    details                   : ALU 2^18.47 (55.2%)  SHIFT 2^17.238 (23.5%)  LOAD 2^16.356 (12.8%)  STORE 2^15.139 (5.5%)  MUL 2^13.288 (1.5%)  MULH 2^13.288 (1.5%)  TOTAL_COMMITTED 2^25.435
  proof size                  : 328.6 KiB
  proving                     : 0.698 s ± 1.2%   1,454,472 cycles/s      peak memory 5.18 GiB
  verifying                   : 7.185 ms
```

### BLAKE2s through the precompile

The `hash` guest hashes 50,000 bytes through the compression instruction, 782 compressions; most of its cycles generate the message.

```bash
cargo leanvm guest programs/hash/hash.elf --advice 50000 --repeat 3
```

```
programs/hash/hash.elf
  cycles (VM steps)           : 869,384
    details                   : ALU 2^18.641 (59.8%)  SHIFT 2^16.61 (14.6%)  STORE 2^15.915 (9.0%)  MULH 2^15.61 (7.3%)  MUL 2^15.61 (7.3%)  LOAD 2^13.618 (1.8%)  HASH 2^9.611 (0.1%)  TOTAL_COMMITTED 2^25.49
  proof size                  : 331.0 KiB
  proving                     : 0.816 s ± 0.9%   1,065,522 cycles/s      peak memory 5.238 GiB
  verifying                   : 7.796 ms
```

### leanXMSS, leanSPHINCS and leanDA

Three programs check what an Ethereum node would: leanXMSS signatures, leanSPHINCS signatures, and leanDA blobs (`programs/leanxmss`, `programs/leansphincs`, `programs/leanda`).

Each guest is a `no_std` library, byte-compatible with the schemes' reference implementations, plus the `main` that runs it. Each host runs the same library natively to build the inputs and the expected output.

```bash
cargo leanvm leanxmss --n 400 --repeat 3
cargo leanvm leansphincs --n 104 --repeat 3
cargo leanvm leanda --blobs 1 --repeat 3
```

The report gives the RISC-V cycles per signature or per blob, the rows per table and the committed witness, then the proving and verifying times.

These are the most one proof holds: continuations are not implemented.

To get the cost of all three without proving, exact and the same on every machine:

```bash
cargo leanvm bench --cycles-only --markdown
```

It prints a markdown table of the RISC-V cycles, per item and in all, and the committed witness words, for these three and the other benchmarks. CI adds it to each run's summary, and tracks the same counts on [Bencher](https://bencher.dev/perf/leanvm), failing a PR that raises any of them; without `--markdown` it prints them as Bencher's JSON, and without `--cycles-only` it proves each program too.

### hashing

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo bench -p flock --bench hash_batch
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
```

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
