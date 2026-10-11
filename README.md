<h1 align="center">leanVM</h1>

<p align="center">
  <img src="./doc/images/banner.svg" alt="leanVM">
</p>

<h3 align="center">minimal hash-based zkVM</h3>

<p align="center">
  <a href="https://github.com/leanEthereum/leanVM/releases/download/doc-latest/leanVM.pdf"><img src="https://img.shields.io/badge/Documentation-PDF-blue?style=for-the-badge&logo=data:image/svg%2bxml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCIgZmlsbD0id2hpdGUiPjxwYXRoIGQ9Ik0xNCAySDZjLTEuMSAwLTIgLjktMiAydjE2YzAgMS4xLjg5IDIgMS45OSAySDE4YzEuMSAwIDItLjkgMi0yVjhsLTYtNnpNOC41IDE0LjVoMS4yNWMuOTcgMCAxLjc1LS43OCAxLjc1LTEuNzVTMTAuNzIgMTEgOS43NSAxMUg3LjV2Nmgxdi0yLjV6bTAtMVYxMmgxLjI1Yy40MSAwIC43NS4zNC43NS43NXMtLjM0Ljc1LS43NS43NUg4LjV6bTUuNSAzLjVoMnYtMWgtMnYtMWgydi0xaC0ydi0xLjVjMC0uMjguMjItLjUuNS0uNUgxN3YtMWgtMmMtLjgzIDAtMS41LjY3LTEuNSAxLjVWMTd6TTEzIDlWMy41TDE4LjUgOUgxM3oiLz48L3N2Zz4=" alt="Documentation"></a>
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

The production wrapping and carry adders and the complete RV shift circuit are authored and proved in [Clean](./verification/circuits/README.md), then exported as checked-in Rust gates. Real instruction and BLAKE2s circuits consume the adder family; real RV shifts consume the complete shift artifact. The proofs cover arbitrary-witness Boolean constraint soundness and honest completeness, with the shift flag domain made explicit. The Rust interpretation and the separate cryptographic composition retain the trust boundaries documented there.

## work in progress

Expect leanVM to change significantly:

* **hash**: BLAKE2s is a placeholder. SHA2, SHA3, BLAKE3 are actively considered.
* **ISA**: leanVM proves RISC-V (rv64im) plus one custom instruction, the BLAKE2s compression. A run is one proof; continuations, for runs whose witness exceeds one commitment, are planned.
* **zk**: Support for zero-knowledge is planned.

**note**: Prior to binary fields leanVM used [KoalaBear](https://crates.io/crates/p3-koala-bear) and [Poseidon](https://eprint.iacr.org/2019/458). The historical design is in [this branch](https://github.com/leanEthereum/leanVM/tree/koalabear).

## programs

A program is a guest: a `no_std` Rust program built for `riscv64im-unknown-none-elf` against the SDK in [`sdk`](./sdk/src/lib.rs). Its `main` does all its I/O: `leanvm_guest::read::<T>()` takes the next value from the advice (a region of memory the prover fills, which the statement says nothing about), in place with no copy or decoding, and `leanvm_guest::commit(&value)` makes a value public. The run's output is the BLAKE2s digest of everything committed, in order, which a verifier recomputes from the public values. Everything else in a guest is ordinary Rust. The SDK's linker script fixes the memory map. Each program lives in its own folder, `programs/<name>/guest`, a standalone package that `cargo build --release` builds there (a dated nightly toolchain, pinned by its `rust-toolchain.toml`, for `-Zbuild-std`); a program whose advice takes work to make also has a host, `programs/<name>/host`, its code off the VM. `programs/build.sh` builds every guest and refreshes its checked-in `programs/<name>/<name>.elf`; then prove and verify a run:

```bash
cargo leanvm guest programs/preimage/preimage.elf --advice 5,0x6f6c6c6568
```

The statement a proof makes is the program (an ELF file) and its four output words, the digest of what it committed; everything a guest reads from its advice it has to check itself, which is what makes a proof a proof of knowledge (`preimage` commits the digest of a message only the prover has).

## benchmarks

Desktop timing benchmarks now use exactly 16 total pool threads, dispatcher included, with no extra efficiency workers. The tracked CLI cases and parallel standalone JSON benchmarks use explicit `-16thread` names, for example `cargo leanvm bench --only hash-50000-16thread`. The existing leanXMSS and aggregation `-1thread`, `-4thread` and `-8thread` cases retain their performance-worker settings; on heterogeneous hosts their actual total can include efficiency workers, recorded in the JSON thread metrics. Direct CLI timing commands default to 16 unless `LEANVM_NUM_THREADS` explicitly selects the existing performance-worker behavior. Standalone pooled targets always use 16; the inherently serial `kernels` benchmark remains single-threaded. Instruction counts and mobile device parallelism are unchanged.

The default desktop timing matrix has 17 tracked proof/tree selectors: eight converted from unspecified pools to explicit `-16thread` cases, plus nine existing 1/4/8-thread scaling cases. Shielded transfers are excluded from these desktop timings; their exact counts, direct CLI command and mobile proving and aggregation benchmarks remain available.

The sample timings below are historical measurements with the configuration used when they were recorded, not newly measured fixed-16 results. Their values have not been relabeled as 16-thread measurements.

The [benchmark website](./site/benchmarks/index.html) reads one complete [JSON snapshot](./site/benchmarks/latest.json): one source commit and one workflow run for every desktop and mobile result. Workloads contain compact machine and thread comparisons; the commit and run appear once, hardware specifications live in a shared reference, and dates, individual samples and verification counts remain in Measurement details. It includes programs and separately labeled aggregation nodes, not field, kernel, Flock or PCS microbenchmarks. Serve it locally with `python3 -m http.server --directory site/benchmarks`; opening the HTML directly as a file does not support fetching the dataset.

The [`Benchmark website` workflow](./.github/workflows/benchmark-site.yml) runs fresh benchmarks every six hours (`23 */6 * * *`) or manually with `gh workflow run benchmark-site.yml --repo leanEthereum/leanVM --ref riscv-exploration`. It resolves `riscv-exploration` once, records an immutable run plan, and checks out that SHA in every benchmark and publication job. Pushes do not refresh the site; PRs validate tooling and upload a preview without running the credential-bearing snapshot pipeline. Existing paired base/PR benchmarks remain independent.

Desktop jobs use the 64 GB `size-attester7870-x64` and `size-attester7870-arm64` runners with native builds, collecting five individual measured timings per case. The suite includes Fibonacci, BLAKE2s, leanXMSS, leanSPHINCS, Falcon, L1 state proofs, leanXMSS aggregation and leanDA. `cargo leanvm bench --only leanda-1-16thread` opts into leanDA on exactly 16 total threads without adding it to the default 17 selectors intended for smaller machines; its count-only identity remains `leanda-1`. The website selects explicit `-16thread` cases and preserves the named leanXMSS and aggregation 1/4/8 cases. Each result must contain actual thread-count evidence matching its selector, with 16 performance and zero efficiency workers for fixed-16 cases; missing evidence or historical unspecified identities are rejected, not relabeled from the host CPU count. The runner also records actual CPU, architecture, OS and RAM rather than inferring them from a runner label.

The reusable [mobile workflow](./.github/workflows/mobile-bench.yml) builds the same SHA and runs shielded proving and aggregation on iPhone 14 / iOS 16 and Pixel 7 / Android 13. Each function requires one verified warmup and three verified samples. Standalone proving covers two spends and four input notes; aggregation combines two independent two-spend leaves, with four spends and eight input notes total, leaf log inverse rate two and tree log inverse rate one. Leaf proving and tree setup are outside the aggregation timing. Shielded timing is mobile-only. The iPhone and Pixel sessions are sequential to respect provider concurrency; desktop jobs can run alongside them.

Every result also reports **Peak memory (MiB)** beside median time, with its measurement method in Measurement details. The schema-3 snapshot requires positive safe-integer `peak_memory_bytes` and a nonempty `peak_memory_method`; one MiB is 1,048,576 bytes. Desktop memory is the maximum of the independent rounds' CLI BMF `peak-memory.value` measurements: Linux process RSS high-water from `getrusage`, not heap allocation or total machine RAM. Aggregation includes leaf preparation, and a higher node's high-water can include preceding first-level work. Mobile memory is the maximum of each function's three SDK absolute process RSS samples, converted from KiB to bytes. Android samples `/proc/self/statm`; iOS samples Mach `resident_size`. These are sampled peaks around measured iterations, not OS lifetime high-water marks or baseline-adjusted memory growth. Resident setup allocations and retained proofs can contribute even though setup, warmup and teardown are outside the mobile sampling windows. See the [mobile measurement details](./bench-mobile/README.md#workloads) for the pinned SDK implementation and sampling limits.

Hardware identity uses the machine name, architecture, operating system, CPU and logical CPU count, not OS-visible RAM, which can vary between observations on the same runner. The hardware reference shows the observed RAM range while each result retains its exact byte count. This does not relax the selector's actual thread-count or peak-memory requirements.

Publication requires every planned desktop case and both mobile devices from that workflow run and SHA. Missing, failed, inconsistent or mixed-revision results, including missing or invalid peak-memory measurements, block publication; no historical artifacts are searched and no older configurations fill gaps. A failed run leaves the previous deployed site untouched. Successful runs generate `latest.json` atomically and upload `benchmark-data` and `benchmark-site` artifacts for 90 days; the JSON is not committed back to Git. The checked-in schema-3 file is an honest empty bootstrap until a complete run is available, not a relabeling of the former mixed-revision dataset. To inspect published data locally, download a successful run's `benchmark-site` artifact and serve that directory.

Scheduled operation requires both workflow definitions on `main`, because GitHub registers schedules only from the default branch and resolves reusable workflows from the caller's revision. Their source checkouts still use the pinned `riscv-exploration` SHA. Manual callers are restricted to `main` or `riscv-exploration` in `leanEthereum/leanVM`. The upstream self-hosted runners and the repository's `BROWSERSTACK_USERNAME` and `BROWSERSTACK_ACCESS_KEY` secrets with App Automate real-device access must be available; missing devices or credentials fail the run. This change does not install workflows on another branch, provision runners, or configure secrets.

For GitHub Pages hosting, a repository administrator must select **Settings > Pages > Build and deployment > Source: GitHub Actions**, set the repository Actions variable `BENCHMARK_PAGES_ENABLED` to `true`, and allow `riscv-exploration` and `main` in the `github-pages` environment deployment rules. The workflow does not change those settings. Pages permissions exist only in the separate deployment job, which checks out and executes no repository code. Until hosting is enabled, use the complete static-site artifact. Focused checks are `python3 -m unittest discover -s scripts -p test_benchmark_site.py`, `python3 -m unittest discover -s scripts -p test_mobile_bench_report.py`, `python3 scripts/benchmark_site.py check --input site/benchmarks/latest.json`, and `node --check site/benchmarks/app.js`.

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

### leanXMSS, leanSPHINCS, leanDA, Falcon-512, L1 state proofs and shielded transfers

Three programs check what an Ethereum node would: leanXMSS signatures, leanSPHINCS signatures, and leanDA blobs (`programs/leanxmss`, `programs/leansphincs`, `programs/leanda`). A fourth verifies Falcon-512 signatures as the round-3 specification defines them (`programs/falcon`), pinned to NIST's known answers. A fifth verifies Ethereum L1 state proofs (`programs/stateproof`): accounts and storage slots at one mainnet block, as `eth_getProof` (EIP-1186) proves them, from the block hash down, keccak256 and RLP in software. A sixth checks shielded transfers (`programs/shielded`): privacy-pool spends of two notes into two over a depth-20 tree, the statement of soispoke's [minimal shielded pool](https://github.com/soispoke/evm-spend-challenge/blob/main/SPEC.md), BLAKE2s edition, whose digests it reproduces.

Each guest is a `no_std` library, byte-compatible with the schemes' reference implementations, plus the `main` that runs it. Each host runs the same library natively to build the inputs and the expected output.

```bash
cargo leanvm leanxmss --n 400 --repeat 3
cargo leanvm leansphincs --n 104 --repeat 3
cargo leanvm leanda --blobs 1 --repeat 3
cargo leanvm falcon --n 28 --repeat 3
cargo leanvm stateproof --n 21 --repeat 3
cargo leanvm shielded --n 1035 --repeat 3
```

The report gives the RISC-V cycles per signature, per blob, per read or per spend, the rows per table and the committed witness, then the proving and verifying times.

These are the most one proof holds: continuations are not implemented.

To get the cost of all six without proving, exact and the same on every machine:

```bash
cargo leanvm bench --cycles-only --markdown
```

It prints a markdown table of the RISC-V cycles, per item and in all, and the committed witness words, for these three and the other benchmarks, then one of the recursion circuits of two aggregation trees over leanXMSS proofs (`cargo leanvm aggregate`; the leaves at `--leaf-log-inv-rate`, 2 by default, the tree's proofs at `--log-inv-rate`), 2 to 1 and 4 to 1 (`aggregate-leanxmss-400-2to1` and `aggregate-leanxmss-400-4to1`: every node combines 2, or 4, proofs into 1): each kind of node's rows per table and committed words, `-first` for a first-level node (the RISC-V verifier in rows over its leaf proofs) and `-node` for a higher node (the recursion verifier in rows over its child proofs). CI adds them to each run's summary, compares the same counts on every PR with the PR's base, comments with the ones that changed, and fails a PR that raises any of them; without `--markdown` it prints them as JSON (Bencher Metric Format), `--markdown-file <path>` appending the tables to a file from the same pass, and without `--cycles-only` it proves each program, and one node of each kind of both trees over leanXMSS-100 leaves, too.

### Hosted Android and iPhone benchmarks

The isolated [mobile benchmark integration](bench-mobile/README.md) packages a real two-spend shielded-transfer proof and a separate 2-to-1 aggregation of two such leaves, using pinned `mobench` tooling and the device's available parallelism. Aggregation prepares and verifies its leaves once outside the measured interval. It uses native ARM64 release builds on BrowserStack App Automate physical devices, with credential-free PR package checks and trusted scheduled or manual device runs. Benchmark inputs, timing boundaries, account requirements and downloadable result artifacts are documented there; these are not emulator performance measurements.

CI tracks shielded-transfer proving and aggregation timings only on these phones, not on desktop runners. Desktop CI retains the exact shielded instruction and witness counts. The standalone `cargo leanvm shielded` command remains available for local runs.

### flock

```bash
BENCH_REPEAT=3 BENCH_COOLDOWN=2 FLOCK_N_LOG=18 cargo bench -p leanvm --bench class_batch -- hash
```

Each instruction class's circuit proven alone by flock, on `2^FLOCK_N_LOG` random instances: the VM's own circuit and witness generator, the commitment, the zerocheck and lincheck, and the opening, each timed, then the verifying time and the instances proven per second. An argument keeps the classes whose name contains it (`hash`, `mul`, ...); none runs every class with a circuit.

## SNARK machinery

- 192-bit binary field (degree-3 tower over the 64-bit field)
- [WHIR](https://eprint.iacr.org/2024/1586) PCS, aka [Ligerito](https://eprint.iacr.org/2025/1187)
- [Flock](https://github.com/succinctlabs/flock/tree/main) hash proving
- [Binius](https://github.com/IrreducibleOSS/binius)/[Binius64](https://github.com/binius-zk/binius64) ring switching, M3 arithmetisation, and more (see [DP23](https://eprint.iacr.org/2023/1784) and [DP24](https://eprint.iacr.org/2024/504))
