# AGENTS.md

## What this is

A minimal virtual machine and recursive SNARK for signature aggregation and blob encoding. Proofs are not zero knowledge.

- Aggregate leanXMSS and leanSPHINCS claims, each a `(pubkey, message)` pair, and LeanDA blob encoding claims.
- Recursively aggregate child proofs, proving that every published signature claim and DA root is supported by a raw input or a verified child.

## Documents

- `doc/leanvm/`: the LaTeX specification of the ISA and the SNARK. Build with `cd doc/leanvm && latexmk -pdf main.tex` (output in the gitignored `.build/`; if latexmk fails oddly after renaming inputs or editing `refs.bib`, delete `.build` and rerun). Sections are `body/01`..`10` plus annexes `a` (ring switching), `b` (PCS), `c` (Keccak by GKR) and `d` (novel basis and additive NTT); every symbol is defined once in `preamble/macros.tex`. Each section file's `% !TeX root` points at a driver in `drafts/`, so the editor's build key compiles just that section; run `make-drafts.sh` after adding, renaming or renumbering one.
- `doc/lean_xmss/`, `doc/lean_sphincs/`: the specifications of the two signature schemes, implemented in `crates/signatures/src/lean_xmss` and `lean_sphincs`. leanXMSS has full keys only, plus `mock` keys (real over a short range of leaf indices) behind the `mock` feature, for the signers cache and tests. `crates/signatures/tests/signatures/ethlib/` vendors EthLib's leanXMSS and leanSPHINCS test vectors, both from one EthLib commit; refresh them with `ethlib/sync.sh <ethlib-commit>`. `crates/signatures/src/lean_sphincs/known_answer.hex` is a leanSPHINCS key and signature, from a scheme seed, that the crate must reproduce byte for byte.
- `formal/lean_xmss/`, `formal/lean_sphincs/`: Lean 4 (VCVio) proofs of the schemes' 127-bit classical security in the random-oracle model. Their `Scheme.lean` models every hash input's bytes as the crate computes them, so changing any of them in the crate invalidates the proof. `lake exe cache get` once, then `lake build`.
- `crates/lean_compiler/zkDSL.md`: the zkDSL, a Python subset that compiles to the ISA.

The one hash function is Ethereum's Keccak-256 (FIPS 202 but for the padding's first byte, `hash::PAD_FIRST`), in `primitives::hash`. The VM's `KECCAK` opcode, one permutation of a state held in thirteen memory cells (`keccak::cell_lanes`), is proven by `crates/keccak_gkr`: its crate docs describe the prover, Annex C the protocol.

## Layout

The root `Cargo.toml` is workspace-only: libraries in `crates/`, the CLI in `bins/`. Dependency order, leaves first:

| crate             | role                                                                   |
| ----------------- | ---------------------------------------------------------------------- |
| `parallel`        | the thread pool (below)                                                |
| `primitives`      | field kernels (NEON/AVX), Keccak, bit transposes, multilinear helpers, streaming stores |
| `bench`           | benchmark harness (`Plan`, `Timing`, `--tracing`, Bencher output, the jemalloc allocator); never linked by the prover |
| `fiat_shamir`     | the duplex sponge transcript and the prover's side of the proof transport |
| `pcs`             | additive NTT, Merkle, ring switch, stacked WHIR: commit and open, no verifier |
| `keccak_gkr`      | the prover of the VM's `KECCAK` argument                               |
| `leanvm_core`     | arithmetization: tables, bus, constraints, `cpu::prove`; `cpu::verify` wraps `verifier` |
| `lean_compiler`   | zkDSL → ISA                                                            |
| `signatures`      | leanXMSS and leanSPHINCS over Keccak-256                               |
| `lean_da`         | additive Reed-Solomon blob encoding, commitments, membership vectors   |
| `verifier`        | the one native verifier (below)                                        |
| `rec_aggregation` | recursive signature and DA aggregation: the guest and public entry points |
| `leanvm`          | the public API                                                         |

`crates/leanvm/src/lib.rs` is the only thing a user imports: every other crate is `publish = false`, so a new user-facing item is a re-export there, and `crates/leanvm/tests/api.rs` is its end-to-end use. Guests are zkDSL under `crates/rec_aggregation/guests/`. The CLI is `bins/leanvm`, run with `cargo leanvm <subcommand>` (`aggregate`, `recursion`, `fibonacci`, `hash`).

## Building and testing

- `.cargo/config.toml` pins `-C target-cpu=native`, and `-D warnings` for rustdoc.
- Run anything touching the VM in `--release`: the zkDSL compiler stack-overflows in debug.
- One test binary per crate: new `lean_compiler` integration tests are modules of `tests/suite/main.rs`.

```bash
cargo testall                     # release workspace tests
cargo clippyall                   # clippy, -D warnings
cargo docall                      # rustdoc, -D warnings
cargo fmt --all                   # max_width = 120
ruff format --line-length 150 python-verifier/verifier.py   # and `ruff check` it
```

An x86-only `cfg` arm never compiles on an Apple machine, so type-check the other target before pushing anything `cfg`-gated (needs only `rustup target add x86_64-unknown-linux-gnu`; `bench` and the CLI are left out because jemalloc's build script wants a cross `gcc`):

```bash
CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512vl,+avx512vbmi,+vpclmulqdq,+pclmulqdq,+gfni,+avx2,+aes" \
  cargo check --release --workspace --exclude leanvm-cli --exclude bench --target x86_64-unknown-linux-gnu
```

To confirm an arm is reached rather than silently skipped, put a `compile_error!` in it and watch the check fail.

Heavy benches are `benches/` targets, run with `cargo bench -p <crate> --bench <name>`: keccak_gkr's `hash_batch`, pcs's `throughput`, primitives' `hash_throughput`. Slow checks are `#[ignore]`d tests, run by name with `-- --ignored --nocapture`: `aggregate_three_levels`, `aggregate_round_trips_through_the_wire`, `print_whir_query_counts`, `encoding_grinding_bits`. `aggregate_two_to_one` is the fast end-to-end check.

Where a proof's time goes is the `tracing` span tree, and only that: `--tracing` on the CLI, `BENCH_TRACING=1` on the benches, `RUST_LOG` for the level. A new stage worth timing gets an `info_span!` (`stage!` in `leanvm_core`), never an `Instant` behind an env var.

## Benchmarking

```bash
cargo leanvm aggregate --xmss 900 --log-inv-rate 1 --repeat 3
cargo leanvm aggregate --sphincs 530 --log-inv-rate 1 --repeat 3
cargo leanvm recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3
cargo leanvm hash --log-n 17 --repeat 3     # the Keccak GKR alone, as keccak_gkr's `hash_batch`
```

`aggregate` takes a count per scheme (both default to zero) and `--blobs`; `recursion` likewise takes `--sphincs-per-leaf` and `--blobs-per-leaf`. Compare schemes and changes by the reported VM cycle counts.

CI compares every PR with its base, never with a history: `bench.yml` runs both on one runner, in turns, on an x86-64 (`haswell`) and an arm64 (`neoverse-n2`, `+aes,+sha3`) testbed, and `bench-comment.yml` posts what moved as one PR comment. The posting workflows never run the PR's code; `.github/scripts/pr_comment.py` (standard-library Python) says what they trust, and its `--dry-run` prints the comment a run's artifacts would give.

## The allocator

The prover's buffers are plain `Vec`s and the libraries impose no allocator. A proof allocates and frees gigabytes, so the CLI and the benches install jemalloc with `dirty_decay_ms:-1` (`bench::Jemalloc`), which keeps freed pages mapped for the next proof at the cost of resident memory, and on Linux with `thp:always`, which backs its extents with transparent huge pages. Skip a buffer's zero-fill with `primitives::uninit_vec` or `filled_vec` (`T: Plain`, every element written before it is read), and drop large buffers where their last use ends.

## The thread pool (`parallel`)

No rayon. Every parallel site is "N independent items, each writing its own disjoint slice", so the pool is a claim counter: `NUM_THREADS - 1` workers plus the dispatcher, both core clusters sharing one queue. Do not add a second pool.

- Nested dispatch panics, because it would deadlock the dispatch lock.
- One site runs beside the pool: `keccak::while_executing` spawns half the pool's count of plain threads while a program executes, gone before the next dispatch.
- `LEANVM_NUM_THREADS` sets the performance-worker count; `1` is strictly sequential. The default is one worker per logical CPU (on Linux, per physical core the process may use), holding back one performance worker when efficiency workers exist.

## Three verifiers, one protocol

The verification algorithm is written out three times, and any change to the protocol lands in all three. `verifier::TAG`, the version string the Fiat-Shamir IV hashes (nothing derives it), and every Fiat-Shamir label stay at `v1` until leanVM ships on Ethereum.

1. **Rust**, `crates/verifier`: the one native verifier, what `EthereumProof::verify` and `cpu::verify` run. It must stay portable by construction: no dependencies, no `unsafe`, no `core::arch`, no `cfg(target_arch)`, no threads. Pinned by `leanvm_core/tests/verifiers/portable_verifier.rs` and every test that verifies.
2. **Python**, `python-verifier/verifier.py` (no dependencies), for readability. Pinned by `leanvm_core/tests/verifiers/python_verifier.rs`.
3. **Recursive**, `crates/rec_aggregation/guests/lean_ethereum.py`: zkDSL, so proving its execution gives a proof of child proofs. Its size and instruction mix are what the recursion benchmark reports first.

The prover's crates contain no verifier, in tests either: a prover test checks against a reference, and a test that needs a verdict goes through `crates/verifier`.

The Rust verifier walks the protocol once for two entry points: `verify_execution` checks a proof, and `replay_unchecked` returns the same `Summary` checking nothing. Every check sits behind `Transcript::checked`, so a new check goes there, and nothing else may depend on the mode. **`aggregate` does not verify its children**: it only replays them to build the guest's witness, refusing a child it cannot walk as `InvalidChild`, and the guest's in-VM verification catches the rest as `ProofError`. A caller that has not checked a child calls `EthereumProof::verify` on it first.

The guest is self-referential: it verifies proofs of itself, so `unified_guest` compiles it to a fixed point on its own size. One claim, on the stacked bytecode, is not verified in-circuit: each node batches its children's into one, and only the root's is discharged natively, by `EthereumProof::verify`. A child must commit at least `2^MU_MIN` cells for the guest to open it, so `aggregate` sets `Program::min_log_committed`. `DBG_PROF=1` (with `DBG_PROF_DUMP`, `DBG_DISASM`) gives the guest's per-function and per-pc cycle profile.

## Soundness

In the recursion program, the prover sends the verifier advice, called hints. Hints are untrusted witness data: every hinted value must be pinned by a constraint, so a malicious prover cannot prove an invalid witness.

## Conventions that bite

- **The prover can be memory-bandwidth bound.** Reduce memory traffic before assuming more workers or fewer instructions help. `primitives::stream::Stream` stores without the read-for-ownership, but only pays where nothing reads the destination again before it is evicted; on Apple silicon it is a plain copy.
- **NEON is the width ceiling on Apple silicon** (no SVE; SME2 has no polynomial multiply), so an AVX-512 win that is purely width does not port. Shape does: NEON wants a butterfly at a time over whole rows, not the register-resident tiles of the AVX-512 arms.
- **A `[F192; N]` in a NEON kernel spills** where on AVX-512 it is one register. Keep quads as tuples or named values; arrays only inside the batched-product helpers (`primitives::field::mul4`), on the target that wants them.
- **Rebuild or store is a per-machine choice**, made once in `primitives::REBUILD_OVER_STORE`: x86 rebuilds an intermediate, Apple silicon stores it. A new trade of that kind takes its choice from the same constant.
- **A hot NEON helper that is `#[inline(always)]` stays so.** A `#[target_feature]` function cannot be forced inline, and LLVM then leaves field helpers out of line in hot loops. Split a product's halves by hand rather than with `array::map`. A helper that needs `unsafe` is an `unsafe fn` its callers wrap.
- **On Zen 4, 512-bit cross-lane moves are half-rate**: prefer kernels where both qwords of every 128-bit lane carry a product and nothing crosses lanes.
- **On Zen 5 the carry-less multiplier is the scarce unit**: reduce modulo `x^64 + x^4 + x^3 + x + 1` with shifts and XORs (`gf2_64::reduce`), and count CLMUL instructions, not products. The exception is the scalar `F64` product (`gf2_64::x86_64::mul`), which keeps the CLMUL folds.
- **`crates/verifier` is still auto-vectorized**: on AVX-512, LLVM turns table lookups into gathers that lose to scalar loads. Check its x86 disassembly after touching a lookup.
- **Fiat-Shamir:** `ProverState::add_scalar` and `Transcript::next_scalar` bind into the transcript as a side effect, and the public statement seeds it at construction. Never re-observe data that rode the stream.
- **Prover and verifiers derive the layout identically** from announced sizes: a change to `placements_of` or the schema lands in the prover and all three verifiers (`crates/verifier`'s `layout.rs` is the native one). `col_kappas` is derived from `col_kappa_sources`; keep it that way.
- **The opening's lane fold binds the committed witness's top variables** (`whir::commit` documents the layout), so every verifier rotates the terminal point left by `INITIAL_FOLDING_FACTOR` before evaluating the basis, while every other read of the opening's point stays in round order.
- **A failed guest `assert` surfaces as a write-once conflict** naming the function and source line. A conflict that `had 0:0:0` can instead be an ordering bug: a cell read before it was written.
- **Guests are single-file**; the compiler skips `from snark_lib import *`, which exists only for editors.
- **One symbol, one meaning, across the leanVM document**, defined in `preamble/macros.tex` (check a letter is free first; Annex B's "Symbols" table maps its letters to WHIR/Ligerito/BCHKS25). A sumcheck challenge is `\fc`, keeping `\rho` for the rate. A rename in the document is a rename in the Rust prover, `crates/verifier`, `verifier.py` and the guest, which name their variables after it.
- **Doc labels are an API**: crates cite `thm:rbr`, `thm:mca-johnson` and sections of `doc/leanvm/main.tex` by label, and `body/NN-*.tex` prefixes match section numbers.
- **Comments only where necessary**, and concise. **Never put a measurement in a comment, a doc comment, or this file**: it goes stale and nothing rechecks it. Measurements belong in the commit message. A comment may say which way a result went and why, never by how much.
- **Commit only tests useful against future regressions.** Simpler is better.
- **No em-dashes or en-dashes** in prose anywhere a human reads it. **Never hard-wrap prose** in Markdown or LaTeX: one paragraph is one line.
- Grinding chooses the smallest valid nonce, including in parallel. Randomized signature inputs can still make proofs differ between runs.

## Env knobs

| var                                                                            | effect                                                |
| ------------------------------------------------------------------------------ | ----------------------------------------------------- |
| `LEANVM_NUM_THREADS`                                                           | performance-worker count; `1` = sequential            |
| `LEANVM_CODEWORD_BUDGET_MIB`                                                   | largest L0 codeword kept in memory (default 1024)     |
| `BENCH_TRACING`, `BENCH_REPEAT`, `BENCH_COOLDOWN`                              | `--tracing`, `--repeat`, `--cooldown` for the benches |
| `LEANVM_HASH_N`, `LEANVM_HASH_UNROLL`                                          | workload sizes in tests                               |
| `KECCAK_N_LOG`, `KECCAK_DEPTH`                                                 | keccak_gkr batch size, rounds between committed states |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`                                                | PCS throughput bench                                  |
| `WHIR_NUM_VARS`, `WHIR_LOG_INV_RATE`                                           | `print_whir_query_counts`'s shape                     |
| `DBG_PROF{,_DUMP}`, `DBG_LOOPS`, `DBG_DISASM`, `DBG_LOWER`, `DBG_PLACEHOLDERS` | compiler / guest-cycle attribution                    |
