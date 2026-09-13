# AGENTS.md

## What this is

A minimal virtual machine and recursive SNARK for signature aggregation and blob encoding. Proofs are not zero knowledge.

- `doc/leanvm/` is the LaTeX project describing the machine ISA and the snark that proves it. Its root is `doc/leanvm/main.tex`; build it with `cd doc/leanvm && latexmk -pdf main.tex`, which writes to the gitignored `doc/leanvm/.build/`. Sections live in `doc/leanvm/body/`, numbered `01`..`10` plus the lettered annexes `a` (ring switching), `b` (the PCS), `c` (Flock), and `d` (novel basis and additive NTT), and every symbol is defined once in `doc/leanvm/preamble/macros.tex`. If latexmk fails oddly (a bibtex error, or a missing `main.log`) right after inputs are renamed or `refs.bib` is edited, remove `doc/leanvm/.build` and rerun; it has not reproduced on unchanged inputs. **Drafting one section:** each section file carries a `% !TeX root` comment pointing at its generated driver in `doc/leanvm/drafts/`, so the LaTeX build key (`F5`, or the extension's `cmd+alt+b`) compiles only that section, numbered as in the full document and with cross-references and citations resolved against `.build/main.aux`; in `main.tex` the same key builds everything. Run `doc/leanvm/make-drafts.sh` after adding, renaming or renumbering a section.
- `doc/xmss/` is the standalone XMSS specification; `crates/xmss` implements its hash inputs and signature verification.
- `doc/sphincs/` is the standalone specification of the concrete SPHINCS+ instance used where statelessness matters; its root is `doc/sphincs/main.tex`, built the same way as `doc/xmss`, and implemented by `crates/sphincs`. It uses the same BLAKE2s primitive and target-sum encoding shape as XMSS, with its own tweak layout, target sum, and signing search.
- `formal/xmss/` and `formal/sphincs/` are Lean 4 proofs (over VCVio) of the ideal schemes' classical random-oracle security, `xmss_has_127_bits_of_classical_security` and `sphincs_has_127_bits_of_classical_security`. Each project's `Statement.lean`, under `XmssSecurity/` or `SphincsSecurity/`, contains the concrete parameters, the byte layout of every hash input, the three algorithms, the game, and the claim. `lake exe cache get` once, then `lake build`.
- The one hash function is BLAKE2s, in `primitives::hash`: scalar, streaming, keyed, and a lane-transposed batched form for the PCS Merkle tree. The VM proves one compression per opcode, and BLAKE2s takes the byte counter and final-block flag as ordinary compression inputs, so repeated opcodes hash arbitrary byte strings by carrying the chaining value and setting the counter and final flag for each block.
- `crates/lean_compiler/zkDSL.md` documents the (pythonic) zkDSL (that compiles to the ISA that our VM runs, and that our snark proves).

Primary uses:

- Aggregate XMSS claims grouped by epoch and message, SPHINCS claims carrying individual messages, and LeanDA blob encoding claims.
- Recursively aggregate child proofs, proving that every published signature claim and DA root is supported by a raw input or a verified child.

## Layout

Dependency order, leaves first:

| crate             | role                                                                   |
| ----------------- | ---------------------------------------------------------------------- |
| `parallel`        | thread pool (below)                                     |
| `zk_alloc`        | proving arena (below)                                    |
| `primitives`      | field kernels (NEON/AVX), bit transposes, multilinear helpers, streaming stores, `bench` |
| `fiat_shamir`     | VM-native `FiatShamirState` + prover/verifier transcript                |
| `pcs`             | additive NTT, Merkle, ring switch, stacked WHIR                    |
| `flock`           | batched R1CS over GF(2) for BLAKE2s: zerocheck + lincheck               |
| `lean_vm`         | arithmetization: tables, bus, constraints, `cpu::prove`/`verify`       |
| `lean_compiler`   | zkDSL (Python subset) → ISA                                            |
| `xmss`            | XMSS over BLAKE2s; an independent leaf, consumed only by `rec_aggregation` |
| `sphincs`         | the stateless SPHINCS+ instance of `doc/sphincs`; an independent leaf, consumed only by `rec_aggregation` |
| `lean_da` | additive Reed-Solomon blob encoding, commitments, and membership vectors |
| `rec_aggregation` | recursive signature and DA aggregation: the guest, public entry points, and benchmarks |

`src/lib.rs` is the public API and the only thing a user imports: every crate above is `publish = false`, so a new user-facing item is a re-export there. `src/main.rs` is the benchmark CLI, `tests/api.rs` the end-to-end use of the API; guests are zkDSL under `crates/rec_aggregation/guests/`.

## Building / Testing / Formatting

- `.cargo/config.toml` pins `-C target-cpu=native` and `-D warnings` for rustdoc
- always run in `--release` mode any test or benchmark touching the VM (the zkDSL compiler stack-overflows in `debug` mode)
- **One test binary per crate, not one per file:** new `lean_compiler` integration tests go in `tests/suite/main.rs`, one linked executable instead of seventeen. Exception: a test opening an arena phase (`lean_vm::init_prover`) needs its own binary. Phases are process-global, so two in one process reclaim each other's `ArenaVec`s and the symptom is a proof that stops verifying, never a crash (`rec_aggregation/tests/arena_prove.rs`).

An x86-only arm never compiles on an Apple dev machine, so a typo in one ships. Type-check the other target before pushing anything `cfg`-gated:

```bash
CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512vl,+vpclmulqdq,+pclmulqdq,+gfni,+avx2,+aes" \
  cargo check --release --workspace --target x86_64-unknown-linux-gnu
```

It needs `rustup target add x86_64-unknown-linux-gnu` and nothing else, since `check` does not link. The `apple-m4 is not a recognized processor` and `x87` notes are the pinned `target-cpu=native` and the bare cross ABI, not findings. To confirm an arm is really being reached rather than silently skipped, drop a `compile_error!` in it and watch the check fail.

```bash
cargo testall                     # release workspace tests
cargo clippyall                   # clippy, -D warnings
cargo docall                      # rustdoc, -D warnings
cargo fmt --all                   # max_width = 120
ruff format --line-length 150 python-verifier/verifier.py   # and `ruff check` it
```

Heavy benches and measurement harnesses are `#[ignore]`d; run by name with `-- --ignored --nocapture`: `hash_batch_prove_verify`, `pcs_throughput`, `aggregate_three_levels`, `aggregate_statement_binds`, `aggregate_hints_bind`, `aggregate_rejects_a_bad_signature`, `print_whir_query_counts`, `encoding_grinding_bits`.

## Benchmarking

The benchmarks we care about:

- `cargo run --release -- aggregate --xmss 900 --log-inv-rate 1 --repeat 3`
- `cargo run --release -- aggregate --sphincs 220 --log-inv-rate 1 --repeat 3`
- `cargo run --release -- recursion --n 2 --xmss-per-leaf 900 --log-inv-rate 2 --repeat 3`

`aggregate` takes a count per scheme, both defaulting to zero, so either alone or a mix of the two is one command; `recursion --sphincs-per-leaf` likewise puts both schemes in one tree. One SPHINCS verification uses 531 compressions against XMSS's 144; use the benchmark output to compare complete VM cycle counts. `aggregate --blobs` adds LeanDA blobs, and `recursion --blobs-per-leaf` includes them in each child.

## The proving arena (`zk_alloc`)

One proof is one **phase**, opened by `cpu::prove`. `ArenaVec` bumps a per-thread slab, a small block's release is at most a cursor pop while a large one is recycled (below), and the next `begin_phase()` reclaims everything. Not a `#[global_allocator]`: `raw_dealloc` picks arena-vs-system by address range, so with no phase open `ArenaVec` is an ordinary system vector (used in particular by the verifier, where correctness and simplicity matters much more than performance).

**The rule:** an `ArenaVec` allocated in a phase dies at the next `begin_phase()`. A reset neither clears nor unmaps, so a buffer that outlives its phase reads the previous proof's plausible bytes, so the symptom is a proof that stops verifying, never a crash. Anything outliving a phase (a `Proof`, a cache, a table) must be a plain `Vec`. And **`drop` means something**: a large released block is handed back out within the phase (a per-thread free list, see the crate docs), so dropping a big buffer where it dies is worth doing, and a use-after-free the bump arena used to mask now reads another buffer's live data. Run `ZK_ALLOC_POISON=1 cargo testall` after changing buffer lifetimes; it fills released blocks and fills what a phase used when it ends, turning a silent wrong answer into a loud failure. That covers both shapes: a buffer read after being dropped, and a buffer that outlives its phase.

`setup_prover_without_arena` (or `lean_vm::init_prover_pool` alone) leaves the arena disengaged, sending every `ArenaVec` to the system allocator. It is the escape hatch for a host where even the recycled peak does not fit; on one that it does fit, the arena is faster, since its pages stay faulted in across proofs.

## The thread pool (`parallel`)

No rayon. Every parallel site is "N independent items, each writing its own disjoint slice", so the pool is a claim counter, not a work-stealing deque: `NUM_THREADS-1` workers plus the dispatcher inline, no per-dispatch allocation. Primitives: `for_each{,_chunk}`, `chunks_mut{,2,_zip}`, `Chunks`, `fill`, `map_collect`, `map_reduce`, `fold_reduce`, `map_reduce_with_state`, `find_first`, `SendPtr`.

- **Nested dispatch panics**, because it would deadlock the dispatch lock.
- **Both core clusters share one queue** (P at `USER_INTERACTIVE`, E at `UTILITY`); guided self-scheduling means a slow core claims fewer batches. Do not add a second pool: that was `primitives::epool`, now deleted.
- **The default holds back one performance worker when efficiency workers exist.**

`LEANVM_NUM_THREADS` sets the **performance**-worker count, leaving E-workers in place. `1` = strictly sequential.

## Three verifiers, one protocol

The same verification algorithm is written out three times, in three languages. Any change to snark protocol has to land in all three.

1. **Rust**, `lean_vm::cpu::verify`. The native verifier.
2. **Python**, `python-verifier/verifier.py` (no dependencies), for readability and simplicity. Pinned by `lean_vm/tests/verifiers/python_verifier.rs`.
3. **Recursive verifier**, `crates/rec_aggregation/guests/lean_ethereum.py`. Its zkDSL compiles to the ISA; proving its execution gives a proof of child proofs.

Understand the third before changing the verifier. `guests/lean_ethereum.py` is zkDSL, not runnable Python. `lean_compiler` lowers it to the six-opcode, write-once-memory VM, so the prover proves every verifier step. Its size and instruction mix are what the recursion benchmark reports first. It verifies raw signatures of both schemes: a node's coverage table has one contiguous region per XMSS epoch group and separate regions for SPHINCS and DA roots, so the one range check a write already needs also keeps a signature off another group's declared keys, of either scheme, and the statement's signer lists say which scheme verified which key against which `(epoch, message)`. The XMSS signers are grouped by epoch, each group carrying its own message, a runtime number of groups (at most `MAX_EPOCHS`) bound through the signer-set digest, which is plain BLAKE2s of a byte string (each list's own digest folded into it, likewise plain BLAKE2s): a run-time length rides the byte counter because the counter is a memory operand, split as `doc/leanvm` §sec:prog-byte-counter describes. A child's groups need not equal its parent's, a hinted map tying each child group to a parent group with the same epoch and message. A SPHINCS signer's message rides its own four-cell slot, so that list is `(key, message)` pairs; both lists count claims rather than distinct signers, an XMSS key claiming once per epoch it signed at. Both schemes' tweaks are built in-circuit: XMSS's from the epochs the statement carries, derived once per group that verifies raw XMSS signatures and skipped by one that verifies none, SPHINCS's per signature from the index its message digest picks. Two consequences:

- The guest is **self-referential**: it verifies proofs of itself, so `unified_guest` compiles it to a fixed point on its own log size. The digest needs no fixed point, riding the statement instead of the code, which is also what lets one bytecode serve any inner size and PCS rate.
- It does not verify *quite* everything in-circuit. Three claims on fixed polynomials (stacked bytecode, flock's A0/B0) are deferred. Each node batches its children's carried claims with the fresh ones its verifications raise, `2n` per polynomial down to one; only the root's are discharged natively, by `EthereumProof::verify` (explained in `doc/leanvm/`).

`aggregate_two_to_one` is the fast end-to-end check; `aggregate_statement_binds` and `aggregate_hints_bind` are the adversarial ones, tampering the wire object and the witness respectively. A child must commit at least `2^MU_MIN` or the guest has no opening arm for it, so `aggregate` sets `Program::min_log_committed` and a smaller run grows its `SET` table through the fill blocks until it clears the floor.

## Conventions that bite

- **The prover can be memory-bandwidth bound.** Reduce memory traffic before assuming that more workers or fewer instructions improve throughput. `primitives::stream::Stream` publishes a buffer without the read-for-ownership an ordinary store pays, but ONLY where nothing reads the destination again before it is evicted. Where a consumer follows in the same pass, the fetch it avoids becomes that consumer's miss: fold kernels earn it by building their round message from registers, or by folding into an L1 stage first (`whir::fold_and_msg_blocks`). That fetch is an x86 cost only: on Apple silicon a store-only fill already sustains what a read-only pass does and `STNP` measures identical to `STP`, so `Stream` is a plain copy there and the L1 stage earns its keep for the read locality alone, which is still better than writing through.
- **NEON is the width ceiling on Apple silicon**, so an AVX-512 win that is purely width has no counterpart: the M4 has no SVE, and its SME2 is streaming-mode matrix work with no polynomial multiply. What does port is *shape*. A fused NTT pass wants a butterfly at a time over whole rows, not the register-resident tile the AVX-512 arms use: they transpose anyway and want to pay for it once per pass, while NEON transposes nothing and a tile leaves only its own width of independent work to cover the reduction's dependent PMULL folds, where a row leaves the whole lane count. Measured both directions: the tile costs the extension NTT, and costs the base encode's `Commit` again.
- **A `[F192; N]` in a NEON kernel is a memory object, where on AVX-512 it is the register.** Four tower products are four independent PMULL chains wanting most of the 32 vector registers, so an array of them spills and the spill costs more than batching the products saves; the same array is free on AVX-512, where the quad IS one register. Keep the quad as a tuple or as named values and let arrays exist only inside the batched-product helper, on the target that wants them (`flock::zerocheck::multilinear`'s `mul_quad`). The symptom is indirect, so suspect the shape rather than the arithmetic: the products measure the same either way, destructuring the results changes nothing, and forcing the helper to inline recovers almost none of it.
- **On Zen 4, 512-bit cross-lane data movement is half-rate** (every 512-bit shuffle is two 256-bit uops), so packing scalars into vector lanes with `vpermi2q`/`vpermq` and extracting with `vextracti64x4` loses to the scalar moves it replaces. Widening the arithmetic still pays: `mul4` beats the same products issued one at a time. Prefer kernels where both qwords of every 128-bit lane carry a product and nothing crosses lanes.
- Use comments only when necessary: uncommented but readable and simple code is better than commented slop. And when you use comments, be concise.
- **Never put a measurement in a comment, a doc comment, or this file.** Timings, throughputs, percentages and speedup factors go stale the moment the code, the compiler or the host changes, and nothing ever rechecks them, so they end up asserting something false with the authority of a comment. The commit message is where they belong: it is dated, it is immutable, and it says what was true when the change landed. A comment may say which way a result went and why (that a tile lost to whole rows, that one reduction beat another), never by how much.
- Commit tests only that are useful in the future, to prevent regressions / failures. Don't add trivial tests that will always pass.
- Simpler is better.
- **Fiat-Shamir:** `add_scalar`/`next_scalar` bind into the Fiat-Shamir state as a side effect. The public statement seeds the transcript at construction; the transport exposes no separate observe operation. Never re-observe data that rode the stream, which silently desynchronizes the two sides.
- **Prover and verifier derive the layout identically** from announced sizes. Changes to `placements_of` or the schema land on both sides. `col_kappas` is derived from `col_kappa_sources` rather than written out twice, so the two can no longer drift; keep it that way.
- **The L0 lane fold binds the committed witness's TOP `INITIAL_FOLDING_FACTOR` variables**, because lane `l` of the interleaved commitment is the stack block `q[l·2^(μ-k) ..)`. That makes the witness's zero tail whole lanes, so `whir::commit` encodes only `StackShape::n_lanes` of them, and the opening's dense weight, its first `k` sumcheck rounds and the stack allocation shrink with it. **A leaf image is still `2^k` words**, the absent lanes contributing their codeword's zeros, but those zeros LEAD it (codeword lane `t` is stack block `n_lanes-1-t`): their whole 64-byte blocks are then one shared chaining value (`hash::zero_prefix_state`) the committer hashes once rather than per leaf, and only the image's tail rides the proof, so `PrunedMerklePaths` stores `n_lanes` words per L0 row while `RawMerklePath` (what the guest and the Python verifier read) carries the full image. The Rust and Python verifiers therefore derive `n_lanes` from the announced layout to read a row; the guest never needs it, its hints being full images. Since `mu = log2_ceil(placed)`, `n_lanes` is always in `[2^(k-1)+1, 2^k]`: the encode saving caps near half, the hashing saving is quantized to whole blocks of 8 lanes, and both are ~0 just above a power of two. The cost is that fold challenges arrive in round order while every transparent weight is written in witness coordinates, so all three verifiers rotate the terminal point left by `k` before evaluating it (`whir.rs` before `eval_b_at`, `verifier.py` before `evaluate_basis`, `open_stacked` in the guest). Anything else that reads the opening's point (per-level induced weights, the residual) stays in round order.
- **A failed guest `assert` surfaces as a write-once memory conflict**, not an assertion message, but it names the source line: `write-once conflict at cell 34 (line 2906, pc ...)`. A failed range check and a wild `DEREF` name the function and line instead (`in verify_sub (line 2204)`). Parse and lowering errors carry a line too. Reach for `DBG_DISASM` only when the line is not enough, or when the pc lands in a fill block, which has no source line by construction.
- Guests are single-file; the compiler skips `from snark_lib import *`, which exists only so editors accept the file as Python.
- **One symbol, one meaning, across the whole leanVM document.** All notation is defined in `doc/leanvm/preamble/macros.tex`: define a new macro there rather than inline, and check the letter is free first. Annex B's "Symbols" table maps its letters back to WHIR/Ligerito/BCHKS25, so read it before renaming one. A sumcheck round challenge is `\fc` everywhere, which is what keeps `\rho` free for the rate; `r` is the point a claim is made at, not a challenge. **A rename in the document is a rename in the implementations**: the Rust prover and verifier, `python-verifier/verifier.py`, and `guests/lean_ethereum.py` name their variables after the document's symbols, so the four have to move together.
- **Doc labels are an API.** `crates/pcs` cites `thm:rbr` and `thm:mca-johnson` by name and several crates cite `doc/leanvm/main.tex` sections, so renaming a label breaks those pointers with nothing to catch it. `doc/leanvm/body/NN-*.tex` prefixes match section numbers, so inserting a section renumbers the rest.
- **No em-dashes or en-dashes in prose**, anywhere a human reads it: docs, LaTeX, comments, commit messages. Restructure with a comma, colon, parentheses, or two sentences.
- **Never hard-wrap prose in Markdown or LaTeX.** One paragraph is one line; let the editor wrap it. Artificial line breaks make every later edit a reflow, so diffs show rewrapped lines instead of changed words. Applies to `.md` and `.tex` alike; code blocks, tables and list items keep their own line.

## Soundness

- In the recursion program, the prover transmits advice to the verifier, called "hints". Hints are untrusted witness data and must be checked by the verifier; a malicious prover must not be able to prove an invalid witness.

## Env knobs

| var                                                                                                     | effect                                           |
| ------------------------------------------------------------------------------------------------------- | ------------------------------------------------ |
| `LEANVM_NUM_THREADS`                                                                                    | performance-worker count; `1` = sequential       |
| `LEANVM_PROFILE`                                                                                        | per-stage prover timings                         |
| `ZK_ALLOC_STATS`                                                                                        | arena peak/phase, high water, overflow           |
| `ZK_ALLOC_POISON`                                                                                       | fill released arena blocks, to catch use-after-free |
| `BENCH_REPEAT`, `BENCH_COOLDOWN`                                                                        | `--repeat`/`--cooldown` for `#[ignore]`d benches |
| `LEANVM_XMSS_N`, `LEANVM_HASH_N`, `LEANVM_HASH_UNROLL`                                                  | workload sizes in tests                          |
| `FLOCK_N_LOG`, `FLOCK_PROVE_TRACE`, `FLOCK_ZC_TIMING`, `LINCHECK_TRACE`                                 | flock batch size, stage traces                   |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`, `PCS_MIN_MU`, `PCS_SAMPLES`                                            | PCS throughput bench                             |
| `WHIR_TRACE`, `WHIR_NUM_VARS`, `WHIR_LOG_INV_RATE`                                          | WHIR NTT/Merkle split                        |
| `DBG_PROF{,_DUMP}`, `DBG_LOOPS`, `DBG_DISASM`, `DBG_LOWER`, `DBG_PLACEHOLDERS` | compiler / guest-cycle attribution               |

## Side notes

- Grinding chooses the smallest valid nonce, including in parallel. Randomized signature inputs can still make proofs differ between runs.
