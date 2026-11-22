# AGENTS.md

A minimal VM and recursive SNARK, not zero knowledge. It aggregates leanXMSS and leanSPHINCS claims (`(pubkey, message)` pairs), LeanDA blob encoding claims, and child proofs.

- Fields: `K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`, `E = K[y]/(y^2 + x*y + 1)` (`primitives::field::F128`). A VM word is one `E` element.
- Hash: Ethereum's Keccak-256 (crate `keccak256`). The `KECCAK` opcode is one permutation over thirteen memory cells, proven by `keccak_gkr` (Annex C).

## Layout

Two prover trees share no prover crate and give the same proof bytes (`bench/tests/identical_proofs.rs`):

- `crates/stable_prover/` (`stable_*`): the reference, written to be read. Plain safe code. `core::arch` and `cfg(target_feature)` only in `primitives::field::lanes`. No uninitialized buffers, non-temporal stores or per-machine tuning. An optimization enters only where leaving it out costs a measurable share of a proof and its simple form stays short.
- `crates/experimental_prover/` (`experimental_*`): the optimized prover. Performance work lands here.

Each tree, leaves first: `parallel` (thread pool), `primitives` (fields, transcript), `pcs` (NTT, Merkle, ring switch, WHIR), `keccak_gkr`, `lean_vm_core` (arithmetization, `cpu::execute`, `cpu::prove`, the tree's `isa::Prover`). They name each other through Cargo renames, so sources say `pcs::` and `fiat_shamir::`. `crates/lean_vm_core` below means either tree's.

Everything else exists once, leaves first:

| crate | role |
| ----- | ---- |
| `verifier` | the native verifier, the fields, `Proof` and its byte encoding |
| `keccak256` | Keccak-256 and its multi-way permutation |
| `fiat_shamir_prover` | the prover's transcript, for both trees |
| `isa` | the instruction set, `Program`, the `Prover` trait |
| `zkdsl_compiler` | zkDSL to ISA (`zkDSL.md`); its tests run the stable prover |
| `lean_xmss`, `lean_sphincs`, `lean_vrf` | the signature schemes and the VRF tree |
| `allocator`, `bench_harness` | jemalloc and the benchmark harness; never linked by a library |
| `lean_da` | Reed-Solomon blob encoding, commitments, membership vectors |
| `claims` | `AggregateClaims`, `OutputClaims` and their byte form |
| `aggregation` | recursive aggregation, generic over the prover |
| `sidecar` | proving and verifying in another process: protocol, client, server |
| `lean_vm` | the public API, the only crate a user imports |

- `guests/lean_ethereum.py`: the guest, in zkDSL.
- `bench/`: the benchmark CLI, `leanvm-bench`.
- `bins/leanvm-sidecar`: serves `aggregate` and verification over a Unix socket. Its `README.md` specifies the protocol.
- `bindings/`: language bindings of the schemes and the sidecar's client. A separate Cargo workspace: run cargo from `bindings/`, see `bindings/README.md`.
- `doc/leanvm/`: the LaTeX spec. `cd doc/leanvm && latexmk -pdf main.tex` builds into the gitignored `.build/` (delete it if latexmk fails oddly). Sections `body/01` to `10`, annexes `a` (ring switching), `b` (PCS), `c` (Keccak GKR), `d` (NTT). Run `make-drafts.sh` after adding, renaming or renumbering a section.
- `doc/lean_xmss/`, `doc/lean_sphincs/`: the schemes' specs.
- `formal/`: Lean 4 proofs in the random-permutation model, vendored from [Verified-zkEVM/leanerVM](https://github.com/Verified-zkEVM/leanerVM). `formal/Statement/` holds what is proved, `formal/statement.tex` what it does not compose to, `formal/AGENTS.md` the build and the gate (`formal/check-all.sh`).

Rules:

- Shared crates prove only through `isa::Prover` (`lean_vm_core::StableProver`, `lean_vm_core::ExperimentalProver`).
- `aggregation` derives the guest's constants and a child's witness from the stable tree (`lean_vm_core::leaf`, whose term order the guest's arrays follow).
- Prover crates contain no verifier, tests included: a verdict goes through `crates/verifier`.
- A new user-facing item is a re-export in `crates/lean_vm/src/lib.rs`, used in `crates/lean_vm/tests/api.rs`. A `pub` method users should not see is `#[doc(hidden)] pub fn __name`.
- `formal/`'s Rust helpers build against stable, except `whir-fold-table` (only experimental's `pcs` keeps the WHIR security search).

## What must change together

- **A protocol change**: both prover trees, the three verifiers, `formal/`. An optimization: experimental alone.
- **Rust that `formal/` transcribes** (the verifier, the guest, the schemes' hash inputs, the executor (both trees' `cpu/execute.rs`, in `formal/Statement/Prover/Execute.lean`), the compiler's hint format (`isa::export_hints`), `aggregation`'s witness streams (`node.rs`, `hints.rs`, `child.rs`, `deferred.rs`, in `formal/Statement/LeanVmGuestProver.lean`'s `honestPushes`), the wire encoding in `formal/lean_vm/LeanVM/Wire/Encoding.lean`): its Lean, in the same PR. CI's `lean-vm-formalization` fails until then.
- **The zkDSL compiler's accepted language or output**: its Lean front end, `formal/lean_vm/LeanVM/Guest/Source.lean` and `Expand.lean`. If the guest's bytecode changes, see "Changing the spec" in `formal/AGENTS.md`.
- **A new program in `crates/zkdsl_compiler/tests/programs/`**: its digest in `tests/suite/determinism.rs` (`GOLDEN`), the regenerated `formal/lean_vm/tests/LeanVMTests/Guest/Programs.lean` (`formal/lean_vm/scripts/regen-guest.sh`), the count in `tests/LeanVMTests/Guest/Data.lean`.
- **The layout** (`placements_of`, the schema): both provers and all three verifiers (`crates/verifier`'s `layout.rs`). `col_kappas` stays derived from `col_kappa_sources`.
- **A rename in the leanVM document**: both provers, `crates/verifier`, the Lean verifier and the guest.
- **The sidecar's protocol** (`crates/sidecar`'s `wire.rs`, `server.rs`) or the claims' byte form (`AggregateClaims::to_bytes`): `bins/leanvm-sidecar/README.md`.
- **The shared crates' public API, the sidecar's protocol or their dependencies**: `bindings/` (`bindings-ci.yml`), and `bindings/Cargo.lock` for dependencies.
- **EthLib's test vectors** (`tests/<crate>/ethlib/` in `lean_xmss` and `lean_sphincs`): both crates' `ethlib/sync.sh <ethlib-commit>`, same commit.

## Building and testing

```bash
cargo testall                     # release workspace tests
cargo clippyall                   # clippy, -D warnings
cargo docall                      # rustdoc, -D warnings
cargo fmt --all                   # max_width = 120
cargo machete --with-metadata     # unused dependencies
```

- Run anything touching the VM in `--release`.
- One test binary per crate: a new `zkdsl_compiler` integration test is a module of `tests/suite/main.rs`.
- `aggregate_two_to_one` is the fast end-to-end check.
- Slow checks are `#[ignore]`d, run with `-- --ignored --nocapture`: `print_whir_query_counts`, `print_whir_query_table`, `encoding_grinding_bits`.
- Heavy benches: `cargo bench -p <package> --bench <name>`, with `hash_batch` (`*_keccak_gkr`), `throughput` (`*_pcs`), `hash_throughput` (`keccak256`).
- Timing is the `tracing` span tree only: `--tracing` on the CLI, `BENCH_TRACING=1` on the benches. A new stage gets an `info_span!` (`stage!` in `lean_vm_core`), never an `Instant` behind an env var.
- Every pull request takes a conventional-commit title (`pr-title.yml`). A breaking change takes `!` (`feat!:`, `fix!:`): a change to a public API or a stored format (keys), and any change to what a proof is checked against, so that proofs made before it no longer verify or aggregate as children: the protocol, the proof's bytes, or the guest's compiled bytecode (the guest, its constants, or a `zkdsl_compiler` change to its output).
- An x86-only `cfg` arm never compiles on an Apple machine. Type-check it before pushing (`rustup target add x86_64-unknown-linux-gnu`):

```bash
RUSTFLAGS="-C target-cpu=znver4" \
  cargo check --release --workspace --exclude leanvm-bench --exclude leanvm-sidecar --exclude allocator --target x86_64-unknown-linux-gnu
```

Use `RUSTFLAGS`, not `CARGO_TARGET_*_RUSTFLAGS`, which would merge with `target-cpu=native`. A `compile_error!` in the arm confirms it is reached.

## Benchmarking

```bash
cargo leanvm-bench --prover experimental aggregate --xmss <n> --sphincs <n> --blobs <b>
cargo leanvm-bench --prover experimental recursion --n <children> --xmss-per-leaf <n>
cargo leanvm-bench --prover stable fibonacci --n <steps>
```

- `--prover stable|experimental` is required.
- `recursion` also takes `--sphincs-per-leaf`, `--blobs-per-leaf`, `--leaf-log-inv-rate`.
- Common: `--log-inv-rate` (1 to 4), `--repeat`, `--cooldown`, `--threads`, `--tracing`.
- Compare schemes and changes by the reported VM cycle counts.
- CI (`bench.yml`) compares every PR with its base on an x86-64 and an arm64 testbed. `.github/scripts/pr_comment.py --dry-run` prints the comment a run's artifacts would give.

## Allocator and thread pool

- Libraries impose no allocator. The CLI, the sidecar and the benches install `allocator::Jemalloc`.
- Experimental skips a buffer's zero-fill with `primitives::uninit_vec` or `filled_vec`. Stable never reads uninitialized memory: it writes a large buffer's first pass with the pool (`parallel::filled`, `parallel::map_collect`).
- Drop a large buffer where its last use ends.
- No rayon. One pool per tree, one tree per process: never add a second pool.
- Shared crates dispatch through `isa::Prover::map_collect`. `lean_da` encodes on one thread.
- Nested dispatch panics. A task of either pool dispatches on neither.
- The thread count is set before a pool starts, by `isa::Prover::set_num_threads` (`lean_vm::setup`, `--threads`). `1` is strictly sequential.

## Three verifiers, one protocol

1. **Rust**, `crates/verifier`: what `AggregateProof::verify` and `cpu::verify` run. No dependencies, `unsafe`, `core::arch`, `cfg(target_arch)` or threads.
2. **Lean**, `formal/Statement/LeanVmVerifier.lean`: the reference, and the trusted statement of the soundness proof. `formal/check-all.sh vectors` pins it against the Rust.
3. **Recursive**, `guests/lean_ethereum.py`.

Security and Fiat-Shamir:

- Every verifier message has at most `2^-125` round-by-round error after its grind (`SECURITY_BITS`). Outside the PCS's fixed grinds, an error of `N/|E|` grinds `ceil(log2 N) - 3` bits, none for `N <= 8` (`grinding_bits`).
- The PCS folds with the affine combiner of [CWYZ26] (ePrint 2026/2863), Annex B.
- `verifier::TAG` and every Fiat-Shamir label stay at `v1` until leanVM ships on Ethereum.
- `ProverState::add_scalar` and `Transcript::next_scalar` bind into the transcript. Never re-observe data that rode the stream.
- Grinding takes the smallest valid nonce, in parallel too. Exception: the Keccak GKR's `s` in `K` takes the next valid nonce (`ProverState::grind_sample`).

The Rust verifier:

- `verify_execution` checks a proof. `replay_unchecked` walks the same code and checks nothing.
- Every check sits behind `Transcript::checked`. Nothing else depends on the mode.
- Reading the proof is not a check: a Merkle path's position and sizes, and the stream's length, are pinned in both modes.
- `aggregate` does not verify its children. It replays them (`AggregateError::InvalidChild` if it cannot), and the guest rejects the rest as `AggregateError::ProvingFailed`. Call `AggregateProof::verify` on an unchecked child first.

The guest:

- Hints are untrusted: every hinted value must be pinned by a constraint.
- It verifies proofs of itself: `unified_guest` compiles it to a fixed point on its own size.
- The stacked-bytecode claim is not verified in-circuit. Each node batches its children's, and `AggregateProof::verify` discharges the root's.
- It accepts exactly what the native verifier does: every stack from `2^min_execution_stacked_log(kbc)` to `2^MAX_STACKED_LOG`, at every rate. One opening arm per size, the rate dispatched inside, so a rate's shape goes in a helper specialized on it.
- Every verifier rotates the opening's terminal point left by `INITIAL_FOLDING_FACTOR` before evaluating the basis (`whir::commit` documents the layout). Every other read of the point stays in round order.
- A failed `assert` is a write-once conflict naming the function and line. One that `had 0:0` can be a cell read before it was written.
- Guests are single-file. The compiler skips `from snark_lib import *`.

## Performance conventions (experimental tree, native verifier)

- **Memory bandwidth can bind**: cut memory traffic first. `primitives::stream::Stream` pays only where nothing reads the destination again before eviction. On Apple silicon it is a plain copy.
- **NEON is the width ceiling on Apple silicon**: a pure-width AVX-512 win does not port. NEON wants a butterfly at a time over whole rows, not register-resident tiles.
- **A `[F128; N]` in a NEON kernel spills**: keep quads as tuples or named values, arrays only inside `primitives::field::mul4`.
- **Rebuild or store an intermediate**: take the choice from `primitives::REBUILD_OVER_STORE`.
- **A hot NEON helper that is `#[inline(always)]` stays so**: a `#[target_feature]` function cannot be forced inline. Split a product's halves by hand, not with `array::map`. A helper that needs `unsafe` is an `unsafe fn` its callers wrap.
- **Zen 4**: 512-bit cross-lane moves are half-rate. Keep products within 128-bit lanes.
- **Zen 5**: the carry-less multiplier is scarce. Reduce with shifts and XORs (`gf2_64::reduce`) and count CLMULs, except in the scalar `F64` product (`gf2_64::x86_64::mul`).
- **`crates/verifier` is auto-vectorized**: on AVX-512, LLVM turns table lookups into gathers that lose to scalar loads, so check the x86 disassembly after touching a lookup. On `znver4` the SLP vectorizer slows the Keccak permutation, and `-C llvm-args=-slp-max-vf=2` measures the verifier without it.

## Writing conventions

- One symbol, one meaning across the leanVM document, defined in `preamble/macros.tex`. Check a letter is free first. A sumcheck challenge is `\fc`, `\rho` is the rate.
- Doc labels are an API: crates cite `thm:rbr`, `lem:colweight` and section labels. `body/NN-*.tex` prefixes match section numbers.
- Comments only where necessary, and concise.
- No measurement in a comment, a doc comment or this file. It goes in the commit message.
- No em-dashes or en-dashes in prose. Never hard-wrap prose in Markdown or LaTeX.
- Commit only tests useful against future regressions.
- Never commit what a script can write: gitignore it and generate it before use, as `formal/.gitignore` does. CI fails a pull request that adds a file over 1 MiB or commits an ignored one (`size.yml`).

## Env knobs

| var | effect |
| --- | ------ |
| `BENCH_TRACING`, `BENCH_REPEAT`, `BENCH_COOLDOWN` | `--tracing`, `--repeat`, `--cooldown` for the benches |
| `KECCAK_N_LOG`, `KECCAK_DEPTH` | keccak_gkr batch size, rounds between committed states |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`, `PCS_POINT_CLAIMS`, `PCS_RING_CLAIMS` | PCS throughput bench: size, rate, claims |
| `WHIR_NUM_VARS`, `WHIR_LOG_INV_RATE` | `print_whir_query_counts`'s shape |
| `DBG_PROF{,_DUMP}`, `DBG_LOOPS`, `DBG_DISASM`, `DBG_LOWER`, `DBG_PLACEHOLDERS` | compiler and guest-cycle attribution |
