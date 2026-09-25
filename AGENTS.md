# AGENTS.md

## What this is

A RISC-V (rv64im) virtual machine and the SNARK that proves its execution. Proofs are not zero knowledge. Every rv64im instruction is proven, plus one custom instruction, the BLAKE2s compression (`blake2s rs1, rs2`). A program is a guest's ELF file (`guests/`, Rust built for `riscv64im-unknown-none-elf`, loaded by `rv::Guest::from_elf`) or a text assembled by hand with `lean_vm::rv::asm`; a run is proven on a public input (four words, RAM's first) and an advice (a region of memory the prover fills), and its statement is the program's digest, the input and the output (`a0..a3` at `exit`). One run is one proof: a run whose witness exceeds one commitment (`pcs::MAX_MU`) is refused up front with `Trap::TooLong`, continuations being unimplemented.

- `doc/leanvm/` is the LaTeX project describing the machine ISA and the snark that proves it. Its root is `doc/leanvm/main.tex`; build it with `cd doc/leanvm && latexmk -pdf main.tex`, which writes to the gitignored `doc/leanvm/.build/`. Sections live in `doc/leanvm/body/`, numbered `01`..`08` plus the lettered annexes `a` (ring switching), `b` (the PCS), `c` (Flock), and `d` (novel basis and additive NTT), and every symbol is defined once in `doc/leanvm/preamble/macros.tex`. If latexmk fails oddly (a bibtex error, or a missing `main.log`) right after inputs are renamed or `refs.bib` is edited, remove `doc/leanvm/.build` and rerun; it has not reproduced on unchanged inputs. **Drafting one section:** each section file carries a `% !TeX root` comment pointing at its generated driver in `doc/leanvm/drafts/`, so the LaTeX build key (`F5`, or the extension's `cmd+alt+b`) compiles only that section, numbered as in the full document and with cross-references and citations resolved against `.build/main.aux`; in `main.tex` the same key builds everything. Run `doc/leanvm/make-drafts.sh` after adding, renaming or renumbering a section.
- The one hash function is BLAKE2s, in `primitives::hash`: scalar, streaming, keyed, and a lane-transposed batched form for the PCS Merkle tree. The VM's compression instruction is the generic gate-list circuit `rv::circuits::blake2s`, proven like every other class; `flock::hash` is the hand-optimized circuit of the same function with its own witness kernels, kept as flock's throughput benchmark and used by nothing else. Moving the precompile onto it is the known speed-up if hashing ever dominates a workload.

## Layout

Dependency order, leaves first:

| crate             | role                                                                   |
| ----------------- | ---------------------------------------------------------------------- |
| `parallel`        | thread pool (below)                                     |
| `zk_alloc`        | proving arena (below)                                    |
| `primitives`      | field kernels (NEON/AVX), bit transposes, multilinear helpers, streaming stores, `bench` |
| `fiat_shamir`     | VM-native `FiatShamirState` + prover/verifier transcript                |
| `pcs`             | additive NTT, Merkle, ring switch, stacked WHIR                    |
| `flock`           | batched R1CS over GF(2): zerocheck + lincheck; gate-list circuits over word ports (`circuit`), the u64 adder and multiplier in them (`arith`), the BLAKE2s circuit (`hash`) |
| `lean_vm`         | the RISC-V machine (`rv`: decoder, class semantics and circuits, interpreter, assembler, ELF loader) and its arithmetization: tables, bus, constraints, `cpu::prove`/`verify` |

`src/lib.rs` is the public API and the only thing a user imports: every crate above is `publish = false`, so a new user-facing item is a re-export there. `src/main.rs` is the CLI (`fibonacci`, the benchmark, and `guest <elf> --input a,b,c,d --advice ...`), `tests/api.rs` the end-to-end use of the API.

`guests/` is a separate cargo workspace (its own toolchain file, nightly with `rust-src`, and `.cargo/config.toml` targeting `riscv64im-unknown-none-elf` with `-Zbuild-std=core`): the runtime crate `rt` (`_start`, `input()`, `advice()`, `output()`, a `Blake2s` hasher over the custom instruction through `.insn r`, a panic that is `unimp`), the guests, `link.ld` fixing the memory map, and `build.sh`, which refreshes the checked-in ELF fixtures in `guests/elf/` that `lean_vm/tests/verifiers/guests.rs` loads. **Rerun `build.sh` after touching a guest or the runtime**: nothing rebuilds the fixtures, so CI would keep testing the old ELF and say nothing. The nightly channel floats, so the fixtures are not reproducible byte for byte across toolchain updates, which is why they are not diffed in CI. The root `.cargo/config.toml` scopes `target-cpu=native` to `cfg(not(target_arch = "riscv64"))` because the guests inherit it. Atomics are why the target is `im` and not `imac`: the builtin target has no compare-and-swap, so a dependency needing one does not compile.

## Building / Testing / Formatting

- `.cargo/config.toml` pins `-C target-cpu=native` and `-D warnings` for rustdoc
- always run in `--release` mode any test or benchmark touching the VM
- **One test binary per crate, not one per file** (`lean_vm/tests/verifiers/main.rs`). Exception: a test opening an arena phase (`lean_vm::init_prover`) needs its own binary. Phases are process-global, so two in one process reclaim each other's `ArenaVec`s and the symptom is a proof that stops verifying, never a crash (`tests/api.rs` is that binary, and `tests/no_arena.rs` the one that must never enable the arena).

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

Heavy benches and measurement harnesses are `#[ignore]`d; run by name with `-- --ignored --nocapture`: `hash_batch_prove_verify`, `add_wrapping_prove_verify`, `mul_wrapping_prove_verify`, `mul_widening_prove_verify`, `pcs_throughput`, `multithreaded_throughput`, `print_whir_query_counts`, `print_whir_query_table`.

## Benchmarking

The benchmarks we care about:

- `cargo run --release -- fibonacci --n 2000000 --log-inv-rate 1 --repeat 3` (Fibonacci mod 2^64, on registers)
- `cargo run --release -- guest guests/elf/hash.elf --input 50000 --repeat 3` (the precompile, from a Rust guest)
- `BENCH_REPEAT=3 FLOCK_N_LOG=18 cargo test --release -p flock --test batch_proving_hashes -- hash_batch_prove_verify --exact --nocapture --include-ignored` (flock alone, on its hand-optimized circuit)

## Read-write arrays

The registers, RAM and the advice are read-write, by timestamped offline memory checking (`doc/leanvm` §sec:memchan). What to keep in mind before touching it:

- **The clock rides the state tuple**, `(pc, ts)`, and advances by the row's stride (`ClassSpec::stride`: 4, or 18 for a hash row): a row's access in slot `k` carries the timestamp `g^k·ts`, which is what lets one row touch the same cell twice (`add a0, a0, a0`). Slots are `rs1` at 0, `rs2` at 1, the RAM access at 2, `rd` at 3; a hash row has no `rd` write and its sixteen block words take slots 2 to 17. The run starts at cycle 1, because a seed is stamped `g^0` and an access must be strictly later than the one before.
- **Strictness is the soundness.** An access pulls `(addr, prev, old)` and pushes `(addr, g^k·ts, new)`, with `prev·lo = g^k·ts·hi`, where `lo` and `hi` are read off two uncommitted range arrays (`{g^(j+1)}` and `{g^(-2^16·j)}`, 2^16 entries each). The `+1` in the low array is the strict `<`: with a gap of zero a read pulls the tuple it pushes and returns anything.
- **Padding rows have clock zero**, and zero is no power of `g`: their state tuples close around a fill block (`0·g^s = 0`), their accesses are forced to `prev = 0` and cancel themselves, and nothing they flush can meet a tuple of the run. They are written out by `cpu::execute`, not executed, and touch no memory. Any new table has to keep this true: every memory tuple's timestamp must be `g^k·ts` or the committed `prev`, nothing else. **The verifier's notion of a padding row is `ts = 0` and nothing else**, so a prover may close its zero-clock rows around any cycle of the program's own control flow rather than a fill block; that is inert too, and the fill blocks exist to make the fill exact, not to make it safe. What makes `prev = 0` is the gap check against the range arrays, whose entries are all nonzero, so a range array that ever held a zero would break this.
- **Two committed columns per array**: what it holds after the run, and each cell's last timestamp. What it holds before is public for the registers (zero) and RAM (`Coord::Sparse`: the input, the image, zeros, evaluated in time proportional to the image), and a third committed column for the advice (`ADV_INIT`), which is the prover's. RAM and the advice share `SEP_MEM`; they never share an address, every region's base being a multiple of its largest size (`rv::TEXT_BASE`, `rv::ADVICE_BASE`, `rv::RAM_BASE`), so word `z` of a region sits at `base ^ (z << 3)` and the seed block's address is the free `Coord::IntIndex`.
- **A padding row rewrites what it writes**, its `old` column set to its `new` (the register write's `vd_old`, the hash's `out_old`), which is why a row can never update a cell in place: the hash reads `h` and writes `out` in different words, since no chaining value is a fixed point of the compression.
- **A gap is below 2^32**, and a cell's first access is measured from zero, so a run is capped near 2^30 cycles. The executor asserts it.
- `a_stale_read_unbalances_the_bus` is the soundness regression test (a forged run that serves an overwritten register), `a_forged_load_unbalances_the_bus` its RAM counterpart, and `leaf::unmatched_leaves` (test-only) names the tuples a forged run leaves unmatched, which says more than a failing proof. `lean_vm/tests/verifiers/programs.rs` holds the hand-assembled programs checked by both verifiers, `guests.rs` the Rust guests.

## The RISC-V machine

`lean_vm::rv` is the machine, `lean_vm::tables` and `lean_vm::cpu` prove it. What to keep in mind:

- **The program is public, so decoding is free.** `rv::decode` turns each word into an `Entry` once: an instruction class, a `flags` word selecting what the class's one function does, the three register cells the row touches, the immediate already sign-extended, the branch target, and the `link` and `jalr` selectors. `LUI`, `AUIPC` and `JAL` fold to constants, `ECALL` is a jump to the halt slot, and everything rv64im does not define (reserved shift encodings, `EBREAK`, CSRs) is an illegal entry. The bytecode lookup returns those fields; no table ever decomposes an instruction word. An entry whose class has no table has tag zero, which no row can read.
- **The statement is about the decoded table**, so the rules that make it RISC-V are checked where a table enters, on both sides (`rv::Entry::is_well_formed` in `Program::new`, `check_bytecode` in Python): two registers below 32 are read, the cell written is in `1..=32`, the successor is `pc + 4`, the flags are ones the class defines. The proof system itself is sound for any table.
- **`x0` is hardwired by the decoder.** Every row reads two registers and writes one. An instruction with fewer reads `x0`; one with no destination, or with `rd = x0`, writes `SINK` (cell 32), which nothing reads. So cell 0 is never written, and its seed is zero.
- **Registers are a read-write array of their own**, under their own separator `REG`, so that loads and stores cannot reach them: 64 cells, a public zero seed, committed final values and timestamps, the same clock, gap check and range arrays as memory. A register's number comes straight from the bytecode, so an access needs no address arithmetic.
- **No integer addition happens on the bus.** A load's or a store's address is its circuit's word, with the misalignment bits ORed back in (`semantics::bus_address`), so a misaligned or out-of-range access names no seeded cell and the bus does not balance; a hash row's block words are at `v1 ^ 8k`, which is `Coord::Sum(Col(v1), Const(8k))`, the XOR being the sum in `K`. The `EXP` lookup of the leanISA days is gone.
- **State is `(pc, ts)`**, `pc` the real byte address. Instruction `z` sits at `TEXT_BASE ^ (z << 2)` and the bytecode block's address coordinate is `Coord::IntIndex { base, shift }`, whose MLE is linear. Everything sits inside one 2 GiB window and below `0x7FFF_F800` for the code models' sake. A computed or misaligned jump target needs no check: the next row's bytecode read finds no entry.
- **A trap is the absence of a proof** (`rv::Trap`): an illegal or unmapped `pc`, a misaligned or unmapped access, an `ecall` that is not `exit`, the cycle cap, and `TooLong`, a run that would not fit one proof. An illegal word follows the text, so a run falling off it traps instead of sliding into the padding blocks or the halt slot.
- **The halt is an exit.** The run ends on the last slot of the padded text, which is never executed. The verifier claims `a7 = 93` and `a0..a3 = output` on the committed final registers at the Boolean points naming them; the output seeds the transcript with the program's digest, which covers the decoded table, the entry and halt `pc`, RAM's and the advice's sizes and the image. Nothing the program fixes is read from the prover; the Python verifier gets the same things through `public.bin`.
- **The precompile is a class like the others** (`Class::Hash`, table `HASH`): `blake2s rs1, rs2` (custom-0 opcode `0x0b`, `funct3 = 1` on the final block, `rd = funct7 = 0`) compresses the 128-byte block at `rs1` (`h` in words 0..4, the result written to 4..8, the message in 8..16, `rv::hash`), with the counter in `rs2` and the finalization word in the bytecode's flags; a base that is no word address traps, an unaligned one permutes the words deterministically (a guest bug, not a forgery). Its row has no `rd`, `imm` or `out` columns (constants `SINK` and 0 in its bytecode tuple), eighteen accesses and a stride of 18.
- **The interpreter is the reference** (`rv::Machine`), tested against an executor written from the specification on byte-addressed memory that shares no code with it. `cpu::execute` is that interpreter plus the memory argument's bookkeeping. `riscv-tests` is still owed: no RISC-V C toolchain on the dev machine.

## Instruction classes and their circuits

Addition with carries, comparisons, shifts, AND/OR, multiplication and division are Boolean relations no degree-2 identity over `K` expresses, so each instruction class is a Boolean circuit proven by flock (`doc/leanvm` Annex C), and a table only does plumbing:

- **One generic table, specialized by a `tables::ClassSpec`**: the state step, the bytecode read, two register reads, one register write (unless `Ram::Block`), and the class's RAM accesses (`Ram::None`, one cell `Read` or `Write`n at the circuit's address, or the hash's `Block`), with `npc = pc4 + taken·dt + jalr·(out + pc4)` and `rd <- out + link·(out + pc4)` as degree-2 bus forms for a class with control flow. A new class is a spec, a circuit in `rv::circuits`, its reference function in `rv::semantics`, a no-op word in `cpu::filler`, its decoding, and the same in Python (`Table(...)` in `TABLES`, its gate list, its flags in `check_bytecode`).
- **Every word the circuit reads or writes is a virtual column** of the table, living in the class's packed witness (`Q_BASE + t`, one committed column per table, instance `j` being row `j`): `flags` and `imm` from the bytecode tuple, `v1` and `v2` from the register tuples, a load's `address` and `cell`, a hash's block words, `out`, `taken`. The bus is the whole binding. `class_flock::Prepared::build` asserts that what the circuit computed is what the interpreter did. A hint (`DIV`'s quotient and remainder) is a port in no column, and what a circuit asserts (`Word::Bad`) rides bytecode slot 13, where the program is zero.
- **Circuits are gate lists over word ports** (`flock::circuit`): inputs, outputs, the constant, then products in the order they are made. A port bit with no gate is an empty row, hence zero, which is what makes a one-bit output such as `taken` a 0 or 1 field element: give such an output a word to itself and never put a free wire on its spare bits. What Rust and Python must agree on is the port layout and the ORDER PRODUCTS ARE MADE IN; XOR order is free. `alu_is_its_reference` pins a circuit to its reference function, and the end-to-end tests pin the Python mirror.
- **One reduction per class, one opening for all**: zerocheck plus lincheck per table, in table order after the exit claims, each leaving a claim on its own witness; `pcs::stack_open` takes one ring-switched region per witness, all under one map challenge.
- **Batch floors.** Flock needs eight instances and a zerocheck cube of `2^13` bits (`class_flock::n_blocks_log`); padding rows supply them, as honest instances on zero registers.
- **Witness generation is the generic walk of the gate list, bit by bit**, and is the prover's largest single stage. A word-arithmetic or bit-sliced generator per circuit is a known follow-up, the hash's `flock::hash` kernels being the model.
- **Circuit sizes are structure, not measurements**: `k_log` per class is pinned in its `ClassSpec` and asserted against the built circuit; product counts are in `doc/leanvm` Annex C.

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

## Two verifiers, one protocol

The same verification algorithm is written out twice, in two languages. Any change to the snark protocol has to land in both.

1. **Rust**, `lean_vm::cpu::verify`. The native verifier.
2. **Python**, `python-verifier/verifier.py` (no dependencies), for readability and simplicity. Pinned by `lean_vm/tests/verifiers/python_verifier.rs`, which feeds it the raw proof `cpu::verify_to_raw` returns.

## Conventions that bite

- **The prover can be memory-bandwidth bound.** Reduce memory traffic before assuming that more workers or fewer instructions improve throughput. `primitives::stream::Stream` publishes a buffer without the read-for-ownership an ordinary store pays, but ONLY where nothing reads the destination again before it is evicted. Where a consumer follows in the same pass, the fetch it avoids becomes that consumer's miss: fold kernels earn it by building their round message from registers, or by folding into an L1 stage first (`whir::fold_and_msg_blocks`). That fetch is an x86 cost only: on Apple silicon a store-only fill already sustains what a read-only pass does and `STNP` measures identical to `STP`, so `Stream` is a plain copy there and the L1 stage earns its keep for the read locality alone, which is still better than writing through.
- **NEON is the width ceiling on Apple silicon**, so an AVX-512 win that is purely width has no counterpart: the M4 has no SVE, and its SME2 is streaming-mode matrix work with no polynomial multiply. What does port is *shape*. A fused NTT pass wants a butterfly at a time over whole rows, not the register-resident tile the AVX-512 arms use: they transpose anyway and want to pay for it once per pass, while NEON transposes nothing and a tile leaves only its own width of independent work to cover the reduction's dependent PMULL folds, where a row leaves the whole lane count. Measured both directions: the tile costs the extension NTT, and costs the base encode's `Commit` again.
- **A `[F192; N]` in a NEON kernel is a memory object, where on AVX-512 it is the register.** Four tower products are four independent PMULL chains wanting most of the 32 vector registers, so an array of them spills and the spill costs more than batching the products saves; the same array is free on AVX-512, where the quad IS one register. Keep the quad as a tuple or as named values and let arrays exist only inside the batched-product helper, on the target that wants them (`flock::zerocheck::multilinear`'s `mul_quad`). The symptom is indirect, so suspect the shape rather than the arithmetic: the products measure the same either way, destructuring the results changes nothing, and forcing the helper to inline recovers almost none of it.
- **On Zen 4, 512-bit cross-lane data movement is half-rate** (every 512-bit shuffle is two 256-bit uops), so packing scalars into vector lanes with `vpermi2q`/`vpermq` and extracting with `vextracti64x4` loses to the scalar moves it replaces. Widening the arithmetic still pays: `mul4` beats the same products issued one at a time. Prefer kernels where both qwords of every 128-bit lane carry a product and nothing crosses lanes.
- **On Zen 5 the carry-less multiplier is the scarce unit, and a CLMUL costs the same at 128, 256 or 512 bits.** Spend it on products only: reduce modulo `x^64 + x^4 + x^3 + x + 1` with shifts and XORs (`gf2_64::reduce`, or its lane-wise twin in the batched kernels), not with the two CLMULs by `0x1B` that NEON prefers, and count CLMUL instructions rather than products when sizing a kernel. The exception is the scalar `F64` product (`gf2_64::x86_64::mul`), whose reduction would cross to integer registers and back: on Zen 4 that loses to the two CLMUL folds, which stay in the vector register. Masked or 512-bit loads of `F192`s passed by value defeat store-to-load forwarding, so the batched kernels pack from scalars.
- Use comments only when necessary: uncommented but readable and simple code is better than commented slop. And when you use comments, be concise.
- **Never put a measurement in a comment, a doc comment, or this file.** Timings, throughputs, percentages and speedup factors go stale the moment the code, the compiler or the host changes, and nothing ever rechecks them, so they end up asserting something false with the authority of a comment. The commit message is where they belong: it is dated, it is immutable, and it says what was true when the change landed. A comment may say which way a result went and why (that a tile lost to whole rows, that one reduction beat another), never by how much.
- Commit tests only that are useful in the future, to prevent regressions / failures. Don't add trivial tests that will always pass.
- Simpler is better.
- **Fiat-Shamir:** `add_scalar`/`next_scalar` bind into the Fiat-Shamir state as a side effect. The public statement seeds the transcript at construction; the transport exposes no separate observe operation. Never re-observe data that rode the stream, which silently desynchronizes the two sides.
- **Prover and verifier derive the layout identically** from announced sizes. Changes to `placements_of` or the schema land on both sides. `col_kappas` is derived from `col_kappa_sources` rather than written out twice, so the two can no longer drift; keep it that way.
- **The L0 lane fold binds the committed witness's TOP `INITIAL_FOLDING_FACTOR` variables**, because lane `l` of the interleaved commitment is the stack block `q[l·2^(μ-k) ..)`. That makes the witness's zero tail whole lanes, so `whir::commit` encodes only `StackShape::n_lanes` of them, and the opening's dense weight, its first `k` sumcheck rounds and the stack allocation shrink with it. **A leaf image is still `2^k` words**, the absent lanes contributing their codeword's zeros, but those zeros LEAD it (codeword lane `t` is stack block `n_lanes-1-t`): their whole 64-byte blocks are then one shared chaining value (`hash::zero_prefix_state`) the committer hashes once rather than per leaf, and only the image's tail rides the proof, so `PrunedMerklePaths` stores `n_lanes` words per L0 row while `RawMerklePath` (what the Python verifier reads) carries the full image. Both verifiers therefore derive `n_lanes` from the announced layout to read a row. Since `mu = log2_ceil(placed)`, `n_lanes` is always in `[2^(k-1)+1, 2^k]`: the encode saving caps near half, the hashing saving is quantized to whole blocks of 8 lanes, and both are ~0 just above a power of two. The cost is that fold challenges arrive in round order while every transparent weight is written in witness coordinates, so both verifiers rotate the terminal point left by `k` before evaluating it (`whir.rs` before `eval_b_at`, `verifier.py` before `evaluate_basis`). Anything else that reads the opening's point (per-level induced weights, the residual) stays in round order.
- **One symbol, one meaning, across the whole leanVM document.** All notation is defined in `doc/leanvm/preamble/macros.tex`: define a new macro there rather than inline, and check the letter is free first. Annex B's "Symbols" table maps its letters back to WHIR/Ligerito/BCHKS25, so read it before renaming one. A sumcheck round challenge is `\fc` everywhere, which is what keeps `\rho` free for the rate; `r` is the point a claim is made at, not a challenge. **A rename in the document is a rename in the implementations**: the Rust prover and verifier and `python-verifier/verifier.py` name their variables after the document's symbols, so the three have to move together.
- **Doc labels are an API.** `crates/pcs` cites `thm:rbr` and `thm:mca-johnson` by name and several crates cite `doc/leanvm/main.tex` sections, so renaming a label breaks those pointers with nothing to catch it. `doc/leanvm/body/NN-*.tex` prefixes match section numbers, so inserting a section renumbers the rest.
- **No em-dashes or en-dashes in prose**, anywhere a human reads it: docs, LaTeX, comments, commit messages. Restructure with a comma, colon, parentheses, or two sentences.
- **Never hard-wrap prose in Markdown or LaTeX.** One paragraph is one line; let the editor wrap it. Artificial line breaks make every later edit a reflow, so diffs show rewrapped lines instead of changed words. Applies to `.md` and `.tex` alike; code blocks, tables and list items keep their own line.

## Env knobs

| var                                                                                                     | effect                                           |
| ------------------------------------------------------------------------------------------------------- | ------------------------------------------------ |
| `LEANVM_NUM_THREADS`                                                                                    | performance-worker count; `1` = sequential       |
| `LEANVM_PROFILE`                                                                                        | per-stage prover timings                         |
| `ZK_ALLOC_STATS`                                                                                        | arena peak/phase, high water, overflow           |
| `ZK_ALLOC_POISON`                                                                                       | fill released arena blocks, to catch use-after-free |
| `BENCH_REPEAT`, `BENCH_COOLDOWN`                                                                        | `--repeat`/`--cooldown` for `#[ignore]`d benches |
| `FLOCK_N_LOG`, `FLOCK_PROVE_TRACE`, `FLOCK_ZC_TIMING`, `LINCHECK_TRACE`                                 | flock batch size, stage traces                   |
| `PCS_LOG_N`, `PCS_LOG_INV_RATE`, `PCS_SAMPLES`                                                          | PCS throughput bench                             |
| `WHIR_TRACE`, `WHIR_NUM_VARS`, `WHIR_LOG_INV_RATE`                                          | WHIR NTT/Merkle split                        |

## Side notes

- Grinding chooses the smallest valid nonce, including in parallel.
