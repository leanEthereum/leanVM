# Iteration log

One section per change to the image, measured from a green tree: what the change touched in the binary, what it rebuilt, and what it cost to repair the proofs.

## I1: `Bump::alloc` aligns every block to 8 (2026-11-20)

**Change.** `guest/src/main.rs`: `NEXT.next_multiple_of(layout.align())` became `NEXT.next_multiple_of(layout.align().max(8))` (3 lines with the doc comment; `guest/ADAPTATIONS.md` 2 lines). Reason: with an alignment below 8 a block could start inside the doubleword that ends the previous one, and `finish_grow`'s `memcpy` would then rewrite a doubleword below `NEXT`, which `Env.Frame` (doubleword-granular) forbids, so `FinishGrowSpec` could not be proved. Only the start is aligned; `NEXT` is still the block's end, so `AllocPost`'s third conjunct stays an equation.

**Binary.** `scripts/regen.sh`: 63.2 CPU-s (58.8 user, 4.4 sys), 59 s wall. New sha256 `d58fd6eb…43aa`. Templates: 75 changed, 155 unchanged, 0 added or removed; 228 link files rewritten. The 75 are not the allocator's callers' own code changing: every caller asks for an alignment of at most 8, so LLVM (fat LTO) drops `alloc`'s alignment argument altogether. `alloc` now takes the size in `a0` (it was `a1`, after the alignment in `a0`), and every function that allocates (directly or through an inlined `try_allocate_in` fast path: `ext_row` now calls `alloc` itself) changed its call sequence. So a one-line change of a leaf's semantics changed its ABI and a third of the templates. This is the design's risk (3), interprocedural rewrites making contracts caller-dependent, observed: dead-argument elimination across the whole program. The frozen config (`inline(never)` for verifier functions) does not cover `alloc`, `core` or the allocator's argument list.

**Link step.** `lake build Rv64mc.Gen`: 1,435 CPU-s (1,134 user, 301 sys), 116 s wall, 307 modules, peak 2.3 GB per module (shared host, load 15 to 25).

**Proofs.** Full `lake build` afterwards: 1,450 CPU-s, 12 min 43 s wall, of which 756 s one other family's unfinished module (`Proof/Field/KInv`, untracked, failing on its own `sorry`s). Rebuilt and green without edits: `Proof/Runtime/{MemWrappers,InputWord,Memcmp,GrowOne,GrowOnes,GrowAmortized}`, `Proof/Multilinear/{Dot,PolyEval,ScalerMul,ScalerNew,IndexMle,PaddingWeight}`, `Proof/Transcript/{Finish,Next}`, `Proof/Hash/DigestFromHalves`, `Proof/Bytecode/IsValidEncoding`, `Proof/Keccak/Mem`, the tables `Table/{Transcript,Multilinear,Hash,Bytecode}`, `Final/End`. Failed: only modules with their authors' `sorry`s, none because of the change (`ScaledMul`, `Duplex`, `SelectorPoint`, `Absorb`, `OnStack`, `LinearTranspose`, `KInv`). Of the 75 changed templates most have no proof yet, so this says little about the proved ones' sensitivity beyond `alloc` itself.

**Repair.** `Spec/Runtime/Alloc.lean`: 13 lines changed (the precondition is now the size in `a0`, below `2^63`; the result is a multiple of 8 instead of the alignment; the size is read from `a0`). `Proof/Runtime/Alloc.lean`: 42 added, 37 removed (a new rounding lemma for the mask-by-7 code, the old remainder-based one gone, the overflow check the code no longer makes covered by the size bound), re-proved in 11.3 CPU-s (`lake env lean`, imports included). Caller proofs edited: none of mine. `Proof/Layout/Term.lean` (another family, the one caller of `AllocSpec` with a proof) was written against the new template and spec while this ran and builds.

## Benchmark C0 to C5: re-proving after a verifier change (2026-11-20)

**Harness.** `scripts/iterate.sh PATCH [--label L]` copies `out/bench/base` (made once by `iterate.sh --init`: `git archive` of `formal/rv64mc`, `formal/Statement` and `crates/verifier` at one commit, `.lake/build` copied and `.lake/packages` hard-linked from this project, then built warm) to `out/bench/L`, applies the patch there, runs the copy's `regen.sh` and `type-layouts.sh` with `VERIFIER_SRC` at the copy's verifier, `elf-diff.py` against the old image, then `lake build Rv64mc` through a `lean` that records each module's CPU time (`iterate.py`, at most 6 modules at once), then `rv_sweep` on each changed template; `iterate.sh --rebuild L` repeats the build after edits in the copy. Rows in `notes/iteration-bench.tsv`, patches in `bench/patches/`. CPU seconds are user plus system of every `lean`; the build's own figure adds Lake. Shared host, load 15 to 30.

**Tree.** Copy of `8b32b983d`: 66 proof files, 74 contracts linked at the image in `Table/`. The base's warm build cost 750 CPU-s (modules whose sources differed from the shared build); C0 then rebuilt nothing.

| change | templates | link CPU-s | proof modules rebuilt (spec, model, table, final) | failed | repair | total CPU-s (wall) |
| --- | --- | --- | --- | --- | --- | --- |
| C0 none | 0 | 0 | 0 (0) | 0 | none | 194 (172 s): regen 59, layouts 99, Lake's check 37 |
| C1 `eq_eval` `x + y` to `x * y`, with `eqEval` and `eqEvalRust` | 1 | 913 | 47 (111) | `Proof/Multilinear/EqEval` | 1 file, 26 lines removed, 29 added, 3 compiles, about 3 min; rebuild 32 CPU-s | 2,751 (584 s) |
| C2 `MerklePath::root` rewritten, Rust only | 1 | 881 | 0 (11) | none | none | 1,245 (380 s) |
| C3 a never-called function kept at the start of `field.rs` | 1 added | 909 | 0 (9) | 8 `Table` modules | function indices: 127 lines in 10 tables by `scripts/renumber-tables.py`, 3 rebuilds 107 CPU-s, about 3 min | 1,354 (413 s) |
| C4 `Sponge` fields `state`, `pending` swapped, Rust only | 5 | 894 | 56 (80) | `Proof/Transcript/Common`, then `Absorb`, `Sample` | 4 files, 21 lines, 4 rebuilds 472 CPU-s, about 9 min | 2,792 (658 s) |
| C5 `1135c5255` reverted (5 functions, 2 of them proved and removed) | 4, 1 added, 4 removed | 1,003 | 1 (7) | 16: the 2 removed functions' template and link modules (4), their 2 proofs, 1 importer, 8 tables, `Proof/Runtime/Drop` | tables renumbered, 2 proofs and 2 specs deleted, 1 lemma moved: 74 CPU-s; `Drop` and the Model's mirror left (below) | 1,461 (420 s) so far |

**C1.** The template changed shape (frame 64 instead of 48, two calls to `E::mul` per pass, accumulator in `s1`/`s0`, loop head at 30 instead of 28). The Statement edit rebuilt everything that imports the Model (20 Model modules, 78 specs, 47 proofs); only `EqEval` failed, at its own fold lemma. Repair: `acc` and `acc_succ` to `1 + x * y`, `step_limbs` with the inner product, the loop invariant's registers, frame and six saved stores, `body_val`'s operands, the head index and `64 + needM`. `Table/Field` took the new frame without an edit (`decide`). Class: statement and mirror change, then the machine-code proof of the changed function. No other proof changed.

**C2.** No proof imports the template; only the link step, the tables (they import every `Link` module) and `Final/End` rebuilt.

**C3.** Pure relocation: modulo addresses no function changed, but the new function is index 18 of `liftProg`, and the tables state each contract at a literal index, so every table with an index of 18 or more failed. No proof was rebuilt. Class: the tables' literal indices (fixed by a script; the tables should take indices from `Gen/Index` by name).

**C4.** `Layouts.lean` changed (4 lines: `pending` 24, `state` 120), the five `Sponge` methods' templates changed, and everything importing `Gen/Layouts` rebuilt. Failures: `Spec/Transcript/Repr` defined a slot's size as `(n_pending - pending) / 4`, which held only while `pending` sat just before `n_pending` (a spec assumption about field adjacency; now `E.byteSize + 8`); `Proof/Transcript/Common` and `Absorb` wrote the slot's offsets as literals (224, 232, 240, now 24, 32, 40) and `Sample` the state's (24, 32, now 120, 128); and the new `absorb` stores the slot's high limb before the low one, so `pushMem` took the new store order. Class: spec representation assumption, layout literals in proof text, store order chosen by the code generator.

**C5.** Template churn beyond the 5 source functions: the `Vec<Table>` drop glue was inlined into `drop_in_place::<Layout>`, an iterator `next` disappeared, `expect_failed` appeared. Failures: the proofs of the two removed functions (`Layout::committed`, `is_output_lane`) and their table entries (deleted), `Proof/Bus/OnStack` (imported `Committed` for one address lemma, moved), the tables (indices again), and `Proof/Runtime/Drop`'s `layout_ok`, whose template now holds the inlined loop over the tables (frame 32, a loop head; its old callee `drop_in_place::<Vec<Table>>` was a hypothesis, never proved). Left after about 20 minutes: `Drop`'s loop lemma (an attempt stalled on an arithmetic side lemma), and the Model: `model-drift.sh` flags `layout.rs` and `lib.rs`, whose mirrors (`placementRust`, `buildLayoutRust`, `LayoutRust.committed` in `Model/Walk`, `verify_keccak_batch`'s bound) no longer match the Rust. Nothing in the build fails for it, because no proof of `build_layout`, `walk` or `verify_keccak_batch` exists yet: the mirror is checked only by the drift script.

**Sweep** (`rv_sweep` on each changed template, imports included, about 5 CPU-s of each): C1 6, C2 6, C3 6, C4 31 (5 templates), C5 100 (`walk` 52, `build_layout` 30).

**Observations.** The link step is the floor of any change, 880 to 1,000 CPU-s (every `Link` module imports `Words`), plus about 160 CPU-s to regenerate. Proofs are rebuilt only when what they import changes: a Rust-only change to an unproved function rebuilds no proof (C2), a relocation none (C3). A Statement or Model edit rebuilds every Model-dependent module (C1, 2,560 CPU-s) and a type-layout change every `Layouts` importer (C4, 2,160 CPU-s). The proofs that broke were the changed function's own (C1), proofs with layout literals or a spec relying on field adjacency (C4), proofs of deleted functions and a function into which the compiler inlined new code (C5); the tables broke on every added or removed function (C3, C5).

## I2: contract-framework change, the stack pointer 16-aligned (2026-11-20)

**Change.** A change to the contracts, not to the verifier or the image: `Holds.pre` (`Core/Holds.lean`) gains a last conjunct `top.toNat % 16 = 0` (the RISC-V ABI's alignment, which `_start` sets with `li sp, 0xbffffff0`), so that a function can read back as doublewords the bytes it wrote into its stack buffers. As the last conjunct it leaves every `hpre_k` name a proof uses unchanged. `Holds.call` and `Holds.pre_call` (`Core/Repr.lean`) take the callee's alignment as one more argument; `Final/Start` proves `main`'s by `decide`. `rv_sym` closes a callee's alignment from the caller's (`Sym.alignGoal`, `Tactic.align_off`: `top - k` with `k` a multiple of 16), so `rv_auto` proofs of straight-line code needed no edit.

**Proofs.** 23 files changed outside the tactic, each by threading the fact, no proof restructured, no statement's meaning changed (lines added, removed):
- `rv_auto` proofs whose loop lemmas call functions inside the loop: the loop lemma takes `(hal : top.toNat % 16 = 0)` (or `hsp16` where `hal` was taken), its caller passes `(by assumption)` or the `hpre_k`: `Multilinear/{Dot 2/2, EqEval 2/2, IndexMle 2/2, PaddingWeight 2/2, PolyEval 2/2}`, `Field/{EPow 3/3, KInv 5/4, ScaledMul 2/2}`, `Whir/{Frobenius8 2/2, RingPsi 2/2}`, `Bytecode/IsValidEncoding 2/2`, `Keccak/LinearTranspose 5/4`, `Transcript/Duplex 2/2`.
- `lsym` proofs that destructure `Holds.pre` or build a callee's: the pattern names the new conjunct, the construction adds it (`by simpa [updReg_apply, hsp] using hal`, or `omega` from the frame size): `Runtime/{Forward 4/4, Panics 4/4, Alloc 2/1, InputWord 2/1, GrowOne 7/4, GrowAmortized 4/4}`, `Core/Example 3/2`.
- The framework: `Core/Holds 6/4`, `Core/Repr 3/3`, `Final/Start 1/1`, `Tactic/Heap 7/0`, `Tactic/Sym 8/7`.

`Bus/OnStack`, first failing on a callee's alignment goal under a `need` that is not a numeral, passed once `alignGoal` stopped requiring the frame's size (the alignment of `top - k` needs `k` a multiple of 16, not `k ≤ need`).

**Cost.** Full `lake build Rv64mc` after the change, from the shared warm build: 2,171 CPU-s (1,719 user, 452 sys), 229 s wall, 6,101 jobs, of which 7 failed: `Runtime/{Alloc, InputWord}` (a `rw` that the next edit replaced by `show … ; rw`), 5 modules that failed on a file another process's regeneration had moved away (they built on the next run), and `Transcript/Samples` (another family's untracked draft, its own `sorry`s). The second full build, everything else cached: 41 CPU-s, 20 s wall, only `Samples` failing. Before landing, the migration ran in a copy of the tree (sources and `.lake/build`, 1.3 GB): a full build there of 1,400 CPU-s (23 min user plus 6.5 min sys) showed the 21 failing modules, then each file was compiled alone (`lake env lean`, 5 to 110 s each). Agent wall-clock from the decision to green: about 20 minutes (20:01 to 20:20), mostly waiting on builds.

**Observations.** A one-conjunct change to the contract every function shares rebuilt the whole proof tree (every module imports `Core/Holds`), but the repair was local and mechanical: hypotheses threaded through 13 loop lemmas and 7 hand-written `lsym` proofs, nothing in any function's own reasoning. The automation absorbed the rest: every `rv_auto` call site discharges the new precondition itself. Loop lemmas are where such a change bites, since they restate the context they need by hand; a loop lemma that took the whole `Holds.pre` context as one hypothesis would not have needed an edit.


## Benchmark round 2: changes to proved functions with proved callers, and the cold build (2026-11-20)

**Tree.** Copy of `c48bd7dea` (`iterate.sh --init`): 104 proof files; the generator now names functions by `Idx.<Module>`, so the tables no longer hold literal indices (C3's and C5's table failures cannot recur). The base itself has one failing module, `Proof/Runtime/FinishGrow` (it needs an uncommitted `Tactic/Sym.lean`); every build below retries it (about 110 CPU-s each) and it is not counted as a failure of the change. The rows of `iteration-bench.tsv` now carry `changed_proved_callers_proved`: per changed template, whether a table links its proof at the image, and how many of the functions calling it are linked too (from the `Link` modules' callee indices).

| change | changed function proved? callers proved? | templates | link CPU-s | rebuilt for the change: proofs (spec, model, table, final) | failed | repair | total CPU-s (wall) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| C6 `<E as Mul>::mul` Karatsuba to schoolbook (4 products) | proved; 11 of 32 callers | 1 | 713 | 1 (5); after the mirror edit 62 (117) | `Proof/Field/EMul`, `Probe/EMul` | mirror `Model.eMul` to the schoolbook shape and `eMul_eq` (10 lines, compiled first time); `EMul`'s proof 1 simp lemma dropped (a linter); 3 builds; about 9 min | 3,230 (797 s) |
| C7 `dot` as an index loop | proved; 1 of 8 | 0: the ELF is byte-identical | 0 | 0 | none | none | 300 (235 s) |
| C7b `dot` summed from the last index down | proved; 1 of 8 | 1 | 710 | 1 (7); after the mirror edit 45 (95) | `Proof/Multilinear/Dot` | mirror `dotRust` reversed, with `foldl_reverse_add` (13 lines); the loop proof walked down (36 lines removed, 57 added), modelled on `PolyEval`'s; about 6 min | 2,627 (655 s) |
| C8 `duplex` lanes by `chunks_exact_mut`, count reset before the permutation | proved; 3 of 3 | 1 | 672 | 1 (8) | `Proof/Transcript/Duplex` | not repaired: the compiler made the four unrolled slot writes a loop, so the proof (287 lines, a five-path meeting point) needs a loop lemma; estimated 1 to 2 h | 1,073 (312 s) |
| C8b `duplex`: only the count reset moved before the permutation | proved; 3 of 3 | 1 | 733 | 1 (8) | `Proof/Transcript/Duplex` | the code generator also swapped `s0`/`s1`: the invariant's two registers, and `tail`'s closing steps for a store before the calls (next, the buffer kept through the store, `Static`, the frame chain, the count and the ground read through the callees' frames): 25 lines, 5 probe compiles, about 9 min | 1,485 (468 s) |
| C9 `poly_eval` Horner from the leading coefficient (contract change; Statement and Model edited by the patch) | proved; 0 of 4 | 1 | 703 | 58 (110) | `Proof/Multilinear/PolyEval`, `Model/Bus` | the loop proof walks up now (63 lines removed, 40 added); `Model/Bus` 1 simp lemma dropped (`polyEvalRust_eq` became `rfl`); about 6 min | 3,054 (621 s) |

**What propagated.** No caller's proof failed in any change: callers take a callee's contract as a hypothesis and do not import its template, so a callee's new code never rebuilds them, and its contract is stated over the Model mirror, so only a change of the mirror rebuilds them (C6, C7b: every module importing `Model.Field` or `Model.Multilinear`, 45 to 62 proofs, all green). C9's contract change reached the Model's own proofs (`Model/Bus`, a linter) and nothing else; `poly_eval` has no proved caller yet, and C1 (round 1) is the case of a changed contract (`eq_eval`) whose proved callers (`StackWeight::evaluate`, `GluedWeight::evaluate`) rebuilt green without edits. The only machine-code proofs that broke were the changed functions' own, plus `Probe/EMul` (the phase-0 `lsym` probe, which steps one fixed instruction list; superseded by `Proof/Field/EMul`, not repaired). Two compiler effects decided the repair cost: in C8 the slot writes became a loop (a new loop lemma), in C8b and C1 the register allocation moved (an invariant's register names).

**Cold build** (`lake build Rv64mc` from an empty `.lake/build` and `Statement/.lake/build`, Mathlib and machine-checked from their caches, 8 modules at once, host load 10 to 15): 4,333 CPU-s (1.20 CPU-h), 516 s wall. By class: Gen 1,535 (230 templates 669, 230 links 811, others 55); Statement 74; Model 371; Spec, Proof and Table 1,770 (454, 1,269, 47); Final 80; Tactic, Core and probes 258. Not built: `FinishGrow` and the modules importing it.

## C0-unbatched: no change, link modules one per function

Copy of `2fd6731ef`; patch `C0.patch` (empty).

**Binary.** raw: unchanged 230, moved 0, changed 0, added 0, removed 0; words differing in matched functions 0; modulo addresses: unchanged 230, moved 0, changed 0, added 0, removed 0; words differing in matched functions 0. templates: 0 changed, 0 added, 0 removed, 230 unchanged.

**Proved before the change** (changed or removed templates): -.

**Generation.** `regen.sh` 63 CPU-s / 59 s, `type-layouts.sh` 109 CPU-s / 100 s (Layouts.lean unchanged).

**Build** (`lake build Rv64mc`, 6 modules at once): 39 CPU-s (the `lean` processes 0), 36 s wall, exit 0.

| class | modules rebuilt | CPU-s |
| --- | --- | --- |

**Failed:** none.


## C2-unbatched: MerklePath::root rewritten, link modules one per function

Copy of `2fd6731ef`; patch `C2.patch` (crates/verifier/src/merkle.rs).

**Binary.** raw: unchanged 92, moved 29, changed 109, added 0, removed 0; words differing in matched functions 641; modulo addresses: unchanged 119, moved 110, changed 1, added 0, removed 0; words differing in matched functions 65. templates: 1 changed, 0 added, 0 removed, 229 unchanged: Verifier.Merkle.MerklePath.Root.

**Proved before the change** (changed or removed templates): Verifier.Merkle.MerklePath.Root: unproved, callers 0/1 proved.

**Generation.** `regen.sh` 64 CPU-s / 60 s, `type-layouts.sh` 105 CPU-s / 97 s (Layouts.lean unchanged).

**Build** (`lake build Rv64mc`, 6 modules at once): 1469 CPU-s (the `lean` processes 1335), 462 s wall, exit 0.

| class | modules rebuilt | CPU-s |
| --- | --- | --- |
| Gen.Tmpl | 1 | 6 |
| Gen.Link | 230 | 1060 |
| Gen other | 6 | 81 |
| Table | 11 | 115 |
| Final | 1 | 74 |

Rebuilt proofs and specs: Final.End, Table.Bus, Table.Bytecode, Table.Field, Table.Hash, Table.Keccak, Table.Layout, Table.Multilinear, Table.Runtime, Table.Transcript, Table.Walk, Table.Whir.

**Failed:** none.

**Sweep** (`rv_sweep` on the changed templates): `Verifier.Merkle.MerklePath.Root` 10.2 CPU-s (ok).


## C0-batched: no change, link modules batched by 20

Copy of `3299473ac`; patch `C0.patch` (empty).

**Binary.** raw: unchanged 230, moved 0, changed 0, added 0, removed 0; words differing in matched functions 0; modulo addresses: unchanged 230, moved 0, changed 0, added 0, removed 0; words differing in matched functions 0. templates: 0 changed, 0 added, 0 removed, 230 unchanged.

**Proved before the change** (changed or removed templates): -.

**Generation.** `regen.sh` 59 CPU-s / 53 s, `type-layouts.sh` 99 CPU-s / 89 s (Layouts.lean unchanged).

**Build** (`lake build Rv64mc`, 6 modules at once): 48 CPU-s (the `lean` processes 0), 46 s wall, exit 0.

| class | modules rebuilt | CPU-s |
| --- | --- | --- |

**Failed:** none.


## C2-batched: MerklePath::root rewritten, link modules batched by 20

Copy of `3299473ac`; patch `C2.patch` (crates/verifier/src/merkle.rs).

**Binary.** raw: unchanged 92, moved 29, changed 109, added 0, removed 0; words differing in matched functions 641; modulo addresses: unchanged 119, moved 110, changed 1, added 0, removed 0; words differing in matched functions 65. templates: 1 changed, 0 added, 0 removed, 229 unchanged: Verifier.Merkle.MerklePath.Root.

**Proved before the change** (changed or removed templates): Verifier.Merkle.MerklePath.Root: unproved, callers 0/1 proved.

**Generation.** `regen.sh` 64 CPU-s / 60 s, `type-layouts.sh` 109 CPU-s / 99 s (Layouts.lean unchanged).

**Build** (`lake build Rv64mc`, 6 modules at once): 678 CPU-s (the `lean` processes 620), 217 s wall, exit 0.

| class | modules rebuilt | CPU-s |
| --- | --- | --- |
| Gen.Tmpl | 1 | 6 |
| Gen.Link | 19 | 354 |
| Gen other | 6 | 79 |
| Table | 11 | 108 |
| Final | 1 | 73 |

Rebuilt proofs and specs: Final.End, Table.Bus, Table.Bytecode, Table.Field, Table.Hash, Table.Keccak, Table.Layout, Table.Multilinear, Table.Runtime, Table.Transcript, Table.Walk, Table.Whir.

**Failed:** none.

**Sweep** (`rv_sweep` on the changed templates): `Verifier.Merkle.MerklePath.Root` 8.4 CPU-s (ok).

