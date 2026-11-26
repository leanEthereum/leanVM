# Status of the machine-code proof campaign

At `8ac1a6c36`. Classes: **A** proved and instantiated at the image (`liftProg Gen.fns`, `Gen.Idx.<Module>`, `Gen.Needs.<Module>`) in `Rv64mc/Table/*.lean` (or `Final/` for `_start`); **B** an `ok` over the template in `Proof/**` with no instance at the image; **C** a contract in `Spec/**` (or `Final/MainSpec.lean`) and no proof; **D** nothing. Function indices are `Rv64mc/Gen/index.tsv`'s.

## Summary

| class | functions | instructions |
| --- | --- | --- |
| A | 94 | 3161 (15.1%) |
| of which no open hypothesis at the image | 47 | 1414 |
| B | 0 | 0 |
| C | 66 | 9758 (46.7%) |
| of which partly proved | 2 (`main`, `counting_sort::<usize>`) | 417 |
| D | 70 | 7969 (38.2%) |
| total | 230 | 20888 |

* "No open hypothesis": every hypothesis of the Table theorem is discharged by another Table theorem (the panic chain, `grinding_bits`, `E::square`, `Scaled::mul`, ...) or is one of the environment facts `hnext`/`hend` (written `env` below), which are `rfl` at `Rv64mc.env` (checked). The other 47 A functions rest on open leaves: the class-C contracts of `compiler_builtins`' `memcpy`/`memset`/`memmove` (223 to 225), `Vec<E>::reserve` (38), `Sponge::new`, `Scaled::new`, `induced_weight`, `ring_weight`, `eq_above`, `stack_point`, the drops of `Vec<Table>` and `Vec<BusBlock>`, `walk` and `main`; and image data facts not discharged (the `clmul_low` constant `d_c8_d07a1b83` as `DataRef.Words`, written `clmul table`; the `n_constraints`, `count_columns`, WHIR query and `linear_transpose` pi/rho/magic tables).
* `memcpy`'s and `memmove`'s contracts (`MemcpySpec`, `MemmoveSpec`, 223 and 225) were false of their templates, which keep scratch below the entry's stack pointer (`Table/CopyScratch.lean`, by concrete runs); they now keep only the bytes apart from that stack and ask `CopyApart` of their ranges (`Spec/Runtime/Mem.lean`). For the same reason `Digest::words`' partial `spec` (`Spec/Hash/DigestWords.lean`) asks its digest apart from that stack, so `Table/Hash`'s instance of it states a contract with that precondition. `MemcpySpec` and `MemmoveSpec` stay class C, with a precondition met with bytes to copy (`copySpec_pre_inhabited`) and no run found refuting them (the pinned runs: `copies`, `memcpy_copies_aboveTop`, `memmove_copies_overlap`). `memcpy`'s partial contract under its total precondition and `Windows` follows from the total one (`Table/MemT.memcpyHolds`), but `MemcpySpec`, whose precondition has neither, does not, and no partial caller up to `main` has `Windows`; so the rows below still name `memcpy (223)`. Removing it takes a partial proof of `MemcpySpec`: `MemcpyT`'s, replayed without `Windows` and `WinOk`.
* To check: other class-C partial contracts keep every byte outside what they write, their own stack included (`ByteFrame`), for functions that may keep scratch below their entry's stack pointer: `DigestPost` (`Spec/Hash/Keccak.lean`, used by `keccak_hash`, `Spec/Merkle/Merkle.lean`, `Spec/Runtime/Input.lean`). `Core/LocalRun.lean` runs a body without calls, so a function that calls others needs more to test.
* Every template proof (`Proof/**` `ok`) has its Table instance, so B is empty. Partial proofs: `main` (stream loop, entry preconditions, `Base`: `Proof/Walk/Main{Base,Entry,Stream}.lean`), `counting_sort::<usize>` (its counting and prefix-sum loops).
* **End theorem.** `Rv64mc.rv64_sound (hmain : MainSpec env (liftProg Gen.fns) Gen.Start.link.main.idx need) : AllDecode image ∧ Sound image` (`Final/End.lean`) and `Rv64mc.Table.Walk.rv64_sound_of_main (hmain : MainSpec Rv64mc.env (liftProg Gen.fns) Gen.Idx.Main Gen.Needs.Main) : AllDecode image ∧ Sound image`. `MainSpec env p i need := ∀ words, Holds env p i need (MainPre env words) (MainPost words)`, `MainPost`: `a0 = 0 → Verdict words`; `Sound img`: every loaded input whose run halts with `0` decodes to `(bytecode, publicInput, proof)` with `verify bytecode publicInput proof = true`. Its one hypothesis is `main`'s contract, which is class C: nothing below `main` (including `verify_execution`'s Table instance) is composed into the end theorem yet. `#print axioms` (by `lake env lean`) of `rv64_sound`, `rv64_sound_of_main`, `loaded_nonempty` and all 97 Table theorems: `[propext, Classical.choice, Quot.sound]`; the committed `#guard_msgs` guards agree. `kernel_eq` adds `Eq.refl` theorems (no `ofReduceBool`).
* **Build.** `lake build Rv64mc` green at HEAD (6135 jobs, warm); `git status` clean, no untracked WIP.
* **Hand-written lines** (non-blank, `Rv64mc/`): Proof 10630, Spec 3369, Table 839, Model 12011, Core 832, Tactic 3182, Final 414, Link 54; total 31331 (the top-level `Rv64mc/*.lean`, 419 more, and the generated `Gen/` not counted). `sorry`, `admit`, `native_decide`, `bv_decide`, `axiom`: 0 in code across these and `Gen/`; one in a comment (`Model/TestsPcs.lean:198`, "the axiom footprint").

## By family

Family totals are `class count/instructions`.

### Alloc, Core (runtime) (A 30/373, C 15/396, D 21/1660)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 3 | `<alloc::raw_vec::RawVecInner>::try_allocate_in @verifier_rv64` | 47 | C | TryAllocRv64Spec | - |
| 8 | `alloc::raw_vec::handle_error` | 5 | A | Table/Runtime `handleError` | none |
| 9 | `alloc::raw_vec::capacity_overflow` | 2 | A | Table/Runtime `capacityOverflow` | none |
| 10 | `<alloc::vec::Vec<_, _>>::remove::assert_failed` | 2 | A | Table/Runtime `removeAssertFailed` | none |
| 11 | `<alloc::vec::Vec<_, _>>::split_off::assert_failed` | 2 | A | Table/Runtime `splitOffAssertFailed` | none |
| 12 | `core::panicking::assert_failed_inner` | 2 | A | Table/Runtime `assertFailedInner` | none |
| 13 | `core::panicking::panic_fmt` | 2 | A | Table/Runtime `panicFmt` | none |
| 14 | `core::panicking::assert_failed::<usize, usize> @core` | 3 | A | Table/Runtime `assertFailedUsizeUsize` | none |
| 15 | `core::slice::index::slice_index_fail` | 2 | A | Table/Runtime `sliceIndexFail` | none |
| 16 | `core::panicking::panic_bounds_check` | 2 | A | Table/Runtime `panicBoundsCheck` | none |
| 17 | `core::panicking::panic_nounwind_fmt` | 2 | A | Table/Runtime `panicNounwindFmt` | none |
| 37 | `<alloc::raw_vec::RawVecInner>::try_allocate_in @verifier` | 56 | C | TryAllocSpec | - |
| 38 | `<alloc::vec::Vec<verifier::field::E>>::reserve @verifier` | 10 | C | ReserveSpec (generic in T) | - |
| 39 | `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<...` | 11 | A | Table/Runtime `doReserve` | env; memcpy (223) |
| 40 | `<alloc::raw_vec::RawVecInner>::grow_amortized @verifier` | 41 | A | Table/Runtime `growAmortized` | env; memcpy (223) |
| 41 | `<alloc::raw_vec::RawVecInner>::finish_grow @verifier` | 66 | A | Table/Runtime `finishGrow` | env; memcpy (223) |
| 55 | `<alloc::vec::Vec<verifier::field::E> as core::clone::Clone>::clone ...` | 49 | C | CloneESpec | - |
| 58 | `<verifier::field::E as alloc::vec::spec_from_elem::SpecFromElem>::f...` | 72 | C | FromElemESpec | - |
| 62 | `<alloc::raw_vec::RawVec<verifier::bus::ColumnClaim>>::grow_one @ver...` | 15 | A | Table/Runtime `growOne_columnClaim` | env; memcpy (223) |
| 63 | `alloc::boxed::box_new_uninit` | 11 | A | Table/Runtime `boxNewUninit` | env |
| 64 | `<alloc::vec::Vec<(verifier::StackWeight, verifier::field::E)>>::ext...` | 55 | D | - | - |
| 65 | `<alloc::raw_vec::RawVec<(verifier::StackWeight, verifier::field::E)...` | 15 | A | Table/Runtime `growOne_stackClaim` | env; memcpy (223) |
| 68 | `core::ptr::drop_glue::<alloc::vec::Vec<(verifier::StackWeight, veri...` | 1 | A | Table/Runtime `dropVecStackClaim` | none |
| 69 | `core::ptr::drop_glue::<alloc::vec::Vec<alloc::vec::Vec<verifier::la...` | 21 | C | DropSpec | - |
| 70 | `core::ptr::drop_glue::<verifier::layout::Layout> @verifier` | 23 | A | Table/Runtime `dropLayout` | drop Vec<Table> (71), drop Vec<BusBlock> (72) |
| 71 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::Table>> @v...` | 25 | C | DropSpec | - |
| 72 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::BusBlock>>...` | 21 | C | DropSpec | - |
| 73 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::Form>> @ve...` | 1 | A | Table/Runtime `dropVecForm` | none |
| 81 | `<alloc::raw_vec::RawVec<verifier::whir::GluedClaim>>::grow_one @ver...` | 15 | A | Table/Runtime `growOne_gluedClaim` | env; memcpy (223) |
| 84 | `<core::option::Option<verifier::field::E> as alloc::vec::spec_from_...` | 89 | D | - | - |
| 87 | `<[&[verifier::field::E]] as alloc::slice::Concat<verifier::field::E...` | 70 | D | - | - |
| 91 | `<alloc::raw_vec::RawVec<verifier::field::E>>::grow_one @verifier` | 15 | A | Table/Runtime `growOne_e` | env; memcpy (223) |
| 92 | `<alloc::raw_vec::RawVec<verifier::whir::FoldRound>>::grow_one @veri...` | 15 | A | Table/Runtime `growOne_foldRound` | env; memcpy (223) |
| 106 | `<alloc::vec::Vec<verifier::field::E> as alloc::vec::spec_extend::Sp...` | 34 | D | - | - |
| 110 | `<[alloc::vec::Vec<verifier::field::E>] as alloc::slice::Concat<veri...` | 66 | D | - | - |
| 115 | `<alloc::vec::Vec<core::option::Option<verifier::field::E>>>::reserv...` | 10 | C | ReserveSpec (generic in T) | - |
| 117 | `<alloc::vec::Vec<verifier::field::K>>::reserve @verifier` | 10 | C | ReserveSpec (generic in T) | - |
| 118 | `<alloc::raw_vec::RawVec<verifier::field::K>>::grow_one @verifier` | 15 | A | Table/Runtime `growOne_k` | env; memcpy (223) |
| 124 | `<alloc::vec::Vec<u8>>::reserve @verifier` | 10 | C | ReserveSpec (generic in T) | - |
| 125 | `<alloc::raw_vec::RawVec<u64>>::grow_one @verifier` | 15 | A | Table/Runtime `growOne_u64` | env; memcpy (223) |
| 129 | `<alloc::raw_vec::RawVec<usize>>::grow_one @verifier` | 15 | A | Table/Runtime `growOne_usize` | env; memcpy (223) |
| 141 | `<alloc::vec::Vec<core::option::Option<verifier::field::E>> as alloc...` | 74 | D | - | - |
| 142 | `core::array::try_from_fn::<core::ops::try_trait::NeverShortCircuit<...` | 110 | D | - | - |
| 143 | `<alloc::vec::Vec<verifier::field::E> as alloc::vec::spec_from_iter_...` | 106 | D | - | - |
| 147 | `<alloc::raw_vec::RawVec<(alloc::vec::Vec<verifier::field::E>, alloc...` | 15 | A | Table/Runtime `growOne_vecEVecE` | env; memcpy (223) |
| 153 | `<[usize; 2]>::try_map::<core::ops::try_trait::NeverShortCircuit<ver...` | 114 | D | - | - |
| 154 | `<alloc::vec::Vec<verifier::bus::ColumnClaim> as core::convert::From...` | 28 | D | - | - |
| 159 | `<verifier::layout::Form as alloc::vec::spec_from_elem::SpecFromElem...` | 188 | D | - | - |
| 160 | `<alloc::vec::Vec<verifier::layout::Form> as alloc::vec::spec_from_e...` | 75 | D | - | - |
| 165 | `<alloc::vec::Vec<usize> as core::clone::Clone>::clone @verifier` | 49 | D | - | - |
| 166 | `<alloc::raw_vec::RawVec<(alloc::vec::Vec<usize>, verifier::field::E...` | 15 | A | Table/Runtime `growOne_vecUsizeE` | env; memcpy (223) |
| 168 | `<alloc::vec::Vec<verifier::layout::Form> as core::clone::Clone>::cl...` | 142 | D | - | - |
| 169 | `<alloc::vec::Vec<verifier::layout::Form>>::reserve @verifier` | 10 | C | ReserveSpec (generic in T) | - |
| 171 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 62 | D | - | - |
| 172 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 39 | D | - | - |
| 173 | `<alloc::vec::Vec<usize>>::reserve @verifier` | 10 | C | ReserveSpec (generic in T) | - |
| 176 | `<alloc::vec::Vec<verifier::layout::BusBlock>>::extend_trusted::<cor...` | 73 | D | - | - |
| 178 | `<alloc::vec::Vec<verifier::layout::BusBlock>>::reserve @verifier` | 10 | C | ReserveSpec (generic in T) | - |
| 183 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 78 | D | - | - |
| 199 | `<[&[verifier::layout::Form]] as alloc::slice::Concat<verifier::layo...` | 80 | D | - | - |
| 201 | `<alloc::raw_vec::RawVec<alloc::vec::Vec<verifier::layout::Form>>>::...` | 15 | A | Table/Runtime `growOne_vecForm` | env; memcpy (223) |
| 202 | `<alloc::vec::Vec<verifier::layout::Form> as alloc::vec::spec_extend...` | 127 | D | - | - |
| 206 | `<[core::mem::maybe_uninit::MaybeUninit<verifier::layout::Form>] as ...` | 1 | D | - | - |
| 212 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 35 | C | Spec/Transcript/ScalarsIter | - |
| 221 | `<alloc::raw_vec::RawVec<(verifier::field::K, alloc::vec::Vec<u16>)>...` | 15 | A | Table/Runtime `growOne_kVecU16` | env; memcpy (223) |
| 222 | `<alloc::raw_vec::RawVec<u16>>::grow_one @verifier` | 15 | A | Table/Runtime `growOne_u16` | env; memcpy (223) |

### Entry, guest, C memory (A 9/63, C 5/812)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 0 | `_start` | 10 | A | Final/Start `ok`, at the image in Final/End `rv64_sound` | MainSpec (7) |
| 1 | `verifier_rv64::halt` | 4 | A | Table/Runtime `halt` | none |
| 2 | `__rustc::rust_begin_unwind` | 2 | A | Table/Runtime `rustBeginUnwind` | none |
| 4 | `<verifier_rv64::Input>::word` | 12 | A | Table/Runtime `inputWord` | none |
| 5 | `<verifier_rv64::Input>::digest` | 92 | C | InputDigestSpec | - |
| 6 | `<verifier_rv64::Bump as core::alloc::global::GlobalAlloc>::alloc` | 17 | A | Table/Runtime `alloc` | env |
| 7 | `main` | 287 | C | MainSpec (Final/MainSpec); partial proof: Proof/Walk/Main{Base,Entry,Stream} | - |
| 223 | `compiler_builtins::mem::memcpy` | 127 | C | MemcpySpec | - |
| 224 | `compiler_builtins::mem::memset` | 38 | C | MemsetSpec | - |
| 225 | `compiler_builtins::mem::memmove` | 268 | C | MemmoveSpec | - |
| 226 | `memcmp` | 12 | A | Table/Runtime `memcmp` | none |
| 227 | `memcpy` | 2 | A | Table/Runtime `memcpy` | memcpy (223) |
| 228 | `memmove` | 2 | A | Table/Runtime `memmove` | memmove (225) |
| 229 | `memset` | 2 | A | Table/Runtime `memset` | memset (224) |

### Verifier (lib.rs) (A 2/85, C 4/996)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 42 | `verifier::walk` | 762 | C | Spec/Walk/Execution | - |
| 47 | `verifier::read_ood` | 50 | C | Spec/Whir/Transcript readOodSpec | - |
| 66 | `verifier::verify_stacked_opening` | 101 | C | Spec/Whir/StackedOpening spec | - |
| 88 | `verifier::verify_stacked_opening::{closure#1} @verifier` | 83 | C | Spec/Whir/StackedOpening basisSpec | - |
| 99 | `<verifier::StackWeight>::evaluate` | 83 | A | Table/Whir `stackWeightEvaluate` | clmul table; ring_weight (103); eq_above (101) |
| 214 | `verifier::verify_execution` | 2 | A | Table/Walk `verifyExecution` | walk (42) |

### Verifier.Bus (A 2/55, C 2/1466, D 4/806)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 48 | `verifier::bus::verify_bus_balance` | 949 | C | Spec/Bus/VerifyBusBalance | - |
| 54 | `verifier::bus::table_sumcheck` | 517 | C | Spec/Bus/TableSumcheck | - |
| 130 | `<verifier::bus::ColumnClaim>::on_stack` | 45 | A | Table/Bus `onStack` | stack_point (131) |
| 150 | `verifier::bus::bus_layout` | 147 | D | - | - |
| 151 | `verifier::bus::bus_grinding_bits` | 10 | A | Table/Bus `busGrindingBits` | none |
| 152 | `verifier::bus::verify_gkr_grand_products` | 462 | D | - | - |
| 155 | `verifier::bus::verify_bus_balance::{closure#0} @verifier` | 52 | D | - | - |
| 158 | `verifier::bus::verify_bus_balance::{closure#2} @verifier` | 145 | D | - | - |

### Verifier.Bytecode (A 1/287, C 3/349, D 3/421)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 161 | `<verifier::bytecode::Bytecode>::evaluate` | 72 | C | Spec/Bytecode/Evaluate | - |
| 215 | `<verifier::bytecode::Bytecode>::new` | 147 | C | Spec/Bytecode/New | - |
| 216 | `verifier::bytecode::is_valid_encoding_of_a_leanisa_program` | 287 | A | Table/Bytecode `isValidEncoding` | none |
| 217 | `verifier::bytecode::block_members` | 123 | D | - | - |
| 218 | `verifier::bytecode::group_by_word` | 193 | D | - | - |
| 219 | `verifier::bytecode::counting_sort::<usize, verifier::bytecode::bloc...` | 130 | C | Spec/Bytecode/CountingSortUsize; partial proof: two loops (Proof/Bytecode/CountingSortUsize) | - |
| 220 | `verifier::bytecode::counting_sort::<(u64, u16), verifier::bytecode:...` | 105 | D | - | - |

### Verifier.Field (A 11/933, C 3/345, D 10/557)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 18 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 62 | D | - | - |
| 19 | `verifier::field::base_mul` | 8 | A | Table/Field `baseMul` | clmul table |
| 20 | `verifier::field::clmul` | 156 | A | Table/Field `clmul` | clmul table |
| 21 | `verifier::field::reduce` | 14 | A | Table/Field `reduce` | none |
| 22 | `verifier::field::clmul_low` | 72 | A | Table/Field `clmulLow` | clmul table |
| 23 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 67 | D | - | - |
| 24 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 60 | D | - | - |
| 25 | `<verifier::field::E as core::ops::arith::Mul>::mul` | 61 | A | Table/Field `eMul` | clmul table |
| 26 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 30 | D | - | - |
| 27 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 79 | D | - | - |
| 29 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 51 | D | - | - |
| 30 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 36 | C | Spec/Field/ESumBits | - |
| 31 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 35 | D | - | - |
| 32 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::op...` | 69 | D | - | - |
| 33 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 72 | D | - | - |
| 34 | `<verifier::field::E>::sum::<core::iter::adapters::chain::Chain<allo...` | 32 | D | - | - |
| 35 | `<verifier::field::E>::sum::<core::iter::adapters::copied::Copied<co...` | 19 | A | Table/Field `eSumCopied` | none |
| 53 | `verifier::field::powers` | 87 | C | Spec/Field/Powers | - |
| 95 | `<verifier::field::Scaled>::mul` | 177 | A | Table/Field `scaledMul` | none |
| 96 | `<verifier::field::Scaled>::new` | 222 | C | Spec/Field/Scaled newSpec | - |
| 104 | `<verifier::field::E>::square` | 36 | A | Table/Field `eSquare` | none |
| 105 | `verifier::field::spread` | 54 | A | Table/Field `spread` | none |
| 127 | `<verifier::field::K>::inv` | 291 | A | Table/Field `kInv` | clmul table |
| 170 | `<verifier::field::E>::pow` | 45 | A | Table/Field `ePow` | clmul table |

### Verifier.Hash (A 3/83, C 3/957)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 46 | `<verifier::hash::Digest>::from_halves` | 61 | A | Table/Hash `digestFromHalves` | none |
| 56 | `<verifier::hash::Digest>::halves` | 19 | A | Table/Hash `digestHalves` | memcpy (223) |
| 114 | `verifier::hash::keccak_f` | 391 | C | Spec/Hash/KeccakF | - |
| 122 | `verifier::hash::keccak_hash` | 136 | C | Spec/Hash/Keccak | - |
| 123 | `verifier::hash::xor_block` | 430 | C | Spec/Hash/Keccak | - |
| 144 | `<verifier::hash::Digest>::words` | 3 | A | Table/Hash `digestWords` | memcpy (223) |

### Verifier.Keccak (A 1/196, C 1/132, D 3/1315)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 36 | `verifier::keccak::linear_transpose::<verifier::field::E> @verifier` | 196 | A | Table/Keccak `linearTranspose` | env; memset (224); Vec<E>::reserve (38); data: pi, rho, magic tables |
| 60 | `verifier::keccak::verify_keccak` | 626 | D | - | - |
| 138 | `verifier::keccak::verify_layer` | 481 | D | - | - |
| 139 | `verifier::keccak::open` | 208 | D | - | - |
| 140 | `verifier::keccak::instance_weights` | 132 | C | Spec/Keccak/InstanceWeights | - |

### Verifier.Layout (A 11/194, C 1/509, D 28/3131)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 45 | `verifier::layout::build_layout` | 509 | C | Spec/Layout/BuildLayout | - |
| 49 | `<verifier::layout::Table>::n_constraints` | 11 | A | Table/Layout `nConstraints` | data: n_constraints table |
| 57 | `<verifier::layout::Layout>::committed` | 21 | A | Table/Layout `committed` | none |
| 145 | `<verifier::layout::Table>::constraints` | 11 | D | - | - |
| 146 | `<verifier::layout::Form>::evaluate` | 16 | D | - | - |
| 148 | `verifier::layout::jump_constraints` | 67 | D | - | - |
| 157 | `verifier::layout::gpow` | 2 | A | Table/Layout `gpow` | clmul table (via E::pow) |
| 162 | `verifier::layout::constant` | 14 | A | Table/Layout `constant` | none |
| 163 | `<verifier::layout::Form>::add_scaled` | 177 | D | - | - |
| 167 | `<verifier::layout::Form>::term` | 35 | A | Table/Layout `term` | env |
| 175 | `verifier::layout::tables` | 222 | D | - | - |
| 177 | `<verifier::layout::Table>::count_columns` | 12 | A | Table/Layout `countColumns` | data: count_columns table |
| 179 | `verifier::layout::col` | 34 | A | Table/Layout `col` | clmul table (via E::pow) |
| 180 | `verifier::layout::keccak_shape` | 7 | A | Table/Layout `keccakShape` | none |
| 181 | `verifier::layout::column_kappas` | 159 | D | - | - |
| 182 | `verifier::layout::stack` | 126 | D | - | - |
| 184 | `verifier::layout::qkeccak_slot` | 12 | A | Table/Layout `qkeccakSlot` | none |
| 185 | `verifier::layout::is_output_lane` | 3 | A | Table/Layout `isOutputLane` | none |
| 186 | `verifier::layout::stacked_blocks` | 90 | D | - | - |
| 187 | `verifier::layout::flushes_keccak` | 370 | D | - | - |
| 188 | `verifier::layout::flushes_arith` | 261 | D | - | - |
| 189 | `verifier::layout::flushes_set` | 111 | D | - | - |
| 190 | `verifier::layout::flushes_deref` | 223 | D | - | - |
| 191 | `verifier::layout::flushes_jump` | 199 | D | - | - |
| 192 | `verifier::layout::prod` | 43 | A | Table/Layout `prod` | clmul table (via E::pow) |
| 193 | `<verifier::layout::Form as core::ops::arith::Add>::add` | 25 | D | - | - |
| 194 | `<verifier::layout::Flushes>::state_derived` | 82 | D | - | - |
| 195 | `<verifier::layout::Flushes>::bytecode` | 117 | D | - | - |
| 196 | `<verifier::layout::Flushes>::memory_cols` | 85 | D | - | - |
| 197 | `<verifier::layout::Flushes>::memory` | 41 | D | - | - |
| 198 | `<verifier::layout::Flushes>::counted` | 65 | D | - | - |
| 200 | `<verifier::layout::Flushes>::pair` | 54 | D | - | - |
| 203 | `<verifier::layout::Form>::sum::<core::iter::adapters::chain::Chain<...` | 146 | D | - | - |
| 204 | `<verifier::layout::Form>::sum::<[verifier::layout::Form; 3]> @verifier` | 63 | D | - | - |
| 205 | `<verifier::layout::Flushes>::state_step` | 23 | D | - | - |
| 207 | `<verifier::layout::Form>::sum::<core::iter::adapters::map::Map<core...` | 84 | D | - | - |
| 208 | `verifier::layout::keccak_cell_lanes` | 59 | D | - | - |
| 209 | `verifier::layout::layout_limb` | 117 | D | - | - |
| 210 | `<verifier::layout::Flushes>::memory_if` | 68 | D | - | - |
| 211 | `<verifier::layout::Form>::sum::<core::iter::adapters::flatten::Flat...` | 70 | D | - | - |

### Verifier.Merkle (C 3/308)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 119 | `<verifier::merkle::MerklePath>::root` | 144 | C | Spec/Merkle/Merkle | - |
| 120 | `verifier::merkle::hash_leaf` | 53 | C | Spec/Merkle/Merkle | - |
| 121 | `verifier::merkle::hash_pair` | 111 | C | Spec/Merkle/Merkle | - |

### Verifier.Multilinear (A 8/336, C 6/546)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 28 | `verifier::multilinear::dot` | 44 | A | Table/Multilinear `dot` | none |
| 59 | `verifier::multilinear::multilinear_eval::<verifier::field::K> @veri...` | 110 | C | Spec/Multilinear/MultilinearEvalK | - |
| 90 | `verifier::multilinear::multilinear_eval::<verifier::field::E> @veri...` | 146 | C | Spec/Multilinear/MultilinearEvalE | - |
| 93 | `<verifier::multilinear::Scaler>::new` | 9 | A | Table/Multilinear `scalerNew` | Scaled::new (96) |
| 94 | `<verifier::multilinear::Scaler>::mul` | 17 | A | Table/Multilinear `scalerMul` | none |
| 98 | `verifier::multilinear::eq_eval` | 40 | A | Table/Field `eqEval` | clmul table |
| 101 | `<verifier::multilinear::Placement>::eq_above` | 34 | C | Spec/Multilinear/EqAbove | - |
| 102 | `verifier::multilinear::selector_point` | 67 | A | Table/Multilinear `selectorPoint` | env; Vec<E>::reserve (38) |
| 108 | `verifier::multilinear::poly_eval` | 39 | A | Table/Multilinear `polyEval` | none |
| 131 | `<verifier::multilinear::Placement>::stack_point` | 32 | C | Spec/Multilinear/StackPoint | - |
| 137 | `verifier::multilinear::eq_kernel` | 102 | C | Spec/Multilinear/EqKernel | - |
| 156 | `verifier::multilinear::index_mle` | 52 | A | Table/Multilinear `indexMle` | none |
| 164 | `verifier::multilinear::padding_weight` | 68 | A | Table/Multilinear `paddingWeight` | none |
| 174 | `verifier::multilinear::stack_offsets` | 122 | C | Spec/Multilinear/StackOffsets | - |

### Verifier.RingSwitch (A 3/69, C 4/408)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 61 | `verifier::ring_switch::ring_switch` | 77 | C | Spec/Whir/RingSwitch switchSpec | - |
| 100 | `<verifier::ring_switch::RingWeight>::evaluate` | 10 | A | Table/Whir `ringWeightEvaluate` | ring_weight (103) |
| 103 | `verifier::ring_switch::ring_weight` | 106 | C | Spec/Whir/RingWeight spec | - |
| 133 | `verifier::ring_switch::ring_coefficients` | 116 | C | Spec/Whir/RingSwitch coefficientsSpec | - |
| 134 | `verifier::ring_switch::ring_target` | 109 | C | Spec/Whir/RingSwitch targetSpec | - |
| 135 | `verifier::ring_switch::ring_psi` | 46 | A | Table/Whir `ringPsi` | clmul table |
| 136 | `verifier::ring_switch::frobenius_8` | 13 | A | Table/Whir `frobenius8` | none |

### Verifier.Transcript (A 11/435, C 5/557)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 43 | `<verifier::transcript::Transcript>::new` | 20 | A | Table/Transcript `new` | Sponge::new (213) |
| 44 | `<verifier::transcript::Transcript>::next_scalars` | 97 | C | Spec/Transcript/NextScalars | - |
| 50 | `verifier::transcript::grinding_bits` | 88 | A | Table/Transcript `grindingBits` | none |
| 51 | `<verifier::transcript::Transcript>::grind_check` | 42 | A | Table/Transcript `grindCheck` | none |
| 52 | `<verifier::transcript::Sponge>::sample` | 19 | A | Table/Transcript `sample` | none |
| 67 | `<verifier::transcript::Transcript>::finish` | 13 | A | Table/Transcript `finish` | none |
| 78 | `<verifier::transcript::Transcript>::merkle` | 148 | C | Spec/Transcript/Merkle | - |
| 85 | `verifier::transcript::sumcheck` | 116 | C | Spec/Transcript/Sumcheck | - |
| 107 | `<verifier::transcript::Transcript>::sumcheck_round_poly` | 159 | C | Spec/Transcript/SumcheckRoundPoly | - |
| 109 | `<verifier::transcript::Transcript>::next_scalar` | 34 | A | Table/Transcript `nextScalar` | none |
| 111 | `<verifier::transcript::Transcript>::next` | 19 | A | Table/Transcript `next` | none |
| 112 | `<verifier::transcript::Sponge>::absorb` | 43 | A | Table/Transcript `absorb` | none |
| 113 | `<verifier::transcript::Sponge>::duplex` | 68 | A | Table/Transcript `duplex` | none |
| 132 | `<verifier::transcript::Transcript>::samples` | 68 | A | Table/Transcript `samples` | env; Vec<E>::reserve (38) |
| 149 | `<verifier::transcript::Sponge>::absorb_nonce` | 21 | A | Table/Transcript `absorbNonce` | none |
| 213 | `<verifier::transcript::Sponge>::new` | 37 | C | Spec/Transcript/SpongeNew | - |

### Verifier.Whir (A 2/52, C 11/1977, D 1/79)

| # | function | instr | class | where | remaining hypotheses |
| --- | --- | --- | --- | --- | --- |
| 74 | `verifier::whir::verify_whir::<verifier::verify_stacked_opening::{cl...` | 928 | C | Spec/Whir/StackedOpening whirSpec | - |
| 75 | `verifier::whir::derive_config` | 150 | C | Spec/Whir/DeriveConfig | - |
| 76 | `<verifier::whir::Subspace>::new` | 80 | C | Spec/Whir/Subspace newSpec | - |
| 77 | `verifier::whir::sample_queries` | 139 | C | Spec/Whir/Transcript sampleQueriesSpec | - |
| 79 | `<verifier::whir::Subspace>::at` | 96 | C | Spec/Whir/Subspace atSpec | - |
| 80 | `verifier::whir::novel_eval` | 35 | C | Spec/Whir/Subspace evalSpec | - |
| 82 | `verifier::whir::ext_row` | 57 | C | Spec/Whir/ExtRow | - |
| 83 | `verifier::whir::fold_row` | 104 | C | Spec/Whir/FoldRow | - |
| 86 | `verifier::whir::verify_whir::<verifier::verify_stacked_opening::{cl...` | 79 | D | - | - |
| 89 | `<verifier::whir::GluedWeight>::evaluate` | 31 | A | Table/Whir `gluedWeightEvaluate` | clmul table; induced_weight (97) |
| 97 | `verifier::whir::induced_weight` | 115 | C | Spec/Whir/InducedWeight | - |
| 116 | `verifier::whir::novel_basis` | 108 | C | Spec/Whir/Subspace basisSpec | - |
| 126 | `verifier::whir::subspace_roots` | 165 | C | Spec/Whir/Subspace rootsSpec | - |
| 128 | `verifier::whir::whir_queries` | 21 | A | Table/Whir `whirQueries` | data: WHIR query tables (InData) |
