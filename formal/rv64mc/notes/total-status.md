# Status of the total-correctness campaign

Which of the functions `main` reaches have a total contract (`HoldsT`, `Core/HoldsT.lean`), toward `main`'s `MainSpecT` (`Final/MainSpecT.lean`), as `notes/status.md` tracks the partial ones. A function is **total** here when it has a total contract over its template in `Proof/**` (a `T` module) and a `Table` instance at the image (`Rv64mc/Table/*T.lean`: `liftProg Gen.fns`, `Gen.Idx`, `Gen.Needs`, its callees' `Table` instances as arguments). Indices and instruction counts are `Rv64mc/Gen/index.tsv`'s; heights are the call graph's from the leaves (0 a leaf); the partial class is `notes/status.md`'s (A proved at the image, C a contract only, D nothing). The call graph has 229 functions (`_start` is not counted: `Final/StartT.lean` proves it from `MainSpecT`).

Open hypotheses of a `Table` theorem: `none`; `env`, the environment's two facts about the image that `alloc` reads (`NEXT`'s data reference is `env.nextAddr`, `env.heapEnd = 0x78000000`); `clmul table`, `clmul_low`'s constant in the static data (`DataRef.InData`, `FieldT.ClmulTable`); `WHIR query tables (InData)`; `N_CONSTRAINTS table (InData)` and `COUNT_COLUMNS tables (InData, CountColumnsData)`, the tables `Table::n_constraints` and `Table::count_columns` read in the static data (the second also its contents, as `Table/Layout.lean` has it); `MemmoveSpecT (225)`, the total contract of `compiler_builtins`' `memmove`, stated in `Proof/Runtime/MemmoveT.lean` and not yet proved. (`memcpy`'s, `MemcpySpecT`, is proved: `Table/MemT.lean`'s `memcpyT`, which `Table/CopyUseT.lean` and `Table/AllocT.lean` compose into the instances that call it.) All but the last are environment facts about the image.

## Summary

| | functions | instructions |
| --- | --- | --- |
| total, with a `Table` instance | 80 | 2150 (10.3%) |
| of which no open hypothesis | 39 | 1120 |
| of which only environment facts open | 79 | 2148 |
| stated, not proved here | 1 | 268 |
| no total contract | 148 | 18460 |
| reachable from `main` | 229 | 20878 |

Every total function has its `Table` instance, and every `Table` theorem's axioms are pinned by `#guard_msgs` to `[propext, Classical.choice, Quot.sound]`. The counts are the table's below, recounted by `awk -F'|' '$7 ~ /yes/ {n++; s+=$5} END {print n, s}' notes/total-status.md` (all total functions; add `&& $10 ~ /none/` for those with no open hypothesis, or match `$2 ~ /^ [0-9]+ $/` for every row).

## By function

| height | # | function | instr | partial | total | proof | `Table` theorem | open hypotheses |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 1 | `verifier_rv64::halt` | 4 | A | yes | Proof/Runtime/HaltT | RuntimeT.halt | none |
| 0 | 21 | `verifier::field::reduce` | 14 | A | yes | Proof/Field/ReduceT | FieldT.reduce | none |
| 0 | 22 | `verifier::field::clmul_low` | 72 | A | yes | Proof/Field/ClmulLowT | FieldT.clmulLow | clmul table |
| 0 | 34 | `<verifier::field::E>::sum::<core::iter::adapters::chain::Chain<allo...` | 32 | D | yes | Proof/Field/SumChainT | FieldSumT.sumChainT | none |
| 0 | 35 | `<verifier::field::E>::sum::<core::iter::adapters::copied::Copied<co...` | 19 | A | yes | Proof/Field/ESumCopiedT | FieldT.eSumCopied | none |
| 0 | 46 | `<verifier::hash::Digest>::from_halves` | 61 | A | yes | Proof/Hash/DigestFromHalvesT | DigestT.digestFromHalves | none |
| 0 | 50 | `verifier::transcript::grinding_bits` | 88 | A | yes | Proof/Transcript/GrindingBitsT | TranscriptT.grindingBits | none |
| 0 | 57 | `<verifier::layout::Layout>::committed` | 21 | A | yes | Proof/Layout/CommittedT | LayoutLeafT.committed | none |
| 0 | 67 | `<verifier::transcript::Transcript>::finish` | 13 | A | yes | Proof/Transcript/FinishT | TranscriptT.finish | none |
| 0 | 68 | `core::ptr::drop_glue::<alloc::vec::Vec<(verifier::StackWeight, veri...` | 1 | A | yes | Proof/Runtime/DropT | RuntimeT.dropVecStackClaim | none |
| 0 | 73 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::Form>> @ve...` | 1 | A | yes | Proof/Runtime/DropT | RuntimeT.dropVecForm | none |
| 0 | 105 | `verifier::field::spread` | 54 | A | yes | Proof/Field/SpreadT | FieldT.spread | none |
| 0 | 111 | `<verifier::transcript::Transcript>::next` | 19 | A | yes | Proof/Transcript/NextT | TranscriptT.next | none |
| 0 | 123 | `verifier::hash::xor_block` | 430 | C | yes | Proof/Hash/XorBlockT | HashT.xorBlockT | none |
| 0 | 128 | `verifier::whir::whir_queries` | 21 | A | yes | Proof/Whir/WhirQueriesT | WhirT.whirQueries | WHIR query tables (InData) |
| 0 | 184 | `verifier::layout::qkeccak_slot` | 12 | A | yes | Proof/Layout/QkeccakSlotT | LayoutLeafT.qkeccakSlot | none |
| 0 | 185 | `verifier::layout::is_output_lane` | 3 | A | yes | Proof/Layout/IsOutputLaneT | LayoutLeafT.isOutputLane | none |
| 0 | 206 | `<[core::mem::maybe_uninit::MaybeUninit<verifier::layout::Form>] as ...` | 1 | D | yes | Proof/Runtime/DropT | RuntimeT.partialDropForm | none |
| 0 | 208 | `verifier::layout::keccak_cell_lanes` | 59 | D | yes | Proof/Layout/KeccakCellLanesT | CellLanesT.keccakCellLanesT | none |
| 0 | 223 | `compiler_builtins::mem::memcpy` | 127 | C | yes | Proof/Runtime/MemcpyT | MemT.memcpyT | none |
| 0 | 224 | `compiler_builtins::mem::memset` | 38 | C | yes | Proof/Runtime/MemsetT | RuntimeT.memsetBuiltin | none |
| 0 | 225 | `compiler_builtins::mem::memmove` | 268 | C | stated | Proof/Runtime/MemmoveT `MemmoveSpecT` (stated; wave 1b proves it) | - | - |
| 0 | 226 | `memcmp` | 12 | A | yes | Proof/Runtime/MemcmpT | RuntimeT.memcmp | none |
| 1 | 2 | `__rustc::rust_begin_unwind` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.rustBeginUnwind | none |
| 1 | 4 | `<verifier_rv64::Input>::word` | 12 | A | yes | Proof/Runtime/InputWordT | RuntimeT.inputWord | none |
| 1 | 6 | `<verifier_rv64::Bump as core::alloc::global::GlobalAlloc>::alloc` | 17 | A | yes | Proof/Runtime/AllocT | RuntimeT.alloc | env |
| 1 | 20 | `verifier::field::clmul` | 156 | A | yes | Proof/Field/ClmulT | FieldT.clmul | clmul table |
| 1 | 69 | `core::ptr::drop_glue::<alloc::vec::Vec<alloc::vec::Vec<verifier::la...` | 21 | C | no | - | - | - |
| 1 | 72 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::BusBlock>>...` | 21 | C | no | - | - | - |
| 1 | 104 | `<verifier::field::E>::square` | 36 | A | yes | Proof/Field/ESquareT | FieldT.eSquare | none |
| 1 | 151 | `verifier::bus::bus_grinding_bits` | 10 | A | yes | Proof/Bus/BusGrindingBitsT | BusT.busGrindingBits | none |
| 1 | 227 | `memcpy` | 2 | A | yes | Proof/Runtime/MemWrappersT | CopyUseT.memcpy | none |
| 1 | 228 | `memmove` | 2 | A | yes | Proof/Runtime/MemWrappersT | RuntimeT.memmove | MemmoveSpecT (225) |
| 1 | 229 | `memset` | 2 | A | yes | Proof/Runtime/MemsetT | RuntimeT.memset | none |
| 2 | 3 | `<alloc::raw_vec::RawVecInner>::try_allocate_in @verifier_rv64` | 47 | C | yes | Proof/Runtime/TryAllocateInT | AllocT.tryAllocateInRv64 | env |
| 2 | 5 | `<verifier_rv64::Input>::digest` | 92 | C | no | - | - | - |
| 2 | 13 | `core::panicking::panic_fmt` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.panicFmt | none |
| 2 | 17 | `core::panicking::panic_nounwind_fmt` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.panicNounwindFmt | none |
| 2 | 19 | `verifier::field::base_mul` | 8 | A | yes | Proof/Field/BaseMulT | FieldT.baseMul | clmul table |
| 2 | 25 | `<verifier::field::E as core::ops::arith::Mul>::mul` | 61 | A | yes | Proof/Field/EMulT | FieldT.eMul | clmul table |
| 2 | 37 | `<alloc::raw_vec::RawVecInner>::try_allocate_in @verifier` | 56 | C | yes | Proof/Runtime/TryAllocateInT | AllocT.tryAllocateIn | env |
| 2 | 41 | `<alloc::raw_vec::RawVecInner>::finish_grow @verifier` | 66 | A | yes | Proof/Runtime/FinishGrowT, FinishGrowAT (block aligned) | CopyUseT.finishGrow | env |
| 2 | 71 | `core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::Table>> @v...` | 25 | C | no | - | - | - |
| 2 | 114 | `verifier::hash::keccak_f` | 391 | C | no | - | - | - |
| 2 | 136 | `verifier::ring_switch::frobenius_8` | 13 | A | yes | Proof/Whir/Frobenius8T | WhirT.frobenius8 | none |
| 2 | 144 | `<verifier::hash::Digest>::words` | 3 | A | yes | Proof/Hash/DigestWordsT | CopyUseT.digestWords | none |
| 3 | 9 | `alloc::raw_vec::capacity_overflow` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.capacityOverflow | none |
| 3 | 10 | `<alloc::vec::Vec<_, _>>::remove::assert_failed` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.removeAssertFailed | none |
| 3 | 11 | `<alloc::vec::Vec<_, _>>::split_off::assert_failed` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.splitOffAssertFailed | none |
| 3 | 12 | `core::panicking::assert_failed_inner` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.assertFailedInner | none |
| 3 | 15 | `core::slice::index::slice_index_fail` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.sliceIndexFail | none |
| 3 | 16 | `core::panicking::panic_bounds_check` | 2 | A | yes | Proof/Runtime/PanicsT | RuntimeT.panicBoundsCheck | none |
| 3 | 18 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 62 | D | no | - | - | - |
| 3 | 40 | `<alloc::raw_vec::RawVecInner>::grow_amortized @verifier` | 41 | A | yes | Proof/Runtime/GrowAmortizedT | AllocT.growAmortized | env |
| 3 | 56 | `<verifier::hash::Digest>::halves` | 19 | A | no | - | - | - |
| 3 | 63 | `alloc::boxed::box_new_uninit` | 11 | A | yes | Proof/Runtime/BoxNewUninitT | AllocT.boxNewUninit | env |
| 3 | 70 | `core::ptr::drop_glue::<verifier::layout::Layout> @verifier` | 23 | A | no | - | - | - |
| 3 | 108 | `verifier::multilinear::poly_eval` | 39 | A | no | - | - | - |
| 3 | 122 | `verifier::hash::keccak_hash` | 136 | C | no | - | - | - |
| 3 | 127 | `<verifier::field::K>::inv` | 291 | A | no | - | - | - |
| 3 | 135 | `verifier::ring_switch::ring_psi` | 46 | A | no | - | - | - |
| 3 | 154 | `<alloc::vec::Vec<verifier::bus::ColumnClaim> as core::convert::From...` | 28 | D | no | - | - | - |
| 3 | 156 | `verifier::multilinear::index_mle` | 52 | A | no | - | - | - |
| 3 | 164 | `verifier::multilinear::padding_weight` | 68 | A | no | - | - | - |
| 3 | 167 | `<verifier::layout::Form>::term` | 35 | A | yes | Proof/Layout/TermT | LayoutT.term | env |
| 3 | 170 | `<verifier::field::E>::pow` | 45 | A | yes | Proof/Field/EPowT | LayoutT.ePow | clmul table |
| 3 | 213 | `<verifier::transcript::Sponge>::new` | 37 | C | no | - | - | - |
| 4 | 8 | `alloc::raw_vec::handle_error` | 5 | A | yes | Proof/Runtime/PanicsT | RuntimeT.handleError | none |
| 4 | 14 | `core::panicking::assert_failed::<usize, usize> @core` | 3 | A | yes | Proof/Runtime/PanicsT | RuntimeT.assertFailedUsizeUsize | none |
| 4 | 26 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 30 | D | no | - | - | - |
| 4 | 29 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 51 | D | no | - | - | - |
| 4 | 30 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 36 | C | no | - | - | - |
| 4 | 31 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 35 | D | no | - | - | - |
| 4 | 33 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 72 | D | no | - | - | - |
| 4 | 43 | `<verifier::transcript::Transcript>::new` | 20 | A | no | - | - | - |
| 4 | 49 | `<verifier::layout::Table>::n_constraints` | 11 | A | yes | Proof/Layout/TableT | LayoutT.nConstraints | N_CONSTRAINTS table (InData) |
| 4 | 95 | `<verifier::field::Scaled>::mul` | 177 | A | no | - | - | - |
| 4 | 113 | `<verifier::transcript::Sponge>::duplex` | 68 | A | no | - | - | - |
| 4 | 121 | `verifier::merkle::hash_pair` | 111 | C | no | - | - | - |
| 4 | 142 | `core::array::try_from_fn::<core::ops::try_trait::NeverShortCircuit<...` | 110 | D | no | - | - | - |
| 4 | 148 | `verifier::layout::jump_constraints` | 67 | D | no | - | - | - |
| 4 | 157 | `verifier::layout::gpow` | 2 | A | yes | Proof/Layout/GpowT | LayoutT.gpow | clmul table |
| 4 | 162 | `verifier::layout::constant` | 14 | A | yes | Proof/Layout/ConstantT | LayoutT.constant | env |
| 4 | 177 | `<verifier::layout::Table>::count_columns` | 12 | A | yes | Proof/Layout/TableT | LayoutT.countColumns | COUNT_COLUMNS tables (InData, CountColumnsData) |
| 4 | 180 | `verifier::layout::keccak_shape` | 7 | A | yes | Proof/Layout/KeccakShapeT | LayoutT.keccakShape | none |
| 4 | 183 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 78 | D | no | - | - | - |
| 4 | 216 | `verifier::bytecode::is_valid_encoding_of_a_leanisa_program` | 287 | A | no | - | - | - |
| 5 | 24 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::sl...` | 60 | D | no | - | - | - |
| 5 | 28 | `verifier::multilinear::dot` | 44 | A | no | - | - | - |
| 5 | 32 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::op...` | 69 | D | no | - | - | - |
| 5 | 39 | `<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<...` | 11 | A | yes | Proof/Runtime/DoReserveT | AllocT.doReserve | env |
| 5 | 52 | `<verifier::transcript::Sponge>::sample` | 19 | A | no | - | - | - |
| 5 | 55 | `<alloc::vec::Vec<verifier::field::E> as core::clone::Clone>::clone ...` | 49 | C | no | - | - | - |
| 5 | 62 | `<alloc::raw_vec::RawVec<verifier::bus::ColumnClaim>>::grow_one @ver...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneColumnClaim | env |
| 5 | 65 | `<alloc::raw_vec::RawVec<(verifier::StackWeight, verifier::field::E)...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneStackClaim | env |
| 5 | 81 | `<alloc::raw_vec::RawVec<verifier::whir::GluedClaim>>::grow_one @ver...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneGluedClaim | env |
| 5 | 83 | `verifier::whir::fold_row` | 104 | C | no | - | - | - |
| 5 | 91 | `<alloc::raw_vec::RawVec<verifier::field::E>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneE | env |
| 5 | 92 | `<alloc::raw_vec::RawVec<verifier::whir::FoldRound>>::grow_one @veri...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneFoldRound | env |
| 5 | 94 | `<verifier::multilinear::Scaler>::mul` | 17 | A | no | - | - | - |
| 5 | 98 | `verifier::multilinear::eq_eval` | 40 | A | no | - | - | - |
| 5 | 103 | `verifier::ring_switch::ring_weight` | 106 | C | no | - | - | - |
| 5 | 112 | `<verifier::transcript::Sponge>::absorb` | 43 | A | no | - | - | - |
| 5 | 118 | `<alloc::raw_vec::RawVec<verifier::field::K>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneK | env |
| 5 | 125 | `<alloc::raw_vec::RawVec<u64>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneU64 | env |
| 5 | 129 | `<alloc::raw_vec::RawVec<usize>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneUsize | env |
| 5 | 145 | `<verifier::layout::Table>::constraints` | 11 | D | no | - | - | - |
| 5 | 146 | `<verifier::layout::Form>::evaluate` | 16 | D | no | - | - | - |
| 5 | 147 | `<alloc::raw_vec::RawVec<(alloc::vec::Vec<verifier::field::E>, alloc...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneVecEVecE | env |
| 5 | 153 | `<[usize; 2]>::try_map::<core::ops::try_trait::NeverShortCircuit<ver...` | 114 | D | no | - | - | - |
| 5 | 155 | `verifier::bus::verify_bus_balance::{closure#0} @verifier` | 52 | D | no | - | - | - |
| 5 | 165 | `<alloc::vec::Vec<usize> as core::clone::Clone>::clone @verifier` | 49 | D | no | - | - | - |
| 5 | 166 | `<alloc::raw_vec::RawVec<(alloc::vec::Vec<usize>, verifier::field::E...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneVecUsizeE | env |
| 5 | 174 | `verifier::multilinear::stack_offsets` | 122 | C | no | - | - | - |
| 5 | 179 | `verifier::layout::col` | 34 | A | yes | Proof/Layout/ColT | LayoutT.col | env; clmul table |
| 5 | 192 | `verifier::layout::prod` | 43 | A | yes | Proof/Layout/ProdT | LayoutT.prod | env; clmul table |
| 5 | 201 | `<alloc::raw_vec::RawVec<alloc::vec::Vec<verifier::layout::Form>>>::...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneVecForm | env |
| 5 | 219 | `verifier::bytecode::counting_sort::<usize, verifier::bytecode::bloc...` | 130 | C | no | - | - | - |
| 5 | 220 | `verifier::bytecode::counting_sort::<(u64, u16), verifier::bytecode:...` | 105 | D | no | - | - | - |
| 5 | 221 | `<alloc::raw_vec::RawVec<(verifier::field::K, alloc::vec::Vec<u16>)>...` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneKVecU16 | env |
| 5 | 222 | `<alloc::raw_vec::RawVec<u16>>::grow_one @verifier` | 15 | A | yes | Proof/Runtime/GrowOneT, GrowOnesT | AllocT.growOneU16 | env |
| 6 | 23 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 67 | D | no | - | - | - |
| 6 | 27 | `<verifier::field::E>::sum::<core::iter::adapters::map::Map<core::it...` | 79 | D | no | - | - | - |
| 6 | 38 | `<alloc::vec::Vec<verifier::field::E>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveE | env |
| 6 | 53 | `verifier::field::powers` | 87 | C | no | - | - | - |
| 6 | 75 | `verifier::whir::derive_config` | 150 | C | no | - | - | - |
| 6 | 77 | `verifier::whir::sample_queries` | 139 | C | no | - | - | - |
| 6 | 79 | `<verifier::whir::Subspace>::at` | 96 | C | no | - | - | - |
| 6 | 100 | `<verifier::ring_switch::RingWeight>::evaluate` | 10 | A | no | - | - | - |
| 6 | 109 | `<verifier::transcript::Transcript>::next_scalar` | 34 | A | no | - | - | - |
| 6 | 115 | `<alloc::vec::Vec<core::option::Option<verifier::field::E>>>::reserv...` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveOptionE | env |
| 6 | 117 | `<alloc::vec::Vec<verifier::field::K>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveK | env |
| 6 | 124 | `<alloc::vec::Vec<u8>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveU8 | env |
| 6 | 149 | `<verifier::transcript::Sponge>::absorb_nonce` | 21 | A | no | - | - | - |
| 6 | 158 | `verifier::bus::verify_bus_balance::{closure#2} @verifier` | 145 | D | no | - | - | - |
| 6 | 163 | `<verifier::layout::Form>::add_scaled` | 177 | D | no | - | - | - |
| 6 | 168 | `<alloc::vec::Vec<verifier::layout::Form> as core::clone::Clone>::cl...` | 142 | D | no | - | - | - |
| 6 | 169 | `<alloc::vec::Vec<verifier::layout::Form>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveForm | env |
| 6 | 173 | `<alloc::vec::Vec<usize>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveUsize | env |
| 6 | 178 | `<alloc::vec::Vec<verifier::layout::BusBlock>>::reserve @verifier` | 10 | C | yes | Proof/Runtime/ReserveT | AllocT.reserveBusBlock | env |
| 6 | 200 | `<verifier::layout::Flushes>::pair` | 54 | D | no | - | - | - |
| 6 | 218 | `verifier::bytecode::group_by_word` | 193 | D | no | - | - | - |
| 7 | 36 | `verifier::keccak::linear_transpose::<verifier::field::E> @verifier` | 196 | A | no | - | - | - |
| 7 | 51 | `<verifier::transcript::Transcript>::grind_check` | 42 | A | no | - | - | - |
| 7 | 58 | `<verifier::field::E as alloc::vec::spec_from_elem::SpecFromElem>::f...` | 72 | C | no | - | - | - |
| 7 | 82 | `verifier::whir::ext_row` | 57 | C | no | - | - | - |
| 7 | 84 | `<core::option::Option<verifier::field::E> as alloc::vec::spec_from_...` | 89 | D | no | - | - | - |
| 7 | 102 | `verifier::multilinear::selector_point` | 67 | A | no | - | - | - |
| 7 | 106 | `<alloc::vec::Vec<verifier::field::E> as alloc::vec::spec_extend::Sp...` | 34 | D | no | - | - | - |
| 7 | 116 | `verifier::whir::novel_basis` | 108 | C | no | - | - | - |
| 7 | 120 | `verifier::merkle::hash_leaf` | 53 | C | no | - | - | - |
| 7 | 126 | `verifier::whir::subspace_roots` | 165 | C | no | - | - | - |
| 7 | 132 | `<verifier::transcript::Transcript>::samples` | 68 | A | no | - | - | - |
| 7 | 133 | `verifier::ring_switch::ring_coefficients` | 116 | C | no | - | - | - |
| 7 | 134 | `verifier::ring_switch::ring_target` | 109 | C | no | - | - | - |
| 7 | 140 | `verifier::keccak::instance_weights` | 132 | C | no | - | - | - |
| 7 | 141 | `<alloc::vec::Vec<core::option::Option<verifier::field::E>> as alloc...` | 74 | D | no | - | - | - |
| 7 | 143 | `<alloc::vec::Vec<verifier::field::E> as alloc::vec::spec_from_iter_...` | 106 | D | no | - | - | - |
| 7 | 150 | `verifier::bus::bus_layout` | 147 | D | no | - | - | - |
| 7 | 159 | `<verifier::layout::Form as alloc::vec::spec_from_elem::SpecFromElem...` | 188 | D | no | - | - | - |
| 7 | 160 | `<alloc::vec::Vec<verifier::layout::Form> as alloc::vec::spec_from_e...` | 75 | D | no | - | - | - |
| 7 | 176 | `<alloc::vec::Vec<verifier::layout::BusBlock>>::extend_trusted::<cor...` | 73 | D | no | - | - | - |
| 7 | 181 | `verifier::layout::column_kappas` | 159 | D | no | - | - | - |
| 7 | 186 | `verifier::layout::stacked_blocks` | 90 | D | no | - | - | - |
| 7 | 193 | `<verifier::layout::Form as core::ops::arith::Add>::add` | 25 | D | no | - | - | - |
| 7 | 194 | `<verifier::layout::Flushes>::state_derived` | 82 | D | no | - | - | - |
| 7 | 202 | `<alloc::vec::Vec<verifier::layout::Form> as alloc::vec::spec_extend...` | 127 | D | no | - | - | - |
| 7 | 212 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 35 | C | no | - | - | - |
| 7 | 217 | `verifier::bytecode::block_members` | 123 | D | no | - | - | - |
| 8 | 44 | `<verifier::transcript::Transcript>::next_scalars` | 97 | C | no | - | - | - |
| 8 | 47 | `verifier::read_ood` | 50 | C | no | - | - | - |
| 8 | 61 | `verifier::ring_switch::ring_switch` | 77 | C | no | - | - | - |
| 8 | 76 | `<verifier::whir::Subspace>::new` | 80 | C | no | - | - | - |
| 8 | 80 | `verifier::whir::novel_eval` | 35 | C | no | - | - | - |
| 8 | 86 | `verifier::whir::verify_whir::<verifier::verify_stacked_opening::{cl...` | 79 | D | no | - | - | - |
| 8 | 87 | `<[&[verifier::field::E]] as alloc::slice::Concat<verifier::field::E...` | 70 | D | no | - | - | - |
| 8 | 96 | `<verifier::field::Scaled>::new` | 222 | C | no | - | - | - |
| 8 | 101 | `<verifier::multilinear::Placement>::eq_above` | 34 | C | no | - | - | - |
| 8 | 110 | `<[alloc::vec::Vec<verifier::field::E>] as alloc::slice::Concat<veri...` | 66 | D | no | - | - | - |
| 8 | 119 | `<verifier::merkle::MerklePath>::root` | 144 | C | no | - | - | - |
| 8 | 182 | `verifier::layout::stack` | 126 | D | no | - | - | - |
| 8 | 199 | `<[&[verifier::layout::Form]] as alloc::slice::Concat<verifier::layo...` | 80 | D | no | - | - | - |
| 8 | 203 | `<verifier::layout::Form>::sum::<core::iter::adapters::chain::Chain<...` | 146 | D | no | - | - | - |
| 8 | 204 | `<verifier::layout::Form>::sum::<[verifier::layout::Form; 3]> @verifier` | 63 | D | no | - | - | - |
| 8 | 205 | `<verifier::layout::Flushes>::state_step` | 23 | D | no | - | - | - |
| 8 | 207 | `<verifier::layout::Form>::sum::<core::iter::adapters::map::Map<core...` | 84 | D | no | - | - | - |
| 8 | 211 | `<verifier::layout::Form>::sum::<core::iter::adapters::flatten::Flat...` | 70 | D | no | - | - | - |
| 8 | 215 | `<verifier::bytecode::Bytecode>::new` | 147 | C | no | - | - | - |
| 9 | 78 | `<verifier::transcript::Transcript>::merkle` | 148 | C | no | - | - | - |
| 9 | 93 | `<verifier::multilinear::Scaler>::new` | 9 | A | no | - | - | - |
| 9 | 97 | `verifier::whir::induced_weight` | 115 | C | no | - | - | - |
| 9 | 99 | `<verifier::StackWeight>::evaluate` | 83 | A | no | - | - | - |
| 9 | 107 | `<verifier::transcript::Transcript>::sumcheck_round_poly` | 159 | C | no | - | - | - |
| 9 | 131 | `<verifier::multilinear::Placement>::stack_point` | 32 | C | no | - | - | - |
| 9 | 171 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 62 | D | no | - | - | - |
| 9 | 198 | `<verifier::layout::Flushes>::counted` | 65 | D | no | - | - | - |
| 9 | 209 | `verifier::layout::layout_limb` | 117 | D | no | - | - | - |
| 10 | 59 | `verifier::multilinear::multilinear_eval::<verifier::field::K> @veri...` | 110 | C | no | - | - | - |
| 10 | 85 | `verifier::transcript::sumcheck` | 116 | C | no | - | - | - |
| 10 | 88 | `verifier::verify_stacked_opening::{closure#1} @verifier` | 83 | C | no | - | - | - |
| 10 | 89 | `<verifier::whir::GluedWeight>::evaluate` | 31 | A | no | - | - | - |
| 10 | 90 | `verifier::multilinear::multilinear_eval::<verifier::field::E> @veri...` | 146 | C | no | - | - | - |
| 10 | 130 | `<verifier::bus::ColumnClaim>::on_stack` | 45 | A | no | - | - | - |
| 10 | 137 | `verifier::multilinear::eq_kernel` | 102 | C | no | - | - | - |
| 10 | 195 | `<verifier::layout::Flushes>::bytecode` | 117 | D | no | - | - | - |
| 10 | 197 | `<verifier::layout::Flushes>::memory` | 41 | D | no | - | - | - |
| 10 | 210 | `<verifier::layout::Flushes>::memory_if` | 68 | D | no | - | - | - |
| 11 | 54 | `verifier::bus::table_sumcheck` | 517 | C | no | - | - | - |
| 11 | 64 | `<alloc::vec::Vec<(verifier::StackWeight, verifier::field::E)>>::ext...` | 55 | D | no | - | - | - |
| 11 | 74 | `verifier::whir::verify_whir::<verifier::verify_stacked_opening::{cl...` | 928 | C | no | - | - | - |
| 11 | 138 | `verifier::keccak::verify_layer` | 481 | D | no | - | - | - |
| 11 | 139 | `verifier::keccak::open` | 208 | D | no | - | - | - |
| 11 | 161 | `<verifier::bytecode::Bytecode>::evaluate` | 72 | C | no | - | - | - |
| 11 | 172 | `<core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<...` | 39 | D | no | - | - | - |
| 11 | 187 | `verifier::layout::flushes_keccak` | 370 | D | no | - | - | - |
| 11 | 196 | `<verifier::layout::Flushes>::memory_cols` | 85 | D | no | - | - | - |
| 12 | 60 | `verifier::keccak::verify_keccak` | 626 | D | no | - | - | - |
| 12 | 66 | `verifier::verify_stacked_opening` | 101 | C | no | - | - | - |
| 12 | 152 | `verifier::bus::verify_gkr_grand_products` | 462 | D | no | - | - | - |
| 12 | 188 | `verifier::layout::flushes_arith` | 261 | D | no | - | - | - |
| 12 | 189 | `verifier::layout::flushes_set` | 111 | D | no | - | - | - |
| 12 | 190 | `verifier::layout::flushes_deref` | 223 | D | no | - | - | - |
| 12 | 191 | `verifier::layout::flushes_jump` | 199 | D | no | - | - | - |
| 13 | 48 | `verifier::bus::verify_bus_balance` | 949 | C | no | - | - | - |
| 13 | 175 | `verifier::layout::tables` | 222 | D | no | - | - | - |
| 14 | 45 | `verifier::layout::build_layout` | 509 | C | no | - | - | - |
| 15 | 42 | `verifier::walk` | 762 | C | no | - | - | - |
| 16 | 214 | `verifier::verify_execution` | 2 | A | no | - | - | - |
| 17 | 7 | `main` | 287 | C | no | - | - | - |
