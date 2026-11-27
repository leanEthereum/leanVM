| height | idx | function | instr | back-edges | partial class |
|---|---|---|---|---|---|
| 0 | 1 | verifier_rv64::halt | 4 | 1 | A |
| 0 | 21 | verifier::field::reduce | 14 | 0 | A |
| 0 | 22 | verifier::field::clmul_low | 72 | 0 | A |
| 0 | 34 | <verifier::field::E>::sum::<core::iter::adapters::chain::Chain<alloc::vec::into_ | 32 | 4 | D |
| 0 | 35 | <verifier::field::E>::sum::<core::iter::adapters::copied::Copied<core::slice::it | 19 | 1 | A |
| 0 | 46 | <verifier::hash::Digest>::from_halves | 61 | 0 | A |
| 0 | 50 | verifier::transcript::grinding_bits | 88 | 0 | A |
| 0 | 57 | <verifier::layout::Layout>::committed | 21 | 0 | A |
| 0 | 67 | <verifier::transcript::Transcript>::finish | 13 | 0 | A |
| 0 | 68 | core::ptr::drop_glue::<alloc::vec::Vec<(verifier::StackWeight, verifier::field:: | 1 | 0 | A |
| 0 | 73 | core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::Form>> @verifier | 1 | 0 | A |
| 0 | 105 | verifier::field::spread | 54 | 0 | A |
| 0 | 111 | <verifier::transcript::Transcript>::next | 19 | 0 | A |
| 0 | 123 | verifier::hash::xor_block | 430 | 0 | C |
| 0 | 128 | verifier::whir::whir_queries | 21 | 0 | A |
| 0 | 184 | verifier::layout::qkeccak_slot | 12 | 0 | A |
| 0 | 185 | verifier::layout::is_output_lane | 3 | 0 | A |
| 0 | 206 | <[core::mem::maybe_uninit::MaybeUninit<verifier::layout::Form>] as core::array:: | 1 | 0 | D |
| 0 | 208 | verifier::layout::keccak_cell_lanes | 59 | 3 | D |
| 0 | 223 | compiler_builtins::mem::memcpy | 127 | 10 | C |
| 0 | 224 | compiler_builtins::mem::memset | 38 | 3 | C |
| 0 | 225 | compiler_builtins::mem::memmove | 268 | 20 | C |
| 0 | 226 | memcmp | 12 | 1 | A |
| 1 | 2 | __rustc::rust_begin_unwind | 2 | 0 | A |
| 1 | 4 | <verifier_rv64::Input>::word | 12 | 0 | A |
| 1 | 6 | <verifier_rv64::Bump as core::alloc::global::GlobalAlloc>::alloc | 17 | 0 | A |
| 1 | 20 | verifier::field::clmul | 156 | 0 | A |
| 1 | 69 | core::ptr::drop_glue::<alloc::vec::Vec<alloc::vec::Vec<verifier::layout::Form>>> | 21 | 1 | C |
| 1 | 72 | core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::BusBlock>> @verifier | 21 | 1 | C |
| 1 | 104 | <verifier::field::E>::square | 36 | 0 | A |
| 1 | 151 | verifier::bus::bus_grinding_bits | 10 | 0 | A |
| 1 | 227 | memcpy | 2 | 0 | A |
| 1 | 228 | memmove | 2 | 0 | A |
| 1 | 229 | memset | 2 | 0 | A |
| 2 | 3 | <alloc::raw_vec::RawVecInner>::try_allocate_in @verifier_rv64 | 47 | 1 | C |
| 2 | 5 | <verifier_rv64::Input>::digest | 92 | 0 | C |
| 2 | 13 | core::panicking::panic_fmt | 2 | 0 | A |
| 2 | 17 | core::panicking::panic_nounwind_fmt | 2 | 0 | A |
| 2 | 19 | verifier::field::base_mul | 8 | 0 | A |
| 2 | 25 | <verifier::field::E as core::ops::arith::Mul>::mul | 61 | 0 | A |
| 2 | 37 | <alloc::raw_vec::RawVecInner>::try_allocate_in @verifier | 56 | 1 | C |
| 2 | 41 | <alloc::raw_vec::RawVecInner>::finish_grow @verifier | 66 | 0 | A |
| 2 | 71 | core::ptr::drop_glue::<alloc::vec::Vec<verifier::layout::Table>> @verifier | 25 | 1 | C |
| 2 | 114 | verifier::hash::keccak_f | 391 | 2 | C |
| 2 | 136 | verifier::ring_switch::frobenius_8 | 13 | 1 | A |
| 2 | 144 | <verifier::hash::Digest>::words | 3 | 0 | A |
| 3 | 9 | alloc::raw_vec::capacity_overflow | 2 | 0 | A |
| 3 | 10 | <alloc::vec::Vec<_, _>>::remove::assert_failed | 2 | 0 | A |
| 3 | 11 | <alloc::vec::Vec<_, _>>::split_off::assert_failed | 2 | 0 | A |
| 3 | 12 | core::panicking::assert_failed_inner | 2 | 0 | A |
| 3 | 15 | core::slice::index::slice_index_fail | 2 | 0 | A |
| 3 | 16 | core::panicking::panic_bounds_check | 2 | 0 | A |
| 3 | 18 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::iter::adapters: | 62 | 1 | D |
| 3 | 40 | <alloc::raw_vec::RawVecInner>::grow_amortized @verifier | 41 | 0 | A |
| 3 | 56 | <verifier::hash::Digest>::halves | 19 | 0 | A |
| 3 | 63 | alloc::boxed::box_new_uninit | 11 | 0 | A |
| 3 | 70 | core::ptr::drop_glue::<verifier::layout::Layout> @verifier | 23 | 0 | A |
| 3 | 108 | verifier::multilinear::poly_eval | 39 | 1 | A |
| 3 | 122 | verifier::hash::keccak_hash | 136 | 1 | C |
| 3 | 127 | <verifier::field::K>::inv | 291 | 0 | A |
| 3 | 135 | verifier::ring_switch::ring_psi | 46 | 1 | A |
| 3 | 154 | <alloc::vec::Vec<verifier::bus::ColumnClaim> as core::convert::From<[verifier::b | 28 | 0 | D |
| 3 | 156 | verifier::multilinear::index_mle | 52 | 1 | A |
| 3 | 164 | verifier::multilinear::padding_weight | 68 | 1 | A |
| 3 | 167 | <verifier::layout::Form>::term | 35 | 0 | A |
| 3 | 170 | <verifier::field::E>::pow | 45 | 2 | A |
| 3 | 213 | <verifier::transcript::Sponge>::new | 37 | 0 | C |
| 4 | 8 | alloc::raw_vec::handle_error | 5 | 0 | A |
| 4 | 14 | core::panicking::assert_failed::<usize, usize> @core | 3 | 0 | A |
| 4 | 26 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::slice::iter::It | 30 | 1 | D |
| 4 | 29 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::iter::adapters: | 51 | 2 | D |
| 4 | 30 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::iter::adapters: | 36 | 2 | C |
| 4 | 31 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::iter::adapters: | 35 | 2 | D |
| 4 | 33 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::slice::iter::It | 72 | 3 | D |
| 4 | 43 | <verifier::transcript::Transcript>::new | 20 | 0 | A |
| 4 | 49 | <verifier::layout::Table>::n_constraints | 11 | 0 | A |
| 4 | 95 | <verifier::field::Scaled>::mul | 177 | 1 | A |
| 4 | 113 | <verifier::transcript::Sponge>::duplex | 68 | 0 | A |
| 4 | 121 | verifier::merkle::hash_pair | 111 | 0 | C |
| 4 | 142 | core::array::try_from_fn::<core::ops::try_trait::NeverShortCircuit<verifier::fie | 110 | 1 | D |
| 4 | 148 | verifier::layout::jump_constraints | 67 | 0 | D |
| 4 | 157 | verifier::layout::gpow | 2 | 0 | A |
| 4 | 162 | verifier::layout::constant | 14 | 0 | A |
| 4 | 177 | <verifier::layout::Table>::count_columns | 12 | 0 | A |
| 4 | 180 | verifier::layout::keccak_shape | 7 | 0 | A |
| 4 | 183 | <core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<core::iter::a | 78 | 0 | D |
| 4 | 216 | verifier::bytecode::is_valid_encoding_of_a_leanisa_program | 287 | 2 | A |
| 5 | 24 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::slice::iter::It | 60 | 1 | D |
| 5 | 28 | verifier::multilinear::dot | 44 | 1 | A |
| 5 | 32 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::ops::range::Ran | 69 | 1 | D |
| 5 | 39 | <alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc: | 11 | 0 | A |
| 5 | 52 | <verifier::transcript::Sponge>::sample | 19 | 0 | A |
| 5 | 55 | <alloc::vec::Vec<verifier::field::E> as core::clone::Clone>::clone @verifier | 49 | 0 | C |
| 5 | 62 | <alloc::raw_vec::RawVec<verifier::bus::ColumnClaim>>::grow_one @verifier | 15 | 0 | A |
| 5 | 65 | <alloc::raw_vec::RawVec<(verifier::StackWeight, verifier::field::E)>>::grow_one  | 15 | 0 | A |
| 5 | 81 | <alloc::raw_vec::RawVec<verifier::whir::GluedClaim>>::grow_one @verifier | 15 | 0 | A |
| 5 | 83 | verifier::whir::fold_row | 104 | 3 | C |
| 5 | 91 | <alloc::raw_vec::RawVec<verifier::field::E>>::grow_one @verifier | 15 | 0 | A |
| 5 | 92 | <alloc::raw_vec::RawVec<verifier::whir::FoldRound>>::grow_one @verifier | 15 | 0 | A |
| 5 | 94 | <verifier::multilinear::Scaler>::mul | 17 | 0 | A |
| 5 | 98 | verifier::multilinear::eq_eval | 40 | 1 | A |
| 5 | 103 | verifier::ring_switch::ring_weight | 106 | 4 | C |
| 5 | 112 | <verifier::transcript::Sponge>::absorb | 43 | 0 | A |
| 5 | 118 | <alloc::raw_vec::RawVec<verifier::field::K>>::grow_one @verifier | 15 | 0 | A |
| 5 | 125 | <alloc::raw_vec::RawVec<u64>>::grow_one @verifier | 15 | 0 | A |
| 5 | 129 | <alloc::raw_vec::RawVec<usize>>::grow_one @verifier | 15 | 0 | A |
| 5 | 145 | <verifier::layout::Table>::constraints | 11 | 0 | D |
| 5 | 146 | <verifier::layout::Form>::evaluate | 16 | 0 | D |
| 5 | 147 | <alloc::raw_vec::RawVec<(alloc::vec::Vec<verifier::field::E>, alloc::vec::Vec<ve | 15 | 0 | A |
| 5 | 153 | <[usize; 2]>::try_map::<core::ops::try_trait::NeverShortCircuit<verifier::bus::C | 114 | 4 | D |
| 5 | 155 | verifier::bus::verify_bus_balance::{closure#0} @verifier | 52 | 0 | D |
| 5 | 165 | <alloc::vec::Vec<usize> as core::clone::Clone>::clone @verifier | 49 | 0 | D |
| 5 | 166 | <alloc::raw_vec::RawVec<(alloc::vec::Vec<usize>, verifier::field::E)>>::grow_one | 15 | 0 | A |
| 5 | 174 | verifier::multilinear::stack_offsets | 122 | 6 | C |
| 5 | 179 | verifier::layout::col | 34 | 0 | A |
| 5 | 192 | verifier::layout::prod | 43 | 0 | A |
| 5 | 201 | <alloc::raw_vec::RawVec<alloc::vec::Vec<verifier::layout::Form>>>::grow_one @ver | 15 | 0 | A |
| 5 | 219 | verifier::bytecode::counting_sort::<usize, verifier::bytecode::block_members::{c | 130 | 3 | C |
| 5 | 220 | verifier::bytecode::counting_sort::<(u64, u16), verifier::bytecode::group_by_wor | 105 | 3 | D |
| 5 | 221 | <alloc::raw_vec::RawVec<(verifier::field::K, alloc::vec::Vec<u16>)>>::grow_one @ | 15 | 0 | A |
| 5 | 222 | <alloc::raw_vec::RawVec<u16>>::grow_one @verifier | 15 | 0 | A |
| 6 | 23 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::iter::adapters: | 67 | 1 | D |
| 6 | 27 | <verifier::field::E>::sum::<core::iter::adapters::map::Map<core::iter::adapters: | 79 | 3 | D |
| 6 | 38 | <alloc::vec::Vec<verifier::field::E>>::reserve @verifier | 10 | 0 | C |
| 6 | 53 | verifier::field::powers | 87 | 2 | C |
| 6 | 75 | verifier::whir::derive_config | 150 | 2 | C |
| 6 | 77 | verifier::whir::sample_queries | 139 | 5 | C |
| 6 | 79 | <verifier::whir::Subspace>::at | 96 | 2 | C |
| 6 | 100 | <verifier::ring_switch::RingWeight>::evaluate | 10 | 0 | A |
| 6 | 109 | <verifier::transcript::Transcript>::next_scalar | 34 | 0 | A |
| 6 | 115 | <alloc::vec::Vec<core::option::Option<verifier::field::E>>>::reserve @verifier | 10 | 0 | C |
| 6 | 117 | <alloc::vec::Vec<verifier::field::K>>::reserve @verifier | 10 | 0 | C |
| 6 | 124 | <alloc::vec::Vec<u8>>::reserve @verifier | 10 | 0 | C |
| 6 | 149 | <verifier::transcript::Sponge>::absorb_nonce | 21 | 0 | A |
| 6 | 158 | verifier::bus::verify_bus_balance::{closure#2} @verifier | 145 | 0 | D |
| 6 | 163 | <verifier::layout::Form>::add_scaled | 177 | 8 | D |
| 6 | 168 | <alloc::vec::Vec<verifier::layout::Form> as core::clone::Clone>::clone @verifier | 142 | 2 | D |
| 6 | 169 | <alloc::vec::Vec<verifier::layout::Form>>::reserve @verifier | 10 | 0 | C |
| 6 | 173 | <alloc::vec::Vec<usize>>::reserve @verifier | 10 | 0 | C |
| 6 | 178 | <alloc::vec::Vec<verifier::layout::BusBlock>>::reserve @verifier | 10 | 0 | C |
| 6 | 200 | <verifier::layout::Flushes>::pair | 54 | 0 | D |
| 6 | 218 | verifier::bytecode::group_by_word | 193 | 7 | D |
| 7 | 36 | verifier::keccak::linear_transpose::<verifier::field::E> @verifier | 196 | 5 | A |
| 7 | 51 | <verifier::transcript::Transcript>::grind_check | 42 | 0 | A |
| 7 | 58 | <verifier::field::E as alloc::vec::spec_from_elem::SpecFromElem>::from_elem::<al | 72 | 1 | C |
| 7 | 82 | verifier::whir::ext_row | 57 | 1 | C |
| 7 | 84 | <core::option::Option<verifier::field::E> as alloc::vec::spec_from_elem::SpecFro | 89 | 2 | D |
| 7 | 102 | verifier::multilinear::selector_point | 67 | 1 | A |
| 7 | 106 | <alloc::vec::Vec<verifier::field::E> as alloc::vec::spec_extend::SpecExtend<&ver | 34 | 0 | D |
| 7 | 116 | verifier::whir::novel_basis | 108 | 3 | C |
| 7 | 120 | verifier::merkle::hash_leaf | 53 | 0 | C |
| 7 | 126 | verifier::whir::subspace_roots | 165 | 4 | C |
| 7 | 132 | <verifier::transcript::Transcript>::samples | 68 | 1 | A |
| 7 | 133 | verifier::ring_switch::ring_coefficients | 116 | 4 | C |
| 7 | 134 | verifier::ring_switch::ring_target | 109 | 2 | C |
| 7 | 140 | verifier::keccak::instance_weights | 132 | 2 | C |
| 7 | 141 | <alloc::vec::Vec<core::option::Option<verifier::field::E>> as alloc::vec::spec_f | 74 | 1 | D |
| 7 | 143 | <alloc::vec::Vec<verifier::field::E> as alloc::vec::spec_from_iter_nested::SpecF | 106 | 1 | D |
| 7 | 150 | verifier::bus::bus_layout | 147 | 3 | D |
| 7 | 159 | <verifier::layout::Form as alloc::vec::spec_from_elem::SpecFromElem>::from_elem: | 188 | 4 | D |
| 7 | 160 | <alloc::vec::Vec<verifier::layout::Form> as alloc::vec::spec_from_elem::SpecFrom | 75 | 1 | D |
| 7 | 176 | <alloc::vec::Vec<verifier::layout::BusBlock>>::extend_trusted::<core::iter::adap | 73 | 1 | D |
| 7 | 181 | verifier::layout::column_kappas | 159 | 2 | D |
| 7 | 186 | verifier::layout::stacked_blocks | 90 | 5 | D |
| 7 | 193 | <verifier::layout::Form as core::ops::arith::Add>::add | 25 | 0 | D |
| 7 | 194 | <verifier::layout::Flushes>::state_derived | 82 | 0 | D |
| 7 | 202 | <alloc::vec::Vec<verifier::layout::Form> as alloc::vec::spec_extend::SpecExtend< | 127 | 2 | D |
| 7 | 212 | <core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<core::ops::ra | 35 | 0 | C |
| 7 | 217 | verifier::bytecode::block_members | 123 | 2 | D |
| 8 | 44 | <verifier::transcript::Transcript>::next_scalars | 97 | 2 | C |
| 8 | 47 | verifier::read_ood | 50 | 0 | C |
| 8 | 61 | verifier::ring_switch::ring_switch | 77 | 0 | C |
| 8 | 76 | <verifier::whir::Subspace>::new | 80 | 1 | C |
| 8 | 80 | verifier::whir::novel_eval | 35 | 0 | C |
| 8 | 86 | verifier::whir::verify_whir::<verifier::verify_stacked_opening::{closure#1}>::{c | 79 | 1 | D |
| 8 | 87 | <[&[verifier::field::E]] as alloc::slice::Concat<verifier::field::E>>::concat @v | 70 | 2 | D |
| 8 | 96 | <verifier::field::Scaled>::new | 222 | 4 | C |
| 8 | 101 | <verifier::multilinear::Placement>::eq_above | 34 | 0 | C |
| 8 | 110 | <[alloc::vec::Vec<verifier::field::E>] as alloc::slice::Concat<verifier::field:: | 66 | 0 | D |
| 8 | 119 | <verifier::merkle::MerklePath>::root | 144 | 2 | C |
| 8 | 182 | verifier::layout::stack | 126 | 2 | D |
| 8 | 199 | <[&[verifier::layout::Form]] as alloc::slice::Concat<verifier::layout::Form>>::c | 80 | 0 | D |
| 8 | 203 | <verifier::layout::Form>::sum::<core::iter::adapters::chain::Chain<core::array:: | 146 | 2 | D |
| 8 | 204 | <verifier::layout::Form>::sum::<[verifier::layout::Form; 3]> @verifier | 63 | 0 | D |
| 8 | 205 | <verifier::layout::Flushes>::state_step | 23 | 0 | D |
| 8 | 207 | <verifier::layout::Form>::sum::<core::iter::adapters::map::Map<core::slice::iter | 84 | 1 | D |
| 8 | 211 | <verifier::layout::Form>::sum::<core::iter::adapters::flatten::Flatten<core::arr | 70 | 3 | D |
| 8 | 215 | <verifier::bytecode::Bytecode>::new | 147 | 2 | C |
| 9 | 78 | <verifier::transcript::Transcript>::merkle | 148 | 6 | C |
| 9 | 93 | <verifier::multilinear::Scaler>::new | 9 | 0 | A |
| 9 | 97 | verifier::whir::induced_weight | 115 | 3 | C |
| 9 | 99 | <verifier::StackWeight>::evaluate | 83 | 1 | A |
| 9 | 107 | <verifier::transcript::Transcript>::sumcheck_round_poly | 159 | 0 | C |
| 9 | 131 | <verifier::multilinear::Placement>::stack_point | 32 | 0 | C |
| 9 | 171 | <core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<core::ops::ra | 62 | 1 | D |
| 9 | 198 | <verifier::layout::Flushes>::counted | 65 | 0 | D |
| 9 | 209 | verifier::layout::layout_limb | 117 | 0 | D |
| 10 | 59 | verifier::multilinear::multilinear_eval::<verifier::field::K> @verifier | 110 | 1 | C |
| 10 | 85 | verifier::transcript::sumcheck | 116 | 2 | C |
| 10 | 88 | verifier::verify_stacked_opening::{closure#1} @verifier | 83 | 1 | C |
| 10 | 89 | <verifier::whir::GluedWeight>::evaluate | 31 | 0 | A |
| 10 | 90 | verifier::multilinear::multilinear_eval::<verifier::field::E> @verifier | 146 | 4 | C |
| 10 | 130 | <verifier::bus::ColumnClaim>::on_stack | 45 | 0 | A |
| 10 | 137 | verifier::multilinear::eq_kernel | 102 | 3 | C |
| 10 | 195 | <verifier::layout::Flushes>::bytecode | 117 | 0 | D |
| 10 | 197 | <verifier::layout::Flushes>::memory | 41 | 0 | D |
| 10 | 210 | <verifier::layout::Flushes>::memory_if | 68 | 0 | D |
| 11 | 54 | verifier::bus::table_sumcheck | 517 | 16 | C |
| 11 | 64 | <alloc::vec::Vec<(verifier::StackWeight, verifier::field::E)>>::extend_desugared | 55 | 3 | D |
| 11 | 74 | verifier::whir::verify_whir::<verifier::verify_stacked_opening::{closure#1}> @ve | 928 | 15 | C |
| 11 | 138 | verifier::keccak::verify_layer | 481 | 4 | D |
| 11 | 139 | verifier::keccak::open | 208 | 3 | D |
| 11 | 161 | <verifier::bytecode::Bytecode>::evaluate | 72 | 0 | C |
| 11 | 172 | <core::iter::adapters::GenericShunt<core::iter::adapters::map::Map<core::slice:: | 39 | 0 | D |
| 11 | 187 | verifier::layout::flushes_keccak | 370 | 7 | D |
| 11 | 196 | <verifier::layout::Flushes>::memory_cols | 85 | 0 | D |
| 12 | 60 | verifier::keccak::verify_keccak | 626 | 24 | D |
| 12 | 66 | verifier::verify_stacked_opening | 101 | 1 | C |
| 12 | 152 | verifier::bus::verify_gkr_grand_products | 462 | 13 | D |
| 12 | 188 | verifier::layout::flushes_arith | 261 | 0 | D |
| 12 | 189 | verifier::layout::flushes_set | 111 | 0 | D |
| 12 | 190 | verifier::layout::flushes_deref | 223 | 0 | D |
| 12 | 191 | verifier::layout::flushes_jump | 199 | 0 | D |
| 13 | 48 | verifier::bus::verify_bus_balance | 949 | 16 | C |
| 13 | 175 | verifier::layout::tables | 222 | 1 | D |
| 14 | 45 | verifier::layout::build_layout | 509 | 11 | C |
| 15 | 42 | verifier::walk | 762 | 16 | C |
| 16 | 214 | verifier::verify_execution | 2 | 0 | A |
| 17 | 7 | main | 287 | 7 | C |
