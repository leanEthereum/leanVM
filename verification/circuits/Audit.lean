import LeanVMCircuits

#print axioms LeanVMCircuits.FullAdder.soundness
#print axioms LeanVMCircuits.FullAdder.completeness
#print axioms LeanVMCircuits.Flock.lowerAffine_correct
#print axioms LeanVMCircuits.Flock.lower_correct
#print axioms LeanVMCircuits.Flock.flatten_correct
#print axioms LeanVMCircuits.Flock.adder64_source
#print axioms LeanVMCircuits.Flock.adder64_layout
#print axioms LeanVMCircuits.Flock.adder64_soundness
#print axioms LeanVMCircuits.Flock.adder64_wellFormed
#print axioms LeanVMCircuits.Flock.adder64_complete
#print axioms LeanVMCircuits.Flock.lookup_rejected
#print axioms LeanVMCircuits.Flock.interaction_rejected

#print axioms LeanVMCircuits.Flock.adder32_source
#print axioms LeanVMCircuits.Flock.adder32_soundness
#print axioms LeanVMCircuits.Flock.adder32_layout
#print axioms LeanVMCircuits.Flock.adder32_wellFormed
#print axioms LeanVMCircuits.Flock.adder32_complete
#print axioms LeanVMCircuits.Flock.carryAdder64_source
#print axioms LeanVMCircuits.Flock.carryAdder64_soundness
#print axioms LeanVMCircuits.Flock.carryAdder64_layout
#print axioms LeanVMCircuits.Flock.carryAdder64_wellFormed
#print axioms LeanVMCircuits.Flock.carryAdder64_complete

#print axioms LeanVMCircuits.Shift.assumptions_iff_legal_flags
#print axioms LeanVMCircuits.Flock.Shift.supported
#print axioms LeanVMCircuits.Flock.Shift.source_eq
#print axioms LeanVMCircuits.Flock.Shift.layout
#print axioms LeanVMCircuits.Flock.Shift.soundness
#print axioms LeanVMCircuits.Flock.Shift.wellFormed
#print axioms LeanVMCircuits.Flock.Shift.complete

#print axioms LeanVMCircuits.Gates.lower_correct
#print axioms LeanVMCircuits.Gates.lower_append
#print axioms LeanVMCircuits.Gates.lower_wellFormed
#print axioms LeanVMCircuits.Gates.witness_exists
#print axioms LeanVMCircuits.Gates.lowerCircuit_soundness
#print axioms LeanVMCircuits.Gates.lowerCircuit_completeness
#print axioms LeanVMCircuits.Blake2s.Rfc7693.abc
#print axioms LeanVMCircuits.Blake2s.program_correct
#print axioms LeanVMCircuits.Blake2s.program_valid
#print axioms LeanVMCircuits.Blake2s.Compress.soundness
#print axioms LeanVMCircuits.Blake2s.Compress.completeness
#print axioms LeanVMCircuits.Blake2s.Compress.lowered
#print axioms LeanVMCircuits.Blake2s.Export.soundness
#print axioms LeanVMCircuits.Blake2s.Export.completeness
#print axioms LeanVMCircuits.Blake2s.Export.adder31_source
#print axioms LeanVMCircuits.Blake2s.Export.adder31_soundness
#print axioms LeanVMCircuits.Blake2s.Export.adder31_layout
#print axioms LeanVMCircuits.Blake2s.Export.adder31_wellFormed
#print axioms LeanVMCircuits.Blake2s.Export.adder31_complete
#print axioms LeanVMCircuits.Blake2s.Export.adder32_canonical
#print axioms LeanVMCircuits.Blake2s.Export.adder31_canonical
#print axioms LeanVMCircuits.Blake2s.Export.adder32_call
#print axioms LeanVMCircuits.Blake2s.Export.adder31_call

#print axioms LeanVMCircuits.Rec.modulus_irreducible
#print axioms LeanVMCircuits.Rec.chain_squares
#print axioms LeanVMCircuits.Rec.cofactor_mul
#print axioms LeanVMCircuits.Rec.root_pow_two_pow_64
#print axioms LeanVMCircuits.Rec.root_pow_two_pow_32_sub_unit
#print axioms LeanVMCircuits.Rec.ev_mul
#print axioms LeanVMCircuits.Rec.toWord_ofWord
#print axioms LeanVMCircuits.Rec.toWord_injective
#print axioms LeanVMCircuits.Rec.toE_mul
#print axioms LeanVMCircuits.Rec.toE_add
#print axioms LeanVMCircuits.Rec.toE_smul
#print axioms LeanVMCircuits.Rec.toE_injective
#print axioms LeanVMCircuits.Rec.Form.eval_expr
#print axioms LeanVMCircuits.Rec.emul_spec
#print axioms LeanVMCircuits.Rec.exk_spec
#print axioms LeanVMCircuits.Rec.boolean_spec
#print axioms LeanVMCircuits.Rec.hash_mux
#print axioms LeanVMCircuits.Rec.split_spec
#print axioms LeanVMCircuits.Rec.Identity.eval_expr
#print axioms LeanVMCircuits.Rec.identities

#print axioms LeanVMCircuits.Rec.inverse_row
#print axioms LeanVMCircuits.Rec.add_row
#print axioms LeanVMCircuits.Rec.pack_row
#print axioms LeanVMCircuits.Rec.cast_views
#print axioms LeanVMCircuits.Rec.hash_outputs
#print axioms LeanVMCircuits.Rec.node_row

#print axioms LeanVMCircuits.Rec.words_ofFn
#print axioms LeanVMCircuits.Rec.hash_ports_compress
#print axioms LeanVMCircuits.Rec.hash_row_compress

#print axioms LeanVMCircuits.Rec.half_digest
#print axioms LeanVMCircuits.Rec.eq_digest
#print axioms LeanVMCircuits.Rec.hWords_digest
#print axioms LeanVMCircuits.Rec.hash_row_digest
#print axioms LeanVMCircuits.Rec.blocksFrom_append
#print axioms LeanVMCircuits.Rec.chain_digest
#print axioms LeanVMCircuits.Rec.node_message
#print axioms LeanVMCircuits.Rec.node_row_digest
#print axioms LeanVMCircuits.Rec.path_root
#print axioms LeanVMCircuits.Rec.opening_node
#print axioms LeanVMCircuits.Rec.parent_row_digest
#print axioms LeanVMCircuits.Rec.parent_right
#print axioms LeanVMCircuits.Rec.tree_nodes
#print axioms LeanVMCircuits.Rec.tree_root
#print axioms LeanVMCircuits.Rec.msg_block
#print axioms LeanVMCircuits.Rec.chain_rows
#print axioms LeanVMCircuits.Rec.statement_digest

#print axioms LeanVMCircuits.Rec.digest_cvWords
#print axioms LeanVMCircuits.Rec.cvWords_digest
#print axioms LeanVMCircuits.Rec.comp_row
#print axioms LeanVMCircuits.Rec.flush_rows
#print axioms LeanVMCircuits.Rec.absorbWord_rows
#print axioms LeanVMCircuits.Rec.squeezeWord_rows
#print axioms LeanVMCircuits.Rec.flush_inv
#print axioms LeanVMCircuits.Rec.step_rows
#print axioms LeanVMCircuits.Rec.run_rows
#print axioms LeanVMCircuits.Rec.seed_row
#print axioms LeanVMCircuits.Rec.new_inv
#print axioms LeanVMCircuits.Rec.trial_rows
#print axioms LeanVMCircuits.Rec.pow_rows

#print axioms LeanVMCircuits.Rec.bus_next
#print axioms LeanVMCircuits.Rec.classNext_forward
#print axioms LeanVMCircuits.Rec.classNext_cls
#print axioms LeanVMCircuits.Rec.classNext_wrap
#print axioms LeanVMCircuits.Rec.classNext_injective
#print axioms LeanVMCircuits.Rec.class_eq
#print axioms LeanVMCircuits.Rec.slotKey_injective
#print axioms LeanVMCircuits.Rec.copy_argument
#print axioms LeanVMCircuits.Rec.card_K
#print axioms LeanVMCircuits.Rec.no_root
#print axioms LeanVMCircuits.Rec.extModulus_irreducible
#print axioms LeanVMCircuits.Rec.exists_inverse

#print axioms LeanVMCircuits.Rec.Model.constant_good
#print axioms LeanVMCircuits.Rec.Model.emul_good
#print axioms LeanVMCircuits.Rec.Model.emulKey_sem
#print axioms LeanVMCircuits.Rec.Model.add_good
#print axioms LeanVMCircuits.Rec.Model.mulAdd_good
#print axioms LeanVMCircuits.Rec.Model.mul_good
#print axioms LeanVMCircuits.Rec.Model.mulKAdd_good
#print axioms LeanVMCircuits.Rec.Model.mulConstAdd_good
#print axioms LeanVMCircuits.Rec.Model.inv_good
#print axioms LeanVMCircuits.Rec.Model.sum_good
#print axioms LeanVMCircuits.Rec.Model.castRow_good
#print axioms LeanVMCircuits.Rec.Model.split_good
#print axioms LeanVMCircuits.Rec.Model.pack_good
#print axioms LeanVMCircuits.Rec.Model.eToK_good
#print axioms LeanVMCircuits.Rec.Model.kToE_good
#print axioms LeanVMCircuits.Rec.Model.dToK_good
#print axioms LeanVMCircuits.Rec.Model.dToEAndK_good
#print axioms LeanVMCircuits.Rec.Model.halvesToD_good
#print axioms LeanVMCircuits.Rec.Model.singleBlock_good
#print axioms LeanVMCircuits.Rec.Model.node_good
#print axioms LeanVMCircuits.Rec.Model.parent_good
#print axioms LeanVMCircuits.Rec.Model.compress_good
#print axioms LeanVMCircuits.Rec.Model.leafBlock_good
#print axioms LeanVMCircuits.Rec.Model.chainBlocks_good
#print axioms LeanVMCircuits.Rec.Model.chain_good
#print axioms LeanVMCircuits.Rec.Model.expose_good
#print axioms LeanVMCircuits.Rec.Model.Call.exec_good
#print axioms LeanVMCircuits.Rec.Model.replay_sound

#print axioms LeanVMCircuits.Rec.absorbWord_fits
#print axioms LeanVMCircuits.Rec.squeezeWord_fits
#print axioms LeanVMCircuits.Rec.step_fits
#print axioms LeanVMCircuits.Rec.run_fits
#print axioms LeanVMCircuits.Rec.tweak_injective
#print axioms LeanVMCircuits.Rec.tag_ne_tweak

open Lean Elab Command in
run_cmd do
  for theoremName in #[
    ``LeanVMCircuits.FullAdder.soundness, ``LeanVMCircuits.FullAdder.completeness,
    ``LeanVMCircuits.Flock.lowerAffine_correct, ``LeanVMCircuits.Flock.lower_correct,
    ``LeanVMCircuits.Flock.flatten_correct, ``LeanVMCircuits.Flock.adder64_source,
    ``LeanVMCircuits.Flock.adder64_layout, ``LeanVMCircuits.Flock.adder64_soundness,
    ``LeanVMCircuits.Flock.adder64_wellFormed, ``LeanVMCircuits.Flock.adder64_complete,
    ``LeanVMCircuits.Flock.adder32_source, ``LeanVMCircuits.Flock.adder32_soundness,
    ``LeanVMCircuits.Flock.adder32_layout, ``LeanVMCircuits.Flock.adder32_wellFormed,
    ``LeanVMCircuits.Flock.adder32_complete, ``LeanVMCircuits.Flock.carryAdder64_source,
    ``LeanVMCircuits.Flock.carryAdder64_soundness, ``LeanVMCircuits.Flock.carryAdder64_layout,
    ``LeanVMCircuits.Flock.carryAdder64_wellFormed, ``LeanVMCircuits.Flock.carryAdder64_complete,
    ``LeanVMCircuits.Shift.assumptions_iff_legal_flags,
    ``LeanVMCircuits.Flock.Shift.supported, ``LeanVMCircuits.Flock.Shift.source_eq,
    ``LeanVMCircuits.Flock.Shift.layout, ``LeanVMCircuits.Flock.Shift.soundness,
    ``LeanVMCircuits.Flock.Shift.wellFormed, ``LeanVMCircuits.Flock.Shift.complete,
    ``LeanVMCircuits.Flock.lookup_rejected, ``LeanVMCircuits.Flock.interaction_rejected,
    ``LeanVMCircuits.Gates.lower_correct, ``LeanVMCircuits.Gates.lower_append,
    ``LeanVMCircuits.Gates.lower_wellFormed, ``LeanVMCircuits.Gates.witness_exists,
    ``LeanVMCircuits.Gates.lowerCircuit_soundness, ``LeanVMCircuits.Gates.lowerCircuit_completeness,
    ``LeanVMCircuits.Blake2s.Rfc7693.abc, ``LeanVMCircuits.Blake2s.program_correct,
    ``LeanVMCircuits.Blake2s.program_valid, ``LeanVMCircuits.Blake2s.Compress.soundness,
    ``LeanVMCircuits.Blake2s.Compress.completeness, ``LeanVMCircuits.Blake2s.Compress.lowered,
    ``LeanVMCircuits.Blake2s.Export.soundness, ``LeanVMCircuits.Blake2s.Export.completeness,
    ``LeanVMCircuits.Blake2s.Export.adder31_source, ``LeanVMCircuits.Blake2s.Export.adder31_soundness,
    ``LeanVMCircuits.Blake2s.Export.adder31_layout, ``LeanVMCircuits.Blake2s.Export.adder31_wellFormed,
    ``LeanVMCircuits.Blake2s.Export.adder31_complete, ``LeanVMCircuits.Blake2s.Export.adder32_canonical,
    ``LeanVMCircuits.Blake2s.Export.adder31_canonical, ``LeanVMCircuits.Blake2s.Export.adder32_call,
    ``LeanVMCircuits.Blake2s.Export.adder31_call,    ``LeanVMCircuits.Rec.modulus_irreducible, ``LeanVMCircuits.Rec.chain_squares,
    ``LeanVMCircuits.Rec.cofactor_mul, ``LeanVMCircuits.Rec.root_pow_two_pow_64,
    ``LeanVMCircuits.Rec.root_pow_two_pow_32_sub_unit, ``LeanVMCircuits.Rec.ev_mul,
    ``LeanVMCircuits.Rec.toWord_ofWord, ``LeanVMCircuits.Rec.toWord_injective,
    ``LeanVMCircuits.Rec.toE_mul, ``LeanVMCircuits.Rec.toE_add,
    ``LeanVMCircuits.Rec.toE_smul, ``LeanVMCircuits.Rec.toE_injective,
    ``LeanVMCircuits.Rec.Form.eval_expr, ``LeanVMCircuits.Rec.emul_spec,
    ``LeanVMCircuits.Rec.exk_spec, ``LeanVMCircuits.Rec.boolean_spec,
    ``LeanVMCircuits.Rec.hash_mux, ``LeanVMCircuits.Rec.split_spec,
    ``LeanVMCircuits.Rec.Identity.eval_expr, ``LeanVMCircuits.Rec.identities,
    ``LeanVMCircuits.Rec.inverse_row, ``LeanVMCircuits.Rec.add_row,
    ``LeanVMCircuits.Rec.pack_row, ``LeanVMCircuits.Rec.cast_views,
    ``LeanVMCircuits.Rec.hash_outputs, ``LeanVMCircuits.Rec.node_row,
    ``LeanVMCircuits.Rec.words_ofFn, ``LeanVMCircuits.Rec.hash_ports_compress,
    ``LeanVMCircuits.Rec.hash_row_compress,
    ``LeanVMCircuits.Rec.half_digest,
    ``LeanVMCircuits.Rec.eq_digest,
    ``LeanVMCircuits.Rec.hWords_digest,
    ``LeanVMCircuits.Rec.hash_row_digest,
    ``LeanVMCircuits.Rec.blocksFrom_append,
    ``LeanVMCircuits.Rec.chain_digest,
    ``LeanVMCircuits.Rec.node_message,
    ``LeanVMCircuits.Rec.node_row_digest,
    ``LeanVMCircuits.Rec.path_root,
    ``LeanVMCircuits.Rec.opening_node,
    ``LeanVMCircuits.Rec.parent_row_digest,
    ``LeanVMCircuits.Rec.parent_right,
    ``LeanVMCircuits.Rec.tree_nodes,
    ``LeanVMCircuits.Rec.tree_root,
    ``LeanVMCircuits.Rec.msg_block,
    ``LeanVMCircuits.Rec.chain_rows,
    ``LeanVMCircuits.Rec.statement_digest,
    ``LeanVMCircuits.Rec.digest_cvWords,
    ``LeanVMCircuits.Rec.cvWords_digest,
    ``LeanVMCircuits.Rec.comp_row,
    ``LeanVMCircuits.Rec.flush_rows,
    ``LeanVMCircuits.Rec.absorbWord_rows,
    ``LeanVMCircuits.Rec.absorb_rows,
    ``LeanVMCircuits.Rec.flush_inv,
    ``LeanVMCircuits.Rec.squeezeWord_rows,
    ``LeanVMCircuits.Rec.squeeze_rows,
    ``LeanVMCircuits.Rec.absorbWord_inv,
    ``LeanVMCircuits.Rec.absorb_inv,
    ``LeanVMCircuits.Rec.step_rows,
    ``LeanVMCircuits.Rec.run_rows,
    ``LeanVMCircuits.Rec.wordAt_append_zeros,
    ``LeanVMCircuits.Rec.seed_row,
    ``LeanVMCircuits.Rec.new_inv,
    ``LeanVMCircuits.Rec.trial_rows,
    ``LeanVMCircuits.Rec.pow_rows,
    ``LeanVMCircuits.Load.circuit, ``LeanVMCircuits.Store.circuit,
    ``LeanVMCircuits.Memory.legal_load_flags, ``LeanVMCircuits.Memory.legal_store_flags,
    ``LeanVMCircuits.Memory.bus_aligned_iff, ``LeanVMCircuits.StoreMask.select_eq_store,
    ``LeanVMCircuits.Flock.Load.supported, ``LeanVMCircuits.Flock.Load.source_eq,
    ``LeanVMCircuits.Flock.Load.soundness, ``LeanVMCircuits.Flock.Load.layout,
    ``LeanVMCircuits.Flock.Load.wellFormed, ``LeanVMCircuits.Flock.Load.complete,
    ``LeanVMCircuits.Flock.Store.supported, ``LeanVMCircuits.Flock.Store.source_eq,
    ``LeanVMCircuits.Flock.Store.soundness, ``LeanVMCircuits.Flock.Store.layout,
    ``LeanVMCircuits.Flock.Store.wellFormed, ``LeanVMCircuits.Flock.Store.complete,
    ``LeanVMCircuits.Rec.bus_next,
    ``LeanVMCircuits.Rec.classNext_forward,
    ``LeanVMCircuits.Rec.classNext_cls,
    ``LeanVMCircuits.Rec.classNext_wrap,
    ``LeanVMCircuits.Rec.classNext_injective,
    ``LeanVMCircuits.Rec.class_eq,
    ``LeanVMCircuits.Rec.slotKey_injective,
    ``LeanVMCircuits.Rec.copy_argument,
    ``LeanVMCircuits.Rec.card_K,
    ``LeanVMCircuits.Rec.no_root,
    ``LeanVMCircuits.Rec.extModulus_irreducible,
    ``LeanVMCircuits.Rec.exists_inverse,
    ``LeanVMCircuits.Rec.Model.constant_good,
    ``LeanVMCircuits.Rec.Model.emul_good,
    ``LeanVMCircuits.Rec.Model.emulKey_sem,
    ``LeanVMCircuits.Rec.Model.add_good,
    ``LeanVMCircuits.Rec.Model.mulAdd_good,
    ``LeanVMCircuits.Rec.Model.mul_good,
    ``LeanVMCircuits.Rec.Model.mulKAdd_good,
    ``LeanVMCircuits.Rec.Model.mulConstAdd_good,
    ``LeanVMCircuits.Rec.Model.inv_good,
    ``LeanVMCircuits.Rec.Model.sum_good,
    ``LeanVMCircuits.Rec.Model.castRow_good,
    ``LeanVMCircuits.Rec.Model.split_good,
    ``LeanVMCircuits.Rec.Model.pack_good,
    ``LeanVMCircuits.Rec.Model.eToK_good,
    ``LeanVMCircuits.Rec.Model.kToE_good,
    ``LeanVMCircuits.Rec.Model.dToK_good,
    ``LeanVMCircuits.Rec.Model.dToEAndK_good,
    ``LeanVMCircuits.Rec.Model.halvesToD_good,
    ``LeanVMCircuits.Rec.Model.kToD_good,
    ``LeanVMCircuits.Rec.Model.dToHalves_good,
    ``LeanVMCircuits.Rec.Model.singleBlock_good,
    ``LeanVMCircuits.Rec.Model.node_good,
    ``LeanVMCircuits.Rec.Model.parent_good,
    ``LeanVMCircuits.Rec.Model.compress_good,
    ``LeanVMCircuits.Rec.Model.leafBlock_good,
    ``LeanVMCircuits.Rec.Model.leafBlock_eq,
    ``LeanVMCircuits.Rec.Model.hashBlock_good,
    ``LeanVMCircuits.Rec.Model.chainBlocks_good,
    ``LeanVMCircuits.Rec.Model.chain_good,
    ``LeanVMCircuits.Rec.Model.expose_good,
    ``LeanVMCircuits.Rec.Model.Call.exec_good,
    ``LeanVMCircuits.Rec.Model.replay_sound,
    ``LeanVMCircuits.Rec.absorbWord_fits,
    ``LeanVMCircuits.Rec.absorb_fits,
    ``LeanVMCircuits.Rec.squeezeWord_fits,
    ``LeanVMCircuits.Rec.squeeze_fits,
    ``LeanVMCircuits.Rec.step_fits,
    ``LeanVMCircuits.Rec.run_fits,
    ``LeanVMCircuits.Rec.tweak_injective,
    ``LeanVMCircuits.Rec.tag_ne_tweak,
    ``LeanVMCircuits.Alu.circuit,
    ``LeanVMCircuits.Alu.spec_raw,
    ``LeanVMCircuits.Alu.afterArithmetic_reference,
    ``LeanVMCircuits.Flock.Alu.supported,
    ``LeanVMCircuits.Flock.Alu.source_eq,
    ``LeanVMCircuits.Flock.Alu.soundness,
    ``LeanVMCircuits.Flock.Alu.soundness_reference,
    ``LeanVMCircuits.Flock.Alu.layout,
    ``LeanVMCircuits.Flock.Alu.output_products_layout,
    ``LeanVMCircuits.Flock.Alu.wellFormed,
    ``LeanVMCircuits.Flock.Alu.complete,
    ``LeanVMCircuits.Bus.Flushes.balanced_iff,
    ``LeanVMCircuits.Bus.product_eq_iff,
    ``LeanVMCircuits.Bus.balanced_iff_product_eq,
    ``LeanVMCircuits.Bus.producer_leaves_eq,
    ``LeanVMCircuits.Bus.balanced_of_product_check,
    ``LeanVMCircuits.Bus.LookupArray.lookup_correct,
    ``LeanVMCircuits.Bus.LookupArray.lookup_correct_of_product_check,
    ``LeanVMCircuits.Bus.LookupArray.read_addr_in_range,
    ``LeanVMCircuits.Bus.bytecode_reads_correct,
    ``LeanVMCircuits.Bus.exists_walk,
    ``LeanVMCircuits.Bus.exists_closedWalks,
    ``LeanVMCircuits.Bus.state_walk,
    ``LeanVMCircuits.Bus.memory_consistent,
    ``LeanVMCircuits.Bus.ofWord_add_slot,
    ``LeanVMCircuits.Bus.memory_consistent_of_state_walk,
    ``LeanVMCircuits.Bus.memory_consistent_shared,
    ``LeanVMCircuits.Bus.machine_correct,
    ``LeanVMCircuits.Bus.machine_correct_of_product_check,
    ``LeanVMCircuits.Bus.ClassTable.all_wellFormed,
    ``LeanVMCircuits.Bus.ClassTable.all_slots,
    ``LeanVMCircuits.Bus.ClassTable.Coord.eval_expr,
    ``LeanVMCircuits.Bus.ClassTable.sourceTuple_eq,
    ``LeanVMCircuits.Bus.ClassTable.Spec.source_eq,
    ``LeanVMCircuits.Bus.ClassTable.Spec.pushes_eq,
    ``LeanVMCircuits.Bus.ClassTable.Spec.pulls_eq,
    ``LeanVMCircuits.Bus.ClassTable.Spec.row_c1,
    ``LeanVMCircuits.Bus.ClassTable.Spec.row_c2,
    ``LeanVMCircuits.Bus.ClassTable.Spec.row_c3,
    ``LeanVMCircuits.Bus.ClassTable.row_correct,
    ``LeanVMCircuits.Bus.clock_next,
    ``LeanVMCircuits.Bus.clock_in_order,
    ``LeanVMCircuits.Bus.machine_reads_at_pc,
    ``LeanVMCircuits.Bus.ClassTable.tables_correct,
    ``LeanVMCircuits.ClockStep.circuit, ``LeanVMCircuits.Flock.Clock.soundness_of,
    ``LeanVMCircuits.Flock.Clock.Registers.supported, ``LeanVMCircuits.Flock.Clock.Registers.source_eq,
    ``LeanVMCircuits.Flock.Clock.Registers.soundness, ``LeanVMCircuits.Flock.Clock.Registers.layout,
    ``LeanVMCircuits.Flock.Clock.Registers.output_products_layout,
    ``LeanVMCircuits.Flock.Clock.Registers.wellFormed, ``LeanVMCircuits.Flock.Clock.Registers.complete,
    ``LeanVMCircuits.Flock.Clock.Load.supported, ``LeanVMCircuits.Flock.Clock.Load.source_eq,
    ``LeanVMCircuits.Flock.Clock.Load.soundness, ``LeanVMCircuits.Flock.Clock.Load.layout,
    ``LeanVMCircuits.Flock.Clock.Load.output_products_layout,
    ``LeanVMCircuits.Flock.Clock.Load.wellFormed, ``LeanVMCircuits.Flock.Clock.Load.complete,
    ``LeanVMCircuits.Flock.Clock.Store.supported, ``LeanVMCircuits.Flock.Clock.Store.source_eq,
    ``LeanVMCircuits.Flock.Clock.Store.soundness, ``LeanVMCircuits.Flock.Clock.Store.layout,
    ``LeanVMCircuits.Flock.Clock.Store.output_products_layout,
    ``LeanVMCircuits.Flock.Clock.Store.wellFormed, ``LeanVMCircuits.Flock.Clock.Store.complete,
    ``LeanVMCircuits.Flock.Clock.Hash.supported, ``LeanVMCircuits.Flock.Clock.Hash.source_eq,
    ``LeanVMCircuits.Flock.Clock.Hash.soundness, ``LeanVMCircuits.Flock.Clock.Hash.layout,
    ``LeanVMCircuits.Flock.Clock.Hash.output_products_layout,
    ``LeanVMCircuits.Flock.Clock.Hash.wellFormed, ``LeanVMCircuits.Flock.Clock.Hash.complete,
    ``LeanVMCircuits.Flock.Clock.Ext.supported, ``LeanVMCircuits.Flock.Clock.Ext.source_eq,
    ``LeanVMCircuits.Flock.Clock.Ext.soundness, ``LeanVMCircuits.Flock.Clock.Ext.layout,
    ``LeanVMCircuits.Flock.Clock.Ext.output_products_layout,
    ``LeanVMCircuits.Flock.Clock.Ext.wellFormed, ``LeanVMCircuits.Flock.Clock.Ext.complete,
    ``LeanVMCircuits.ExtClockValues.incrOut_value,
    ``LeanVMCircuits.ExtClock.circuit,
    ``LeanVMCircuits.Flock.ExtClock.supported,
    ``LeanVMCircuits.Flock.ExtClock.source_eq,
    ``LeanVMCircuits.Flock.ExtClock.soundness,
    ``LeanVMCircuits.Flock.ExtClock.layout,
    ``LeanVMCircuits.Flock.ExtClock.output_products_layout,
    ``LeanVMCircuits.Flock.ExtClock.wellFormed,
    ``LeanVMCircuits.Flock.ExtClock.complete,
    ``LeanVMCircuits.Bus.ClassTable.clock_sound,
    ``LeanVMCircuits.Bus.ClassTable.tables_correct_of_clock,
    ``LeanVMCircuits.Multiply.check64,
    ``LeanVMCircuits.Multiply.check128,
    ``LeanVMCircuits.Multiply.product_value,
    ``LeanVMCircuits.Multiply.gates_product,
    ``LeanVMCircuits.Multiply.layout_wellOrdered,
    ``LeanVMCircuits.Multiply.soundness,
    ``LeanVMCircuits.Multiply.completeness,
    ``LeanVMCircuits.Netlist.holds_iff,
    ``LeanVMCircuits.Netlist.lower_opsFrom,
    ``LeanVMCircuits.Netlist.complete,
    ``LeanVMCircuits.MulDiv.mul_eq,
    ``LeanVMCircuits.MulDiv.mulh_eq,
    ``LeanVMCircuits.MulDiv.div_eq,
    ``LeanVMCircuits.Mul.circuit,
    ``LeanVMCircuits.Mulh.circuit,
    ``LeanVMCircuits.Div.circuit,
    ``LeanVMCircuits.Div.compose,
    ``LeanVMCircuits.Div.honest_hints,
    ``LeanVMCircuits.MulDivExport.multiplier_call,
    ``LeanVMCircuits.MulDivExport.Mul.source,
    ``LeanVMCircuits.MulDivExport.Mul.soundness,
    ``LeanVMCircuits.MulDivExport.Mul.completeness,
    ``LeanVMCircuits.MulDivExport.Mulh.source,
    ``LeanVMCircuits.MulDivExport.Mulh.soundness,
    ``LeanVMCircuits.MulDivExport.Mulh.completeness,
    ``LeanVMCircuits.MulDivExport.Div.source,
    ``LeanVMCircuits.MulDivExport.Div.soundness,
    ``LeanVMCircuits.MulDivExport.Div.completeness,
    ``LeanVMCircuits.ExtensionProduct.source,
    ``LeanVMCircuits.ExtensionProduct.source_holds,
    ``LeanVMCircuits.ExtensionProduct.result_limbs,
    ``LeanVMCircuits.ExtensionProduct.soundness_iff,
    ``LeanVMCircuits.ExtensionProduct.instruction_soundness,
    ``LeanVMCircuits.ExtensionProduct.base_operand,
    ``LeanVMCircuits.ExtensionProduct.witness_exists] do
    let axioms ← collectAxioms theoremName
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{theoremName} depends on unexpected axiom {axiomName}"

#print axioms LeanVMCircuits.Load.circuit
#print axioms LeanVMCircuits.Store.circuit
#print axioms LeanVMCircuits.Memory.legal_load_flags
#print axioms LeanVMCircuits.Memory.legal_store_flags
#print axioms LeanVMCircuits.Memory.bus_aligned_iff
#print axioms LeanVMCircuits.StoreMask.select_eq_store
#print axioms LeanVMCircuits.Flock.Load.supported
#print axioms LeanVMCircuits.Flock.Load.source_eq
#print axioms LeanVMCircuits.Flock.Load.soundness
#print axioms LeanVMCircuits.Flock.Load.layout
#print axioms LeanVMCircuits.Flock.Load.wellFormed
#print axioms LeanVMCircuits.Flock.Load.complete
#print axioms LeanVMCircuits.Flock.Store.supported
#print axioms LeanVMCircuits.Flock.Store.source_eq
#print axioms LeanVMCircuits.Flock.Store.soundness
#print axioms LeanVMCircuits.Flock.Store.layout
#print axioms LeanVMCircuits.Flock.Store.wellFormed
#print axioms LeanVMCircuits.Flock.Store.complete

#print axioms LeanVMCircuits.Alu.circuit
#print axioms LeanVMCircuits.Alu.spec_raw
#print axioms LeanVMCircuits.Alu.afterArithmetic_reference
#print axioms LeanVMCircuits.Flock.Alu.supported
#print axioms LeanVMCircuits.Flock.Alu.source_eq
#print axioms LeanVMCircuits.Flock.Alu.soundness
#print axioms LeanVMCircuits.Flock.Alu.soundness_reference
#print axioms LeanVMCircuits.Flock.Alu.layout
#print axioms LeanVMCircuits.Flock.Alu.output_products_layout
#print axioms LeanVMCircuits.Flock.Alu.wellFormed
#print axioms LeanVMCircuits.Flock.Alu.complete

#print axioms LeanVMCircuits.Bus.Flushes.balanced_iff
#print axioms LeanVMCircuits.Bus.product_eq_iff
#print axioms LeanVMCircuits.Bus.balanced_iff_product_eq
#print axioms LeanVMCircuits.Bus.producer_leaves_eq
#print axioms LeanVMCircuits.Bus.balanced_of_product_check
#print axioms LeanVMCircuits.Bus.LookupArray.lookup_correct
#print axioms LeanVMCircuits.Bus.LookupArray.lookup_correct_of_product_check
#print axioms LeanVMCircuits.Bus.LookupArray.read_addr_in_range
#print axioms LeanVMCircuits.Bus.bytecode_reads_correct
#print axioms LeanVMCircuits.Bus.exists_walk
#print axioms LeanVMCircuits.Bus.exists_closedWalks
#print axioms LeanVMCircuits.Bus.state_walk
#print axioms LeanVMCircuits.Bus.memory_consistent
#print axioms LeanVMCircuits.Bus.ofWord_add_slot
#print axioms LeanVMCircuits.Bus.memory_consistent_of_state_walk
#print axioms LeanVMCircuits.Bus.memory_consistent_shared
#print axioms LeanVMCircuits.Bus.machine_correct
#print axioms LeanVMCircuits.Bus.machine_correct_of_product_check
#print axioms LeanVMCircuits.Bus.ClassTable.all_wellFormed
#print axioms LeanVMCircuits.Bus.ClassTable.all_slots
#print axioms LeanVMCircuits.Bus.ClassTable.Coord.eval_expr
#print axioms LeanVMCircuits.Bus.ClassTable.sourceTuple_eq
#print axioms LeanVMCircuits.Bus.ClassTable.Spec.source_eq
#print axioms LeanVMCircuits.Bus.ClassTable.Spec.pushes_eq
#print axioms LeanVMCircuits.Bus.ClassTable.Spec.pulls_eq
#print axioms LeanVMCircuits.Bus.ClassTable.Spec.row_c1
#print axioms LeanVMCircuits.Bus.ClassTable.Spec.row_c2
#print axioms LeanVMCircuits.Bus.ClassTable.Spec.row_c3
#print axioms LeanVMCircuits.Bus.ClassTable.row_correct
#print axioms LeanVMCircuits.Bus.clock_next
#print axioms LeanVMCircuits.Bus.clock_in_order
#print axioms LeanVMCircuits.Bus.machine_reads_at_pc
#print axioms LeanVMCircuits.Bus.ClassTable.tables_correct

#print axioms LeanVMCircuits.ClockStep.circuit
#print axioms LeanVMCircuits.Flock.Clock.soundness_of
#print axioms LeanVMCircuits.Flock.Clock.Registers.supported
#print axioms LeanVMCircuits.Flock.Clock.Registers.source_eq
#print axioms LeanVMCircuits.Flock.Clock.Registers.soundness
#print axioms LeanVMCircuits.Flock.Clock.Registers.layout
#print axioms LeanVMCircuits.Flock.Clock.Registers.output_products_layout
#print axioms LeanVMCircuits.Flock.Clock.Registers.wellFormed
#print axioms LeanVMCircuits.Flock.Clock.Registers.complete
#print axioms LeanVMCircuits.Flock.Clock.Load.supported
#print axioms LeanVMCircuits.Flock.Clock.Load.source_eq
#print axioms LeanVMCircuits.Flock.Clock.Load.soundness
#print axioms LeanVMCircuits.Flock.Clock.Load.layout
#print axioms LeanVMCircuits.Flock.Clock.Load.output_products_layout
#print axioms LeanVMCircuits.Flock.Clock.Load.wellFormed
#print axioms LeanVMCircuits.Flock.Clock.Load.complete
#print axioms LeanVMCircuits.Flock.Clock.Store.supported
#print axioms LeanVMCircuits.Flock.Clock.Store.source_eq
#print axioms LeanVMCircuits.Flock.Clock.Store.soundness
#print axioms LeanVMCircuits.Flock.Clock.Store.layout
#print axioms LeanVMCircuits.Flock.Clock.Store.output_products_layout
#print axioms LeanVMCircuits.Flock.Clock.Store.wellFormed
#print axioms LeanVMCircuits.Flock.Clock.Store.complete
#print axioms LeanVMCircuits.Flock.Clock.Hash.supported
#print axioms LeanVMCircuits.Flock.Clock.Hash.source_eq
#print axioms LeanVMCircuits.Flock.Clock.Hash.soundness
#print axioms LeanVMCircuits.Flock.Clock.Hash.layout
#print axioms LeanVMCircuits.Flock.Clock.Hash.output_products_layout
#print axioms LeanVMCircuits.Flock.Clock.Hash.wellFormed
#print axioms LeanVMCircuits.Flock.Clock.Hash.complete
#print axioms LeanVMCircuits.Flock.Clock.Ext.supported
#print axioms LeanVMCircuits.Flock.Clock.Ext.source_eq
#print axioms LeanVMCircuits.Flock.Clock.Ext.soundness
#print axioms LeanVMCircuits.Flock.Clock.Ext.layout
#print axioms LeanVMCircuits.Flock.Clock.Ext.output_products_layout
#print axioms LeanVMCircuits.Flock.Clock.Ext.wellFormed
#print axioms LeanVMCircuits.Flock.Clock.Ext.complete
#print axioms LeanVMCircuits.ExtClockValues.incrOut_value
#print axioms LeanVMCircuits.ExtClock.circuit
#print axioms LeanVMCircuits.Flock.ExtClock.supported
#print axioms LeanVMCircuits.Flock.ExtClock.source_eq
#print axioms LeanVMCircuits.Flock.ExtClock.soundness
#print axioms LeanVMCircuits.Flock.ExtClock.layout
#print axioms LeanVMCircuits.Flock.ExtClock.output_products_layout
#print axioms LeanVMCircuits.Flock.ExtClock.wellFormed
#print axioms LeanVMCircuits.Flock.ExtClock.complete
#print axioms LeanVMCircuits.Bus.ClassTable.clock_sound
#print axioms LeanVMCircuits.Bus.ClassTable.tables_correct_of_clock

#print axioms LeanVMCircuits.ExtensionProduct.source
#print axioms LeanVMCircuits.ExtensionProduct.source_holds
#print axioms LeanVMCircuits.ExtensionProduct.result_limbs
#print axioms LeanVMCircuits.ExtensionProduct.soundness_iff
#print axioms LeanVMCircuits.ExtensionProduct.instruction_soundness
#print axioms LeanVMCircuits.ExtensionProduct.base_operand
#print axioms LeanVMCircuits.ExtensionProduct.witness_exists
