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

#print axioms LeanVMCircuits.Rec.Bind.closure_agree
#print axioms LeanVMCircuits.Rec.Bind.certifyT_sound
#print axioms LeanVMCircuits.Rec.Bind.Cert.times_sound
#print axioms LeanVMCircuits.Rec.Bind.tests_by
#print axioms LeanVMCircuits.Rec.Bind.Just.valid
#print axioms LeanVMCircuits.Rec.Bind.rules_valid
#print axioms LeanVMCircuits.Rec.Bind.Sat.holds
#print axioms LeanVMCircuits.Rec.Bind.checkbind_sound
#print axioms LeanVMCircuits.Rec.Bind.tests_determined
#print axioms LeanVMCircuits.Rec.Model.replayR_sound
#print axioms LeanVMCircuits.Rec.PoolParse.parse_unique
#print axioms LeanVMCircuits.Rec.Bind.PoolCert.pool_sem
#print axioms LeanVMCircuits.Rec.Bind.PoolCert.pool_unique
#print axioms LeanVMCircuits.Rec.Bind.prod_agree
#print axioms LeanVMCircuits.Rec.Bind.claim_valid
#print axioms LeanVMCircuits.Rec.Bind.unionsValid
#print axioms LeanVMCircuits.Rec.Bind.point_sem
#print axioms LeanVMCircuits.Rec.Bind.prod_closed
#print axioms LeanVMCircuits.Rec.Bind.prod_slotsAt
#print axioms LeanVMCircuits.Rec.Bind.slots_agree
#print axioms LeanVMCircuits.Rec.Bind.cover_side
#print axioms LeanVMCircuits.Rec.Bind.union_cover
#print axioms LeanVMCircuits.Rec.Bind.uniform_count
#print axioms LeanVMCircuits.Rec.Bind.Cert.accepts_parts
#print axioms LeanVMCircuits.Rec.Bind.union_sound
#print axioms LeanVMCircuits.Rec.Bind.taintOk_sound
#print axioms LeanVMCircuits.Rec.Bind.tests_cover
#print axioms LeanVMCircuits.Rec.UnionSound.poly_injective
#print axioms LeanVMCircuits.Rec.UnionSound.slots_eq
#print axioms LeanVMCircuits.Rec.UnionSound.coverage_sound
#print axioms LeanVMCircuits.Rec.UnionSound.union_coverage_sound
#print axioms LeanVMCircuits.Rec.UnionSound.chain_unique
#print axioms LeanVMCircuits.Rec.PoolClaims.run_reads
#print axioms LeanVMCircuits.Rec.PoolClaims.readC_blocks
#print axioms LeanVMCircuits.Rec.PoolClaims.reads_sum
#print axioms LeanVMCircuits.Rec.Bind.pool_claims
#print axioms LeanVMCircuits.Rec.Bind.decl_claims
#print axioms LeanVMCircuits.Rec.Bind.cur_runAt
#print axioms LeanVMCircuits.Rec.Bind.sel_claims
#print axioms LeanVMCircuits.Rec.Bind.union_sound_sets
#print axioms LeanVMCircuits.Rec.Bind.sets_differ
#print axioms LeanVMCircuits.Rec.Bind.union_sound_queries
#print axioms LeanVMCircuits.Rec.Bind.union_sound_sets_queries
#print axioms LeanVMCircuits.Rec.Sumcheck.sumcheck_sound
#print axioms LeanVMCircuits.Rec.Sumcheck.sumcheck_sound_frac
#print axioms LeanVMCircuits.Rec.Sumcheck.accepts_ofFun
#print axioms LeanVMCircuits.Rec.Sumcheck.sumcheck_sound_fun
#print axioms LeanVMCircuits.Rec.Sumcheck.sumcheck_sound_on
#print axioms LeanVMCircuits.Rec.Bind.sumRound_sem
#print axioms LeanVMCircuits.Rec.Bind.pow_sem
#print axioms LeanVMCircuits.Rec.Bind.Cert.accepts_rounds
#print axioms LeanVMCircuits.Rec.Bind.coeffs_agree
#print axioms LeanVMCircuits.Rec.Bind.sumcheck_test_sound
#print axioms LeanVMCircuits.Rec.Bind.grinding_bound
#print axioms LeanVMCircuits.Rec.Bind.pow_test_sound
#print axioms LeanVMCircuits.Rec.TreeSound.tree_sound
#print axioms LeanVMCircuits.Rec.TreeSound.tree_sound_frac
#print axioms LeanVMCircuits.Rec.TreeSound.tree_sound_eps
#print axioms LeanVMCircuits.Rec.Edges.stmtClaims_map
#print axioms LeanVMCircuits.Rec.Edges.stmtClaims_congr
#print axioms LeanVMCircuits.Rec.Edges.ScaleCert.sem
#print axioms LeanVMCircuits.Rec.Edges.allHold_of_replay
#print axioms LeanVMCircuits.Rec.Edges.EdgeCert.edge
#print axioms LeanVMCircuits.Rec.Edges.EdgeCert.edge_holds
#print axioms LeanVMCircuits.Rec.Edges.hedge_of_certs
#print axioms LeanVMCircuits.Rec.Edges.hedge_at
#print axioms LeanVMCircuits.Rec.Edges.InstCert.limb_sem
#print axioms LeanVMCircuits.Rec.Edges.InstCert.verifies
#print axioms LeanVMCircuits.Rec.Edges.sat_tree
#print axioms LeanVMCircuits.Rec.Edges.sat_tree_at
#print axioms LeanVMCircuits.Rec.Edges.tree_sound_certs
#print axioms LeanVMCircuits.Rec.Edges.tree_sound_certs_off
#print axioms LeanVMCircuits.Rec.Edges.tree_sound_certs_frac
#print axioms LeanVMCircuits.Rec.balanced_of_eq
#print axioms LeanVMCircuits.Rec.bus_balance_sound
#print axioms LeanVMCircuits.Rec.bus_copy_sound
#print axioms LeanVMCircuits.Rec.Sumcheck.coeff_polyOf
#print axioms LeanVMCircuits.Rec.Bind.odd_sem
#print axioms LeanVMCircuits.Rec.Bind.odd_test_sound
#print axioms LeanVMCircuits.Rec.toE_surjective
#print axioms LeanVMCircuits.Rec.Bind.Holds.toP
#print axioms LeanVMCircuits.Rec.Bind.RomAnswers.of_holds
#print axioms LeanVMCircuits.Rec.Bind.bound_agree
#print axioms LeanVMCircuits.Rec.Bind.RomExample.sumcheck_answers_exist
#print axioms LeanVMCircuits.Rec.Bind.RomExample.sumcheck_hinted_answers_exist
#print axioms LeanVMCircuits.Rec.Bind.ro_agree
#print axioms LeanVMCircuits.Rec.Bind.RomExample.odd_answers_exist
#print axioms LeanVMCircuits.Rec.Bind.RomExample.pow_answers_exist
#print axioms LeanVMCircuits.Rec.Bind.Cert.timesRO_sound
#print axioms LeanVMCircuits.Rec.Bind.Cert.timesX_sound
#print axioms LeanVMCircuits.Rec.Bind.whirBound_closure
#print axioms LeanVMCircuits.Rec.Bind.WindowCR.toP
#print axioms LeanVMCircuits.Rec.Bind.HashCR.toP
#print axioms LeanVMCircuits.Rec.Design.check_eq_none
#print axioms LeanVMCircuits.Rec.Design.length_places
#print axioms LeanVMCircuits.Rec.Design.places_getElem
#print axioms LeanVMCircuits.Rec.Design.places_getElem?
#print axioms LeanVMCircuits.Rec.Design.tier_lt
#print axioms LeanVMCircuits.Rec.Design.tier_iff
#print axioms LeanVMCircuits.Rec.Design.tiers_cover
#print axioms LeanVMCircuits.Rec.Design.first_iff
#print axioms LeanVMCircuits.Rec.Design.nTiers_eq
#print axioms LeanVMCircuits.Rec.Design.kindBits_le_shift
#print axioms LeanVMCircuits.Rec.Design.index_lt
#print axioms LeanVMCircuits.Rec.Design.code_eq
#print axioms LeanVMCircuits.Rec.Design.position_code
#print axioms LeanVMCircuits.Rec.Design.code_position
#print axioms LeanVMCircuits.Rec.Design.code_injective
#print axioms LeanVMCircuits.Rec.Design.code_div
#print axioms LeanVMCircuits.Rec.Design.code_mod
#print axioms LeanVMCircuits.Rec.Design.code_eq_zero
#print axioms LeanVMCircuits.Rec.Design.shift_le
#print axioms LeanVMCircuits.Rec.Design.code_lt
#print axioms LeanVMCircuits.Rec.Design.children_tier
#print axioms LeanVMCircuits.Rec.Design.children_none
#print axioms LeanVMCircuits.Rec.Design.all_built
#print axioms LeanVMCircuits.Rec.Design.tierCapacity_le
#print axioms LeanVMCircuits.Rec.Design.items_mono
#print axioms LeanVMCircuits.Rec.Design.set_items_le
#print axioms LeanVMCircuits.Rec.Design.runChunks_le
#print axioms LeanVMCircuits.Rec.Design.children_fit
#print axioms LeanVMCircuits.Rec.Design.declared_fit
#print axioms LeanVMCircuits.Rec.Design.union_capacity
#print axioms LeanVMCircuits.Rec.Design.vars_le_dense
#print axioms LeanVMCircuits.Rec.Design.fixed_vars
#print axioms LeanVMCircuits.Rec.Design.fixed_poly_present
#print axioms LeanVMCircuits.Rec.Design.wide_absent
#print axioms LeanVMCircuits.Rec.Design.start_succ
#print axioms LeanVMCircuits.Rec.Design.len_eq
#print axioms LeanVMCircuits.Rec.Design.section_unique
#print axioms LeanVMCircuits.Rec.Design.kind_digest_words
#print axioms LeanVMCircuits.Rec.Design.le_step
#print axioms LeanVMCircuits.Rec.Design.converge_fits
#print axioms LeanVMCircuits.Rec.Design.converge_least
#print axioms LeanVMCircuits.Rec.Model.Good.seq
#print axioms LeanVMCircuits.Rec.Model.vanish_good
#print axioms LeanVMCircuits.Rec.Model.holdBits_good
#print axioms LeanVMCircuits.Rec.Model.tops_good
#print axioms LeanVMCircuits.Rec.Model.firstFold_good
#print axioms LeanVMCircuits.Rec.Model.vanish_root
#print axioms LeanVMCircuits.Rec.Model.split_bits
#print axioms LeanVMCircuits.Rec.Model.first_core
#print axioms LeanVMCircuits.Rec.Model.prod_zero_or_one
#print axioms LeanVMCircuits.Rec.Model.kindRows_good
#print axioms LeanVMCircuits.Rec.Model.kind_exposed
#print axioms LeanVMCircuits.Rec.Model.kindConst_ev
#print axioms LeanVMCircuits.Rec.Model.mapM_eToK_good
#print axioms LeanVMCircuits.Rec.Model.limbRows_good
#print axioms LeanVMCircuits.Rec.Model.oneChild_good
#print axioms LeanVMCircuits.Rec.Model.readChildren_good
#print axioms LeanVMCircuits.Rec.Model.nodeRows_good
#print axioms LeanVMCircuits.Rec.Bind.resid_sem
#print axioms LeanVMCircuits.Rec.Bind.squares_sem
#print axioms LeanVMCircuits.Rec.Bind.terms_sem
#print axioms LeanVMCircuits.Rec.Bind.split_sem
#print axioms LeanVMCircuits.Rec.Bind.top_sem
#print axioms LeanVMCircuits.Rec.Bind.PExpr.natDegree_poly
#print axioms LeanVMCircuits.Rec.Bind.PExpr.poly_congr
#print axioms LeanVMCircuits.Rec.Bind.PExpr.vanish_eval
#print axioms LeanVMCircuits.Rec.Bind.PExpr.fixes_eval
#print axioms LeanVMCircuits.Rec.Bind.WhirRound.poly_congr
#print axioms LeanVMCircuits.Rec.Bind.WhirCert.deg_le
#print axioms LeanVMCircuits.Rec.Bind.pexpr_sem
#print axioms LeanVMCircuits.Rec.Bind.quad_sem
#print axioms LeanVMCircuits.Rec.Bind.whirRound_sem
#print axioms LeanVMCircuits.Rec.Bind.card_line_zero
#print axioms LeanVMCircuits.Rec.Bind.card_plane_zero
#print axioms LeanVMCircuits.Rec.Bind.top_test_sound
#print axioms LeanVMCircuits.Rec.Bind.split_test_sound
#print axioms LeanVMCircuits.Rec.Bind.whir_test_sound
#print axioms LeanVMCircuits.Rec.Bind.RomExample.top_answers_exist
#print axioms LeanVMCircuits.Rec.Bind.RomExample.whir_answers_exist
#print axioms LeanVMCircuits.Rec.Bind.Cert.accepts_chals
#print axioms LeanVMCircuits.Rec.Bind.chalsOk_sem
#print axioms LeanVMCircuits.Rec.Bind.ChalCert.read
#print axioms LeanVMCircuits.Rec.Bind.oracleAt_own
#print axioms LeanVMCircuits.Rec.Bind.readR_oracleAt
#print axioms LeanVMCircuits.Rec.Bind.oracleAt_readR
#print axioms LeanVMCircuits.Rec.Bind.oracleAt_oracleAt
#print axioms LeanVMCircuits.Rec.Bind.card_lens
#print axioms LeanVMCircuits.Rec.Bind.run_frac
#print axioms LeanVMCircuits.Rec.Bind.Run.seed_at
#print axioms LeanVMCircuits.Rec.Bind.Run.sib_at
#print axioms LeanVMCircuits.Rec.Bind.Run.chal_at
#print axioms LeanVMCircuits.Rec.Bind.Run.chals
#print axioms LeanVMCircuits.Rec.Bind.Run.sumcheckAnswers
#print axioms LeanVMCircuits.Rec.Bind.Run.oddAnswers
#print axioms LeanVMCircuits.Rec.Bind.Run.topAnswers
#print axioms LeanVMCircuits.Rec.Bind.Run.whirAnswers
#print axioms LeanVMCircuits.Rec.Bind.Run.cr_at
#print axioms LeanVMCircuits.Rec.Bind.Run.crAt
#print axioms LeanVMCircuits.Rec.Bind.mem_ownAll
#print axioms LeanVMCircuits.Rec.Bind.PairCR.of_full
#print axioms LeanVMCircuits.Rec.Bind.PairCR.anti
#print axioms LeanVMCircuits.Rec.Bind.Cert.liveOn_mono
#print axioms LeanVMCircuits.Rec.Bind.mem_hintNodes
#print axioms LeanVMCircuits.Rec.Bind.ro_agree
#print axioms LeanVMCircuits.Rec.Bind.bound_agree
#print axioms LeanVMCircuits.Rec.Bind.closure_agree_on
#print axioms LeanVMCircuits.Rec.Bind.rules_valid
#print axioms LeanVMCircuits.Rec.Bind.RomExample.pairCR
#print axioms LeanVMCircuits.Rec.Bind.card_coord
#print axioms LeanVMCircuits.Rec.Bind.pow_run_sound
#print axioms LeanVMCircuits.Rec.Bind.RomExample.run_exists
#print axioms LeanVMCircuits.Rec.Bind.RomExample.chalsOk_mutations
#print axioms LeanVMCircuits.Rec.Bind.sumcheck_claim_agree
#print axioms LeanVMCircuits.Rec.Bind.card_at
#print axioms LeanVMCircuits.Rec.Bind.CommittedBefore.const
#print axioms LeanVMCircuits.Rec.Bind.CommittedBefore.comp
#print axioms LeanVMCircuits.Rec.Bind.Run.committed_at
#print axioms LeanVMCircuits.Rec.Bind.draws_not_fixed
#print axioms LeanVMCircuits.Rec.Bind.Run.sumcheck_committed
#print axioms LeanVMCircuits.Rec.Bind.Run.whir_committed
#print axioms LeanVMCircuits.Rec.Bind.Run.odd_committed
#print axioms LeanVMCircuits.Rec.Bind.Run.top_committed
#print axioms LeanVMCircuits.Rec.Bind.sumcheck_run_sound_at
#print axioms LeanVMCircuits.Rec.Bind.sumcheck_part
#print axioms LeanVMCircuits.Rec.Bind.whir_run_sound_at
#print axioms LeanVMCircuits.Rec.Bind.odd_run_sound_at
#print axioms LeanVMCircuits.Rec.Bind.top_run_sound_at
#print axioms LeanVMCircuits.Rec.Bind.whir_part
#print axioms LeanVMCircuits.Rec.Bind.odd_part
#print axioms LeanVMCircuits.Rec.Bind.top_part
#print axioms LeanVMCircuits.Rec.Edges.RecParts.least_ok
#print axioms LeanVMCircuits.Rec.Edges.RecParts.ins_ok
#print axioms LeanVMCircuits.Rec.Edges.RecParts.hrec
#print axioms LeanVMCircuits.Rec.Edges.tree_sound_parts
#print axioms LeanVMCircuits.Rec.DesignClaims.flockKLogs_length
#print axioms LeanVMCircuits.Rec.DesignClaims.flockKLogs_le
#print axioms LeanVMCircuits.Rec.DesignClaims.nPolys_le
#print axioms LeanVMCircuits.Rec.DesignClaims.edgeLayout_ok
#print axioms LeanVMCircuits.Rec.DesignClaims.edgeLayout_len
#print axioms LeanVMCircuits.Rec.DesignClaims.stmtOf_point
#print axioms LeanVMCircuits.Rec.DesignClaims.stmtOf_value
#print axioms LeanVMCircuits.Rec.DesignClaims.stmtOf_row
#print axioms LeanVMCircuits.Rec.DesignClaims.stmtOf_col
#print axioms LeanVMCircuits.Rec.DesignClaims.stmtOf_mat
#print axioms LeanVMCircuits.Rec.DesignClaims.stmtOf_head
#print axioms LeanVMCircuits.Rec.DesignClaims.stmtClaims_stmtOf
#print axioms LeanVMCircuits.Rec.DesignClaims.map_getD_range
#print axioms LeanVMCircuits.Rec.DesignClaims.reduced_dense_mem
#print axioms LeanVMCircuits.Rec.DesignClaims.reduced_matrix_mem
#print axioms LeanVMCircuits.Rec.DesignClaims.stmt_exposed
#print axioms LeanVMCircuits.Rec.DesignClaims.before_trans
#print axioms LeanVMCircuits.Rec.DesignClaims.before_irrefl
#print axioms LeanVMCircuits.Rec.DesignClaims.before_total
#print axioms LeanVMCircuits.Rec.DesignClaims.offset_aligned
#print axioms LeanVMCircuits.Rec.DesignClaims.offset_before
#print axioms LeanVMCircuits.Rec.DesignClaims.offset_disjoint
#print axioms LeanVMCircuits.Rec.DesignClaims.offset_fits
#print axioms LeanVMCircuits.Rec.DesignClaims.tau_le_kappa
#print axioms LeanVMCircuits.Rec.DesignClaims.block_spec
#print axioms LeanVMCircuits.Rec.DesignClaims.bitsOf_length
#print axioms LeanVMCircuits.Rec.DesignClaims.bitsOf_getD
#print axioms LeanVMCircuits.Rec.DesignClaims.bitsOf_eq
#print axioms LeanVMCircuits.Rec.DesignClaims.mle_bitsOf
#print axioms LeanVMCircuits.Rec.DesignClaims.bitsOf_append
#print axioms LeanVMCircuits.Rec.DesignClaims.mle_append_bitsOf
#print axioms LeanVMCircuits.Rec.DesignClaims.mle_congr
#print axioms LeanVMCircuits.Rec.DesignClaims.stackAt_read
#print axioms LeanVMCircuits.Rec.DesignClaims.term_reads
#print axioms LeanVMCircuits.Rec.DesignClaims.fresh_fixed_reads
#print axioms LeanVMCircuits.Rec.DesignClaims.bindState_good
#print axioms LeanVMCircuits.Rec.DesignClaims.bindState_binds
#print axioms LeanVMCircuits.Rec.DesignClaims.digestHalves_good
#print axioms LeanVMCircuits.Rec.DesignClaims.digest_roundtrip
#print axioms LeanVMCircuits.Rec.DesignClaims.mapM_kConst_good
#print axioms LeanVMCircuits.Rec.DesignClaims.w64_const
#print axioms LeanVMCircuits.Rec.DesignClaims.flatten_map_w64
#print axioms LeanVMCircuits.Rec.DesignClaims.digestRows_good
#print axioms LeanVMCircuits.Rec.DesignClaims.firstProd_bits
#print axioms LeanVMCircuits.Rec.DesignClaims.nodeScale_small
#print axioms LeanVMCircuits.Rec.DesignClaims.nodeScale_two
#print axioms LeanVMCircuits.Rec.DesignClaims.tierMode_scale
#print axioms LeanVMCircuits.Rec.DesignClaims.modeOk_mutations
#print axioms LeanVMCircuits.Rec.DesignClaims.bindOk_mutations
#print axioms LeanVMCircuits.Rec.DesignClaims.carriedOk_mutations
#print axioms LeanVMCircuits.Rec.DesignClaims.exposedOk_mutations
#print axioms LeanVMCircuits.Rec.DesignClaims.fixed_placement
#print axioms LeanVMCircuits.Rec.DesignClaims.fixedOk_mutations
#print axioms LeanVMCircuits.Rec.Edges.ofWord_zero_limb
#print axioms LeanVMCircuits.Rec.Edges.DigestCert.exposed
#print axioms LeanVMCircuits.Rec.Edges.DigestCert.wrap_states
#print axioms LeanVMCircuits.Rec.Edges.DigestCert.node_states
#print axioms LeanVMCircuits.Rec.Edges.wrap_mutations
#print axioms LeanVMCircuits.Rec.Edges.node_mutations
#print axioms LeanVMCircuits.Rec.Collision.answers_length
#print axioms LeanVMCircuits.Rec.Collision.mem_answers
#print axioms LeanVMCircuits.Rec.Collision.answers_congr
#print axioms LeanVMCircuits.Rec.Collision.query_congr
#print axioms LeanVMCircuits.Rec.Collision.first_fresh
#print axioms LeanVMCircuits.Rec.Collision.event_fresh
#print axioms LeanVMCircuits.Rec.Collision.fresh_card
#print axioms LeanVMCircuits.Rec.Collision.event_card
#print axioms LeanVMCircuits.Rec.Collision.frac_le
#print axioms LeanVMCircuits.Rec.Collision.birthday_card
#print axioms LeanVMCircuits.Rec.Collision.birthday_frac
#print axioms LeanVMCircuits.Rec.Collision.injOn_of_not_coll
#print axioms LeanVMCircuits.Rec.Collision.AgreeOn.symm
#print axioms LeanVMCircuits.Rec.Collision.agree_mul_le
#print axioms LeanVMCircuits.Rec.Collision.answers_take
#print axioms LeanVMCircuits.Rec.Collision.qAt_answers
#print axioms LeanVMCircuits.Rec.Collision.answers_getElem
#print axioms LeanVMCircuits.Rec.Collision.winTargets_card
#print axioms LeanVMCircuits.Rec.Collision.freshPairs_sum
#print axioms LeanVMCircuits.Rec.Collision.agree_card_eq
#print axioms LeanVMCircuits.Rec.Collision.charged_card
#print axioms LeanVMCircuits.Rec.Collision.winHit_charged
#print axioms LeanVMCircuits.Rec.Collision.sum_range_mul_pred
#print axioms LeanVMCircuits.Rec.Collision.win_card
#print axioms LeanVMCircuits.Rec.Collision.win_frac
#print axioms LeanVMCircuits.Rec.Bind.hashIn_map
#print axioms LeanVMCircuits.Rec.Bind.hashOut_map
#print axioms LeanVMCircuits.Rec.Bind.hashSrc_chain
#print axioms LeanVMCircuits.Rec.Bind.chainOf_rowIn
#print axioms LeanVMCircuits.Rec.Bind.restFin_val
#print axioms LeanVMCircuits.Rec.Bind.input_ext
#print axioms LeanVMCircuits.Rec.Bind.hashRest_map
#print axioms LeanVMCircuits.Rec.Bind.hashCRP_of_oracle
#print axioms LeanVMCircuits.Rec.Bind.windowCRP_of_oracle
#print axioms LeanVMCircuits.Rec.Bind.oracleRows_exists
#print axioms LeanVMCircuits.Rec.Bind.pairCR_of_oracle
#print axioms LeanVMCircuits.Rec.Edges.card_filter_prod
#print axioms LeanVMCircuits.Rec.Edges.crEvent_frac
#print axioms LeanVMCircuits.Rec.Edges.not_mem_crEvent
#print axioms LeanVMCircuits.Rec.Edges.crBad_frac
#print axioms LeanVMCircuits.Rec.Edges.PcsBound.one
#print axioms LeanVMCircuits.Rec.Edges.tree_sound_eps
#print axioms LeanVMCircuits.Rec.Edges.finalBound_nonneg
#print axioms LeanVMCircuits.Rec.Edges.card_preimage
#print axioms LeanVMCircuits.Rec.Edges.Pcs551.frac
#print axioms LeanVMCircuits.Rec.Edges.pcsBound_of_551
#print axioms LeanVMCircuits.Rec.Edges.restrict_fiber_eq
#print axioms LeanVMCircuits.Rec.Edges.restrict_fiber
#print axioms LeanVMCircuits.Rec.Edges.pair_fiber
#print axioms LeanVMCircuits.Rec.Edges.compress_fiber
#print axioms LeanVMCircuits.Rec.Bind.run_frac_off
#print axioms LeanVMCircuits.Rec.Collision.late_card
#print axioms LeanVMCircuits.Rec.Collision.answers_strat
#print axioms LeanVMCircuits.Rec.Collision.queries_strat
#print axioms LeanVMCircuits.Rec.Bind.WinOn.mono
#print axioms LeanVMCircuits.Rec.Bind.oracleRows_of_late
#print axioms LeanVMCircuits.Rec.Bind.out_of_prefix
#print axioms LeanVMCircuits.Rec.Bind.Run.cr_of_extract
#print axioms LeanVMCircuits.Rec.Collision.answers_along
#print axioms LeanVMCircuits.Rec.Collision.queries_along
#print axioms LeanVMCircuits.Rec.Collision.normalize_lt
#print axioms LeanVMCircuits.Rec.Collision.answers_normalize
#print axioms LeanVMCircuits.Rec.Collision.extra_mem_queries
#print axioms LeanVMCircuits.Rec.Bind.Run.cr_of_normal
#print axioms LeanVMCircuits.Rec.Bind.stageN_eq_iff
#print axioms LeanVMCircuits.Rec.Bind.stageN_spec
#print axioms LeanVMCircuits.Rec.Bind.stageN_le
#print axioms LeanVMCircuits.Rec.Bind.stageN_lt
#print axioms LeanVMCircuits.Rec.Bind.hcaus_of_staged
#print axioms LeanVMCircuits.Rec.Bind.Run.cr_of_staged
#print axioms LeanVMCircuits.Rec.Sumcheck.sum_cube_zero
#print axioms LeanVMCircuits.Rec.Sumcheck.sum_cube_succ
#print axioms LeanVMCircuits.Rec.Sumcheck.eval_bind
#print axioms LeanVMCircuits.Rec.Sumcheck.round_eval
#print axioms LeanVMCircuits.Rec.Sumcheck.mvInst_sum
#print axioms LeanVMCircuits.Rec.Sumcheck.degreeOf_bind
#print axioms LeanVMCircuits.Rec.Sumcheck.mvInst_ok
#print axioms LeanVMCircuits.Rec.Sumcheck.mvInst_final
#print axioms LeanVMCircuits.Rec.Sumcheck.mvInst_weight
#print axioms LeanVMCircuits.Rec.Sumcheck.sum_cube_rev
#print axioms LeanVMCircuits.Rec.AirLink.Quad.eval_poly
#print axioms LeanVMCircuits.Rec.AirLink.Quad.degreeOf_poly
#print axioms LeanVMCircuits.Rec.AirLink.ofId_eval
#print axioms LeanVMCircuits.Rec.AirLink.mem_owned_of_ids
#print axioms LeanVMCircuits.Rec.AirLink.eval_summandPoly
#print axioms LeanVMCircuits.Rec.AirLink.degreeOf_cornerEq
#print axioms LeanVMCircuits.Rec.AirLink.degreeOf_eqPoly
#print axioms LeanVMCircuits.Rec.AirLink.degreeOf_mle
#print axioms LeanVMCircuits.Rec.AirLink.degreeOf_tablePoly
#print axioms LeanVMCircuits.Rec.AirLink.tableInst_ok
#print axioms LeanVMCircuits.Rec.AirLink.tableInst_weight
#print axioms LeanVMCircuits.Rec.AirLink.bitPoint_injOn
#print axioms LeanVMCircuits.Rec.AirLink.cube_eq_image
#print axioms LeanVMCircuits.Rec.AirLink.sum_cube_bits
#print axioms LeanVMCircuits.Rec.AirLink.corner_sum
#print axioms LeanVMCircuits.Rec.AirLink.rowEq_mod
#print axioms LeanVMCircuits.Rec.AirLink.eval_eqPoly_mod
#print axioms LeanVMCircuits.Rec.AirLink.eval_mle
#print axioms LeanVMCircuits.Rec.AirLink.eval_cornerEq
#print axioms LeanVMCircuits.Rec.AirLink.table_cube_sum
#print axioms LeanVMCircuits.Rec.AirLink.allIds_mem_ids
#print axioms LeanVMCircuits.Rec.AirLink.tableInst_sum
#print axioms LeanVMCircuits.Rec.AirLink.foldl_mul_eq
#print axioms LeanVMCircuits.Rec.AirLink.foldWeight_eq
#print axioms LeanVMCircuits.Rec.AirLink.tableInst_final
#print axioms LeanVMCircuits.Rec.AirLink.committedAt_fits
#print axioms LeanVMCircuits.Rec.AirLink.committedAt_pub
#print axioms LeanVMCircuits.Rec.AirLink.tauOf_committedAt
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveInst_of_table
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveRows_of_table
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveTable_claims
#print axioms LeanVMCircuits.Rec.AirLink.heightsHold_clog
#print axioms LeanVMCircuits.Rec.AirLink.layoutFits_of_le
#print axioms LeanVMCircuits.Rec.AirLink.layoutFits_converge
#print axioms LeanVMCircuits.Rec.AirLink.taus_le_rounds
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveRows_of_converge
#print axioms LeanVMCircuits.Rec.AirLink.le_pow_log2Ceil
#print axioms LeanVMCircuits.Rec.AirLink.le_pow_heightLog
#print axioms LeanVMCircuits.Rec.AirLink.heightsHold_circuit
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveRows_of_tree
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveTable_of_named
#print axioms LeanVMCircuits.Rec.AirLink.named_inputs
#print axioms LeanVMCircuits.Rec.Bind.card_fix_mul
#print axioms LeanVMCircuits.Rec.Bind.frac_fix_le
#print axioms LeanVMCircuits.Rec.Bind.frac_pick_le
#print axioms LeanVMCircuits.Rec.Bind.frac_pick_le_mul
#print axioms LeanVMCircuits.Rec.Bind.bitPick_frac
#print axioms LeanVMCircuits.Rec.Edges.tries_bound_deployed
#print axioms LeanVMCircuits.Rec.Bind.TableCert.sem
#print axioms LeanVMCircuits.Rec.Bind.TableCert.answers_weight
#print axioms LeanVMCircuits.Rec.Bind.TableCert.claim_iff
#print axioms LeanVMCircuits.Rec.Sumcheck.eqv_cons
#print axioms LeanVMCircuits.Rec.Sumcheck.eqRound_eval
#print axioms LeanVMCircuits.Rec.Sumcheck.eqInst_sum
#print axioms LeanVMCircuits.Rec.Sumcheck.eqInst_ok
#print axioms LeanVMCircuits.Rec.Sumcheck.eqInst_final
#print axioms LeanVMCircuits.Rec.Sumcheck.eqInst_weight
#print axioms LeanVMCircuits.Rec.AirLink.prod_range_mul
#print axioms LeanVMCircuits.Rec.AirLink.level_zero
#print axioms LeanVMCircuits.Rec.AirLink.level_two
#print axioms LeanVMCircuits.Rec.AirLink.level_four
#print axioms LeanVMCircuits.Rec.AirLink.level_root
#print axioms LeanVMCircuits.Rec.AirLink.root_eq_level
#print axioms LeanVMCircuits.Rec.AirLink.pullRoot_eq_level
#print axioms LeanVMCircuits.Rec.AirLink.pushRoot_eq_level
#print axioms LeanVMCircuits.Rec.AirLink.eval_childMle
#print axioms LeanVMCircuits.Rec.AirLink.layerInst_sum
#print axioms LeanVMCircuits.Rec.AirLink.degreeOf_childMle
#print axioms LeanVMCircuits.Rec.AirLink.layerInst_ok
#print axioms LeanVMCircuits.Rec.AirLink.layerInst_weight
#print axioms LeanVMCircuits.Rec.AirLink.layerInst_final
#print axioms LeanVMCircuits.Rec.AirLink.one_sub_eq_one_add
#print axioms LeanVMCircuits.Rec.AirLink.eval_eqPoly_eqv
#print axioms LeanVMCircuits.Rec.AirLink.eval_childMle_eq
#print axioms LeanVMCircuits.Rec.AirLink.sum_range_mul
#print axioms LeanVMCircuits.Rec.AirLink.bitPoint_four
#print axioms LeanVMCircuits.Rec.AirLink.next_claim
#print axioms LeanVMCircuits.Rec.AirLink.layerInst_sum_level
#print axioms LeanVMCircuits.Rec.AirLink.mleAt_zero
#print axioms LeanVMCircuits.Rec.AirLink.odd_next
#print axioms LeanVMCircuits.Rec.Bind.LayerCert.link_sem
#print axioms LeanVMCircuits.Rec.Bind.LayerCert.chain_cons
#print axioms LeanVMCircuits.Rec.Bind.GkrCert.sem
#print axioms LeanVMCircuits.Rec.Bind.LayerCert.layer_sem
#print axioms LeanVMCircuits.Rec.Bind.lamBad_card
#print axioms LeanVMCircuits.Rec.Bind.lineE_sub
#print axioms LeanVMCircuits.Rec.Bind.lineBad_card
#print axioms LeanVMCircuits.Rec.Bind.layer_part
#print axioms LeanVMCircuits.Rec.Bind.LayerCert.chal_sem
#print axioms LeanVMCircuits.Rec.Bind.LayerCert.lam_closure
#print axioms LeanVMCircuits.Rec.Bind.Run.sib_agree
#print axioms LeanVMCircuits.Rec.Bind.layer_run_sound_at
#print axioms LeanVMCircuits.Rec.Bind.LayerCert.chal_eval
#print axioms LeanVMCircuits.Rec.Bind.mca_sem
#print axioms LeanVMCircuits.Rec.Bind.FormCert.sem
#print axioms LeanVMCircuits.Rec.Bind.IdCert.sem
#print axioms LeanVMCircuits.Rec.Bind.TermCert.weight_sem
#print axioms LeanVMCircuits.Rec.Bind.ResidCert.pow_sem
#print axioms LeanVMCircuits.Rec.Bind.prod_range_eq_foldWeight
#print axioms LeanVMCircuits.Rec.Bind.sum_filter_list
#print axioms LeanVMCircuits.Rec.Bind.sum_idsOf
#print axioms LeanVMCircuits.Rec.Bind.Quad.eval_congr
#print axioms LeanVMCircuits.Rec.Bind.idsColsOk_eq
#print axioms LeanVMCircuits.Rec.Bind.idAt_eq
#print axioms LeanVMCircuits.Rec.Bind.summandAt_congr
#print axioms LeanVMCircuits.Rec.Bind.TermCert.summand_sem
#print axioms LeanVMCircuits.Rec.Bind.TermCert.weight_fold
#print axioms LeanVMCircuits.Rec.Bind.ResidCert.sem
#print axioms LeanVMCircuits.Rec.Bind.ResidCert.final_eq
#print axioms LeanVMCircuits.Rec.AirLink.rowEq_block
#print axioms LeanVMCircuits.Rec.AirLink.rowEq_succ
#print axioms LeanVMCircuits.Rec.AirLink.sum_rowEq
#print axioms LeanVMCircuits.Rec.AirLink.leaf_decompose
#print axioms LeanVMCircuits.Rec.AirLink.blockLeaf_eq
#print axioms LeanVMCircuits.Rec.AirLink.sum_list_comm
#print axioms LeanVMCircuits.Rec.AirLink.block_sum
#print axioms LeanVMCircuits.Rec.AirLink.Quad.eval_add
#print axioms LeanVMCircuits.Rec.AirLink.Quad.eval_smul
#print axioms LeanVMCircuits.Rec.AirLink.sum_filter_list'
#print axioms LeanVMCircuits.Rec.AirLink.sideForm_eval
#print axioms LeanVMCircuits.Rec.AirLink.side_decompose
#print axioms LeanVMCircuits.Rec.AirLink.totals_eq
#print axioms LeanVMCircuits.Rec.AirLink.totals_eq_formSums
#print axioms LeanVMCircuits.Rec.AirLink.rowEq_restrict
#print axioms LeanVMCircuits.Rec.AirLink.formSums_restrict
#print axioms LeanVMCircuits.Rec.AirLink.tableClaim_of_leaves
#print axioms LeanVMCircuits.Rec.AirLink.xi_roots_low
#print axioms LeanVMCircuits.Rec.AirLink.parts_zero
#print axioms LeanVMCircuits.Rec.AirLink.balDraws_card
#print axioms LeanVMCircuits.Rec.AirLink.balBad_frac
#print axioms LeanVMCircuits.Rec.AirLink.balRun_frac
#print axioms LeanVMCircuits.Rec.AirLink.balance_part
#print axioms LeanVMCircuits.Rec.AirLink.balance_of_inst
#print axioms LeanVMCircuits.Rec.Bind.table_part
#print axioms LeanVMCircuits.Rec.Bind.balance_named
#print axioms LeanVMCircuits.Rec.Edges.tableParts_ok
#print axioms LeanVMCircuits.Rec.Edges.checksGiveTable_of_parts
#print axioms LeanVMCircuits.Rec.Edges.lateEvent_frac
#print axioms LeanVMCircuits.Rec.Edges.not_mem_exec
#print axioms LeanVMCircuits.Rec.AirLink.frac_prod_le
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_exec
#print axioms LeanVMCircuits.Rec.AirLink.add_rearr
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_end
#print axioms LeanVMCircuits.Rec.Edges.card_E
#print axioms LeanVMCircuits.Rec.Edges.epsCR_mono
#print axioms LeanVMCircuits.Rec.Edges.epsLate_mono
#print axioms LeanVMCircuits.Rec.Edges.exec_bound_deployed
#print axioms LeanVMCircuits.Rec.Edges.epsCR_cap
#print axioms LeanVMCircuits.Rec.Edges.finalBound_mono
#print axioms LeanVMCircuits.Rec.Edges.child_bound_deployed
#print axioms LeanVMCircuits.Rec.Edges.tree_bound_deployed
#print axioms LeanVMCircuits.Rec.Edges.pcs_dominates
#print axioms LeanVMCircuits.Rec.AirLink.forms_length
#print axioms LeanVMCircuits.Rec.AirLink.firstSlot_inj
#print axioms LeanVMCircuits.Rec.AirLink.wireClass_spec
#print axioms LeanVMCircuits.Rec.AirLink.wireClass_eq_iff
#print axioms LeanVMCircuits.Rec.AirLink.assign_class
#print axioms LeanVMCircuits.Rec.AirLink.joined_val
#print axioms LeanVMCircuits.Rec.AirLink.mem_slots
#print axioms LeanVMCircuits.Rec.AirLink.pairwise_disjoint
#print axioms LeanVMCircuits.Rec.AirLink.slots_nodup
#print axioms LeanVMCircuits.Rec.AirLink.key_inj
#print axioms LeanVMCircuits.Rec.AirLink.key_injective
#print axioms LeanVMCircuits.Rec.AirLink.copy
#print axioms LeanVMCircuits.Rec.AirLink.assign_eq
#print axioms LeanVMCircuits.Rec.AirLink.slotClass_row
#print axioms LeanVMCircuits.Rec.AirLink.row_sat
#print axioms LeanVMCircuits.Rec.AirLink.limbs_pub
#print axioms LeanVMCircuits.Rec.AirLink.sat_of_claims
#print axioms LeanVMCircuits.Rec.AirLink.sat_row
#print axioms LeanVMCircuits.Rec.AirLink.balanced_of_next
#print axioms LeanVMCircuits.Rec.AirLink.honest_carried
#print axioms LeanVMCircuits.Rec.AirLink.honest_next
#print axioms LeanVMCircuits.Rec.AirLink.claims_of_sat
#print axioms LeanVMCircuits.Rec.AirLink.limbsOf_zero
#print axioms LeanVMCircuits.Rec.AirLink.limbsOf_one0
#print axioms LeanVMCircuits.Rec.AirLink.union_rejected
#print axioms LeanVMCircuits.Rec.AirLink.statement_rejected
#print axioms LeanVMCircuits.Rec.AirLink.ev_limbsOf_one
#print axioms LeanVMCircuits.Rec.AirLink.ev_limbsOf_zero
#print axioms LeanVMCircuits.Rec.AirLink.emul_rejected
#print axioms LeanVMCircuits.Rec.AirLink.claims_example
#print axioms LeanVMCircuits.Rec.AirLink.busTuple_injOn
#print axioms LeanVMCircuits.Rec.AirLink.key_lt
#print axioms LeanVMCircuits.Rec.AirLink.bus_event
#print axioms LeanVMCircuits.Rec.AirLink.bus_of_product
#print axioms LeanVMCircuits.Rec.AirLink.busDraws_card
#print axioms LeanVMCircuits.Rec.AirLink.product_honest
#print axioms LeanVMCircuits.Rec.AirLink.product_rejected
#print axioms LeanVMCircuits.Rec.AirLink.busBad_frac
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveRows_claims
#print axioms LeanVMCircuits.Rec.AirLink.hair_of_air
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_air
#print axioms LeanVMCircuits.Rec.AirLink.frac_le_one
#print axioms LeanVMCircuits.Rec.AirLink.frac_empty
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_bound
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_crEvent
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_ideal
#print axioms LeanVMCircuits.Rec.AirLink.allIds_length
#print axioms LeanVMCircuits.Rec.AirLink.mem_allIds
#print axioms LeanVMCircuits.Rec.AirLink.height_le_pow
#print axioms LeanVMCircuits.Rec.AirLink.no_viol
#print axioms LeanVMCircuits.Rec.AirLink.batch_of_rows
#print axioms LeanVMCircuits.Rec.AirLink.eval_coefPoly
#print axioms LeanVMCircuits.Rec.AirLink.one_add_one
#print axioms LeanVMCircuits.Rec.AirLink.eval_eqPoly
#print axioms LeanVMCircuits.Rec.AirLink.emb_injective
#print axioms LeanVMCircuits.Rec.AirLink.eval_coefPoly_point
#print axioms LeanVMCircuits.Rec.AirLink.totalDegree_coefPoly
#print axioms LeanVMCircuits.Rec.AirLink.zeros_card
#print axioms LeanVMCircuits.Rec.AirLink.eval_xiPoly
#print axioms LeanVMCircuits.Rec.AirLink.coeff_xiPoly
#print axioms LeanVMCircuits.Rec.AirLink.xi_roots
#print axioms LeanVMCircuits.Rec.AirLink.card_pairs
#print axioms LeanVMCircuits.Rec.AirLink.card_draws
#print axioms LeanVMCircuits.Rec.AirLink.batchDraws_card
#print axioms LeanVMCircuits.Rec.AirLink.card_E_ge
#print axioms LeanVMCircuits.Rec.AirLink.batch_rejects
#print axioms LeanVMCircuits.Rec.AirLink.badSplit_viol
#print axioms LeanVMCircuits.Rec.AirLink.badSplit_rejected
#print axioms LeanVMCircuits.Rec.AirLink.tables_of
#print axioms LeanVMCircuits.Rec.AirLink.flocked_honest
#print axioms LeanVMCircuits.Rec.AirLink.eval_zero_row
#print axioms LeanVMCircuits.Rec.AirLink.batch_honest
#print axioms LeanVMCircuits.Rec.AirLink.batchBad_frac
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveRows_of_batch
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveBatch_claims
#print axioms LeanVMCircuits.Rec.AirLink.batchClaim_of_sum
#print axioms LeanVMCircuits.Rec.AirLink.productClaim_iff
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveBatch_of_inst
#print axioms LeanVMCircuits.Rec.AirLink.checksGiveInst_claims
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_batch
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_ideal_batch
#print axioms LeanVMCircuits.Rec.AirLink.batchOf_card
#print axioms LeanVMCircuits.Rec.AirLink.busRun_frac
#print axioms LeanVMCircuits.Rec.AirLink.batchRun_frac
#print axioms LeanVMCircuits.Rec.AirLink.tree_sound_run
#print axioms LeanVMCircuits.Rec.Bind.selCalls_sem
#print axioms LeanVMCircuits.Rec.Bind.sel_eq_prod
#print axioms LeanVMCircuits.Rec.Bind.idxCalls_sem
#print axioms LeanVMCircuits.Rec.Bind.idx_sem
#print axioms LeanVMCircuits.Rec.Bind.mle_step
#print axioms LeanVMCircuits.Rec.Bind.idx_mle
#print axioms LeanVMCircuits.Rec.Bind.termsRun_sem
#print axioms LeanVMCircuits.Rec.Bind.coordRun_sem
#print axioms LeanVMCircuits.Rec.Bind.blockRun_sem
#print axioms LeanVMCircuits.Rec.Bind.sideRun_sem
#print axioms LeanVMCircuits.Rec.Bind.SideCert.sem
#print axioms LeanVMCircuits.Rec.Bind.framework_congr
#print axioms LeanVMCircuits.Rec.Bind.SideCert.fits
#print axioms LeanVMCircuits.Rec.Bind.SideCert.dec
#print axioms LeanVMCircuits.Rec.Bind.formTerms_val
#print axioms LeanVMCircuits.Rec.Bind.limb_leaf
#print axioms LeanVMCircuits.Rec.Bind.fpAt_busTuple
#print axioms LeanVMCircuits.Rec.Bind.slotLeaf
#print axioms LeanVMCircuits.Rec.Bind.idxKey_val
#print axioms LeanVMCircuits.Rec.Bind.FormCert.isFinal_quad
#print axioms LeanVMCircuits.Rec.Bind.SideCert.dec_named
#print axioms LeanVMCircuits.Rec.Bind.balance_sides
#print axioms LeanVMCircuits.Rec.AirLink.stackLeaf_block
#print axioms LeanVMCircuits.Rec.AirLink.stackLeaf_pad
#print axioms LeanVMCircuits.Rec.AirLink.prod_stackLeaf
#print axioms LeanVMCircuits.Rec.AirLink.prod_busSlots
#print axioms LeanVMCircuits.Rec.AirLink.pullRoot_eq_slots
#print axioms LeanVMCircuits.Rec.AirLink.pushRoot_eq_slots
#print axioms LeanVMCircuits.Rec.AirLink.root_eq_stack
#print axioms LeanVMCircuits.Rec.AirLink.level_stack
#print axioms LeanVMCircuits.Rec.AirLink.pullRoot_eq_stack
#print axioms LeanVMCircuits.Rec.AirLink.pushRoot_eq_stack
#print axioms LeanVMCircuits.Rec.Flock.sChunk0
#print axioms LeanVMCircuits.Rec.Flock.sChunk1
#print axioms LeanVMCircuits.Rec.Flock.sChunk2
#print axioms LeanVMCircuits.Rec.Flock.sChunk3
#print axioms LeanVMCircuits.Rec.Flock.sChunk4
#print axioms LeanVMCircuits.Rec.Flock.sChunk5
#print axioms LeanVMCircuits.Rec.Flock.sChunk6
#print axioms LeanVMCircuits.Rec.Flock.sChunk7
#print axioms LeanVMCircuits.Rec.Flock.lChunk0
#print axioms LeanVMCircuits.Rec.Flock.lChunk1
#print axioms LeanVMCircuits.Rec.Flock.lChunk2
#print axioms LeanVMCircuits.Rec.Flock.lChunk3
#print axioms LeanVMCircuits.Rec.Flock.lChunk4
#print axioms LeanVMCircuits.Rec.Flock.lChunk5
#print axioms LeanVMCircuits.Rec.Flock.lChunk6
#print axioms LeanVMCircuits.Rec.Flock.lChunk7
#print axioms LeanVMCircuits.Rec.Flock.chunks_all
#print axioms LeanVMCircuits.Rec.Flock.sWords_van
#print axioms LeanVMCircuits.Rec.Flock.lWords_van
#print axioms LeanVMCircuits.Rec.Flock.skipOk_eq
#print axioms LeanVMCircuits.Rec.Flock.ofWord_lt
#print axioms LeanVMCircuits.Rec.Flock.kw_lt
#print axioms LeanVMCircuits.Rec.Flock.kw_inj
#print axioms LeanVMCircuits.Rec.Flock.negE
#print axioms LeanVMCircuits.Rec.Flock.sub_eq_addE
#print axioms LeanVMCircuits.Rec.Flock.ev_sqs
#print axioms LeanVMCircuits.Rec.Flock.all_getD
#print axioms LeanVMCircuits.Rec.Flock.skip_facts
#print axioms LeanVMCircuits.Rec.Flock.emb_pow
#print axioms LeanVMCircuits.Rec.Flock.emb_one'
#print axioms LeanVMCircuits.Rec.Flock.vanS_eval
#print axioms LeanVMCircuits.Rec.Flock.vanS_kw
#print axioms LeanVMCircuits.Rec.Flock.sNode_eq
#print axioms LeanVMCircuits.Rec.Flock.lNode_eq
#print axioms LeanVMCircuits.Rec.Flock.node_lt
#print axioms LeanVMCircuits.Rec.Flock.node_inj
#print axioms LeanVMCircuits.Rec.Flock.sNode_injective
#print axioms LeanVMCircuits.Rec.Flock.lNode_injective
#print axioms LeanVMCircuits.Rec.Flock.vanS_sNode
#print axioms LeanVMCircuits.Rec.Flock.vanS_lNode
#print axioms LeanVMCircuits.Rec.Flock.vanL_lNode
#print axioms LeanVMCircuits.Rec.Flock.vanL_eval
#print axioms LeanVMCircuits.Rec.Flock.offWord_lt
#print axioms LeanVMCircuits.Rec.Flock.d128_mul
#print axioms LeanVMCircuits.Rec.Flock.d64_mul
#print axioms LeanVMCircuits.Rec.Flock.two_pow_succE
#print axioms LeanVMCircuits.Rec.Flock.derivative_vanS
#print axioms LeanVMCircuits.Rec.Flock.derivative_vanL
#print axioms LeanVMCircuits.Rec.Flock.vanS_natDegree
#print axioms LeanVMCircuits.Rec.Flock.vanL_natDegree
#print axioms LeanVMCircuits.Rec.Flock.quo_mul
#print axioms LeanVMCircuits.Rec.Flock.quo_eval_root
#print axioms LeanVMCircuits.Rec.Flock.quo_eval_other
#print axioms LeanVMCircuits.Rec.Flock.quo_eval
#print axioms LeanVMCircuits.Rec.Flock.quo_natDegree
#print axioms LeanVMCircuits.Rec.Flock.lagS_natDegree
#print axioms LeanVMCircuits.Rec.Flock.lagS_node
#print axioms LeanVMCircuits.Rec.Flock.lagS_eval
#print axioms LeanVMCircuits.Rec.Flock.phat_natDegree
#print axioms LeanVMCircuits.Rec.Flock.phat_sNode
#print axioms LeanVMCircuits.Rec.Flock.phat_lNode
#print axioms LeanVMCircuits.Rec.Flock.phat_eval
#print axioms LeanVMCircuits.Rec.Flock.eq_zero_of_nodes
#print axioms LeanVMCircuits.Rec.Flock.phat_unique
#print axioms LeanVMCircuits.Rec.Flock.zeroInst_sum
#print axioms LeanVMCircuits.Rec.Flock.degreeOf_sliceMle
#print axioms LeanVMCircuits.Rec.Flock.degreeOf_quirky
#print axioms LeanVMCircuits.Rec.Flock.zeroInst_ok
#print axioms LeanVMCircuits.Rec.Flock.zeroInst_final
#print axioms LeanVMCircuits.Rec.Flock.zeroInst_weight
#print axioms LeanVMCircuits.Rec.Flock.quirkyY_eval
#print axioms LeanVMCircuits.Rec.Flock.honestP_eval
#print axioms LeanVMCircuits.Rec.Flock.quirkyY_natDegree
#print axioms LeanVMCircuits.Rec.Flock.honestP_natDegree
#print axioms LeanVMCircuits.Rec.Flock.eval_sliceMle
#print axioms LeanVMCircuits.Rec.Flock.honestP_sNode
#print axioms LeanVMCircuits.Rec.Flock.skipDraws_card
#print axioms LeanVMCircuits.Rec.Flock.rows_of_skip
#print axioms LeanVMCircuits.Rec.Flock.phat_honest
#print axioms LeanVMCircuits.Rec.Flock.W3.lt_iff
#print axioms LeanVMCircuits.Rec.Flock.evW_mul
#print axioms LeanVMCircuits.Rec.Flock.ew_eq_evW
#print axioms LeanVMCircuits.Rec.Flock.evW_onePlus
#print axioms LeanVMCircuits.Rec.Flock.flatMap_pairs
#print axioms LeanVMCircuits.Rec.Flock.eqWs_eq
#print axioms LeanVMCircuits.Rec.Flock.evW_eqW
#print axioms LeanVMCircuits.Rec.Flock.limbs_spec
#print axioms LeanVMCircuits.Rec.Flock.limbs_toE
#print axioms LeanVMCircuits.Rec.Flock.limbs_add
#print axioms LeanVMCircuits.Rec.Flock.coeff_add'
#print axioms LeanVMCircuits.Rec.Flock.coeff_zero'
#print axioms LeanVMCircuits.Rec.Flock.bitZ_xor
#print axioms LeanVMCircuits.Rec.Flock.bitZ_and
#print axioms LeanVMCircuits.Rec.Flock.sum_bitZ_parH
#print axioms LeanVMCircuits.Rec.Flock.phi_evW
#print axioms LeanVMCircuits.Rec.Flock.rowCheck_sem
#print axioms LeanVMCircuits.Rec.Flock.evW_smul
#print axioms LeanVMCircuits.Rec.Flock.smallEq_eq
#print axioms LeanVMCircuits.Rec.Flock.medEq_eq
#print axioms LeanVMCircuits.Rec.Flock.eChunk0
#print axioms LeanVMCircuits.Rec.Flock.eChunk1
#print axioms LeanVMCircuits.Rec.Flock.eChunk2
#print axioms LeanVMCircuits.Rec.Flock.eChunk3
#print axioms LeanVMCircuits.Rec.Flock.eq_rows
#print axioms LeanVMCircuits.Rec.Flock.dChunk0
#print axioms LeanVMCircuits.Rec.Flock.dChunk1
#print axioms LeanVMCircuits.Rec.Flock.dChunk2
#print axioms LeanVMCircuits.Rec.Flock.dChunk3
#print axioms LeanVMCircuits.Rec.Flock.dChunk4
#print axioms LeanVMCircuits.Rec.Flock.dChunk5
#print axioms LeanVMCircuits.Rec.Flock.dChunk6
#print axioms LeanVMCircuits.Rec.Flock.dChunk7
#print axioms LeanVMCircuits.Rec.Flock.dual_rows
#print axioms LeanVMCircuits.Rec.Flock.fixedOk_eq
#print axioms LeanVMCircuits.Rec.Flock.fixed_facts
#print axioms LeanVMCircuits.Rec.Flock.eqv_append
#print axioms LeanVMCircuits.Rec.Flock.bitPoint_add
#print axioms LeanVMCircuits.Rec.Flock.eqv_eqWs
#print axioms LeanVMCircuits.Rec.Flock.eqv_fixedPt
#print axioms LeanVMCircuits.Rec.Flock.fixed_indep
#print axioms LeanVMCircuits.Rec.Flock.bitPoint_append
#print axioms LeanVMCircuits.Rec.Flock.rowSum_append
#print axioms LeanVMCircuits.Rec.Flock.totalDegree_eqPoly
#print axioms LeanVMCircuits.Rec.Flock.fixDraws_card
#print axioms LeanVMCircuits.Rec.Flock.no_viol_of_rows
#print axioms LeanVMCircuits.Rec.Flock.no_viol_of_claim
#print axioms LeanVMCircuits.Rec.Bind.ev_mulConstAdd_K
#print axioms LeanVMCircuits.Rec.Bind.ev_eConst_K
#print axioms LeanVMCircuits.Rec.Bind.callsOk_mem
#print axioms LeanVMCircuits.Rec.Bind.SkipCert.sem
#print axioms LeanVMCircuits.Rec.Bind.ZeroCert.okIn_parts
#print axioms LeanVMCircuits.Rec.Bind.ZeroCert.final_eq
#print axioms LeanVMCircuits.Rec.Bind.ZeroCert.claim0_eq
#print axioms LeanVMCircuits.Rec.Bind.ZeroCert.weights_parts
#print axioms LeanVMCircuits.Rec.Bind.ZeroCert.weights_eq
#print axioms LeanVMCircuits.Rec.Bind.ZeroCert.point_eq
#print axioms LeanVMCircuits.Rec.Bind.zero_part
#print axioms LeanVMCircuits.Rec.Bind.no_viol_cast
#print axioms LeanVMCircuits.Rec.Bind.zero_rows
#print axioms LeanVMCircuits.Rec.FlockLin.eval_mlePoly_bit
#print axioms LeanVMCircuits.Rec.FlockLin.eval_mlePoly
#print axioms LeanVMCircuits.Rec.FlockLin.eval_eqX
#print axioms LeanVMCircuits.Rec.FlockLin.eval_eqPoly_at
#print axioms LeanVMCircuits.Rec.FlockLin.eqv_bitPoint
#print axioms LeanVMCircuits.Rec.FlockLin.eval_combPoly_bit
#print axioms LeanVMCircuits.Rec.FlockLin.linInst_sum
#print axioms LeanVMCircuits.Rec.FlockLin.degreeOf_mlePoly
#print axioms LeanVMCircuits.Rec.FlockLin.degreeOf_eqX
#print axioms LeanVMCircuits.Rec.FlockLin.degreeOf_combPoly
#print axioms LeanVMCircuits.Rec.FlockLin.degreeOf_linPoly
#print axioms LeanVMCircuits.Rec.FlockLin.linInst_ok
#print axioms LeanVMCircuits.Rec.FlockLin.linInst_weight
#print axioms LeanVMCircuits.Rec.FlockLin.linInst_final
#print axioms LeanVMCircuits.Rec.FlockLin.sum_cols
#print axioms LeanVMCircuits.Rec.FlockLin.colZ_split
#print axioms LeanVMCircuits.Rec.FlockLin.rowW_split
#print axioms LeanVMCircuits.Rec.FlockLin.sum3_comm
#print axioms LeanVMCircuits.Rec.FlockLin.sum_marg
#print axioms LeanVMCircuits.Rec.FlockLin.linInst_sum_eq
#print axioms LeanVMCircuits.Rec.FlockLin.formVal_eq
#print axioms LeanVMCircuits.Rec.FlockLin.eval_alphaPoly
#print axioms LeanVMCircuits.Rec.FlockLin.coeff_alphaPoly
#print axioms LeanVMCircuits.Rec.FlockLin.alphaBad_card
#print axioms LeanVMCircuits.Rec.FlockLin.batch_eq
#print axioms LeanVMCircuits.Rec.FlockLin.claim_true
#print axioms LeanVMCircuits.Rec.FlockLin.alphaRun_frac
#print axioms LeanVMCircuits.Rec.FlockLin.sum_eqv_one
#print axioms LeanVMCircuits.Rec.FlockLin.eval_pinPoly
#print axioms LeanVMCircuits.Rec.FlockLin.totalDegree_pinPoly
#print axioms LeanVMCircuits.Rec.FlockLin.pinBad_card
#print axioms LeanVMCircuits.Rec.FlockLin.pin_rows
#print axioms LeanVMCircuits.Rec.FlockLin.pinRun_frac
#print axioms LeanVMCircuits.Rec.FlockLin.pinV_outerFold
#print axioms LeanVMCircuits.Rec.FlockLin.bitPoint_append
#print axioms LeanVMCircuits.Rec.FlockLin.eqv_append
#print axioms LeanVMCircuits.Rec.FlockLin.slice_mle
#print axioms LeanVMCircuits.Rec.Bind.bits_sem
#print axioms LeanVMCircuits.Rec.Bind.eqe_sem
#print axioms LeanVMCircuits.Rec.Bind.listProd_range
#print axioms LeanVMCircuits.Rec.Bind.listSum_range
#print axioms LeanVMCircuits.Rec.Bind.LinCert.shape
#print axioms LeanVMCircuits.Rec.Bind.LinCert.sem
#print axioms LeanVMCircuits.Rec.Bind.LinCert.final_eq
#print axioms LeanVMCircuits.Rec.Bind.LinCert.answers_weight
#print axioms LeanVMCircuits.Rec.Bind.lin_part
#print axioms LeanVMCircuits.Rec.Bind.lin_triple
#print axioms LeanVMCircuits.Rec.RingSwitch.emb_pow
#print axioms LeanVMCircuits.Rec.RingSwitch.emb_one
#print axioms LeanVMCircuits.Rec.RingSwitch.emb_inj
#print axioms LeanVMCircuits.Rec.RingSwitch.frob_inj
#print axioms LeanVMCircuits.Rec.RingSwitch.frobK
#print axioms LeanVMCircuits.Rec.RingSwitch.y_pow_eight
#print axioms LeanVMCircuits.Rec.RingSwitch.y_frob
#print axioms LeanVMCircuits.Rec.RingSwitch.toE_frob
#print axioms LeanVMCircuits.Rec.RingSwitch.frobE
#print axioms LeanVMCircuits.Rec.RingSwitch.frob2
#print axioms LeanVMCircuits.Rec.RingSwitch.vr_val
#print axioms LeanVMCircuits.Rec.RingSwitch.phiN_add
#print axioms LeanVMCircuits.Rec.RingSwitch.phiN_zero
#print axioms LeanVMCircuits.Rec.RingSwitch.phiHom_apply
#print axioms LeanVMCircuits.Rec.RingSwitch.two_pow_six_sub
#print axioms LeanVMCircuits.Rec.RingSwitch.six_sub_succ
#print axioms LeanVMCircuits.Rec.RingSwitch.dsh_pos
#print axioms LeanVMCircuits.Rec.RingSwitch.dsh_le
#print axioms LeanVMCircuits.Rec.RingSwitch.coef_support
#print axioms LeanVMCircuits.Rec.RingSwitch.coef_zero_of_ge
#print axioms LeanVMCircuits.Rec.RingSwitch.eval_coef_succ
#print axioms LeanVMCircuits.Rec.RingSwitch.phiN_expand
#print axioms LeanVMCircuits.Rec.RingSwitch.phi_expand
#print axioms LeanVMCircuits.Rec.RingSwitch.coef_vars
#print axioms LeanVMCircuits.Rec.RingSwitch.sep_zero
#print axioms LeanVMCircuits.Rec.RingSwitch.not_mem_vars_sum
#print axioms LeanVMCircuits.Rec.RingSwitch.not_mem_vars_C_mul
#print axioms LeanVMCircuits.Rec.RingSwitch.vr_not_mem
#print axioms LeanVMCircuits.Rec.RingSwitch.sum_coef_ne_zero
#print axioms LeanVMCircuits.Rec.RingSwitch.kk_rev6
#print axioms LeanVMCircuits.Rec.RingSwitch.kk_dvd
#print axioms LeanVMCircuits.Rec.RingSwitch.coef_kk_sub
#print axioms LeanVMCircuits.Rec.RingSwitch.coef_kk_add
#print axioms LeanVMCircuits.Rec.RingSwitch.coef_kk_ne_zero
#print axioms LeanVMCircuits.Rec.RingSwitch.coef_ne_zero
#print axioms LeanVMCircuits.Rec.RingSwitch.phiDeg_eq
#print axioms LeanVMCircuits.Rec.RingSwitch.phiDeg_lt
#print axioms LeanVMCircuits.Rec.RingSwitch.coef_totalDegree
#print axioms LeanVMCircuits.Rec.RingSwitch.root_ne_frob32
#print axioms LeanVMCircuits.Rec.RingSwitch.frobS_mul
#print axioms LeanVMCircuits.Rec.RingSwitch.frobS_sub
#print axioms LeanVMCircuits.Rec.RingSwitch.frobS_gcd
#print axioms LeanVMCircuits.Rec.RingSwitch.root_frob_inj
#print axioms LeanVMCircuits.Rec.RingSwitch.node_frob
#print axioms LeanVMCircuits.Rec.RingSwitch.node_inj
#print axioms LeanVMCircuits.Rec.RingSwitch.pair_eq
#print axioms LeanVMCircuits.Rec.RingSwitch.exists_pair_ne_zero
#print axioms LeanVMCircuits.Rec.RingSwitch.eval_errPoly
#print axioms LeanVMCircuits.Rec.RingSwitch.errPoly_ne_zero
#print axioms LeanVMCircuits.Rec.RingSwitch.errPoly_totalDegree
#print axioms LeanVMCircuits.Rec.RingSwitch.ringBad_card
#print axioms LeanVMCircuits.Rec.RingSwitch.card_E
#print axioms LeanVMCircuits.Rec.RingSwitch.ringBad_frac
#print axioms LeanVMCircuits.Rec.RingSwitch.bitZ_toWord
#print axioms LeanVMCircuits.Rec.RingSwitch.pack
#print axioms LeanVMCircuits.Rec.RingSwitch.phi_sum
#print axioms LeanVMCircuits.Rec.RingSwitch.phi_bit
#print axioms LeanVMCircuits.Rec.RingSwitch.weighted_sum_eq
#print axioms LeanVMCircuits.Rec.RingSwitch.target_sub
#print axioms LeanVMCircuits.Rec.RingSwitch.mem_ringBad
#print axioms LeanVMCircuits.Rec.RingSwitch.ring_switch_sound
#print axioms LeanVMCircuits.Rec.RingSwitch.eqv_frob
#print axioms LeanVMCircuits.Rec.RingSwitch.sum_eqv_mul
#print axioms LeanVMCircuits.Rec.RingSwitch.weight_mle
#print axioms LeanVMCircuits.Rec.RingSwitch.eqv_char2
#print axioms LeanVMCircuits.Rec.RingSwitch.weight_mle_moved
#print axioms LeanVMCircuits.Rec.Bind.ofWord_zero_rs
#print axioms LeanVMCircuits.Rec.Bind.ofWord_one_rs
#print axioms LeanVMCircuits.Rec.Bind.RingCert.frob_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.sq_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.lad_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.fV_vr
#print axioms LeanVMCircuits.Rec.Bind.RingCert.cw_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.coef_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.word_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.horn_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.term_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.close_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.target_sem
#print axioms LeanVMCircuits.Rec.Bind.RingCert.sound
#print axioms LeanVMCircuits.Rec.Bind.RingCert.coefs_of_okIn
#print axioms LeanVMCircuits.Rec.Bind.RingCert.weight_sem
#print axioms LeanVMCircuits.Rec.Flocked.nc_eq
#print axioms LeanVMCircuits.Rec.Flocked.split_pt
#print axioms LeanVMCircuits.Rec.Flocked.pos_split
#print axioms LeanVMCircuits.Rec.Flocked.eval_slice
#print axioms LeanVMCircuits.Rec.Flocked.quirky_eval
#print axioms LeanVMCircuits.Rec.Flocked.quirky_c
#print axioms LeanVMCircuits.Rec.Flocked.bitE_a
#print axioms LeanVMCircuits.Rec.Flocked.bitE_b
#print axioms LeanVMCircuits.Rec.Flocked.fold_mat
#print axioms LeanVMCircuits.Rec.Flocked.quirky_a
#print axioms LeanVMCircuits.Rec.Flocked.quirky_b
#print axioms LeanVMCircuits.Rec.Flocked.bitE_coeff
#print axioms LeanVMCircuits.Rec.Flocked.ring_slice
#print axioms LeanVMCircuits.Rec.Bind.SkipCert.van_sem
#print axioms LeanVMCircuits.Rec.Bind.LagCert.sem
#print axioms LeanVMCircuits.Rec.Bind.LinCert.xin_length
#print axioms LeanVMCircuits.Rec.Bind.FlockCert.ok_parts
#print axioms LeanVMCircuits.Rec.Bind.wordBits_block
#print axioms LeanVMCircuits.Rec.Bind.ringDraws_card
#print axioms LeanVMCircuits.Rec.Bind.flock_rows
#print axioms LeanVMCircuits.Rec.Bind.flocked_of_rows
#print axioms LeanVMCircuits.Rec.Bind.skipRun_frac
#print axioms LeanVMCircuits.Rec.Bind.fixRun_frac
#print axioms LeanVMCircuits.Rec.Bind.ringRun_frac
#print axioms LeanVMCircuits.Rec.Edges.flockDeg_le
#print axioms LeanVMCircuits.Rec.Edges.tree_bound_flock
#print axioms LeanVMCircuits.Rec.Edges.RunHeld.sc
#print axioms LeanVMCircuits.Rec.AirLink.mleL_two
#print axioms LeanVMCircuits.Rec.AirLink.mleL_cons2
#print axioms LeanVMCircuits.Rec.AirLink.mleL_rowEq
#print axioms LeanVMCircuits.Rec.Bind.chal_readR
#print axioms LeanVMCircuits.Rec.Bind.LayerCert.chain_at
#print axioms LeanVMCircuits.Rec.Bind.GkrCert.ptR_length
#print axioms LeanVMCircuits.Rec.Bind.GkrCert.ptAt_length
#print axioms LeanVMCircuits.Rec.Bind.GkrCert.point_eq
#print axioms LeanVMCircuits.Rec.Bind.GkrCert.ptAt_ev
#print axioms LeanVMCircuits.Rec.Bind.top_step
#print axioms LeanVMCircuits.Rec.Bind.odd_step
#print axioms LeanVMCircuits.Rec.Bind.layer_step
#print axioms LeanVMCircuits.Rec.Bind.SideCert.leafClaim_mleL
#print axioms LeanVMCircuits.Rec.Edges.ChildCerts.lengths
#print axioms LeanVMCircuits.Rec.Bind.ResidCert.tausOk_sem
#print axioms LeanVMCircuits.Rec.Edges.ChildCerts.kappa_tau
#print axioms LeanVMCircuits.Rec.Edges.ChildCerts.layer_ok
#print axioms LeanVMCircuits.Rec.Edges.ChildCerts.leaves
#print axioms LeanVMCircuits.Rec.Edges.tableParts_certs
#print axioms LeanVMCircuits.Rec.Bind.recCoords_eq
#print axioms LeanVMCircuits.Rec.Bind.forms_slot_length
#print axioms LeanVMCircuits.Rec.Bind.pubLeaf
#print axioms LeanVMCircuits.Rec.Bind.stackLeaf_congr
#print axioms LeanVMCircuits.Rec.Bind.level_stack_of_eq
#print axioms LeanVMCircuits.Rec.Bind.SideCert.stack_root
#print axioms LeanVMCircuits.Rec.Edges.ChildCerts.roots
#print axioms LeanVMCircuits.Rec.Edges.ported_committedAt
#print axioms LeanVMCircuits.Rec.Edges.slotOf_firstSlot
#print axioms LeanVMCircuits.Rec.Edges.checksGiveTable_certs
#print axioms LeanVMCircuits.Rec.Bind.DrawCert.round_sem
#print axioms LeanVMCircuits.Rec.Bind.DrawCert.tbl_sem
#print axioms LeanVMCircuits.Rec.Bind.DrawCert.owns
#print axioms LeanVMCircuits.Rec.Bind.DrawCert.sem
#print axioms LeanVMCircuits.Rec.Edges.ChildCerts.drawOk
#print axioms LeanVMCircuits.Rec.Model.mem_pubFirst
#print axioms LeanVMCircuits.Rec.Model.length_pubFirst
#print axioms LeanVMCircuits.Rec.Model.sat_stmtFirst
#print axioms LeanVMCircuits.Rec.AirLink.size_rowsOf_stmtFirst
#print axioms LeanVMCircuits.Rec.Edges.checksGiveTable_opened
#print axioms LeanVMCircuits.Rec.HashRows.val_emit
#print axioms LeanVMCircuits.Rec.HashRows.run_holds
#print axioms LeanVMCircuits.Rec.HashRows.foldl_slots
#print axioms LeanVMCircuits.Rec.HashRows.nProducts_model
#print axioms LeanVMCircuits.Rec.HashRows.artifact_products
#print axioms LeanVMCircuits.Rec.HashRows.freeSlots_nodup
#print axioms LeanVMCircuits.Rec.HashRows.rowsOf_slots
#print axioms LeanVMCircuits.Rec.HashRows.rowsOf_map
#print axioms LeanVMCircuits.Rec.HashRows.outAff_eq
#print axioms LeanVMCircuits.Rec.HashRows.rows_sound
#print axioms LeanVMCircuits.Rec.Bind.FlockCert.roundsOk_sem
#print axioms LeanVMCircuits.Rec.Bind.columnWord_bit
#print axioms LeanVMCircuits.Rec.Bind.hashGates
#print axioms LeanVMCircuits.Rec.Bind.FlockCert.heightOk_sem
#print axioms LeanVMCircuits.Rec.Edges.tableParts_named
