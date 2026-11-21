/-
The axioms of the named statements of the library `DeepFold` listed below: Lean's three
(`propext`, `Classical.choice`, `Quot.sound`) and nothing else. Each check is under `#guard_msgs`,
so the build fails if a statement gains an axiom (a `sorry` would show as `sorryAx`). The first two
examples show that the typeclass hypotheses are satisfiable at the deployed field size.
-/
import DeepFold.Main

namespace DeepFold

/-- The hypotheses on the field are satisfiable: `GF(2^128)` with four lanes. -/
noncomputable example := @lemmaF_round (GaloisField 2 128) _ (Fintype.ofFinite _) (Fin 4) _ _

noncomputable example := @lemmaF_exc (GaloisField 2 128) _ (Fintype.ofFinite _) (Fin 4) _

/-- info: 'DeepFold.Delta_eq_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Delta_eq_det

/-- info: 'DeepFold.Delta_char_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Delta_char_two

/-- info: 'DeepFold.Delta_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Delta_eval_eq_zero

/-- info: 'DeepFold.Delta_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Delta_natDegree_le

/-- info: 'DeepFold.Delta_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Delta_eq_zero_iff

/-- info: 'DeepFold.isFold_pair_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isFold_pair_left

/-- info: 'DeepFold.isFold_pair_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isFold_pair_right

/-- info: 'DeepFold.isFold_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isFold_unique

/-- info: 'DeepFold.Delta_eq_zero_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Delta_eq_zero_iff_exists

/-- info: 'DeepFold.fold_anchor_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fold_anchor_dichotomy

/-- info: 'DeepFold.class_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms class_trichotomy

/-- info: 'DeepFold.class_poly_of_card_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms class_poly_of_card_gt

/-- info: 'DeepFold.card_agr_outside_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_agr_outside_le

/-- info: 'DeepFold.agrPair_card_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agrPair_card_ge

/-- info: 'DeepFold.card_vanish_all_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_vanish_all_le

/-- info: 'DeepFold.prob_vanish_all_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prob_vanish_all_le

/-- info: 'DeepFold.sum_Ncount_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_Ncount_le

/-- info: 'DeepFold.card_Exc_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_Exc_mul_le

/-- info: 'DeepFold.density_Exc_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms density_Exc_le

/-- info: 'DeepFold.card_nondep_triples_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_nondep_triples_ge

/-- info: 'DeepFold.exists_big_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_big_class

/-- info: 'DeepFold.exists_big_class_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_big_class_quarter

/-- info: 'DeepFold.quarter_cube_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quarter_cube_le

/-- info: 'DeepFold.card_ExcD_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_ExcD_mul_le

/-- info: 'DeepFold.density_ExcD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms density_ExcD_le

/-- info: 'DeepFold.card_T_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_T_le

/-- info: 'DeepFold.deepFold_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deepFold_class

/-- info: 'DeepFold.deepFold_theorem3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deepFold_theorem3

/-- info: 'DeepFold.evL_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evL_add

/-- info: 'DeepFold.evL_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evL_mul

/-- info: 'DeepFold.evL_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evL_halves

/-- info: 'DeepFold.card_evL_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_evL_zero_le

/-- info: 'DeepFold.evL_DeltaL_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evL_DeltaL_eq_zero

/-- info: 'DeepFold.DeltaL_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DeltaL_eq_zero_iff

/-- info: 'DeepFold.isFoldL_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isFoldL_unique

/-- info: 'DeepFold.card_ExcL_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_ExcL_mul_le

/-- info: 'DeepFold.density_ExcL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms density_ExcL_le

/-- info: 'DeepFold.deepFoldL_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deepFoldL_class

/-- info: 'DeepFold.classL_poly_of_card_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms classL_poly_of_card_gt

/-- info: 'DeepFold.card_agrL_outside_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_agrL_outside_le

/-- info: 'DeepFold.exists_nearL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nearL

/-- info: 'DeepFold.deepFoldL_theorem3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deepFoldL_theorem3

/-- info: 'DeepFold.card_quadric_zeros_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_quadric_zeros_le

/-- info: 'DeepFold.deepFoldL_fold_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deepFoldL_fold_round

/-- info: 'DeepFold.deepFold_lemmaF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deepFold_lemmaF

/-- info: 'DeepFold.mem_fullT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_fullT

/-- info: 'DeepFold.lemmaF_exc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaF_exc

/-- info: 'DeepFold.lemmaF_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaF_round

/-- info: 'DeepFold.lemmaD4_exc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaD4_exc

/-- info: 'DeepFold.lemmaD4_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaD4_round

end DeepFold
