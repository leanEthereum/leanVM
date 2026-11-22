/-
The axioms of every public statement of the library: Lean's three (`propext`, `Classical.choice`,
`Quot.sound`) and nothing else. Each check is under `#guard_msgs`, so the build fails if a
statement gains an axiom (a `sorry` would show as `sorryAx`). The messages were produced by Lean
and are compared again at every build.
-/
import PeriodDescent.Johnson3
import PeriodDescent.Affine
import PeriodDescent.Theorem35
import PeriodDescent.Numbers
import PeriodDescent.Instance

namespace PeriodDescent

/-! ### `Johnson3.lean` -/

/-- info: 'PeriodDescent.two_mul_choose_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_choose_two

/-- info: 'PeriodDescent.six_mul_choose_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms six_mul_choose_three

/-- info: 'PeriodDescent.H3_eq_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms H3_eq_choose

/-- info: 'PeriodDescent.H3_tangent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms H3_tangent

/-- info: 'PeriodDescent.H3_slope' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms H3_slope

/-- info: 'PeriodDescent.H3_slope_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms H3_slope_nonneg

/-- info: 'PeriodDescent.tripleSum_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tripleSum_const

/-- info: 'PeriodDescent.tripleSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tripleSum_le

/-- info: 'PeriodDescent.tripleSum_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tripleSum_sum

/-- info: 'PeriodDescent.tripleSum_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tripleSum_indicator

/-- info: 'PeriodDescent.deg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deg_le

/-- info: 'PeriodDescent.sum_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_deg

/-- info: 'PeriodDescent.threewise_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threewise_identity

/-- info: 'PeriodDescent.threewise_jensen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threewise_jensen

/-- info: 'PeriodDescent.threewise_closed_form_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threewise_closed_form_arith

/-- info: 'PeriodDescent.threewise_johnson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threewise_johnson

/-- info: 'PeriodDescent.threewise_johnson_rat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threewise_johnson_rat


/-! ### `Base.lean` -/

/-- info: 'PeriodDescent.step_arith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms step_arith

/-- info: 'PeriodDescent.agr_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agr_le_card

/-- info: 'PeriodDescent.pinned_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pinned_bound

/-- info: 'PeriodDescent.list_bound_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms list_bound_nat

/-- info: 'PeriodDescent.polyAgr_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polyAgr_le_card

/-- info: 'PeriodDescent.eq_of_natDegree_le_of_eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_of_natDegree_le_of_eval_eq

/-- info: 'PeriodDescent.base_bound_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms base_bound_nat

/-- info: 'PeriodDescent.base_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms base_bound

/-- info: 'PeriodDescent.ordinary_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ordinary_bound

/-- info: 'PeriodDescent.collinear_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms collinear_bound


/-! ### `Affine.lean` -/

/-- info: 'PeriodDescent.affine_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affine_bound

/-- info: 'PeriodDescent.finrank_add_card_common_zeros_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finrank_add_card_common_zeros_le

/-- info: 'PeriodDescent.card_common_zeros_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_common_zeros_le

/-- info: 'PeriodDescent.affine_poly_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affine_poly_bound

/-- info: 'PeriodDescent.affine_ordinary_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affine_ordinary_bound


/-! ### `Core.lean` -/

/-- info: 'PeriodDescent.qPoly_monic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qPoly_monic

/-- info: 'PeriodDescent.qPoly_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qPoly_natDegree

/-- info: 'PeriodDescent.qPoly_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qPoly_ne_one

/-- info: 'PeriodDescent.eval_qPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_qPoly

/-- info: 'PeriodDescent.comp_qPoly_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms comp_qPoly_eq_zero

/-- info: 'PeriodDescent.comp_qPoly_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms comp_qPoly_injective

/-- info: 'PeriodDescent.exists_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_decomp

/-- info: 'PeriodDescent.decomp_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decomp_unique

/-- info: 'PeriodDescent.decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decomp

/-- info: 'PeriodDescent.parts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parts_eq

/-- info: 'PeriodDescent.natDegree_mul_comp_qPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_mul_comp_qPoly

/-- info: 'PeriodDescent.natDegree_le_of_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_le_of_descent

/-- info: 'PeriodDescent.descent_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descent_unique

/-- info: 'PeriodDescent.eval_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_descent

/-- info: 'PeriodDescent.agree_iff_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agree_iff_of_ne_zero

/-- info: 'PeriodDescent.eval_eq_of_eval_rho_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_eq_of_eval_rho_eq_zero

/-- info: 'PeriodDescent.Periodic.swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Periodic.swap

/-- info: 'PeriodDescent.Periodic.base_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Periodic.base_swap

/-- info: 'PeriodDescent.periodic_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms periodic_of_const

/-- info: 'PeriodDescent.qPoly_comp_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qPoly_comp_shift

/-- info: 'PeriodDescent.comp_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms comp_shift

/-- info: 'PeriodDescent.invariant_iff_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invariant_iff_part1

/-- info: 'PeriodDescent.invariant_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invariant_iff_exists

/-- info: 'PeriodDescent.periodic_iff_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms periodic_iff_parts

/-- info: 'PeriodDescent.eGcd_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eGcd_ne_zero

/-- info: 'PeriodDescent.rho_mul_eGcd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rho_mul_eGcd

/-- info: 'PeriodDescent.rho_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rho_ne_zero

/-- info: 'PeriodDescent.natDegree_rho_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_rho_le

/-- info: 'PeriodDescent.periodic_iff_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms periodic_iff_exists

/-- info: 'PeriodDescent.periodic_triple_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms periodic_triple_iff


/-! ### `Level.lean` -/

/-- info: 'PeriodDescent.subPoly_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subPoly_eval_eq_zero

/-- info: 'PeriodDescent.fiber_card_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fiber_card_eq_kernel

/-- info: 'PeriodDescent.fiber_card_le_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fiber_card_le_kernel

/-- info: 'PeriodDescent.image_card_mul_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms image_card_mul_kernel

/-- info: 'PeriodDescent.IsLevel.additive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.additive

/-- info: 'PeriodDescent.IsLevel.comp_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.comp_translate

/-- info: 'PeriodDescent.IsLevel.kernel_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.kernel_card

/-- info: 'PeriodDescent.IsLevel.fiber_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.fiber_card_le

/-- info: 'PeriodDescent.IsLevel.image_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.image_card

/-- info: 'PeriodDescent.IsLevel.level_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.level_le

/-- info: 'PeriodDescent.IsLevel.image_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.image_card_eq

/-- info: 'PeriodDescent.IsLevel.dirs_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.dirs_card_le

/-- info: 'PeriodDescent.IsLevel.exists_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.exists_dir

/-- info: 'PeriodDescent.IsLevel.exists_subspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLevel.exists_subspace


/-! ### `Step.lean` -/

/-- info: 'PeriodDescent.nextWord_of_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nextWord_of_eval_eq_zero

/-- info: 'PeriodDescent.nextWord_agree_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nextWord_agree_iff

/-- info: 'PeriodDescent.polyAgr_descent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polyAgr_descent_eq

/-- info: 'PeriodDescent.card_zeros_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_zeros_le

/-- info: 'PeriodDescent.polyAgr_descent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polyAgr_descent_le

/-- info: 'PeriodDescent.slack_arith' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms slack_arith

/-- info: 'PeriodDescent.descentMap_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descentMap_spec

/-- info: 'PeriodDescent.descentMap_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descentMap_injOn

/-- info: 'PeriodDescent.LevelPb.next_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LevelPb.next_mem

/-- info: 'PeriodDescent.LevelPb.descent_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LevelPb.descent_step


/-! ### `Induction.lean` -/

/-- info: 'PeriodDescent.greedy_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms greedy_cover

/-- info: 'PeriodDescent.one_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_step

/-- info: 'PeriodDescent.supersaturation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms supersaturation

/-- info: 'PeriodDescent.bnd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bnd_le

/-- info: 'PeriodDescent.expo_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expo_eq

/-- info: 'PeriodDescent.bnd_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bnd_closed

/-- info: 'PeriodDescent.abstract_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abstract_descent

/-- info: 'PeriodDescent.choose_two_le_choose_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms choose_two_le_choose_three

/-- info: 'PeriodDescent.succ_le_four_mul_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms succ_le_four_mul_choose

/-- info: 'PeriodDescent.abstract_descent_notes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abstract_descent_notes

/-- info: 'PeriodDescent.abstract_descent_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abstract_descent_sharp

/-- info: 'PeriodDescent.bndDP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bndDP_le

/-- info: 'PeriodDescent.abstract_descent_DP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abstract_descent_DP


/-! ### `TheoremR.lean` -/

/-- info: 'PeriodDescent.PL_of_PLsub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PL_of_PLsub

/-- info: 'PeriodDescent.baseB_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baseB_zero

/-- info: 'PeriodDescent.baseB_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baseB_nonneg

/-- info: 'PeriodDescent.LevelPb.card_le_baseB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LevelPb.card_le_baseB

/-- info: 'PeriodDescent.LevelPb.ofWord_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LevelPb.ofWord_mem

/-- info: 'PeriodDescent.BadTriple.exists_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BadTriple.exists_dir

/-- info: 'PeriodDescent.theoremR_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theoremR_gen

/-- info: 'PeriodDescent.theoremR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theoremR

/-- info: 'PeriodDescent.theoremR_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theoremR_top

/-- info: 'PeriodDescent.theoremR_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theoremR_sharp


/-! ### `Theorem35.lean` -/

/-- info: 'PeriodDescent.theorem35' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theorem35


/-! ### `Numbers.lean` -/

/-- info: 'PeriodDescent.T_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms T_eq

/-- info: 'PeriodDescent.Delta_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Delta_eq

/-- info: 'PeriodDescent.expo_24' depends on axioms: [propext] -/
#guard_msgs in
#print axioms expo_24

/-- info: 'PeriodDescent.expo_20' depends on axioms: [propext] -/
#guard_msgs in
#print axioms expo_20

/-- info: 'PeriodDescent.choose_8_3' does not depend on any axioms -/
#guard_msgs in
#print axioms choose_8_3

/-- info: 'PeriodDescent.choose_7_2' does not depend on any axioms -/
#guard_msgs in
#print axioms choose_7_2

/-- info: 'PeriodDescent.choose_17_3' does not depend on any axioms -/
#guard_msgs in
#print axioms choose_17_3

/-- info: 'PeriodDescent.choose_134_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_134_3

/-- info: 'PeriodDescent.choose_135_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_135_3

/-- info: 'PeriodDescent.bound_f7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f7

/-- info: 'PeriodDescent.bound_f7_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f7_lower

/-- info: 'PeriodDescent.bound_f16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f16

/-- info: 'PeriodDescent.bound_f16_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f16_lower

/-- info: 'PeriodDescent.bound_f133' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f133

/-- info: 'PeriodDescent.bound_f133_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f133_lower

/-- info: 'PeriodDescent.bound_f134' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f134

/-- info: 'PeriodDescent.bound_f134_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f134_lower

/-- info: 'PeriodDescent.bound_sharp_f7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_sharp_f7

/-- info: 'PeriodDescent.theoremR_N25_f7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theoremR_N25_f7

/-- info: 'PeriodDescent.kappa_20' depends on axioms: [propext] -/
#guard_msgs in
#print axioms kappa_20

/-- info: 'PeriodDescent.baseB_20_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baseB_20_le

/-- info: 'PeriodDescent.bound_f7_j20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f7_j20

/-- info: 'PeriodDescent.bound_f16_j20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f16_j20

/-- info: 'PeriodDescent.bound_f134_j20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_f134_j20

/-- info: 'PeriodDescent.bound_sharp_f7_j20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_sharp_f7_j20

/-- info: 'PeriodDescent.theoremR_N25_f7_j20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theoremR_N25_f7_j20


/-! ### `Instance.lean` -/

/-- info: 'PeriodDescent.PLsub_one_of_prod_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLsub_one_of_prod_le

/-- info: 'PeriodDescent.allK64_isSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allK64_isSubspace

/-- info: 'PeriodDescent.allK64_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allK64_card

/-- info: 'PeriodDescent.concrete_K64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms concrete_K64

end PeriodDescent
