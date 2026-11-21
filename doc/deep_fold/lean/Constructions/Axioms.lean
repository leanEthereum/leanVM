/-
The axioms of the named statements of the library `Constructions` listed below: Lean's three
(`propext`, `Classical.choice`, `Quot.sound`) and nothing else. Each check is under `#guard_msgs`,
so the build fails if a statement gains an axiom (a `sorry` would show as `sorryAx`). The
statements of `Concrete.lean` instantiate the hypotheses in `GaloisField 2 128` at the deployed
sizes, so they are satisfiable.
-/
import Constructions.Concrete
import Constructions.UnionOfFlats

namespace Constructions

/-- info: 'Constructions.locator_coset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms locator_coset

/-- info: 'Constructions.subPoly_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subPoly_eval_eq_zero

/-- info: 'Constructions.subPoly_comp_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subPoly_comp_add

/-- info: 'Constructions.subPoly_eval_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subPoly_eval_add

/-- info: 'Constructions.subPoly_adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subPoly_adjoin

/-- info: 'Constructions.addSubgroup_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms addSubgroup_induction

/-- info: 'Constructions.exists_card_eq_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_card_eq_two_pow

/-- info: 'Constructions.subPoly_isLinearized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subPoly_isLinearized

/-- info: 'Constructions.IsLinearized.aeval_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLinearized.aeval_add

/-- info: 'Constructions.subPoly_aeval_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subPoly_aeval_add

/-- info: 'Constructions.IsLinearized.natDegree_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsLinearized.natDegree_sub_le

/-- info: 'Constructions.natDegree_subPoly_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_subPoly_sub_le

/-- info: 'Constructions.flatPoly_mul_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatPoly_mul_X

/-- info: 'Constructions.flatPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatPoly_eval

/-- info: 'Constructions.flatPoly_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatPoly_eq

/-- info: 'Constructions.agree_flatPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agree_flatPoly

/-- info: 'Constructions.flatPoly_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatPoly_injective

/-- info: 'Constructions.flatPoly_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatPoly_natDegree_le

/-- info: 'Constructions.flatPoly_degree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatPoly_degree_lt

/-- info: 'Constructions.flatPoly_mem_RSList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatPoly_mem_RSList

/-- info: 'Constructions.flats_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flats_list

/-- info: 'Constructions.card_hyperplanes_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_hyperplanes_ge

/-- info: 'Constructions.flats_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flats_quarter

/-- info: 'Constructions.pole_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pole_collapse

/-- info: 'Constructions.combiner_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms combiner_collapse

/-- info: 'Constructions.polyFold_pole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polyFold_pole

/-- info: 'Constructions.affFold_pole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affFold_pole

/-- info: 'Constructions.polyFold_pole_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polyFold_pole_close

/-- info: 'Constructions.polyFold_pole_close_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polyFold_pole_close_iff

/-- info: 'Constructions.affFold_pole_close_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affFold_pole_close_iff

/-- info: 'Constructions.card_bad_affFold_pole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_bad_affFold_pole

/-- info: 'Constructions.card_agree_poleWord_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_agree_poleWord_le

/-- info: 'Constructions.scalFold_pole_close_of_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scalFold_pole_close_of_list

/-- info: 'Constructions.lemmaA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaA

/-- info: 'Constructions.lemmaA_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaA_witness

/-- info: 'Constructions.lemmaA_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaA_card

/-- info: 'Constructions.exists_pole_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_pole_injOn

/-- info: 'Constructions.list_gives_bad_challenges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms list_gives_bad_challenges

/-- info: 'Constructions.flat_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flat_direction

/-- info: 'Constructions.natDegree_locator_flat_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_locator_flat_sub_le

/-- info: 'Constructions.padPoly_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms padPoly_natDegree_le

/-- info: 'Constructions.padPoly_mem_RSList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms padPoly_mem_RSList

/-- info: 'Constructions.agree_padPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agree_padPoly

/-- info: 'Constructions.padded_flats_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms padded_flats_list

/-- info: 'Constructions.five_eighths_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms five_eighths_slack

/-- info: 'Constructions.five_eighths_genuine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms five_eighths_genuine

/-- info: 'Constructions.HasGap.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasGap.mul

/-- info: 'Constructions.gap_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_lemma

/-- info: 'Constructions.gap_lemma_locator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_lemma_locator

/-- info: 'Constructions.hasGap_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasGap_flat

/-- info: 'Constructions.hasGap_coset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasGap_coset

/-- info: 'Constructions.FlatUnion.card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlatUnion.card

/-- info: 'Constructions.FlatUnion.dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlatUnion.dvd

/-- info: 'Constructions.FlatUnion.hasGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlatUnion.hasGap

/-- info: 'Constructions.hasGap_subPoly_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasGap_subPoly_sq

/-- info: 'Constructions.hasGap_subPoly_odd_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasGap_subPoly_odd_pow

/-- info: 'Constructions.FlatUnion.natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlatUnion.natDegree_le

/-- info: 'Constructions.flatUnion_five_eighths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatUnion_five_eighths

/-- info: 'Constructions.flatUnion_mem_RSList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flatUnion_mem_RSList

/-- info: 'Constructions.locator_glued' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms locator_glued

/-- info: 'Constructions.card_glued' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_glued

/-- info: 'Constructions.glued_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glued_injective

/-- info: 'Constructions.subPoly_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subPoly_eq_comp

/-- info: 'Constructions.natDegree_gluedPoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natDegree_gluedPoly_le

/-- info: 'Constructions.gluedPoly_mem_RSList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gluedPoly_mem_RSList

/-- info: 'Constructions.glued_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glued_list

/-- info: 'Constructions.glued_five_eighths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glued_five_eighths

/-- info: 'Constructions.glued_eq_imp_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glued_eq_imp_invariant

/-- info: 'Constructions.sum_pts_adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_pts_adjoin

/-- info: 'Constructions.exists_label_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_label_set

/-- info: 'Constructions.glued_list_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glued_list_card

/-- info: 'Constructions.exists_addSubgroup_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_addSubgroup_card

/-- info: 'Constructions.flats_break_mca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flats_break_mca

/-- info: 'Constructions.exists_domain_GF128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_domain_GF128

/-- info: 'Constructions.flats_quarter_GF128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flats_quarter_GF128

/-- info: 'Constructions.flats_break_mca_GF128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flats_break_mca_GF128

/-- info: 'Constructions.five_eighths_slack_GF128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms five_eighths_slack_GF128

/-- info: 'Constructions.five_eighths_genuine_GF128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms five_eighths_genuine_GF128

/-- info: 'Constructions.glued_list_card_GF128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glued_list_card_GF128

end Constructions
