/-
The axioms of the named statements of the library `Rounds` listed below: Lean's three (`propext`,
`Classical.choice`, `Quot.sound`) and nothing else. Each check is under `#guard_msgs`, so the
build fails if a statement gains an axiom (a `sorry` would show as `sorryAx`). The examples show
that the typeclass hypotheses are satisfiable at the deployed field size.
-/
import Rounds.Fold
import Rounds.Final
import Rounds.Extract
import Rounds.Pinned

namespace Rounds

/-- The hypotheses on the field are satisfiable: `GF(2^128)`, four lanes after the fold. -/
noncomputable example := @fold_transition (GaloisField 2 128) _ (Fintype.ofFinite _) (Fin 4) _ _

noncomputable example := @batch_transition (GaloisField 2 128) _ (Fintype.ofFinite _) (Fin 64) _

noncomputable example :=
  @query_transition (GaloisField 2 128) _ (Fintype.ofFinite _) (Fin 16) _ _

noncomputable example := @final_transition (GaloisField 2 128) _

noncomputable example :=
  @tail_round_transition (GaloisField 2 128) _ (Fintype.ofFinite _) (Fin 4) _

noncomputable example := @descent_step (GaloisField 2 128) _ (Fin 4) _

/-- info: 'Rounds.Doomed.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Doomed.mono

/-- info: 'Rounds.agr_foldWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agr_foldWord

/-- info: 'Rounds.agr_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agr_elim

/-- info: 'Rounds.weight_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms weight_elim

/-- info: 'Rounds.agr_subset_agr_foldTuple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agr_subset_agr_foldTuple

/-- info: 'Rounds.evL_exHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evL_exHalves

/-- info: 'Rounds.fold_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fold_transition

/-- info: 'Rounds.fold_transition_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fold_transition_density

/-- info: 'Rounds.pull_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pull_true

/-- info: 'Rounds.fold_transition_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fold_transition_plain

/-- info: 'Rounds.card_powsum_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_powsum_zero_le

/-- info: 'Rounds.card_batch_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_batch_zero_le

/-- info: 'Rounds.batch_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batch_transition

/-- info: 'Rounds.k2_hfalse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms k2_hfalse

/-- info: 'Rounds.batch_transition_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batch_transition_density

/-- info: 'Rounds.card_filter_prod_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_filter_prod_le

/-- info: 'Rounds.card_queries_in_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_queries_in_le

/-- info: 'Rounds.card_queries_agree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_queries_agree_le

/-- info: 'Rounds.density_queries_agree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms density_queries_agree_le

/-- info: 'Rounds.card_batch3_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_batch3_zero_le

/-- info: 'Rounds.Doomed.one_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Doomed.one_lane

/-- info: 'Rounds.query_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms query_transition

/-- info: 'Rounds.query_transition_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms query_transition_density

/-- info: 'Rounds.final_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms final_core

/-- info: 'Rounds.final_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms final_transition

/-- info: 'Rounds.final_transition_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms final_transition_plain

/-- info: 'Rounds.final_transition_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms final_transition_density

/-- info: 'Rounds.tail_round_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tail_round_transition

/-- info: 'Rounds.tail_round_transition_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tail_round_transition_density

/-- info: 'Rounds.nearT_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nearT_unique

/-- info: 'Rounds.NearT.inList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearT.inList

/-- info: 'Rounds.NearT.fold_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearT.fold_eq

/-- info: 'Rounds.NearT.degree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NearT.degree_lt

/-- info: 'Rounds.descent_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descent_step

/-- info: 'Rounds.existsUnique_nearT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms existsUnique_nearT

/-- info: 'Rounds.inList_iff_mem_listW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inList_iff_mem_listW

/-- info: 'Rounds.sep_of_not_mem_nonSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sep_of_not_mem_nonSep

/-- info: 'Rounds.batch_transition_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batch_transition_pinned

/-- info: 'Rounds.query_transition_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms query_transition_pinned

end Rounds
