/-
The axioms of every statement of the `Protocol` library: Lean's three (`propext`,
`Classical.choice`, `Quot.sound`) or a subset of them, and nothing else. Each check is under
`#guard_msgs`, so the build fails if a statement gains an axiom (a `sorry` would show as
`sorryAx`). The first examples show that the hypotheses on the field of the deployed statements
are satisfiable.
-/
import Protocol.Params

namespace Protocol

/-- `GF(2^128)` has `2^128` elements: the hypothesis `hq` of the deployed statements. -/
theorem card_galoisField_two_128 :
    @Fintype.card (GaloisField 2 128) (Fintype.ofFinite _) = 2 ^ 128 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 128 (by norm_num)]

/-- The deployed statements at `GF(2^128)`. -/
noncomputable example := @level0_point_error (GaloisField 2 128) _ (Fintype.ofFinite _)
  card_galoisField_two_128

noncomputable example := @level0_ladder_error (GaloisField 2 128) _ (Fintype.ofFinite _)
  card_galoisField_two_128

noncomputable example := @levelPot_step (GaloisField 2 128) _ (Fintype.ofFinite _)

noncomputable example := @ladderPot_step (GaloisField 2 128) _ (Fintype.ofFinite _)

/-- info: 'Protocol.point_error_level0_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms point_error_level0_arith

/-- info: 'Protocol.point_error_level0_arith_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms point_error_level0_arith_11

/-- info: 'Protocol.held_ladder0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms held_ladder0

/-- info: 'Protocol.ladder_error_level0_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladder_error_level0_arith

/-- info: 'Protocol.fold_error_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fold_error_arith

/-- info: 'Protocol.fold_error_last_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fold_error_last_arith

/-- info: 'Protocol.threshold_level0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threshold_level0_pos

/-- info: 'Protocol.level0_point_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms level0_point_error

/-- info: 'Protocol.level0_ladder_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms level0_ladder_error

/-- info: 'Protocol.exL_succ' depends on axioms: [propext] -/
#guard_msgs in
#print axioms exL_succ

/-- info: 'Protocol.two_pow_dvd_exL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms two_pow_dvd_exL

/-- info: 'Protocol.exL_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exL_add_le

/-- info: 'Protocol.exL_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exL_injective

/-- info: 'Protocol.evL_exL_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evL_exL_halves

/-- info: 'Protocol.foldW_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms foldW_apply

/-- info: 'Protocol.levelPot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelPot_zero

/-- info: 'Protocol.levelPot_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelPot_succ

/-- info: 'Protocol.levelPot_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelPot_eq_sum

/-- info: 'Protocol.levelPot_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelPot_nonneg

/-- info: 'Protocol.levelPot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelPot_step

/-- info: 'Protocol.dens_excW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_excW_le

/-- info: 'Protocol.levelPot_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelPot_init

/-- info: 'Protocol.dens_not_good_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_not_good_le

/-- info: 'Protocol.agrL_eq_agrW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agrL_eq_agrW

/-- info: 'Protocol.agrPairL_eq_agrW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agrPairL_eq_agrW

/-- info: 'Protocol.finite_tuples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_tuples

/-- info: 'Protocol.mem_listW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_listW

/-- info: 'Protocol.listW_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms listW_natDegree_le

/-- info: 'Protocol.listW_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms listW_anti

/-- info: 'Protocol.mem_fullT_iff_mem_listW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_fullT_iff_mem_listW

/-- info: 'Protocol.card_fullT_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_fullT_fiber

/-- info: 'Protocol.fullT_fiber_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fullT_fiber_le

/-- info: 'Protocol.potS_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potS_zero

/-- info: 'Protocol.potS_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potS_succ

/-- info: 'Protocol.potS_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potS_nonneg

/-- info: 'Protocol.potS_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potS_step

/-- info: 'Protocol.avg_ofFn_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_ofFn_append

/-- info: 'Protocol.held_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms held_zero

/-- info: 'Protocol.held_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms held_succ

/-- info: 'Protocol.avg_potS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_potS_le

/-- info: 'Protocol.potS_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potS_init

/-- info: 'Protocol.not_mem_ExcL_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_mem_ExcL_iff

/-- info: 'Protocol.NcountL_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NcountL_ofFn

/-- info: 'Protocol.avg_NcountL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_NcountL_le

/-- info: 'Protocol.ladderPot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladderPot_zero

/-- info: 'Protocol.ladderPot_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladderPot_succ

/-- info: 'Protocol.ladderCost_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladderCost_nonneg

/-- info: 'Protocol.ladderPot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladderPot_step

/-- info: 'Protocol.ladderPot_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladderPot_init

/-- info: 'Protocol.dens_not_goodS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_not_goodS_le

/-- info: 'Protocol.dens_eq_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_eq_avg

/-- info: 'Protocol.dens_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_mem

/-- info: 'Protocol.avg_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_nonneg

/-- info: 'Protocol.avg_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_mono

/-- info: 'Protocol.avg_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_add

/-- info: 'Protocol.avg_mul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_mul_left

/-- info: 'Protocol.avg_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_zero

/-- info: 'Protocol.avg_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_const

/-- info: 'Protocol.avg_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_sum

/-- info: 'Protocol.avg_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_comm

/-- info: 'Protocol.avg_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_prod

/-- info: 'Protocol.avg_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_equiv

/-- info: 'Protocol.dens_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_nonneg

/-- info: 'Protocol.dens_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_le_one

/-- info: 'Protocol.dens_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_mono

/-- info: 'Protocol.dens_or_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_or_le

/-- info: 'Protocol.dens_le_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_le_avg

/-- info: 'Protocol.pot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pot_zero

/-- info: 'Protocol.pot_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pot_succ

/-- info: 'Protocol.pot_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pot_nonneg

/-- info: 'Protocol.avg_pot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_pot_step

/-- info: 'Protocol.pot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pot_step

/-- info: 'Protocol.meanCost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms meanCost_zero

/-- info: 'Protocol.meanCost_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms meanCost_succ

/-- info: 'Protocol.pot_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pot_eq_sum

/-- info: 'Protocol.potT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potT_zero

/-- info: 'Protocol.potT_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potT_succ

/-- info: 'Protocol.potT_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potT_one

/-- info: 'Protocol.potT_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potT_nonneg

/-- info: 'Protocol.probBad_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms probBad_zero

/-- info: 'Protocol.probBad_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms probBad_succ

/-- info: 'Protocol.potT_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potT_eq_sum

/-- info: 'Protocol.potT_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potT_step

/-- info: 'Protocol.avg_potT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_potT_le

/-- info: 'Protocol.potT_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potT_init

/-- info: 'Protocol.potT_init_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms potT_init_const

/-- info: 'Protocol.evL_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evL_sub

/-- info: 'Protocol.card_evL_eq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_evL_eq_le

/-- info: 'Protocol.card_evL_eq_all_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_evL_eq_all_le

/-- info: 'Protocol.card_nonSep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_nonSep_le

/-- info: 'Protocol.dens_nonSep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_nonSep_le

/-- info: 'Protocol.pinned_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pinned_unique

/-- info: 'Protocol.card_pinned_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_pinned_le_one

/-- info: 'Protocol.lemmaP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaP

/-- info: 'Protocol.card_galoisField_two_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_galoisField_two_128

/-- info: 'Protocol.card_listW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_listW_le

/-- info: 'Protocol.listBound_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms listBound_level

/-- info: 'Protocol.probBad_eq_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms probBad_eq_card

/-- info: 'Protocol.levelPot_eq_sum_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelPot_eq_sum_card

end Protocol
