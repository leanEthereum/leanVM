/-
The axioms of every theorem of the library `Soundness`: Lean's three (`propext`,
`Classical.choice`, `Quot.sound`) or a subset of them, and nothing else. Each check is under
`#guard_msgs`, so the build fails if a statement gains an axiom (a `sorry` would show as
`sorryAx`). This file is generated from the sources (the theorem names) and from the output of
`#print axioms`.

The typeclass hypotheses of the end statements are satisfiable at the deployed field size:
`Soundness.protocolD_sound_concrete_unique` and `Soundness.protocolD_sound_concrete_ladder` (in
`Hypothesis.lean`) instantiate the soundness theorem over a field of `2^128` elements with every
hypothesis discharged, and the examples below instantiate the round-by-round statement, the
soundness theorem and the full-state transitions at `GaloisField 2 128`. In each example every
typeclass argument is discharged, the characteristic included (`CharP (GaloisField 2 128) 2` is
Mathlib's instance), and so is every hypothesis on the analysis constants where they are fixed
(`K₀ = 2^9 q`, `M = 2 q`, `τ = 2^-119`). What an example leaves as an argument is what the
statement is about: the ladder with its list hypothesis, or the state before a transition.
-/
import Soundness.Extract
import Soundness.Hypothesis
import Protocol.Axioms

namespace Soundness

/-- The round-by-round statement at `GF(2^128)` with no tail: no hypothesis is left. -/
noncomputable example (J : ℕ) :=
  @protocolD_rbr (GaloisField 2 128) _ (Terminal.direct _) (Fintype.ofFinite _) (1 / 2 ^ 119)
    (2 ^ 137) (2 ^ 129) inferInstance (by norm_num)
    (by rw [Protocol.card_galoisField_two_128]; norm_num) Protocol.threshold_level0_pos J

/-- The soundness theorem at `GF(2^128)`: what is left is the ladder, its tail and the hypothesis
`Level.OK` on its levels. -/
noncomputable example (T : Terminal (GaloisField 2 128)) :=
  @protocolD_sound (GaloisField 2 128) _ (Fintype.ofFinite _) T (1 / 2 ^ 119) (2 ^ 137)
    (2 ^ 129) inferInstance (by norm_num)
    (by rw [Protocol.card_galoisField_two_128]; norm_num) Protocol.threshold_level0_pos

/-- The transitions of the full state at `GF(2^128)`. -/
noncomputable example :=
  @fold_full (GaloisField 2 128) _ (Fintype.ofFinite _) inferInstance

noncomputable example :=
  @query_full (GaloisField 2 128) _ (Fintype.ofFinite _) inferInstance

noncomputable example := @points_full (GaloisField 2 128) _ (Fintype.ofFinite _)

/-! ### `Soundness/RBR.lean` -/

/-- info: 'Soundness.PublicCoin.winProb_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PublicCoin.winProb_zero

/-- info: 'Soundness.PublicCoin.winProb_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PublicCoin.winProb_succ

/-- info: 'Soundness.PublicCoin.winProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PublicCoin.winProb_nonneg

/-- info: 'Soundness.PublicCoin.winProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PublicCoin.winProb_le_one

/-- info: 'Soundness.PublicCoin.winProb_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PublicCoin.winProb_mono

/-- info: 'Soundness.PublicCoin.strategy_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PublicCoin.strategy_nonempty

/-- info: 'Soundness.avg_le_dens_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avg_le_dens_add

/-- info: 'Soundness.StateFunction.of_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StateFunction.of_positions

/-- info: 'Soundness.StateFunction.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StateFunction.mono

/-- info: 'Soundness.StateFunction.winProb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StateFunction.winProb_le

/-- info: 'Soundness.RBRSound.winProb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RBRSound.winProb_le

/-- info: 'Soundness.RBRSound.winProb_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RBRSound.winProb_le_mul

/-! ### `Soundness/State.lean` -/

/-- info: 'Soundness.dens_eq_card_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_eq_card_div

/-- info: 'Soundness.dens_of_forall_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_of_forall_not

/-- info: 'Soundness.card_queries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_queries_le

/-- info: 'Soundness.card_queries_prod_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_queries_prod_le

/-- info: 'Soundness.points_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms points_full

/-- info: 'Soundness.Good.not_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Good.not_bad

/-- info: 'Soundness.batch_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms batch_full

/-- info: 'Soundness.fold_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fold_full

/-- info: 'Soundness.query_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms query_full

/-- info: 'Soundness.FullState.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FullState.mono

/-- info: 'Soundness.final_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms final_full

/-! ### `Soundness/ProtocolD.lean` -/

/-- info: 'Soundness.pull_not_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pull_not_iff

/-- info: 'Soundness.winPlain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms winPlain_le

/-- info: 'Soundness.winExtract_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms winExtract_le

/-- info: 'Soundness.dens_not_and_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dens_not_and_le

/-- info: 'Soundness.step_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_commit

/-- info: 'Soundness.step_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_opening

/-- info: 'Soundness.step_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_fold

/-- info: 'Soundness.step_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_final

/-- info: 'Soundness.step_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_tail

/-- info: 'Soundness.step_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_terminal

/-- info: 'Soundness.step_handover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_handover

/-- info: 'Soundness.step_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_boundary

/-- info: 'Soundness.doomed_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms doomed_step

/-- info: 'Soundness.doomed_not_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms doomed_not_win

/-- info: 'Soundness.start_doomed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms start_doomed

/-- info: 'Soundness.protocolD_stateFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_stateFunction

/-- info: 'Soundness.protocolD_rbr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_rbr

/-! ### `Soundness/Sound.lean` -/

/-- info: 'Soundness.errPoints_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errPoints_nonneg

/-- info: 'Soundness.errFold_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errFold_nonneg

/-- info: 'Soundness.errQuery_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errQuery_nonneg

/-- info: 'Soundness.budgetFolds_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budgetFolds_nonneg

/-- info: 'Soundness.budgetEnd_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budgetEnd_nonneg

/-- info: 'Soundness.budget_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budget_nonneg

/-- info: 'Soundness.budget_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budget_step

/-- info: 'Soundness.budgetFolds_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budgetFolds_succ

/-- info: 'Soundness.budget_one_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budget_one_level

/-- info: 'Soundness.budgetFolds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budgetFolds_eq

/-- info: 'Soundness.one_le_of_tripleThr_pos' depends on axioms: [propext] -/
#guard_msgs in
#print axioms one_le_of_tripleThr_pos

/-- info: 'Soundness.protocolD_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound

/-- info: 'Soundness.protocolD_sound_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound_plain

/-- info: 'Soundness.protocolD_sound_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound_extract

/-- info: 'Soundness.protocolD_sound_one_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound_one_level

/-- info: 'Soundness.chal_nonempty_of_doomed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chal_nonempty_of_doomed

/-- info: 'Soundness.strategy_nonempty_one_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strategy_nonempty_one_level

/-- info: 'Soundness.Terminal.direct_admitsZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Terminal.direct_admitsZero

/-- info: 'Soundness.Terminal.point_admitsZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Terminal.point_admitsZero

/-- info: 'Soundness.finalMsg_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finalMsg_isEmpty

/-- info: 'Soundness.handover_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms handover_isEmpty

/-- info: 'Soundness.strategy_nonempty_of_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strategy_nonempty_of_fits

/-- info: 'Soundness.strategy_nonempty_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strategy_nonempty_ladder

/-- info: 'Soundness.roundsEnd_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms roundsEnd_pos

/-- info: 'Soundness.rounds_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rounds_next

/-- info: 'Soundness.done_of_rounds_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms done_of_rounds_eq_zero

/-! ### `Soundness/Extract.lean` -/

/-- info: 'Soundness.descend_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descend_step

/-- info: 'Soundness.descend_iff_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descend_iff_unique

/-- info: 'Soundness.claimsHold_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms claimsHold_unique

/-! ### `Soundness/Hypothesis.lean` -/

/-- info: 'Soundness.card_listW_le_of_rsListBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_listW_le_of_rsListBound

/-- info: 'Soundness.thr_zero_le' does not depend on any axioms -/
#guard_msgs in
#print axioms thr_zero_le

/-- info: 'Soundness.Level.OK.of_rsListBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Level.OK.of_rsListBound

/-- info: 'Soundness.Level.HK.ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Level.HK.ok

/-- info: 'Soundness.Level.Unique.ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Level.Unique.ok

/-- info: 'Soundness.protocolD_sound_of_HK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound_of_HK

/-- info: 'Soundness.protocolD_sound_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound_unique

/-- info: 'Soundness.errPoints_level0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errPoints_level0

/-- info: 'Soundness.errFold_level0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errFold_level0

/-- info: 'Soundness.errFold_level0_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errFold_level0_last

/-- info: 'Soundness.err_level0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms err_level0

/-- info: 'Soundness.card_K64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_K64

/-- info: 'Soundness.card_E128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_E128

/-- info: 'Soundness.levelConcrete_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelConcrete_unique

/-- info: 'Soundness.protocolD_sound_concrete_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound_concrete_unique

/-- info: 'Soundness.errPoints_levelConcrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errPoints_levelConcrete

/-- info: 'Soundness.card_levelConcrete_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_levelConcrete_D

/-- info: 'Soundness.errQuery_levelConcrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms errQuery_levelConcrete

/-- info: 'Soundness.budget_levelConcrete_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budget_levelConcrete_le

/-- info: 'Soundness.protocolD_sound_concrete_unique_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound_concrete_unique_le

/-- info: 'Soundness.levelConcrete₁_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms levelConcrete₁_unique

/-- info: 'Soundness.protocolD_sound_concrete_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocolD_sound_concrete_ladder

/-- info: 'Soundness.ladderFits_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ladderFits_concrete

/-- info: 'Soundness.strategy_nonempty_concrete_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms strategy_nonempty_concrete_ladder

end Soundness
