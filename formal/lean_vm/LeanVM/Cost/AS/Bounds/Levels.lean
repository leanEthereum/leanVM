module

public import LeanVM.Cost.AS.Bounds.Newton
import all LeanVM.Protocol.Whir.Sound.DescentC
import all LeanVM.Protocol.Whir.Params.Check
import all LeanVM.Protocol.Whir.Params.Deployed

/-!
# Bounds: the levels' shapes

`foldTable_cost`: the table of the deployed levels, built from its sixty constants;
`levelsOf_cost`; **`lvC_cost`**: a level's shape.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Whir.Params LeanVM.Protocol.Whir

public section

variable (P : MachineProgram)

theorem foldTable_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable.c790.costDeps) :
    machineCost P Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable.c790.costIdx [] ≤ 30000 := by
  rw [Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable.c790.costEq P hP]
  simp only [Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_16.c791.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_17.c792.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_18.c793.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_19.c794.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_20.c795.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_21.c796.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_22.c797.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_23.c798.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_24.c799.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_25.c800.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_26.c801.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_27.c802.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_28.c803.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_29.c804.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_1_30.c805.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_16.c806.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_17.c807.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_18.c808.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_19.c809.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_20.c810.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_21.c811.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_22.c812.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_23.c813.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_24.c814.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_25.c815.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_26.c816.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_27.c817.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_28.c818.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_29.c819.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_2_30.c820.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_16.c821.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_17.c822.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_18.c823.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_19.c824.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_20.c825.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_21.c826.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_22.c827.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_23.c828.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_24.c829.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_25.c830.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_26.c831.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_27.c832.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_28.c833.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_29.c834.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_3_30.c835.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_16.c836.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_17.c837.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_18.c838.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_19.c839.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_20.c840.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_21.c841.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_22.c842.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_23.c843.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_24.c844.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_25.c845.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_26.c846.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_27.c847.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_28.c848.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_29.c849.costEq P (by includes),
      Auto.LeanVM.Protocol.Whir.AffineCombiner.foldTable_4_30.c850.costEq P (by includes)]
  omega

theorem foldTable_small : ∀ a ∈ AffineCombiner.foldTable, ∀ b ∈ a, ∀ lv ∈ b,
    lv.1 < 2 ^ 62 ∧ lv.2.1 < 2 ^ 62 := by
  decide +kernel

theorem levelsOf_small (μ R i : ℕ) :
    ((levelsOf μ R).getD i junkLv).1 < 2 ^ 62 ∧ ((levelsOf μ R).getD i junkLv).2.1 < 2 ^ 62 := by
  have key : ∀ lv ∈ levelsOf μ R, lv.1 < 2 ^ 62 ∧ lv.2.1 < 2 ^ 62 := by
    intro lv hlv
    unfold levelsOf at hlv
    rcases getD_mem_or AffineCombiner.foldTable (R - 1) [] with hA | hA
    · rcases getD_mem_or (AffineCombiner.foldTable.getD (R - 1) []) (μ - 16) [] with hB | hB
      · exact foldTable_small _ hA _ hB lv hlv
      · rw [hB] at hlv; simp at hlv
    · rw [hA] at hlv; simp at hlv
  rcases getD_mem_or (levelsOf μ R) i junkLv with h | h
  · exact key _ h
  · rw [h]; decide

theorem levelsOf_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.Params.levelsOf.c789.costDeps)
    (μ R : ℕ) (hμ : μ < 2 ^ 62) (hR : R < 2 ^ 62) :
    machineCost P Auto.LeanVM.Protocol.Whir.Params.levelsOf.c789.costIdx [encodeValue μ,
      encodeValue R] ≤ 30000 + 30 * μ + 15 * R + 100 := by
  rw [Auto.LeanVM.Protocol.Whir.Params.levelsOf.c789.costEq P hP, limbs_of_lt (by omega : R < 2 ^ 64),
    limbs_of_lt (by omega : μ < 2 ^ 64)]
  have h1 := foldTable_cost P (by includes)
  have h2 := getD_cost_idx P (by includes) AffineCombiner.foldTable (R - 1) [] (by omega)
  have h3 := getD_cost_idx P (by includes) (AffineCombiner.foldTable.getD (R - 1) []) (μ - 16) []
    (by omega)
  omega

/-- **A level's shape, priced.** -/
theorem lvC_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.Sound.lvC.c788.costDeps) (μ R i : ℕ)
    (hμ : μ < 2 ^ 62) (hR : R < 2 ^ 62) (hi : i < 2 ^ 62) :
    machineCost P Auto.LeanVM.Protocol.Whir.Sound.lvC.c788.costIdx [encodeValue μ, encodeValue R,
      encodeValue i] ≤ 30000 + 30 * μ + 15 * R + 15 * i + 300 := by
  rw [Auto.LeanVM.Protocol.Whir.Sound.lvC.c788.costEq P hP]
  obtain ⟨h1, h2⟩ := levelsOf_small μ R i
  rw [limbs_of_lt (by omega : ((levelsOf μ R).getD i junkLv).1 + ((levelsOf μ R).getD i junkLv).2.1 < 2 ^ 64),
    limbs_of_lt (by omega : ((levelsOf μ R).getD i junkLv).1 < 2 ^ 64),
    limbs_of_lt (by omega : ((levelsOf μ R).getD i junkLv).2.1 < 2 ^ 64)]
  have c1 := levelsOf_cost P (by includes) μ R hμ hR
  have c2 := getD_cost_idx P (by includes) (levelsOf μ R) i junkLv (by omega)
  rw [Auto.LeanVM.Protocol.Whir.Params.junkLv.c851.costEq P (by includes)]
  split_ifs <;> simp only [max_self] <;> omega

end

end LeanVM.Cost.Bounds.AS
