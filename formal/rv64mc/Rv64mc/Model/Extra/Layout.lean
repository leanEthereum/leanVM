/-
  Rv64mc.Model.Extra.Layout

  `Model.Layout`'s values in the forms the compiled code computes them: `qkeccak_slot` as the three ranges of
  global columns the code compares against (`qkeccakSlotRust_closed`), `is_output_lane` as one range, and `gpow`'s
  limbs (`limbs_gpowRust`).
-/

import Rv64mc.Model.Layout

namespace Rv64mc.Model

section Helpers

private theorem find?_spare (l : ℕ) :
    ∀ n ≤ 15, (List.range n).find? (fun k ↦ decide (spareLocalRust k = l)) = if l < n then some l else none
  | 0, _ => by simp
  | n + 1, hn => by
    rw [List.range_succ, List.find?_append, find?_spare l n (by omega)]
    have hs : spareLocalRust n = n := by
      rw [spareLocalRust, ite_eq_left (show n < keccakInRust by simp only [keccakInRust, KeccakCol.len]; omega)]
    by_cases h : l < n
    · simp [h, show l < n + 1 by omega]
    · by_cases h' : l = n
      · subst h'; simp [hs]
      · simp [h, hs, show ¬ l < n + 1 by omega, Ne.symm h']

end Helpers

/-- **`qkeccak_slot` by ranges**: below `KECCAK`'s base (66) none; its first fourteen columns ride the spare slots
    `50..64`; its input lanes (global `81..106`) are slots `0..25`; nothing else. -/
theorem qkeccakSlotRust_closed (c : ℕ) :
    qkeccakSlotRust c =
      if c < 66 then none else if c < 80 then some (c - 16) else if 81 ≤ c ∧ c < 106 then some (c - 81) else none := by
  have hb : globalColumnBasesRust.getD opKeccakRust 0 = 66 := by decide +kernel
  have hs : qkeccakSpareRust = 14 := by rw [qkeccakSpareRust, log2CeilRust_eq]; decide +kernel
  unfold qkeccakSlotRust
  dsimp only
  rw [hb, hs, find?_spare _ 14 (by omega)]
  simp only [keccakInRust, KeccakCol.len, keccakOutRust, stateLanesRust, qkeccakSlotsRust, keccakDepthRust]
  by_cases h : c < 66
  · simp [h]
  · by_cases h1 : c < 80
    · simp [h, h1, show c - 66 < 14 by omega]; omega
    · simp only [h, h1, ↓reduceIte, show ¬ c - 66 < 14 by omega]
      by_cases h2 : 81 ≤ c ∧ c < 106
      · simp [h2, show 15 ≤ c - 66 ∧ c - 66 < 40 by omega]; omega
      · simp [h2, show ¬ (15 ≤ c - 66 ∧ c - 66 < 40) by omega]

/-- **`is_output_lane` by range**: `KECCAK`'s output lanes are the global columns `106..131`. -/
theorem isOutputLaneRust_closed (c : ℕ) : isOutputLaneRust c = decide (106 ≤ c ∧ c < 131) := by
  unfold isOutputLaneRust
  rw [show globalColumnBasesRust.getD opKeccakRust 0 = 66 by decide +kernel]
  rfl

/-- `gpow`'s limbs are `E::pow`'s on `GEN`'s. -/
theorem limbs_gpowRust (index : BitVec 64) : limbs (gpowRust index) = ePow eGen index := by
  rw [gpowRust, limbs_gen, ofLimbsW, limbs_ofLimbs, BF64.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]

end Rv64mc.Model
