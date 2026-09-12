import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.UniformProposalMixedMoments
namespace SphincsSecurity.Concrete

open ENNReal

theorem stirlingPowerMoment_ne_top (rate : ENNReal) (hrate : rate ≠ ⊤) (degree : Nat) :
    stirlingPowerMoment rate degree ≠ ⊤ := by
  unfold stirlingPowerMoment
  apply ENNReal.sum_ne_top.mpr
  intro order _
  exact ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top hrate)

set_option maxHeartbeats 5000000 in
theorem stirlingPowerMoment_full_mean_le :
    (2 ^ 26 : ENNReal) * (2 ^ 48 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 14 ≤ 1 / 5 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 14
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

set_option maxHeartbeats 5000000 in
theorem stirlingPowerMoment_full_variance_le :
    (2 ^ 26 : ENNReal) * (2 ^ 96 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 28 ≤ 13 / 25000 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 28
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

end SphincsSecurity.Concrete
