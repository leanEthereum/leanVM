import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.StirlingMomentBounds
import SphincsSecurity.Proof.Fts.UniformProposalVariance
namespace SphincsSecurity.Concrete

open ENNReal

def fixedProposalLength : Nat := 25313293

noncomputable def fixedFullProposalPrice (word : List Index) : ENNReal :=
  (2 ^ 48 : ENNReal)⁻¹ * proposalPowerSum 14 word

theorem fixedProposalLength_rate_le :
    (fixedProposalLength : ENNReal) * (Fintype.card Index : ENNReal)⁻¹ ≤ 19 / 50 := by
  have hcard : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  rw [hcard]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [fixedProposalLength, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]

theorem fixedFullProposalPrice_ne_top (word : List Index) : fixedFullProposalPrice word ≠ ⊤ := by
  apply ENNReal.mul_ne_top (by finiteness)
  apply ENNReal.sum_ne_top.mpr
  intro index _
  finiteness

theorem uniformWordAverage_fixedFull_mean_le :
    uniformWordAverage fixedProposalLength fixedFullProposalPrice ≤ 1 / 5 := by
  unfold fixedFullProposalPrice
  rw [uniformWordAverage_mul_left]
  have h := mul_le_mul' (a := (2 ^ 48 : ENNReal)⁻¹) le_rfl
    (uniformWordAverage_powerSum_le (α := Index) fixedProposalLength 14 (19 / 50) fixedProposalLength_rate_le)
  have hcard : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  rw [hcard] at h
  apply h.trans
  calc
    _ = (2 ^ 26 : ENNReal) * (2 ^ 48 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 14 := by
      push_cast
      ring
    _ ≤ _ := stirlingPowerMoment_full_mean_le

theorem uniformWordAverage_fixedFull_secondMoment_le :
    uniformWordAverage fixedProposalLength (fun word => fixedFullProposalPrice word ^ 2) ≤
      uniformWordAverage fixedProposalLength fixedFullProposalPrice ^ 2 + 13 / 25000 := by
  unfold fixedFullProposalPrice
  simp only [mul_pow, uniformWordAverage_mul_left]
  have h := mul_le_mul' (a := ((2 ^ 48 : ENNReal)⁻¹) ^ 2) le_rfl
    (uniformWordAverage_powerSum_square_le (α := Index) fixedProposalLength 14 (19 / 50) fixedProposalLength_rate_le)
  have hcard : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  rw [hcard, mul_add] at h
  apply h.trans
  apply add_le_add le_rfl
  have hscale : ((2 ^ 48 : ENNReal)⁻¹) ^ 2 = (2 ^ 96 : ENNReal)⁻¹ := by
    rw [← ENNReal.inv_pow, ← pow_mul]
  rw [hscale]
  calc
    _ = (2 ^ 26 : ENNReal) * (2 ^ 96 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 50) 28 := by
      push_cast
      ring
    _ ≤ _ := stirlingPowerMoment_full_variance_le

end SphincsSecurity.Concrete
