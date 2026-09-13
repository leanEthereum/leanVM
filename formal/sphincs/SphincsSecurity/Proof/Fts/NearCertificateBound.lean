import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FixedProposalMoments
import SphincsSecurity.Proof.Fts.TerminalProposalEnvelope

namespace SphincsSecurity.Concrete

open ENNReal

set_option maxHeartbeats 2000000 in
theorem stirlingPowerMoment_thirteen :
    stirlingPowerMoment (19 / 50) 13 =
      (1986585224814431503899382459 : ENNReal) / 12207031250000000000000 := by
  unfold stirlingPowerMoment
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.sum_ne_top.mpr (fun _ _ => by finiteness)) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_sum, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

/-- The average price, over a uniform proposal word of the fixed length, of a certificate that covers thirteen of the fourteen trees. -/
theorem uniformWordAverage_nearPrice (required : Finset FtsTree) (hdegree : required.card = 13) :
    uniformWordAverage fixedProposalLength (terminalCertificatePrice required) ≤
      ((557 : ENNReal) / 14) / (2 ^ 128 : Nat) := by
  have hprice : terminalCertificatePrice required = fun word =>
      ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) * targetCertificateScale required) *
        proposalPowerSum required.card word := by
    funext word
    unfold terminalCertificatePrice proposalPowerSum
    ring
  rw [hprice, uniformWordAverage_mul_left]
  refine (mul_le_mul' le_rfl (uniformWordAverage_powerSum_le (α := Index) fixedProposalLength required.card (19 / 50)
    fixedProposalLength_rate_le)).trans ?_
  rw [hdegree, stirlingPowerMoment_thirteen]
  unfold targetCertificateScale
  rw [hdegree]
  have hindex : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  have hleaf : Fintype.card FtsLeaf = 2 ^ 10 := Fintype.card_fin _
  rw [hindex, hleaf]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ftsTreeHeight, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_pow]

end SphincsSecurity.Concrete
