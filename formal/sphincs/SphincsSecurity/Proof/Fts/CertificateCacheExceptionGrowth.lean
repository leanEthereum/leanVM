import SphincsSecurity.Proof.Fts.CertificateCacheExceptionPotential
import SphincsSecurity.Proof.Fts.MessageDeficitHashMoments
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] messageDeficitMoment cachedIndexExcessMoment positiveScoreMoment
set_option backward.isDefEq.respectTransparency false

noncomputable def certificateCacheExceptionWeight (key : SecretKey) (cache : QueryCache HashSpec) : ENNReal :=
  messageDeficitMoment key.parameter key.root cache 2 / 2 ^ 186 + cachedIndexExcessMoment key.parameter cache / 2 ^ 160

noncomputable def certificateCacheExceptionRate : ENNReal := 1023 / 2 ^ 186 + (2 ^ 10 : ENNReal)⁻¹ / 2 ^ 160

theorem certificateCacheExceptionRate_le : certificateCacheExceptionRate ≤ (2 ^ 169 : ENNReal)⁻¹ := by
  apply (ENNReal.toReal_le_toReal (by unfold certificateCacheExceptionRate; finiteness) (by finiteness)).mp
  rw [certificateCacheExceptionRate, ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow]

theorem messageDeficitExceptional_secondMoment_le (key : SecretKey) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hbad : MessageDeficitExceptional key cache) :
    (2 : ENNReal) ^ 186 ≤ messageDeficitMoment key.parameter key.root cache 2 := by
  obtain ⟨message, hmessage⟩ := hbad
  have hscaled : (2 : ENNReal) ^ 93 ≤ 1024 * messageAdmissibleDeficit key message cache := by
    calc
      _ = 1024 * ((2 ^ 83 : Nat) : ENNReal) := by norm_num
      _ ≤ _ := mul_le_mul' le_rfl hmessage.le
  calc
    _ = ((2 : ENNReal) ^ 93) ^ 2 := by rw [← pow_mul]
    _ ≤ (1024 * messageAdmissibleDeficit key message cache) ^ 2 := pow_le_pow_left' hscaled 2
    _ = positiveScoreMoment (messageDeficitScore key.parameter key.root message cache) 2 := by
      rw [positiveScoreMoment_eq_pow_ofReal, messageDeficitScore_ofReal_eq key message cache hfinite]
    _ ≤ _ := positiveScoreMoment_le_messageDeficitMoment key.parameter key.root cache 2 message

theorem certificateCacheExceptionWeight_bad (key : SecretKey) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (hbad : CertificateCacheExceptional key cache) : 1 ≤ certificateCacheExceptionWeight key cache := by
  rcases hbad with hdeficit | hindex
  · apply le_trans (b := messageDeficitMoment key.parameter key.root cache 2 / 2 ^ 186) _ le_self_add
    calc
      1 = (2 ^ 186 : ENNReal) / 2 ^ 186 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (messageDeficitExceptional_secondMoment_le key cache hfinite hdeficit) _
  · apply le_trans (b := cachedIndexExcessMoment key.parameter cache / 2 ^ 160) _ le_add_self
    calc
      1 = (2 ^ 160 : ENNReal) / 2 ^ 160 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (cachedIndexExcessExceptional_moment_ge key.parameter cache hindex) _

theorem certificateCacheExceptionWeight_initial (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    certificateCacheExceptionWeight key cache = 0 := by
  have hcount := cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache
    (fun payload => hnone _ ⟨payload, rfl⟩)
  rw [certificateCacheExceptionWeight, messageDeficitMoment_zero_of_no_inputs key.parameter key.root cache hcount 2 (by decide),
    cachedIndexExcessMoment_zero_of_no_message key.parameter cache hnone, ENNReal.zero_div, ENNReal.zero_div, add_zero]

theorem expected_certificateCacheExceptionWeight_le (key : SecretKey)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      certificateCacheExceptionWeight key (cache.cacheQuery input output)) ≤
      certificateCacheExceptionWeight key cache + certificateCacheExceptionRate := by
  simp only [certificateCacheExceptionWeight, certificateCacheExceptionRate, div_eq_mul_inv, mul_add,
    ← mul_assoc, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  exact (add_le_add
    (mul_le_mul' (expected_messageDeficitMoment_second_le key.parameter key.root cache hfinite input hfresh) le_rfl)
    (mul_le_mul' (expected_cachedIndexExcessMoment_le key.parameter cache hfinite input hfresh) le_rfl)).trans_eq (by ring)

end SphincsSecurity.Concrete
