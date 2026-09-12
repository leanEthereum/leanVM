import SphincsSecurity.Proof.Fts.CertificateProposalPrefixException
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

noncomputable def proposalTailBase : ENNReal := 257 / 256
noncomputable def proposalTailMoment : ENNReal := 67634176 / 66845695

theorem proposalBlockLength_power_moment (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (base : ENNReal) :
    (∑' length, proposalBlockLength accept hpos hle length * base ^ length) =
      accept * base / (1 - (1 - accept) * base) := by
  rw [tsum_eq_zero_add' ENNReal.summable, proposalBlockLength_zero, zero_mul, zero_add]
  simp only [proposalBlockLength_succ, pow_succ]
  calc
    _ = ∑' failures, (accept * base) * ((1 - accept) * base) ^ failures := by
      apply tsum_congr
      intro failures
      rw [mul_pow]
      ac_rfl
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]; rfl

theorem proposalTailMoment_eq : proposalTailMoment =
    targetProposalAcceptance * proposalTailBase ^ 2 / (1 - (1 - targetProposalAcceptance) * proposalTailBase ^ 2) := by
  have hrem : (1 - targetProposalAcceptance).toReal = 1 - targetProposalAcceptance.toReal := by
    rw [ENNReal.toReal_sub_of_le targetProposalAcceptance_lt_one.le (by finiteness), ENNReal.toReal_one]
  have hlt : (1 - targetProposalAcceptance) * proposalTailBase ^ 2 < 1 := by
    apply (ENNReal.toReal_lt_toReal (by unfold proposalTailBase; finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul, hrem]
    norm_num [ENNReal.toReal_pow, targetProposalAcceptance, targetProposalOverhead,
      proposalTailBase, ENNReal.toReal_inv, ENNReal.toReal_div]
  have hnz : 1 - (1 - targetProposalAcceptance) * proposalTailBase ^ 2 ≠ 0 := (tsub_pos_iff_lt.mpr hlt).ne'
  have haccept : targetProposalAcceptance ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) targetProposalAcceptance_lt_one.le
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold proposalTailMoment; finiteness)
    (ENNReal.div_ne_top (ENNReal.mul_ne_top haccept (by unfold proposalTailBase; finiteness)) hnz)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le hlt.le (by finiteness)]
  simp only [ENNReal.toReal_mul, hrem]
  norm_num [proposalTailMoment, ENNReal.toReal_pow, targetProposalAcceptance,
    targetProposalOverhead, proposalTailBase, ENNReal.toReal_inv, ENNReal.toReal_div]

theorem proposalTailMoment_ge_cube : proposalTailBase ^ 3 ≤ proposalTailMoment := by
  apply (ENNReal.toReal_le_toReal (by unfold proposalTailBase; finiteness) (by unfold proposalTailMoment; finiteness)).mp
  norm_num [proposalTailBase, proposalTailMoment, ENNReal.toReal_pow, ENNReal.toReal_div]

theorem proposalTailBase_one_le : 1 ≤ proposalTailBase := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold proposalTailBase; finiteness)).mp
  norm_num [proposalTailBase, ENNReal.toReal_div]

noncomputable def proposalPrefixWeight (proposals completed : Nat) : ENNReal :=
  proposalTailBase ^ (2 * proposals) * proposalTailMoment ^ (signatureLimit - completed) /
    proposalTailBase ^ (3 * signatureLimit + 262144)

theorem proposalPrefixWeight_bad (proposals completed : Nat) (hcap : completed ≤ signatureLimit)
    (hbad : ProposalPrefixExceptional proposals completed) : 1 ≤ proposalPrefixWeight proposals completed := by
  have hcount : 3 * completed + 262144 ≤ 2 * proposals := by
    have h := (ENNReal.toReal_lt_toReal (by unfold targetProposalOverhead; finiteness) (by finiteness)).mpr hbad
    rw [ENNReal.toReal_add (by unfold targetProposalOverhead; finiteness) (by finiteness), ENNReal.toReal_mul] at h
    norm_num [targetProposalOverhead, ENNReal.toReal_div] at h
    have hc : (0 : ℝ) ≤ completed := Nat.cast_nonneg _
    have h' : (3 : ℝ) * completed + 262144 ≤ 2 * proposals := by linarith
    exact_mod_cast h'
  have hexp : 3 * signatureLimit + 262144 ≤ 2 * proposals + 3 * (signatureLimit - completed) := by omega
  have hbase : proposalTailBase ≠ 0 := by norm_num [proposalTailBase]
  have hfinite : proposalTailBase ≠ ⊤ := by unfold proposalTailBase; finiteness
  rw [proposalPrefixWeight]
  calc
    1 = proposalTailBase ^ (3 * signatureLimit + 262144) /
        proposalTailBase ^ (3 * signatureLimit + 262144) := (ENNReal.div_self (pow_ne_zero _ hbase) (by finiteness)).symm
    _ ≤ _ := ENNReal.div_le_div_right (calc
      _ ≤ proposalTailBase ^ (2 * proposals + 3 * (signatureLimit - completed)) :=
        pow_le_pow_right₀ proposalTailBase_one_le hexp
      _ = proposalTailBase ^ (2 * proposals) * (proposalTailBase ^ 3) ^ (signatureLimit - completed) := by simp only [pow_add, pow_mul]
      _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left₀ (by positivity) proposalTailMoment_ge_cube _)) _

theorem expected_proposalPrefixWeight (proposals completed : Nat) (hcap : completed < signatureLimit) :
    (∑' length, proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le length *
      proposalPrefixWeight (proposals + length) (completed + 1)) = proposalPrefixWeight proposals completed := by
  have hremaining : signatureLimit - completed = (signatureLimit - (completed + 1)) + 1 := by omega
  simp only [proposalPrefixWeight, Nat.mul_add]
  calc
    _ = (proposalTailBase ^ (2 * proposals) * proposalTailMoment ^ (signatureLimit - (completed + 1)) /
        proposalTailBase ^ (3 * signatureLimit + 262144)) *
        ∑' length, proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le length *
          (proposalTailBase ^ 2) ^ length := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro length
      simp only [pow_add, pow_mul, div_eq_mul_inv]
      ac_rfl
    _ = _ := by
      rw [proposalBlockLength_power_moment, ← proposalTailMoment_eq, hremaining]
      simp only [pow_add, pow_one, div_eq_mul_inv]
      ac_rfl

theorem proposalPrefixWeight_initial_le : proposalPrefixWeight 0 0 ≤ (2 ^ 700 : ENNReal)⁻¹ := by
  let z : ℝ := 257 / 256
  let ratio : ℝ := 17179869184 / 17179343615
  have hz : 0 < z := by norm_num [z]
  have hr : 0 < ratio := by norm_num [ratio]
  have hlog : (signatureLimit : ℝ) * Real.log ratio - 262144 * Real.log z ≤ -700 * Real.log 2 := by
    have hratio := Real.log_le_sub_one_of_pos hr
    have hbase := Real.one_sub_inv_le_log_of_pos hz
    have htwo := Real.log_two_lt_d9
    norm_num [ratio, z, signatureLimit] at hratio hbase ⊢
    linarith
  have hreal : (ratio * z ^ 3) ^ signatureLimit / z ^ (3 * signatureLimit + 262144) ≤ (2 ^ 700 : ℝ)⁻¹ := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul hr.ne' (by positivity),
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_pow]
    push_cast
    nlinarith only [hlog]
  have hmoment : proposalTailMoment.toReal = ratio * z ^ 3 := by
    norm_num [proposalTailMoment, ENNReal.toReal_div, ratio, z]
  have hbase : proposalTailBase.toReal = z := by norm_num [proposalTailBase, ENNReal.toReal_div, z]
  have hfinite : proposalPrefixWeight 0 0 ≠ ⊤ := by
    unfold proposalPrefixWeight
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by unfold proposalTailBase; finiteness))
        (ENNReal.pow_ne_top (by unfold proposalTailMoment; finiteness))
    · exact pow_ne_zero _ (by norm_num [proposalTailBase])
  apply (ENNReal.toReal_le_toReal hfinite (by finiteness)).mp
  simpa only [proposalPrefixWeight, Nat.mul_zero, pow_zero, one_mul, Nat.sub_zero, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, hmoment, hbase] using hreal

end SphincsSecurity.Concrete
