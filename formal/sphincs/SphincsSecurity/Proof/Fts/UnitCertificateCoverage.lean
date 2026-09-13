import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateJointExceptions
import SphincsSecurity.Proof.Fts.FixedCertificateCoverage

/-! ## PositivePartMomentBound -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

theorem uniformWordAverage_const {α : Type} [SampleableType α] [Fintype α] [Nonempty α] [DecidableEq α]
    (steps : Nat) (value : ENNReal) :
    uniformWordAverage steps (fun _word : List α => value) = value := by
  let index : α := Classical.choice inferInstance
  rw [uniformWordAverage, expected_uniformProposalWord_count index steps (fun _ => value)]
  exact binomialAverage_const (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos)) steps value

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false

private theorem unit_excess_le_square_with_mean (value mean : ENNReal) (hvalue : value ≠ ⊤)
    (hmean : mean ≤ 1 / 5) :
    (16 / 5 : ENNReal) * (value - 1) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 := by
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have hmr : mean.toReal ≤ 1 / 5 := by
    have h := (ENNReal.toReal_le_toReal hm (by finiteness)).mpr hmean
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  by_cases hsmall : value ≤ 1
  · rw [tsub_eq_zero_of_le hsmall, mul_zero, zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
      ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal)]
  · have hlarge : 1 ≤ value := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hvalue, ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal - 8 / 5)]

theorem uniformWordAverage_fixedFull_unit_excess_le :
    uniformWordAverage fixedProposalLength (fun word => fixedFullProposalPrice word - 1) ≤
      (11 / 2 ^ 16 : ENNReal) := by
  let mean := uniformWordAverage fixedProposalLength fixedFullProposalPrice
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) uniformWordAverage_fixedFull_mean_le
  have h := uniformWordAverage_mono fixedProposalLength (fun word =>
    unit_excess_le_square_with_mean (fixedFullProposalPrice word) mean (fixedFullProposalPrice_ne_top word)
      uniformWordAverage_fixedFull_mean_le)
  rw [uniformWordAverage_add, uniformWordAverage_add,
    uniformWordAverage_mul_left, uniformWordAverage_mul_left, uniformWordAverage_const] at h
  have hcancel : (16 / 5 : ENNReal) *
      uniformWordAverage fixedProposalLength (fun word => fixedFullProposalPrice word - 1) ≤ 13 / 25000 := by
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (by finiteness)
    calc
      _ = (16 / 5 : ENNReal) *
          uniformWordAverage fixedProposalLength (fun word => fixedFullProposalPrice word - 1) +
            2 * mean * uniformWordAverage fixedProposalLength fixedFullProposalPrice := by
        change _ = _ + 2 * mean * mean
        ring
      _ ≤ uniformWordAverage fixedProposalLength (fun word => fixedFullProposalPrice word ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 13 / 25000) + mean ^ 2 :=
        add_le_add uniformWordAverage_fixedFull_secondMoment_le le_rfl
      _ = _ := by ring
  have hunit : (5 / 16 : ENNReal) * (16 / 5) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (5 / 16 : ENNReal) * ((16 / 5) *
        uniformWordAverage fixedProposalLength (fun word => fixedFullProposalPrice word - 1)) := by
      rw [← mul_assoc, hunit, one_mul]
    _ ≤ (5 / 16 : ENNReal) * (13 / 25000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]

theorem expected_fixedCertificateGame_full_unit_count_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateStopRule) (hbudget : q ≤ 2 ^ 127)
    (hbound : HasHashQueryBound scheme adversary q) :
    (∑' result, Pr[= result | fixedCertificateGame adversary q Finset.univ stopAfter] *
      certificateBankCount result.1.2.2.2.bank) ≤
        (2 ^ 128 : ENNReal)⁻¹ *
          (∑' result, Pr[= result | fixedCertificateGame adversary q Finset.univ stopAfter] *
            result.1.2.2.2.messageCalls) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) := by
  apply (expected_fixedCertificateGame_count_le_message_excess adversary q Finset.univ stopAfter
    hbudget hbound (2 ^ 128 : ENNReal)⁻¹).trans
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  have hscale (word : List Index) :
      terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹ =
        (2 ^ 128 : ENNReal)⁻¹ * (fixedFullProposalPrice word - 1) := by
    rw [terminalCertificatePrice_full, ENNReal.mul_sub (fun _ _ => by finiteness), mul_one]
  simp_rw [hscale]
  rw [uniformWordAverage_mul_left]
  calc
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (11 / 2 ^ 16 : ENNReal) :=
      mul_le_mul' le_rfl uniformWordAverage_fixedFull_unit_excess_le
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_pow]

theorem expected_certificateCacheGame_full_unit_count_le (adversary : Adversary) (q : Nat)
    (stopAfter : SecretKey → CertificateStopRule) (hq : q ≤ 2 ^ 127)
    (hbound : HasHashQueryBound scheme adversary q) :
    let law := certificateCacheGame adversary q Finset.univ
      (fun key input state length record => proposalPrefixStop input state length record ||
        stopAfter key input state length record) false
    (∑' result, Pr[= result | law] * certificateBankCount result.2.2.2.1.bank) ≤
      (2 ^ 128 : ENNReal)⁻¹ *
        (∑' result, Pr[= result | law] * result.2.2.2.1.messageCalls) +
          (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) := by
  dsimp only
  have h := expected_fixedCertificateGame_full_unit_count_le adversary q stopAfter hq hbound
  unfold fixedCertificateGame at h
  rw [expected_certificateTerminalGame_project adversary q Finset.univ _ false fixedProposalLength
      (fun result => certificateBankCount result.2.2.2.bank),
    expected_certificateTerminalGame_project adversary q Finset.univ _ false fixedProposalLength
      (fun result => (result.2.2.2.messageCalls : ENNReal))] at h
  have hbank := expected_certificateCacheGame_project adversary q Finset.univ
    (fun key input state length record => proposalPrefixStop input state length record ||
      stopAfter key input state length record) false (fun result => certificateBankCount result.2.2.2.bank)
  have hmessage := expected_certificateCacheGame_project adversary q Finset.univ
    (fun key input state length record => proposalPrefixStop input state length record ||
      stopAfter key input state length record) false (fun result => (result.2.2.2.messageCalls : ENNReal))
  change (∑' result : CertificateCacheGameResult, Pr[= result | _] * certificateBankCount result.2.2.2.1.bank) = _ at hbank
  change (∑' result : CertificateCacheGameResult, Pr[= result | _] * (result.2.2.2.1.messageCalls : ENNReal)) = _ at hmessage
  rw [hbank, hmessage]
  exact h

end SphincsSecurity.Concrete
