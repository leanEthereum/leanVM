import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FixedProposalMoments
import SphincsSecurity.Proof.Fts.TerminalCertificateCharge
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

noncomputable def fixedCertificateGame (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) :
    PMF (CertificateGameResult × List Index) :=
  certificateTerminalGame adversary budget required
    (fun key input state length record =>
      proposalPrefixStop input state length record || stopAfter key input state length record)
    false fixedProposalLength

theorem uniformWordAverage_eq_independent {α : Type} [SampleableType α] [Fintype α] [Nonempty α]
    (steps : Nat) (payoff : List α → ENNReal) :
    uniformWordAverage steps payoff =
      ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype α) steps] * payoff word := by
  simp only [uniformWordAverage, probOutput_def, evalDist_sampleUniformProposalWord, PMF.evalDist_eq]

theorem expected_fixedCertificateGame_count_le_message_excess (adversary : Adversary)
    (q : Nat) (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) (baseline : ENNReal) :
    (∑' result, Pr[= result | fixedCertificateGame adversary q required stopAfter] *
      certificateBankCount result.1.2.2.2.bank) ≤
        baseline * (∑' result, Pr[= result | fixedCertificateGame adversary q required stopAfter] *
          result.1.2.2.2.messageCalls) +
          (q : ENNReal) * uniformWordAverage fixedProposalLength
            (fun word => terminalCertificatePrice required word - baseline) := by
  let law := fixedCertificateGame adversary q required stopAfter
  have hmass :
      (∑' result, Pr[= result | law] * result.1.2.2.2.creationMass) ≤
        ∑' result, Pr[= result | law] * result.1.2.2.2.messageCalls := by
    change (∑' result, Pr[= result | certificateTerminalGame adversary q required _ false fixedProposalLength] *
      result.1.2.2.2.creationMass) ≤ _
    rw [expected_certificateTerminalGame_project adversary q required _ false fixedProposalLength
      (fun result => result.2.2.2.creationMass)]
    change _ ≤ ∑' result, Pr[= result | certificateTerminalGame adversary q required _ false fixedProposalLength] *
      (result.1.2.2.2.messageCalls : ENNReal)
    rw [expected_certificateTerminalGame_project adversary q required _ false fixedProposalLength
      (fun result => (result.2.2.2.messageCalls : ENNReal))]
    exact expected_certificateGame_creationMass_le_messageCalls adversary q required _ false
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        (result.1.2.2.2.creationMass * terminalCertificatePrice required result.2) := by
      simpa [fixedCertificateGame, law, fixedProposalLength] using
        expected_certificateTerminalGame_count_le_mass_price adversary q fixedProposalLength required stopAfter hbudget
    _ ≤ ∑' result, Pr[= result | law] *
        (result.1.2.2.2.creationMass * (baseline + (terminalCertificatePrice required result.2 - baseline))) := by
      apply ENNReal.tsum_le_tsum
      intro result
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl le_add_tsub)
    _ = baseline * (∑' result, Pr[= result | law] * result.1.2.2.2.creationMass) +
        ∑' result, Pr[= result | law] *
          (result.1.2.2.2.creationMass * (terminalCertificatePrice required result.2 - baseline)) := by
      simp_rw [mul_add, ENNReal.tsum_add]
      congr 1
      calc
        _ = ∑' result, baseline * (Pr[= result | law] * result.1.2.2.2.creationMass) := by
          apply tsum_congr
          intro result
          ring
        _ = _ := ENNReal.tsum_mul_left
    _ ≤ _ := by
      apply add_le_add (mul_le_mul' le_rfl hmass)
      rw [uniformWordAverage_eq_independent]
      exact expected_certificateTerminalGame_mass_payoff_le adversary q required _ false fixedProposalLength hbound _

private theorem terminalCertificatePrice_factor (required : Finset FtsTree) (word : List Index) :
    terminalCertificatePrice required word =
      ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        targetCertificateScale required) * proposalPowerSum required.card word := by
  unfold terminalCertificatePrice proposalPowerSum
  ring

theorem terminalCertificatePrice_full (word : List Index) :
    terminalCertificatePrice Finset.univ word = (2 ^ 128 : ENNReal)⁻¹ * fixedFullProposalPrice word := by
  have htrees : Fintype.card FtsTree = 14 := Fintype.card_fin _
  have hindex : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  have hleaf : Fintype.card FtsLeaf = 2 ^ 10 := Fintype.card_fin _
  rw [terminalCertificatePrice_factor, Finset.card_univ, htrees]
  have hcoefficient :
      ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        targetCertificateScale Finset.univ) = (2 ^ 128 : ENNReal)⁻¹ * (2 ^ 48 : ENNReal)⁻¹ := by
    unfold targetCertificateScale
    rw [Finset.card_univ, htrees, hindex, hleaf]
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ftsTreeHeight, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
  rw [hcoefficient, fixedFullProposalPrice, mul_assoc]

end SphincsSecurity.Concrete
