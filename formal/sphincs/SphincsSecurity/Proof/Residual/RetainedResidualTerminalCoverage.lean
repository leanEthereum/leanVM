import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualOriginalBudget
import SphincsSecurity.Proof.Residual.RetainedResidualProposalPayment
import SphincsSecurity.Proof.Fts.UnitCertificateCoverage
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (unloggedRetainedRestComputation)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem terminalProposalPotential_le_baseline_excess (total : Nat) (payoff : List Index → ENNReal)
    (baseline : ENNReal) (consumed : List Index) :
    terminalProposalPotential (PMF.uniformOfFintype Index) total payoff consumed ≤
      baseline + terminalProposalPotential (PMF.uniformOfFintype Index) total (fun word => payoff word - baseline) consumed := by
  unfold terminalProposalPotential
  calc
    _ ≤ ∑' word, Pr[= word | completeProposalWord (PMF.uniformOfFintype Index) total consumed] *
        (baseline + (payoff word - baseline)) :=
      ENNReal.tsum_le_tsum fun word => mul_le_mul' le_rfl le_add_tsub
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]

theorem terminalProposalPotential_empty (total : Nat) (payoff : List Index → ENNReal) :
    terminalProposalPotential (PMF.uniformOfFintype Index) total payoff [] = uniformWordAverage total payoff := by
  simp only [terminalProposalPotential, uniformWordAverage, completeProposalWord_nil, probOutput_def,
    evalDist_sampleUniformProposalWord, PMF.evalDist_eq]

theorem expected_weighted_terminalPotential_le {Result : Type} (law : SPMF Result)
    (consumed : Result → List Index) (mass : Result → ENNReal) (bound baseline : ENNReal)
    (hmass : ∀ result, law result ≠ 0 → mass result ≤ bound) (total : Nat) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | law] *
      (mass result * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff (consumed result))) ≤
        baseline * (∑' result, Pr[= result | law] * mass result) +
          bound * ∑' result, Pr[= result | law] *
            terminalProposalPotential (PMF.uniformOfFintype Index) total (fun word => payoff word - baseline) (consumed result) := by
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        (baseline * mass result + bound *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (fun word => payoff word - baseline) (consumed result)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | law] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        calc
          _ ≤ mass result * (baseline + terminalProposalPotential (PMF.uniformOfFintype Index) total
              (fun word => payoff word - baseline) (consumed result)) :=
            mul_le_mul' le_rfl (terminalProposalPotential_le_baseline_excess total payoff baseline (consumed result))
          _ ≤ _ := by
            rw [mul_add, mul_comm (mass result) baseline]
            exact add_le_add le_rfl (mul_le_mul' (hmass result (by rwa [SPMF.probOutput_eq_apply] at hr)) le_rfl)
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ baseline, mul_left_comm _ bound, ENNReal.tsum_mul_left]

theorem uniformWordAverage_full_price_excess_le :
    uniformWordAverage fixedProposalLength
      (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹) ≤ (11 / 2 ^ 144 : ENNReal) := by
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

theorem expected_initialMonitoredSource_full_unit_count_le
    (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (q : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hparameter : key.parameter ∈ support sampleParameter) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hq : HasHashQueryBound scheme adversary q) (hbudget : q ≤ 2 ^ 127) :
    (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] *
      certificateBankCount result.2.2.bank) ≤
        (2 ^ 128 : ENNReal)⁻¹ *
          (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] *
            result.2.1.memory.messageCalls.length) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) := by
  let state : ProposalState (gameInputs adversary) :=
    ([], initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed, initialCertificateMonitor 1212415 stopped)
  let law := proposalRun key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter)
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) state
  have hvalid : MonitoredValid (gameInputs adversary) state.2 :=
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
  have hinv : ProposalInvariant key fixedProposalLength state :=
    certificateProposalInvariant_initial key fixedProposalLength 1212415 _ stopped (fun _ => le_rfl)
  have hproject : Prod.map id Prod.snd <$> law =
      initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped :=
    proposalRun_erasure key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
      (referenceFamilyWords encoding.selections dummy)
      (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
      encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter) _ state
  have herase (weight : Option (Forgery × Bool) × MonitoredState (gameInputs adversary) → ENNReal) :
      (∑' result, Pr[= result | law] * weight (Prod.map id Prod.snd result)) =
        ∑' result, Pr[= result |
          initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] * weight result := by
    have h := congrArg (fun p => ∑' result, Pr[= result | p] * weight result) hproject
    rw [tsum_probOutput_map_mul] at h
    exact h
  have hmass : ∀ result, law result ≠ 0 → result.2.2.2.creationMass ≤ (q : ENNReal) := by
    intro result hresult
    have h := map_nonzero law (Prod.map id Prod.snd) result hresult
    rw [hproject] at h
    exact initialMonitoredSource_creationMass_le key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped
      hparameter hencoding hroot hq _ h
  have hcost := expected_proposalRun_creationCost_le_mass_terminalPotential key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ stopAfter fixedProposalLength
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) state hvalid
    (sourceInputs_unlogged_subset_gameInputs adversary key) hbudget hinv
  have huniform := expected_proposalRun_terminalPotential key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter)
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) state hvalid
    (sourceInputs_unlogged_subset_gameInputs adversary key) fixedProposalLength
    (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹)
  change (∑' result, Pr[= result | law] * terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength
    (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹) result.2.1) = _ at huniform
  have hzero : state.2.2.creationCost = 0 := rfl
  rw [hzero, zero_add] at hcost
  have hempty : state.1 = [] := rfl
  rw [hempty, terminalProposalPotential_empty] at huniform
  calc
    _ ≤ ∑' result, Pr[= result |
        initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] * result.2.2.creationCost :=
      expected_initialMonitoredSource_count_le_creationCost key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped
    _ = ∑' result, Pr[= result | law] * result.2.2.2.creationCost := (herase (fun result => result.2.2.creationCost)).symm
    _ ≤ ∑' result, Pr[= result | law] * (result.2.2.2.creationMass *
        terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength (terminalCertificatePrice Finset.univ) result.2.1) := hcost
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (∑' result, Pr[= result | law] * result.2.2.2.creationMass) +
        (q : ENNReal) * ∑' result, Pr[= result | law] * terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength
          (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹) result.2.1 :=
      expected_weighted_terminalPotential_le law (fun result => result.2.1) (fun result => result.2.2.2.creationMass)
        q (2 ^ 128 : ENNReal)⁻¹ hmass fixedProposalLength (terminalCertificatePrice Finset.univ)
    _ ≤ _ := by
      rw [huniform]
      have hm := herase (fun result => result.2.2.creationMass)
      dsimp only [Prod.map] at hm
      rw [hm]
      exact add_le_add (mul_le_mul' le_rfl
        (expected_initialMonitoredSource_creationMass_le_messageCalls key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped))
        (mul_le_mul' le_rfl uniformWordAverage_full_price_excess_le)

end SphincsSecurity.Concrete.RetainedResidual
