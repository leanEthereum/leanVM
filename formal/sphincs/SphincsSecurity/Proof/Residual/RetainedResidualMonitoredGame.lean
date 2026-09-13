import SphincsSecurity.Proof.Residual.RetainedResidualCertificateTransfer
import SphincsSecurity.Proof.Residual.RetainedResidualGameTransfer
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop signAfterDigest gameInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def initialMonitoredPrior (parameter : PublicParameter) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (stopAfter : CertificateStopRule) : SPMF (Option (Forgery × Bool) × MonitoredState (gameInputs adversary)) := do
  let words := referenceFamilyWords encoding.selections dummy
  let labels ← UniformTableCompletion.complete (initialAllowed words exposed)
  let key : SecretKey := ⟨parameter, knownRoot (initialKnown words exposed), coordinateOtsSecrets labels, coordinateFtsSecrets labels⟩
  initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) false

theorem initialMonitoredPrior_erasure (parameter : PublicParameter) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (stopAfter : CertificateStopRule) :
    (fun result => (result.1, result.2.1)) <$> initialMonitoredPrior parameter adversary encoding dummy exposed high budget stopAfter =
      lazyRun
        (environment parameter (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary parameter)
          (referenceFamilyWords encoding.selections dummy)
          (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
          encoding.selections encoding.rows)
        (simulateQ (adversaryImpl (gameInputs adversary) parameter
          (knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
          (referenceFamilyWords encoding.selections dummy) encoding.selections)
          (FtsProbeSimulation.unloggedRetainedRestComputation adversary
            ⟨knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed), parameter⟩))
        (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed) := by
  simp only [initialMonitoredPrior, map_bind, initialMonitoredSource, monitoredRun_erasure]
  rw [UniformTableCompletion.complete_of_nonempty _ (initialAllowed_nonempty _ exposed)]
  exact RetainedObservation.lift_bind_const _
    (lazyRun
      (environment parameter (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary parameter)
        (referenceFamilyWords encoding.selections dummy)
        (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
        encoding.selections encoding.rows)
      (simulateQ (adversaryImpl (gameInputs adversary) parameter
        (knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
        (referenceFamilyWords encoding.selections dummy) encoding.selections)
        (FtsProbeSimulation.unloggedRetainedRestComputation adversary
          ⟨knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed), parameter⟩))
      (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed))

noncomputable def monitoredSourceGame (dummy : OtsReferenceWords) (adversary : Adversary)
    (budget : Nat) (stopAfter : CertificateStopRule) : SPMF (Option (Forgery × Bool) × MonitoredState (gameInputs adversary)) := do
  let parameter ← 𝒟[sampleParameter]
  let encoding ← 𝒟[referenceEncodingAuxiliarySample]
  let words := referenceFamilyWords encoding.selections dummy
  let high ← 𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves]
  let exposed ← 𝒟[PMF.uniformOfFintype (InitialPublicLabels words)]
  initialMonitoredPrior parameter adversary encoding dummy exposed high budget stopAfter

theorem monitoredSourceGame_erasure (dummy : OtsReferenceWords) (adversary : Adversary)
    (budget : Nat) (stopAfter : CertificateStopRule) :
    (fun result => (result.1, result.2.1)) <$> monitoredSourceGame dummy adversary budget stopAfter = sourceGame dummy adversary := by
  simp only [monitoredSourceGame, map_bind, initialMonitoredPrior_erasure, sourceGame]

private theorem probEvent_bind_add_le_const_add {A B : Type} (law : SPMF A) (next : A → SPMF B)
    (left right exception : B → Prop) (bound : ENNReal)
    (h : ∀ value, law value ≠ 0 → Pr[left | next value] + Pr[right | next value] ≤ bound + Pr[exception | next value]) :
    Pr[left | law >>= next] + Pr[right | law >>= next] ≤ bound + Pr[exception | law >>= next] := by
  simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add, ← mul_add]
  calc
    _ ≤ ∑' value, Pr[= value | law] * (bound + Pr[exception | next value]) := by
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases hvalue : law value = 0
      · simp only [SPMF.probOutput_eq_apply, hvalue, zero_mul, le_refl]
      exact mul_le_mul' le_rfl (h value hvalue)
    _ = (∑' value, Pr[= value | law]) * bound + ∑' value, Pr[= value | law] * Pr[exception | next value] := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

theorem monitoredSourceGame_stop_add_strong_le (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) (adversary : Adversary)
    (budget : Nat) (stopAfter : CertificateStopRule)
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127) :
    Pr[fun result => result.1 = none | monitoredSourceGame dummy adversary budget stopAfter] +
      Pr[MonitoredStrongWin | monitoredSourceGame dummy adversary budget stopAfter] ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
        Pr[MonitoredStrongException | monitoredSourceGame dummy adversary budget stopAfter] := by
  unfold monitoredSourceGame
  apply probEvent_bind_add_le_const_add
  intro parameter hparameter
  have hparameter' : parameter ∈ support sampleParameter := (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hparameter
  apply probEvent_bind_add_le_const_add
  intro encoding hencoding
  have hencoding' : encoding ∈ referenceEncodingAuxiliarySample.support := by
    apply (PMF.mem_support_iff _ _).mpr
    simpa only [PMF.evalDist_eq, SPMF.liftM_apply] using hencoding
  apply probEvent_bind_add_le_const_add
  intro high _
  apply probEvent_bind_add_le_const_add
  intro exposed _
  unfold initialMonitoredPrior
  apply probEvent_bind_add_le_const_add
  intro labels _
  exact initialMonitoredSource_stop_add_strong_le _ adversary encoding dummy hdummy exposed high budget stopAfter false
    hparameter' hencoding' rfl hcost hbudget

theorem forgeAdvantage_le_monitored_bound_add_exception (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) (adversary : Adversary)
    (budget : Nat) (stopAfter : CertificateStopRule)
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
        Pr[MonitoredStrongException | monitoredSourceGame dummy adversary budget stopAfter] := by
  have h := forgeAdvantage_le_source_stop_add_win dummy adversary
  rw [← monitoredSourceGame_erasure dummy adversary budget stopAfter, probEvent_map, probEvent_map] at h
  exact h.trans (monitoredSourceGame_stop_add_strong_le dummy hdummy adversary budget stopAfter hcost hbudget)

end SphincsSecurity.Concrete.RetainedResidual
