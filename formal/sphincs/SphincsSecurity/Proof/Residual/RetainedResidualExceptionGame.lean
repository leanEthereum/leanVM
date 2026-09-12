import SphincsSecurity.Proof.Residual.RetainedResidualExceptionClassification
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredGame
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs gameInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def initialExceptionHistorySource (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) : SPMF (Option (Forgery × Bool) × ExceptionHistoryState (gameInputs adversary)) :=
  exceptionHistoryRun key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ (proposalStop (fun _ _ _ _ => false))
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    ((initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor 1212415 false), (false, false))

theorem initialExceptionHistorySource_erasure (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) :
    (fun result => (result.1, result.2.1)) <$> initialExceptionHistorySource key adversary encoding dummy exposed high budget =
      initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop (fun _ _ _ _ => false)) false := by
  exact exceptionHistoryRun_erasure _ _ _ _ _ _ _ _ _ _ _ _

theorem initialExceptionHistorySource_exception (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127)
    (result : Option (Forgery × Bool) × ExceptionHistoryState (gameInputs adversary))
    (hresult : initialExceptionHistorySource key adversary encoding dummy exposed high budget result ≠ 0)
    (hexception : MonitoredStrongException (result.1, result.2.1)) :
    result.2.2.1 = true ∨ result.2.2.2 = true := by
  by_contra hflags
  have hclean : result.2.2 = (false, false) := by
    rcases hf : result.2.2 with ⟨cache, proposals⟩
    cases cache <;> cases proposals <;> simp_all only [Bool.false_eq_true, or_self, not_false_eq_true, not_true_eq_false,
      or_true, true_or]
  obtain ⟨⟨value, hvalue, hwin⟩, hstop⟩ := hexception
  have hlive : result.1 ≠ none := by rw [hvalue]; exact Option.some_ne_none _
  have hlog : result.2.1.1.memory.log.length ≤ signatureLimit := by
    simp only [sourceVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1.1
  have hnative := map_nonzero _ (fun result => (result.1, result.2.1)) result hresult
  rw [initialExceptionHistorySource_erasure] at hnative
  have hbound := initialMonitoredSource_hashCalls_le key adversary encoding dummy exposed high budget Finset.univ
    (proposalStop (fun _ _ _ _ => false)) false hparameter hencoding hroot hcost (result.1, result.2.1) hnative
  have halive := exceptionHistoryRun_unstopped key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ _ _
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key) (fun _ => rfl)
    (monitoredBankComplete_initial key (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) Finset.univ exposed 1212415 false)
    (show CacheSizeBound (initialMemory (referenceFamilyWords encoding.selections dummy) exposed) from by
      change QueryCache.enncard (∅ : QueryCache HashSpec) ≤ (1212415 : ENNReal)
      rw [QueryCache.enncard_empty]
      exact zero_le)
    (by intro entry hentry; cases hentry) rfl hbudget result hresult hlive hbound hlog hclean
  simp only [halive, Bool.false_eq_true] at hstop

noncomputable def initialExceptionHistoryPrior (parameter : PublicParameter) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) : SPMF (Option (Forgery × Bool) × ExceptionHistoryState (gameInputs adversary)) := do
  let words := referenceFamilyWords encoding.selections dummy
  let labels ← UniformTableCompletion.complete (initialAllowed words exposed)
  let key : SecretKey := ⟨parameter, knownRoot (initialKnown words exposed), coordinateOtsSecrets labels, coordinateFtsSecrets labels⟩
  initialExceptionHistorySource key adversary encoding dummy exposed high budget

theorem initialExceptionHistoryPrior_erasure (parameter : PublicParameter) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) :
    (fun result => (result.1, result.2.1)) <$> initialExceptionHistoryPrior parameter adversary encoding dummy exposed high budget =
      initialMonitoredPrior parameter adversary encoding dummy exposed high budget (fun _ _ _ _ => false) := by
  simp only [initialExceptionHistoryPrior, initialMonitoredPrior, map_bind, initialExceptionHistorySource_erasure]

noncomputable def exceptionHistorySourceGame (dummy : OtsReferenceWords) (adversary : Adversary)
    (budget : Nat) : SPMF (Option (Forgery × Bool) × ExceptionHistoryState (gameInputs adversary)) := do
  let parameter ← 𝒟[sampleParameter]
  let encoding ← 𝒟[referenceEncodingAuxiliarySample]
  let words := referenceFamilyWords encoding.selections dummy
  let high ← 𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves]
  let exposed ← 𝒟[PMF.uniformOfFintype (InitialPublicLabels words)]
  initialExceptionHistoryPrior parameter adversary encoding dummy exposed high budget

theorem exceptionHistorySourceGame_erasure (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat) :
    (fun result => (result.1, result.2.1)) <$> exceptionHistorySourceGame dummy adversary budget =
      monitoredSourceGame dummy adversary budget (fun _ _ _ _ => false) := by
  simp only [exceptionHistorySourceGame, monitoredSourceGame, map_bind, initialExceptionHistoryPrior_erasure]

theorem exceptionHistorySourceGame_exception (dummy : OtsReferenceWords) (adversary : Adversary)
    (budget : Nat) (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127)
    (result : Option (Forgery × Bool) × ExceptionHistoryState (gameInputs adversary))
    (hresult : exceptionHistorySourceGame dummy adversary budget result ≠ 0)
    (hexception : MonitoredStrongException (result.1, result.2.1)) :
    result.2.2.1 = true ∨ result.2.2.2 = true := by
  rw [exceptionHistorySourceGame, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨parameter, hparameter, hresult⟩ := hresult
  have hparameter' : parameter ∈ support sampleParameter := (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hparameter
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨encoding, hencoding, hresult⟩ := hresult
  have hencoding' : encoding ∈ referenceEncodingAuxiliarySample.support := by
    apply (PMF.mem_support_iff _ _).mpr
    simpa only [PMF.evalDist_eq, SPMF.liftM_apply] using hencoding
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨high, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨exposed, _, hresult⟩ := hresult
  rw [initialExceptionHistoryPrior, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨labels, _, hresult⟩ := hresult
  exact initialExceptionHistorySource_exception _ adversary encoding dummy exposed high budget
    hparameter' hencoding' rfl hcost hbudget result hresult hexception

theorem monitoredSourceGame_exception_le_history (dummy : OtsReferenceWords) (adversary : Adversary)
    (budget : Nat) (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127) :
    Pr[MonitoredStrongException | monitoredSourceGame dummy adversary budget (fun _ _ _ _ => false)] ≤
      Pr[fun result => result.2.2.1 = true | exceptionHistorySourceGame dummy adversary budget] +
      Pr[fun result => result.2.2.2 = true | exceptionHistorySourceGame dummy adversary budget] := by
  rw [← exceptionHistorySourceGame_erasure dummy adversary budget, probEvent_map]
  apply le_trans ?_ (probEvent_or_le _ _ _)
  apply probEvent_mono
  intro result hsupport hexception
  have hresult := probOutput_ne_zero_of_mem_support hsupport
  rw [SPMF.probOutput_eq_apply] at hresult
  exact exceptionHistorySourceGame_exception dummy adversary budget hcost hbudget result hresult hexception

theorem forgeAdvantage_le_native_bound_add_histories (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf)) (adversary : Adversary)
    (budget : Nat) (hcost : HasHashQueryBound scheme adversary budget) (hbudget : budget ≤ 2 ^ 127) :
    forgeAdvantage scheme adversary ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
        (Pr[fun result => result.2.2.1 = true | exceptionHistorySourceGame dummy adversary budget] +
          Pr[fun result => result.2.2.2 = true | exceptionHistorySourceGame dummy adversary budget]) :=
  (forgeAdvantage_le_monitored_bound_add_exception dummy hdummy adversary budget (fun _ _ _ _ => false) hcost hbudget).trans
    (add_le_add le_rfl (monitoredSourceGame_exception_le_history dummy adversary budget hcost hbudget))

end SphincsSecurity.Concrete.RetainedResidual
