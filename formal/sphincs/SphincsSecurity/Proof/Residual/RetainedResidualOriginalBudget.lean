import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeVerifierSource
import SphincsSecurity.Proof.Residual.RetainedResidualEnvelope
import SphincsSecurity.Proof.Residual.RetainedResidualInitial
import SphincsSecurity.Proof.Residual.RetainedResidualMessagePayment
import SphincsSecurity.Proof.Residual.RetainedResidualResources
import SphincsSecurity.Proof.Residual.RetainedWorldCoverBudget

/-! ## PublicSigningInitial -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting UniformTableCompletion
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem initialKnown_root (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words)
    (labels : Labels) (hlabels : complete (initialAllowed words exposedValues) labels ≠ 0)
    (high : CanonicalGraphHighHalves) :
    knownRoot (initialKnown words exposedValues) = canonicalGraphRoot (coordinateGraphLabels labels high) := by
  apply knownRoot_eq (coordinateOtsSecrets labels) (coordinateFtsSecrets labels)
    (coordinateGraphLabels labels high) words (fun _ _ _ => False)
  rw [coordinateGraphLabels_value]
  exact initialKnown_agrees words exposedValues labels hlabels

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (unloggedRetainedRestComputation liftOracleWorldLeft)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  gameInputs initialAllowed initialKnown referenceFamilyWords
  simulateQ adversaryImpl unloggedRetainedRestComputation environment lazyRun
set_option backward.isDefEq.respectTransparency false

theorem sourceInputs_bind_subset {A B : Type} (key : SecretKey) (inputs : Finset HashInput)
    (first : OracleComp (OracleWorld + SigningSpec) A) (next : A → OracleComp (OracleWorld + SigningSpec) B)
    (hfirst : sourceInputs key first ⊆ inputs) (hnext : ∀ value, sourceInputs key (next value) ⊆ inputs) :
    sourceInputs key (first >>= next) ⊆ inputs := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input tail ih =>
      rw [bind_assoc, sourceInputs_query_bind]
      apply Finset.union_subset
      · exact (requestInputs_subset key input tail).trans hfirst
      · intro row hrow
        obtain ⟨answer, _, hrow⟩ := Finset.mem_biUnion.mp hrow
        exact ih answer ((sourceInputs_next_subset key input tail answer).trans hfirst) hrow

theorem sourceInputs_world (key : SecretKey) {Result : Type} (computation : OracleComp OracleWorld Result) :
    sourceInputs key (liftOracleWorldLeft computation) = hashInputs computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftOracleWorldLeft, liftM_pure, sourceInputs_pure, hashInputs_pure]
  | query_bind input next ih =>
      rw [FtsProbeSimulation.liftOracleWorldLeft_query_bind, sourceInputs_query_bind, hashInputs_query_bind]
      simp only [ih, requestInputs]
      rw [← bind_pure (liftM (OracleWorld.query input)), hashInputs_query_bind]
      have hempty : (Finset.univ.biUnion fun _ : OracleWorld.Range input => (∅ : Finset HashInput)) = ∅ := by
        ext row
        simp
      simp only [hashInputs_pure, hempty, Finset.union_empty]
      cases input <;> rfl

theorem sourceInputs_unlogged_subset_gameInputs (adversary : Adversary) (key : SecretKey) :
    sourceInputs key (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) ⊆ gameInputs adversary := by
  rw [unloggedRetainedRestComputation]
  apply sourceInputs_bind_subset key (gameInputs adversary) _ _ (sourceInputs_subset_gameInputs adversary key)
  intro forgery
  apply sourceInputs_bind_subset
  · rw [sourceInputs_world]
    exact verifyInputs_subset_gameInputs adversary key forgery
  · intro checked
    rw [sourceInputs_pure]
    exact Finset.empty_subset _

theorem referenceEncodingAuxiliary_support_seed (inputs : Finset HashInput) (encoding : ReferenceEncodingAuxiliary)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support) (seed : inputs → HashOutput) :
    (⟨encoding.selections, encoding.rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support := by
  rw [referenceEncodingAuxiliarySample, PMF.mem_support_bind_iff] at hencoding
  obtain ⟨selections, hs, hencoding⟩ := hencoding
  rw [PMF.mem_support_map_iff] at hencoding
  obtain ⟨rows, hr, rfl⟩ := hencoding
  rw [referenceAuxiliarySample, PMF.mem_support_bind_iff]
  refine ⟨selections, hs, ?_⟩
  rw [PMF.mem_support_bind_iff]
  refine ⟨rows, hr, ?_⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨seed, by simp, rfl⟩

theorem observedInitialSource_hashCalls_le (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (inputs : Finset HashInput) (hcanonical : canonicalEncodingInputs parameter ⊆ inputs)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (seed : inputs → HashOutput)
    (dummy : OtsReferenceWords) (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy))
    (high : CanonicalGraphHighHalves) (labels : Labels)
    (hlabels : UniformTableCompletion.complete (initialAllowed (referenceFamilyWords encoding.selections dummy) exposed) labels ≠ 0)
    (adversary : Adversary)
    (hinputs : ∀ key : SecretKey, sourceInputs key (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) ⊆ inputs)
    (q : Nat) (hq : HasHashQueryBound scheme adversary q) (result : Option (Forgery × Bool) × State inputs)
    (hresult : observedRun
      (environment parameter inputs hcanonical (referenceFamilyWords encoding.selections dummy)
        (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high) encoding.selections encoding.rows)
      labels seed
      (simulateQ (adversaryImpl inputs parameter (knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
        (referenceFamilyWords encoding.selections dummy) encoding.selections)
        (unloggedRetainedRestComputation adversary ⟨knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed), parameter⟩))
      (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) result ≠ 0) :
    result.2.memory.external.hashCalls ≤ q := by
  let auxiliary : ReferenceAuxiliary inputs := ⟨encoding.selections, encoding.rows, seed⟩
  have hauxiliary := referenceEncodingAuxiliary_support_seed inputs encoding hencoding seed
  let context := initialContext parameter inputs hcanonical auxiliary hauxiliary dummy exposed high labels
  have hroot : context.key.root = canonicalGraphRoot context.graph :=
    initialKnown_root (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
  obtain ⟨hcost, hbound⟩ := context.rest_queryBound hroot hparameter adversary q hq
  have hsource := FtsProbeSimulation.expanded_unloggedRetainedRest_queryBound context.oracle adversary context.key (q - 1212415) hbound
  have hcompatible : Compatible context (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed).memory := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [context, auxiliary, Context.words, Context.actual, initialContext, coordinateGraphLabels_value, initialState, initialMemory] using
        initialKnown_agrees (referenceFamilyWords encoding.selections dummy) exposed labels hlabels
    · exact initialKnown_graphReplies (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
  have hrun : observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections)
        (unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩))
      (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) result ≠ 0 := by
    simpa only [context, auxiliary, Context.environment, Context.actual, Context.words, initialContext, coordinateGraphLabels_value] using hresult
  have h := observedRun_source_hashCalls_le context (unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)
    (hinputs context.key) (q - 1212415) hsource
    (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) (initialState_rowsCovered _ _ exposed)
    hcompatible result hrun
  simp only [initialState, initialMemory] at h
  omega

private theorem lazyRun_observed_support {Result : Type} (inputs : Finset HashInput)
    (runEnvironment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs Memory)
    (computation : OracleComp (World inputs) Result) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (result : Option Result × State inputs)
    (hresult : lazyRun runEnvironment computation state result ≠ 0) :
    ∃ labels seed, UniformTableCompletion.complete state.candidates labels ≠ 0 ∧
      observedRun runEnvironment labels seed computation state result ≠ 0 := by
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨labels, hlabels, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  exact ⟨labels, seed, hlabels, hresult⟩

theorem initialState_completion (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposed : InitialPublicLabels words) :
    UniformTableCompletion.complete (initialState inputs words exposed).candidates =
      UniformTableCompletion.complete (initialAllowed words exposed) := rfl

theorem lazyInitialSource_hashCalls_le (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (inputs : Finset HashInput) (hcanonical : canonicalEncodingInputs parameter ⊆ inputs) (adversary : Adversary)
    (hinputs : ∀ key : SecretKey, sourceInputs key (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) ⊆ inputs)
    (encoding : ReferenceEncodingAuxiliary)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (q : Nat) (hq : HasHashQueryBound scheme adversary q)
    (result : Option (Forgery × Bool) × State inputs)
    (hresult : lazyRun
      (environment parameter inputs hcanonical
        (referenceFamilyWords encoding.selections dummy) (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
        encoding.selections encoding.rows)
      (simulateQ (adversaryImpl inputs parameter (knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
        (referenceFamilyWords encoding.selections dummy) encoding.selections)
        (unloggedRetainedRestComputation adversary ⟨knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed), parameter⟩))
      (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) result ≠ 0) :
    result.2.memory.external.hashCalls ≤ q := by
  obtain ⟨labels, seed, hlabels, hresult⟩ := lazyRun_observed_support inputs _ _ _
    (initialAllowed_nonempty _ exposed) result hresult
  rw [initialState_completion] at hlabels
  exact observedInitialSource_hashCalls_le parameter hparameter inputs
    hcanonical encoding hencoding seed dummy exposed high labels hlabels adversary hinputs q hq result hresult

variable (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
  (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
  (q : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)

noncomputable def initialMonitoredSource : SPMF (Option (Forgery × Bool) × MonitoredState (gameInputs adversary)) :=
  monitoredRun key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor 1212415 stopped)

theorem initialMonitoredSource_hashCalls_le (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hq : HasHashQueryBound scheme adversary q)
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped result ≠ 0) :
    result.2.1.memory.external.hashCalls ≤ q := by
  unfold initialMonitoredSource at hresult
  have hnative := map_nonzero _ (fun result => (result.1, result.2.1)) result hresult
  rw [monitoredRun_erasure, hroot] at hnative
  exact lazyInitialSource_hashCalls_le key.parameter hparameter (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) adversary
    (sourceInputs_unlogged_subset_gameInputs adversary) encoding hencoding dummy exposed high q hq (result.1, result.2.1) hnative

theorem initialMonitoredSource_resources
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped result ≠ 0) :
    MonitorResources result.2.2 result.2.1.memory :=
  monitoredRun_resources key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor 1212415 stopped)
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key) ⟨le_rfl, bot_le, Nat.zero_le _⟩ result hresult

theorem initialMonitoredSource_creationMass_le (hparameter : key.parameter ∈ support sampleParameter)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hq : HasHashQueryBound scheme adversary q)
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped result ≠ 0) :
    result.2.2.creationMass ≤ (q : ENNReal) :=
  (initialMonitoredSource_resources key adversary encoding dummy exposed high q required stopAfter stopped result hresult).2.1.trans
    (Nat.cast_le.mpr (initialMonitoredSource_hashCalls_le key adversary encoding dummy exposed high q required stopAfter stopped
      hparameter hencoding hroot hq result hresult))

theorem expected_initialMonitoredSource_count_le_creationCost :
    (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] *
      certificateBankCount result.2.2.bank) ≤
    ∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] *
      result.2.2.creationCost :=
  expected_monitoredRun_count_le_creationCost key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed) 1212415 stopped
    (initialAllowed_nonempty _ exposed) (initialState_rowsCovered _ _ exposed)
    (sourceInputs_unlogged_subset_gameInputs adversary key) (fun _ _ => rfl)

theorem expected_initialMonitoredSource_creationMass_le_messageCalls :
    (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] *
      result.2.2.creationMass) ≤
    ∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] *
      result.2.1.memory.messageCalls.length := by
  have hpayment := expected_monitoredRun_creationMass_le_messageCalls key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed) 1212415 stopped
    (initialAllowed_nonempty _ exposed) (initialState_rowsCovered _ _ exposed)
    (sourceInputs_unlogged_subset_gameInputs adversary key)
  apply hpayment.trans
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] = 0
  · change Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped] * _ ≤ _
    simp only [hr, zero_mul, le_refl]
  · rw [SPMF.probOutput_eq_apply] at hr
    exact mul_le_mul' le_rfl (Nat.cast_le.mpr
      (initialMonitoredSource_resources key adversary encoding dummy exposed high q required stopAfter stopped result hr).2.2)

end SphincsSecurity.Concrete.RetainedResidual
